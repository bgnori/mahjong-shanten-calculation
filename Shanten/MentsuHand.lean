import Shanten.Specification
import Shanten.SevenPairs
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.FinCases

namespace Shanten

/-!
# 面子手シャンテン数：証明の地図

このファイルの主な目的は、面子手シャンテン数の仕様と、
完成形の目標を探索する手続きとを結び付けることです。

```text
mentsuHandTargetMinimumSearch hand = some value
  ↔ IsShapeShanten hand .mentsuHand value
```

証明は次の順序で進みます。

1. DP が扱う探索選択と状態を定義する。
2. 使用牌とブロック履歴が一致し、到達可能な状態が手牌を越えないという
   基本不変量を証明する。
3. 抽象的な選択列と、牌種を固定順に走査する探索を関連付ける。
4. 完成目標と、目標までの不足距離を定義する。
5. 不足距離が、完成形に到達するために必要な交換回数と一致することを示す。
6. 面子・ターツ・雀頭による部分的な面子手分解を表現する。
7. 1 種類 4 枚制限を加え、妥当なブロック分解を、同一牌種で複数ブロックを
   処理できるバッチ走査へ埋め込むための局所補題を整備する。
8. 全ターゲットを列挙する既存の有限 DP と、条件付きブロック走査を区別して
   定理化する。後者は、任意の13枚手・全ターゲットをカバーする完全性をまだ
   与えない。
9. 目標距離を最小化し、その最小値を形シャンテン数に結び付ける。
10. 制約付きブロック探索からシャンテン数の証人を取り出す補題を維持する。
    これを全手牌の最小値一致と解釈するには、より一般的な不足ブロック・雀頭なし・
    孤立牌を扱う探索と被覆性の証明が別途必要である。

以下の章は、Lean で必要となる依存関係の順序に従っています。
各章の冒頭の短い説明は、その章の証明全体における役割を示すものであり、
実装上の構造を変更するものではありません。
-/

/-!
## 1. 基本的なデータ構造

ターツ、探索状態、探索で選ぶ項目、および部分ブロックを完成面子に
変換する局所的な操作を導入します。
-/

inductive Taatsu
  | pair (tile : Tile)
  | sequence (suit : Suit) (start : Fin 8)
  deriving DecidableEq, Fintype

/-- The counters carried by the mentsu-hand dynamic program. -/
structure MentsuHandSearchState where
  tileIndex : Nat
  used : Multiset Tile
  pair : Option Tile
  meldHistory : List Meld
  taatsuHistory : List Taatsu
  melds : Nat
  taatsu : Nat
  deriving DecidableEq

/-- One branch of the mentsu-hand decomposition search. -/
inductive MentsuHandChoice
  | skip
  | pair (tile : Tile)
  | taatsu (taatsu : Taatsu)
  | meld (meld : Meld)
  deriving DecidableEq

def taatsuTiles : Taatsu → Multiset Tile
  | .pair tile => pairTiles tile
  | .sequence suit start =>
      Multiset.ofList
        [ Tile.suited suit ⟨start.val, by omega⟩
        , Tile.suited suit ⟨start.val + 1, by omega⟩ ]

def taatsuCompletionTile : Taatsu → Tile
  | .pair tile => tile
  | .sequence suit start =>
      if hstart : start.val ≤ 6 then
        Tile.suited suit ⟨start.val + 2, by omega⟩
      else
        Tile.suited suit ⟨start.val - 1, by omega⟩

def taatsuCompletionMeld : Taatsu → Meld
  | .pair tile => .triplet tile
  | .sequence suit start =>
      .sequence suit
        ⟨if hstart : start.val ≤ 6 then start.val else start.val - 1, by
          by_cases h : start.val ≤ 6 <;> simp [h] <;> omega⟩

lemma taatsuTiles_add_completionTile
    (taatsu : Taatsu) :
    taatsuTiles taatsu + Multiset.replicate 1 (taatsuCompletionTile taatsu) =
      meldTiles (taatsuCompletionMeld taatsu) := by
  cases taatsu with
  | pair tile =>
      simp [taatsuTiles, taatsuCompletionTile, taatsuCompletionMeld,
        pairTiles, meldTiles, Multiset.replicate_succ]
  | sequence suit start =>
      by_cases hstart : start.val ≤ 6
      · simp only [taatsuTiles, taatsuCompletionTile, taatsuCompletionMeld,
          meldTiles, dif_pos hstart]
        change Multiset.ofList
            [ Tile.suited suit ⟨start.val, by omega⟩
            , Tile.suited suit ⟨start.val + 1, by omega⟩ ] +
            Multiset.ofList [Tile.suited suit ⟨start.val + 2, by omega⟩] =
          Multiset.ofList
            [ Tile.suited suit ⟨start.val, by omega⟩
            , Tile.suited suit ⟨start.val + 1, by omega⟩
            , Tile.suited suit ⟨start.val + 2, by omega⟩ ]
        rw [Multiset.coe_add]
        rfl
      · have hstart' : start.val = 7 := by omega
        simp only [taatsuTiles, taatsuCompletionTile, taatsuCompletionMeld,
          meldTiles, dif_neg hstart, hstart', dif_neg (by omega)]
        change Multiset.ofList
            [ Tile.suited suit ⟨7, by omega⟩
            , Tile.suited suit ⟨8, by omega⟩ ] +
            Multiset.ofList [Tile.suited suit ⟨6, by omega⟩] =
          Multiset.ofList
            [ Tile.suited suit ⟨6, by omega⟩
            , Tile.suited suit ⟨7, by omega⟩
            , Tile.suited suit ⟨8, by omega⟩ ]
        rw [Multiset.coe_add]
        apply Multiset.coe_eq_coe.mpr
        exact
          (List.Perm.cons _ (List.Perm.swap _ _ [])).trans
            (List.Perm.swap _ _ _).symm

/-!
## 2. 探索遷移と不変量

選択を一つずつ状態に適用します。ここで証明する中心的な事実は、
妥当な遷移が手牌を越えないことと、到達可能な状態を雀頭・面子・
ターツの履歴から再構成できることです。
-/

def choiceTiles : MentsuHandChoice → Multiset Tile
  | .skip => 0
  | .pair tile => pairTiles tile
  | .taatsu taatsu => taatsuTiles taatsu
  | .meld meld => meldTiles meld

def mentsuHandChoiceRepresentative : MentsuHandChoice → Option Tile
  | .skip => none
  | .pair tile => some tile
  | .taatsu (.pair tile) => some tile
  | .taatsu (.sequence suit start) =>
      some (Tile.suited suit ⟨start.val, by omega⟩)
  | .meld (.triplet tile) => some tile
  | .meld (.sequence suit start) =>
      some (Tile.suited suit ⟨start.val, by omega⟩)

lemma mentsuHandChoiceRepresentative_mem
    {choice : MentsuHandChoice} {tile : Tile}
    (hrep : mentsuHandChoiceRepresentative choice = some tile) :
    tile ∈ choiceTiles choice := by
  cases choice with
  | skip =>
      simp [mentsuHandChoiceRepresentative] at hrep
  | pair pairTile =>
      simp [mentsuHandChoiceRepresentative] at hrep
      subst tile
      simp [choiceTiles, pairTiles]
  | taatsu taatsu =>
      cases taatsu with
      | pair pairTile =>
          simp [mentsuHandChoiceRepresentative] at hrep
          subst tile
          simp [choiceTiles, taatsuTiles, pairTiles]
      | sequence suit start =>
          simp [mentsuHandChoiceRepresentative] at hrep
          subst tile
          simp [choiceTiles, taatsuTiles]
  | meld meld =>
      cases meld with
      | triplet meldTile =>
          simp [mentsuHandChoiceRepresentative] at hrep
          subst tile
          simp [choiceTiles, meldTiles]
      | sequence suit start =>
          simp [mentsuHandChoiceRepresentative] at hrep
          subst tile
          simp [choiceTiles, meldTiles]

def mentsuHandChoicesForTile
    (tile : Tile) : List MentsuHandChoice → List MentsuHandChoice
  | [] => []
  | choice :: choices =>
      if mentsuHandChoiceRepresentative choice = some tile then
        choice :: mentsuHandChoicesForTile tile choices
      else
        mentsuHandChoicesForTile tile choices

lemma mentsuHandChoicesForTile_sublist
    (tile : Tile) (choices : List MentsuHandChoice) :
    List.Sublist (mentsuHandChoicesForTile tile choices) choices := by
  induction choices with
  | nil =>
      exact .slnil
  | cons choice choices ih =>
      by_cases hrep :
          mentsuHandChoiceRepresentative choice = some tile
      · simpa [mentsuHandChoicesForTile, hrep] using
          (List.Sublist.cons_cons choice ih)
      · simpa [mentsuHandChoicesForTile, hrep] using
          (List.Sublist.cons choice ih)

lemma mentsuHandChoicesForTile_representative
    {tile : Tile} {choices : List MentsuHandChoice}
    {choice : MentsuHandChoice}
    (hmem : choice ∈ mentsuHandChoicesForTile tile choices) :
    mentsuHandChoiceRepresentative choice = some tile := by
  induction choices with
  | nil =>
      simp [mentsuHandChoicesForTile] at hmem
  | cons head choices ih =>
      by_cases hrep :
          mentsuHandChoiceRepresentative head = some tile
      · simp [mentsuHandChoicesForTile, hrep] at hmem
        rcases hmem with rfl | hmem
        · exact hrep
        · exact ih hmem
      · simp [mentsuHandChoicesForTile, hrep] at hmem
        exact ih hmem

def mentsuHandChoicesWithoutTile
    (tile : Tile) : List MentsuHandChoice → List MentsuHandChoice
  | [] => []
  | choice :: choices =>
      if mentsuHandChoiceRepresentative choice = some tile then
      mentsuHandChoicesWithoutTile tile choices
      else
      choice :: mentsuHandChoicesWithoutTile tile choices

lemma mentsuHandChoicesWithoutTile_mem
    {tile : Tile} {choices : List MentsuHandChoice}
    {choice : MentsuHandChoice}
    (hmem : choice ∈ mentsuHandChoicesWithoutTile tile choices) :
    choice ∈ choices := by
  induction choices with
  | nil =>
      simp [mentsuHandChoicesWithoutTile] at hmem
  | cons head choices ih =>
      by_cases hrep :
          mentsuHandChoiceRepresentative head = some tile
      · simp [mentsuHandChoicesWithoutTile, hrep] at hmem
        exact List.mem_cons_of_mem head (ih hmem)
      · simp [mentsuHandChoicesWithoutTile, hrep] at hmem
        rcases hmem with rfl | hmem
        · simp
        · exact List.mem_cons_of_mem head (ih hmem)

def mentsuHandChoicesGroupedByTiles :
    List Tile → List MentsuHandChoice → List MentsuHandChoice
  | [], _ => []
  | tile :: tiles, choices =>
      mentsuHandChoicesForTile tile choices ++
        mentsuHandChoicesGroupedByTiles tiles
          (mentsuHandChoicesWithoutTile tile choices)

def mentsuHandChoicesWithoutTileForTiles :
    List Tile → List MentsuHandChoice → List MentsuHandChoice
  | [], choices => choices
  | tile :: tiles, choices =>
      mentsuHandChoicesWithoutTileForTiles tiles
        (mentsuHandChoicesWithoutTile tile choices)

lemma list_perm_rotate
    {α : Type} (choice : α) (pre suffix : List α) :
    List.Perm (pre ++ choice :: suffix)
      (choice :: pre ++ suffix) := by
  induction pre with
  | nil =>
      exact .refl _
  | cons head pre ih =>
      exact (List.Perm.cons head ih).trans
        (List.Perm.swap choice head (pre ++ suffix))

lemma mentsuHandChoicesForTile_partition
    (tile : Tile) (choices : List MentsuHandChoice) :
    List.Perm
      (mentsuHandChoicesForTile tile choices ++
      mentsuHandChoicesWithoutTile tile choices)
      choices := by
  induction choices with
  | nil =>
      exact .refl _
  | cons choice choices ih =>
      by_cases hrep :
        mentsuHandChoiceRepresentative choice = some tile
      · simp [mentsuHandChoicesForTile, mentsuHandChoicesWithoutTile, hrep]
        exact ih
      · simp [mentsuHandChoicesForTile, mentsuHandChoicesWithoutTile, hrep]
        exact (list_perm_rotate choice
        (mentsuHandChoicesForTile tile choices)
        (mentsuHandChoicesWithoutTile tile choices)).trans
          (List.Perm.cons choice ih)

lemma mentsuHandChoicesWithoutTile_representative_ne
    {tile : Tile} {choices : List MentsuHandChoice}
    {choice : MentsuHandChoice}
    (hmem : choice ∈ mentsuHandChoicesWithoutTile tile choices) :
    mentsuHandChoiceRepresentative choice ≠ some tile := by
  induction choices with
  | nil =>
      simp [mentsuHandChoicesWithoutTile] at hmem
  | cons head choices ih =>
      by_cases hrep :
          mentsuHandChoiceRepresentative head = some tile
      · simp [mentsuHandChoicesWithoutTile, hrep] at hmem
        exact ih hmem
      · simp [mentsuHandChoicesWithoutTile, hrep] at hmem
        rcases hmem with rfl | hmem
        · exact hrep
        · exact ih hmem

lemma mentsuHandChoicesWithoutTile_mem_of_mem_of_ne
    {tile : Tile} {choices : List MentsuHandChoice}
    {choice : MentsuHandChoice}
    (hmem : choice ∈ choices)
    (hne : mentsuHandChoiceRepresentative choice ≠ some tile) :
    choice ∈ mentsuHandChoicesWithoutTile tile choices := by
  induction choices with
  | nil =>
      simp at hmem
  | cons head choices ih =>
      by_cases hrep :
          mentsuHandChoiceRepresentative head = some tile
      · simp only [mentsuHandChoicesWithoutTile, hrep]
        have hmem' : choice = head ∨ choice ∈ choices := by
          simpa using hmem
        rcases hmem' with hmem | hmem
        · subst choice
          exact (hne hrep).elim
        · exact ih hmem
      · simp only [mentsuHandChoicesWithoutTile, hrep]
        have hmem' : choice = head ∨ choice ∈ choices := by
          simpa using hmem
        rcases hmem' with hmem | hmem
        · subst choice
          simp
        · exact List.mem_cons_of_mem head (ih hmem)

lemma mentsuHandChoicesWithoutTileForTiles_mem
    {tiles : List Tile} {choices : List MentsuHandChoice}
    {choice : MentsuHandChoice}
    (hmem : choice ∈
      mentsuHandChoicesWithoutTileForTiles tiles choices) :
    choice ∈ choices := by
  induction tiles generalizing choices with
  | nil =>
      exact hmem
  | cons tile tiles ih =>
      exact mentsuHandChoicesWithoutTile_mem (ih hmem)

lemma mentsuHandChoicesWithoutTileForTiles_representative_ne
    {tiles : List Tile} {choices : List MentsuHandChoice}
    {choice : MentsuHandChoice}
    (hmem : choice ∈
      mentsuHandChoicesWithoutTileForTiles tiles choices) :
    ∀ tile, tile ∈ tiles →
      mentsuHandChoiceRepresentative choice ≠ some tile := by
  induction tiles generalizing choices with
  | nil =>
      intro tile htile
      simp at htile
  | cons tile tiles ih =>
      intro target htarget
      have hmemImmediate :
          choice ∈ mentsuHandChoicesWithoutTile tile choices :=
        mentsuHandChoicesWithoutTileForTiles_mem hmem
      simp only [List.mem_cons] at htarget
      rcases htarget with rfl | htarget
      · exact mentsuHandChoicesWithoutTile_representative_ne
          hmemImmediate
      · exact ih hmem target htarget

lemma mentsuHandChoicesWithoutTileForTiles_eq_nil
    {tiles : List Tile} {choices : List MentsuHandChoice}
    (hrep :
      ∀ choice, choice ∈ choices →
        ∃ tile, tile ∈ tiles ∧
          mentsuHandChoiceRepresentative choice = some tile) :
    mentsuHandChoicesWithoutTileForTiles tiles choices = [] := by
  by_contra hne
  obtain ⟨choice, hchoice⟩ :=
    List.exists_mem_of_ne_nil
      (mentsuHandChoicesWithoutTileForTiles tiles choices) hne
  obtain ⟨tile, htile, hchoiceTile⟩ :=
    hrep choice
      (mentsuHandChoicesWithoutTileForTiles_mem hchoice)
  exact (mentsuHandChoicesWithoutTileForTiles_representative_ne hchoice
    tile htile) hchoiceTile

lemma mentsuHandChoicesGroupedByTiles_perm_append
    {tiles : List Tile} {choices : List MentsuHandChoice}
    (hrep :
      ∀ choice, choice ∈ choices →
        ∃ tile, tile ∈ tiles ∧
          mentsuHandChoiceRepresentative choice = some tile) :
    List.Perm
      (mentsuHandChoicesGroupedByTiles tiles choices ++
        mentsuHandChoicesWithoutTileForTiles tiles choices)
      choices := by
  induction tiles generalizing choices with
  | nil =>
      simp [mentsuHandChoicesGroupedByTiles,
        mentsuHandChoicesWithoutTileForTiles]
  | cons tile tiles ih =>
      have htail :
          ∀ choice, choice ∈
              mentsuHandChoicesWithoutTile tile choices →
            ∃ nextTile, nextTile ∈ tiles ∧
              mentsuHandChoiceRepresentative choice = some nextTile := by
        intro choice hchoice
        obtain ⟨choiceTile, hchoiceTile, hchoiceRep⟩ :=
          hrep choice
            (mentsuHandChoicesWithoutTile_mem hchoice)
        simp only [List.mem_cons] at hchoiceTile
        rcases hchoiceTile with rfl | hchoiceTile
        · exact False.elim
            (mentsuHandChoicesWithoutTile_representative_ne hchoice
              hchoiceRep)
        · exact ⟨_, hchoiceTile, hchoiceRep⟩
      have hpartition :=
        mentsuHandChoicesForTile_partition tile choices
      have hgrouped :=
        ih htail
      simpa [mentsuHandChoicesGroupedByTiles,
        mentsuHandChoicesWithoutTileForTiles, List.append_assoc] using
        ((List.Perm.append_left
            (mentsuHandChoicesForTile tile choices) hgrouped).trans
          hpartition)

lemma mentsuHandChoicesGroupedByTiles_perm
    {tiles : List Tile} {choices : List MentsuHandChoice}
    (hrep :
      ∀ choice, choice ∈ choices →
        ∃ tile, tile ∈ tiles ∧
          mentsuHandChoiceRepresentative choice = some tile) :
    List.Perm
      (mentsuHandChoicesGroupedByTiles tiles choices)
      choices := by
  have hperm :=
    mentsuHandChoicesGroupedByTiles_perm_append hrep
  rw [mentsuHandChoicesWithoutTileForTiles_eq_nil hrep] at hperm
  simpa using hperm

def choiceUsesMeld : MentsuHandChoice → Bool
  | .meld _ => true
  | _ => false

def choiceUsesPair : MentsuHandChoice → Bool
  | .pair _ => true
  | _ => false

def choiceUsesTaatsu : MentsuHandChoice → Bool
  | .taatsu _ => true
  | _ => false

def ValidMentsuHandChoice
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice) : Prop :=
  (∀ tile, (state.used + choiceTiles choice).count tile ≤ hand.counts tile) ∧
  state.melds + (if choiceUsesMeld choice = true then 1 else 0) ≤ 4 ∧
  state.taatsu + (if choiceUsesTaatsu choice = true then 1 else 0) ≤ 4 ∧
  (state.pair.isNone ∨ choiceUsesPair choice = false)

lemma validMentsuHandChoice_of
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hused :
      ∀ tile, (state.used + choiceTiles choice).count tile ≤ hand.counts tile)
    (hmelds :
      state.melds + (if choiceUsesMeld choice = true then 1 else 0) ≤ 4)
    (htaatsu :
      state.taatsu + (if choiceUsesTaatsu choice = true then 1 else 0) ≤ 4)
    (hpair : state.pair.isNone ∨ choiceUsesPair choice = false) :
    ValidMentsuHandChoice hand state choice :=
  ⟨hused, hmelds, htaatsu, hpair⟩

def applyMentsuHandChoice
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (_ : ValidMentsuHandChoice hand state choice) : MentsuHandSearchState :=
  { state with
    tileIndex := state.tileIndex + 1
    used := state.used + choiceTiles choice
    pair := match choice with
      | .pair tile => some tile
      | _ => state.pair
    meldHistory := match choice with
      | .meld meld => meld :: state.meldHistory
      | _ => state.meldHistory
    taatsuHistory := match choice with
      | .taatsu taatsu => taatsu :: state.taatsuHistory
      | _ => state.taatsuHistory
    melds := state.melds + (if choiceUsesMeld choice = true then 1 else 0)
    taatsu := state.taatsu + (if choiceUsesTaatsu choice = true then 1 else 0)
    }

lemma applyMentsuHandChoice_used_subset
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice) :
    ∀ tile,
      (applyMentsuHandChoice hand state choice hvalid).used.count tile ≤
        hand.counts tile := by
  intro tile
  exact hvalid.1 tile

def allMentsuHandChoices : Finset MentsuHandChoice :=
  insert .skip
    (Finset.univ.image MentsuHandChoice.pair ∪
      Finset.univ.image MentsuHandChoice.meld ∪
      Finset.univ.image (fun taatsu =>
        MentsuHandChoice.taatsu taatsu))

lemma mentsuHandChoice_mem_all
    (choice : MentsuHandChoice) :
    choice ∈ allMentsuHandChoices := by
  cases choice with
  | skip =>
      simp [allMentsuHandChoices]
  | pair tile =>
      simp [allMentsuHandChoices]
  | taatsu taatsu =>
      simp [allMentsuHandChoices]
  | meld meld =>
      simp [allMentsuHandChoices]

def NextMentsuHandState
    (hand : Hand) (state next : MentsuHandSearchState) : Prop :=
  ∃ choice, choice ∈ allMentsuHandChoices ∧
    ∃ hvalid : ValidMentsuHandChoice hand state choice,
      next = applyMentsuHandChoice hand state choice hvalid

lemma nextMentsuHandState_used_subset
    (hand : Hand) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandState hand state next) :
    ∀ tile, next.used.count tile ≤ hand.counts tile := by
  rcases hnext with ⟨choice, _, hvalid, rfl⟩
  exact applyMentsuHandChoice_used_subset hand state choice hvalid

lemma nextMentsuHandState_tileIndex
    (hand : Hand) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandState hand state next) :
    state.tileIndex < next.tileIndex := by
  rcases hnext with ⟨choice, _, hvalid, rfl⟩
  simp [applyMentsuHandChoice]

def initialMentsuHandState : MentsuHandSearchState :=
  { tileIndex := 0
    used := 0
    pair := none
    meldHistory := []
    taatsuHistory := []
    melds := 0
    taatsu := 0 }

/-- States reachable after exactly `fuel` decomposition choices. -/
def reachableWithin
    (hand : Hand) : Nat → MentsuHandSearchState → Prop
  | 0, state => state = initialMentsuHandState
  | fuel + 1, state =>
      ∃ previous,
        reachableWithin hand fuel previous ∧
          NextMentsuHandState hand previous state

def IsMentsuHandSearchComplete
    (hand : Hand) (state : MentsuHandSearchState) : Prop :=
  state.melds + hand.fixedMelds = 4 ∧ state.pair.isSome

/-- A DP state containing four meld-or-taatsu blocks and one pair. -/
def IsMentsuHandBlockSearchComplete
    (hand : Hand) (state : MentsuHandSearchState) : Prop :=
  state.melds + state.taatsu + hand.fixedMelds = 4 ∧ state.pair.isSome

/-- The DP query: a complete mentsuHand decomposition is reachable in `fuel` choices. -/
def MentsuHandSearch
    (hand : Hand) (fuel : Nat) : Prop :=
  ∃ state, reachableWithin hand fuel state ∧
    IsMentsuHandSearchComplete hand state

/-- The DP query using the four-block criterion. -/
def MentsuHandBlockSearch
    (hand : Hand) (fuel : Nat) : Prop :=
  ∃ state, reachableWithin hand fuel state ∧
    IsMentsuHandBlockSearchComplete hand state

def pairHistoryTiles (pair : Option Tile) : Multiset Tile :=
  pair.elim 0 pairTiles

def taatsuHistoryTiles : List Taatsu → Multiset Tile
  | [] => 0
  | taatsu :: taatsus => taatsuTiles taatsu + taatsuHistoryTiles taatsus

def taatsuCompletionMelds : List Taatsu → List Meld
  | [] => []
  | taatsu :: taatsus =>
      taatsuCompletionMeld taatsu :: taatsuCompletionMelds taatsus

def taatsuCompletionTiles : List Taatsu → Multiset Tile
  | [] => 0
  | taatsu :: taatsus =>
      Multiset.replicate 1 (taatsuCompletionTile taatsu) +
        taatsuCompletionTiles taatsus

lemma taatsuHistoryTiles_add_completionTiles
    (taatsus : List Taatsu) :
    taatsuHistoryTiles taatsus + taatsuCompletionTiles taatsus =
      meldsTiles (taatsuCompletionMelds taatsus) := by
  induction taatsus with
  | nil =>
      rfl
  | cons taatsu taatsus ih =>
      simp only [taatsuHistoryTiles, taatsuCompletionTiles,
        taatsuCompletionMelds, meldsTiles]
      calc
        _ =
            (taatsuTiles taatsu +
                Multiset.replicate 1 (taatsuCompletionTile taatsu)) +
              (taatsuHistoryTiles taatsus + taatsuCompletionTiles taatsus) := by
                ac_rfl
        _ = meldTiles (taatsuCompletionMeld taatsu) +
              meldsTiles (taatsuCompletionMelds taatsus) := by
                rw [taatsuTiles_add_completionTile, ih]
        _ = _ := by rfl

lemma taatsuCompletionMelds_length (taatsus : List Taatsu) :
    (taatsuCompletionMelds taatsus).length = taatsus.length := by
  induction taatsus <;> simp [taatsuCompletionMelds, *]

lemma taatsuCompletionTiles_card (taatsus : List Taatsu) :
    (taatsuCompletionTiles taatsus).card = taatsus.length := by
  induction taatsus with
  | nil =>
      rfl
  | cons taatsu taatsus ih =>
      simp [taatsuCompletionTiles, ih]

lemma taatsuCompletionTiles_count_le_of_sublist
    {taatsus subset : List Taatsu}
    (hsub : List.Sublist subset taatsus) :
    ∀ tile,
      (taatsuCompletionTiles subset).count tile ≤
        (taatsuCompletionTiles taatsus).count tile := by
  induction hsub with
  | slnil =>
      simp
  | cons taatsu hsub ih =>
      intro tile
      have htail := ih tile
      simp only [taatsuCompletionTiles, Multiset.count_add,
        Multiset.count_replicate]
      exact htail.trans (Nat.le_add_left _ _)
  | cons_cons taatsu hsub ih =>
      intro tile
      simp only [taatsuCompletionTiles, Multiset.count_add,
        Multiset.count_replicate]
      have htail := ih tile
      omega

lemma taatsuCompletionTiles_of_perm
    {taatsus taatsus' : List Taatsu}
    (hperm : List.Perm taatsus taatsus') :
    taatsuCompletionTiles taatsus =
      taatsuCompletionTiles taatsus' := by
  induction hperm with
  | nil =>
      rfl
  | cons taatsu hperm ih =>
      simp [taatsuCompletionTiles, ih]
  | swap taatsu taatsu' taatsus =>
      simp [taatsuCompletionTiles, add_comm, add_left_comm, add_assoc]
  | trans hperm hperm' ih ih' =>
      exact ih.trans ih'

lemma pairTiles_card (tile : Tile) :
    (pairTiles tile).card = 2 := by
  simp [pairTiles]

lemma meldTiles_card (meld : Meld) : (meldTiles meld).card = 3 := by
  cases meld <;> simp [meldTiles]

lemma meldsTiles_card (melds : List Meld) :
    (meldsTiles melds).card = 3 * melds.length := by
  induction melds with
  | nil =>
      rfl
  | cons meld melds ih =>
      change (meldTiles meld + meldsTiles melds).card =
        3 * (melds.length + 1)
      rw [Multiset.card_add, meldTiles_card, ih]
      omega

def completedMeldsForState (state : MentsuHandSearchState) : List Meld :=
  state.meldHistory.reverse ++
    taatsuCompletionMelds state.taatsuHistory.reverse

lemma completedMeldsForState_length
    (state : MentsuHandSearchState) :
    (completedMeldsForState state).length =
      state.meldHistory.length + state.taatsuHistory.length := by
  simp [completedMeldsForState, taatsuCompletionMelds_length,
    Nat.add_comm]

lemma meldsTiles_append (left right : List Meld) :
    meldsTiles (left ++ right) = meldsTiles left + meldsTiles right := by
  induction left with
  | nil =>
      simp [meldsTiles]
  | cons meld left ih =>
      change meldTiles meld + meldsTiles (left ++ right) =
        (meldTiles meld + meldsTiles left) + meldsTiles right
      rw [ih]
      ac_rfl

def stateHistoryTiles (state : MentsuHandSearchState) : Multiset Tile :=
  pairHistoryTiles state.pair +
    meldsTiles state.meldHistory.reverse +
    taatsuHistoryTiles state.taatsuHistory.reverse

lemma taatsuHistoryTiles_append_single (history : List Taatsu) (taatsu : Taatsu) :
    taatsuHistoryTiles (history ++ [taatsu]) =
      taatsuHistoryTiles history + taatsuTiles taatsu := by
  induction history with
  | nil => simp [taatsuHistoryTiles]
  | cons head tail ih =>
      simp [taatsuHistoryTiles, ih, Multiset.add_assoc]

lemma meldsTiles_append_single (history : List Meld) (meld : Meld) :
    meldsTiles (history ++ [meld]) =
      meldsTiles history + meldTiles meld := by
  have aux : ∀ (items : List Meld) (acc : Multiset Tile),
      List.foldr (fun item rest => meldTiles item + rest) acc items =
        List.foldr (fun item rest => meldTiles item + rest) 0 items + acc := by
    intro items
    induction items with
    | nil =>
        intro acc
        simp
    | cons head tail ih =>
        intro acc
        simp only [List.foldr]
        rw [ih]
        ac_rfl
  simpa [meldsTiles, List.foldr_append] using aux history (meldTiles meld)

lemma applyMentsuHandChoice_used_eq_historyTiles
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hstate : state.used = stateHistoryTiles state) :
    (applyMentsuHandChoice hand state choice hvalid).used =
      stateHistoryTiles (applyMentsuHandChoice hand state choice hvalid) := by
  cases choice with
  | skip =>
      simpa [applyMentsuHandChoice, stateHistoryTiles, pairHistoryTiles,
        taatsuHistoryTiles, choiceTiles] using hstate
  | pair tile =>
      have hpair : state.pair.isNone := by
        simpa [choiceUsesPair] using hvalid.2.2.2
      cases hstatePair : state.pair with
      | none =>
          simp only [applyMentsuHandChoice]
          change state.used + pairTiles tile = _
          rw [hstate]
          simp [applyMentsuHandChoice, stateHistoryTiles, pairHistoryTiles,
            taatsuHistoryTiles, choiceTiles, hstatePair]
          ac_rfl
      | some oldPair =>
          simp [hstatePair] at hpair
  | taatsu taatsu =>
      simp only [applyMentsuHandChoice]
      change state.used + taatsuTiles taatsu = _
      rw [hstate]
      simp [applyMentsuHandChoice, stateHistoryTiles, pairHistoryTiles,
        taatsuHistoryTiles, choiceTiles, List.reverse_cons,
        taatsuHistoryTiles_append_single]
      ac_rfl
  | meld meld =>
      simp only [applyMentsuHandChoice]
      change state.used + meldTiles meld = _
      rw [hstate]
      simp [applyMentsuHandChoice, stateHistoryTiles, pairHistoryTiles,
        taatsuHistoryTiles, choiceTiles, List.reverse_cons,
        meldsTiles_append_single]
      ac_rfl

lemma reachableWithin_used_eq_historyTiles
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) :
    state.used = stateHistoryTiles state := by
  induction fuel generalizing state with
  | zero =>
      subst state
      rfl
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, rfl⟩
      exact applyMentsuHandChoice_used_eq_historyTiles
        hand previous choice hvalid (ih previous hprevious)

lemma applyMentsuHandChoice_melds_eq_history_length
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hstate : state.melds = state.meldHistory.length) :
    (applyMentsuHandChoice hand state choice hvalid).melds =
      (applyMentsuHandChoice hand state choice hvalid).meldHistory.length := by
  cases choice <;> simp [applyMentsuHandChoice, hstate, choiceUsesMeld]

lemma reachableWithin_melds_eq_history_length
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) :
    state.melds = state.meldHistory.length := by
  induction fuel generalizing state with
  | zero =>
      subst state
      rfl
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, rfl⟩
      exact applyMentsuHandChoice_melds_eq_history_length
        hand previous choice hvalid (ih previous hprevious)

lemma applyMentsuHandChoice_taatsu_eq_history_length
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hstate : state.taatsu = state.taatsuHistory.length) :
    (applyMentsuHandChoice hand state choice hvalid).taatsu =
      (applyMentsuHandChoice hand state choice hvalid).taatsuHistory.length := by
  cases choice <;> simp [applyMentsuHandChoice, hstate, choiceUsesTaatsu]

lemma reachableWithin_taatsu_eq_history_length
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) :
    state.taatsu = state.taatsuHistory.length := by
  induction fuel generalizing state with
  | zero =>
      subst state
      rfl
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, rfl⟩
      exact applyMentsuHandChoice_taatsu_eq_history_length
        hand previous choice hvalid (ih previous hprevious)

/-
## 3. 到達可能性と固定牌順

抽象的な到達可能状態と、あらかじめ定めた牌種の順序を関連付けます。
後で使う、牌種ごとの走査との接続を確立します。
-/

lemma reachableWithin_zero_iff
    (hand : Hand) (state : MentsuHandSearchState) :
    reachableWithin hand 0 state ↔ state = initialMentsuHandState := by
  rfl

lemma reachableWithin_succ_iff
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState) :
    reachableWithin hand (fuel + 1) state ↔
      ∃ previous,
        reachableWithin hand fuel previous ∧
          NextMentsuHandState hand previous state := by
  rfl

lemma reachableWithin_used_subset
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) :
    ∀ tile, state.used.count tile ≤ hand.counts tile := by
  induction fuel generalizing state with
  | zero =>
      intro tile
      subst state
      simp [initialMentsuHandState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      intro tile
      exact nextMentsuHandState_used_subset hand previous state hnext tile

lemma mentsuHandSearch_complete_iff
    (hand : Hand) (fuel : Nat) :
    MentsuHandSearch hand fuel ↔
      ∃ state, reachableWithin hand fuel state ∧
        state.melds + hand.fixedMelds = 4 ∧
        state.pair.isSome := by
  rfl

lemma mentsuHandBlockSearch_complete_iff
    (hand : Hand) (fuel : Nat) :
    MentsuHandBlockSearch hand fuel ↔
        ∃ state, reachableWithin hand fuel state ∧
          state.melds + state.taatsu + hand.fixedMelds = 4 ∧
          state.pair.isSome := by
  rfl

def mentsuHandTileAt (index : Fin 34) : Tile :=
  match index with
  | ⟨value, hvalue⟩ =>
        if hsuited : value < 27 then
          let suit :=
            if hman : value < 9 then Suit.man
            else if hpin : value < 18 then Suit.pin
            else Suit.sou
          Tile.suited suit ⟨value % 9, by omega⟩
        else
          Tile.honor ⟨value - 27, by omega⟩

def mentsuHandTileOrder : List Tile :=
  (List.finRange 34).map mentsuHandTileAt

lemma mentsuHandTileOrder_length :
    mentsuHandTileOrder.length = 34 := by
  simp [mentsuHandTileOrder]

lemma tile_mem_mentsuHandTileOrder :
    ∀ tile : Tile, tile ∈ mentsuHandTileOrder := by
  native_decide

/-- A mentsu-hand-form target before the fixed melds are added. -/
/-
## 4. 目標形と交換距離

ここでは、雀頭と面子列を完成目標として扱います。周辺の補題によって、
部分履歴が目標形に対応することと、交換によって目標までの不足量が
どのように変化するかを確立します。
-/

def mentsuHandTarget (pair : Tile) (melds : List Meld) : Multiset Tile :=
  pairTiles pair + meldsTiles melds

def mentsuHandTargetWithTaatsu
    (pair : Tile) (melds : List Meld) (taatsus : List Taatsu) : Multiset Tile :=
  mentsuHandTarget pair melds + taatsuHistoryTiles taatsus

lemma completedMeldsForState_tiles
    (state : MentsuHandSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    pairTiles pair + meldsTiles (completedMeldsForState state) =
      mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
          state.taatsuHistory.reverse +
        taatsuCompletionTiles state.taatsuHistory.reverse := by
  simp only [completedMeldsForState, mentsuHandTargetWithTaatsu, mentsuHandTarget]
  rw [meldsTiles_append]
  rw [← taatsuHistoryTiles_add_completionTiles]
  ac_rfl

def mentsuHandTargetWithTaatsuOfState
    (state : MentsuHandSearchState) : Option (Multiset Tile) :=
  state.pair.map fun pair =>
    mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
      state.taatsuHistory.reverse

lemma mentsuHandTargetWithTaatsuOfState_eq_some_iff
    (state : MentsuHandSearchState) (target : Multiset Tile) :
    mentsuHandTargetWithTaatsuOfState state = some target ↔
      ∃ pair, state.pair = some pair ∧
        target = mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
          state.taatsuHistory.reverse := by
  constructor
  · intro htarget
    cases hpair : state.pair with
    | none =>
        simp [mentsuHandTargetWithTaatsuOfState, hpair] at htarget
    | some pair =>
        refine ⟨pair, rfl, ?_⟩
        simpa [mentsuHandTargetWithTaatsuOfState, hpair] using htarget.symm
  · rintro ⟨pair, hpair, rfl⟩
    rw [mentsuHandTargetWithTaatsuOfState, hpair]
    rfl

lemma mentsuHandTargetWithTaatsuOfState_eq_stateHistoryTiles
    (state : MentsuHandSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
        state.taatsuHistory.reverse =
      stateHistoryTiles state := by
  simp [mentsuHandTargetWithTaatsu, mentsuHandTarget, stateHistoryTiles,
    pairHistoryTiles, hpair, Multiset.add_assoc]

lemma mentsuHandTargetWithTaatsu_count_le_hand
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
        state.taatsuHistory.reverse).count tile ≤ hand.counts tile := by
  intro tile
  rw [mentsuHandTargetWithTaatsuOfState_eq_stateHistoryTiles state pair hpair]
  rw [← reachableWithin_used_eq_historyTiles hand fuel state hreachable]
  exact reachableWithin_used_subset hand fuel state hreachable tile

lemma mentsuHandTargetExchange_handStep
    (target : TileCounts) (before : Hand) (discarded drawn : Tile)
    (hdrawn : target drawn > before.counts drawn)
    (hdiscarded : before.counts discarded > target discarded)
    (hne : discarded ≠ drawn) :
    HandStep before (exchangeHand before discarded drawn) := by
  apply TargetExchange.handStep
  exact ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩

lemma reachesExchange_of_targetExchange
    (target : TileCounts) (before : Hand) (discarded drawn : Tile)
    (hdrawn : target drawn > before.counts drawn)
    (hdiscarded : before.counts discarded > target discarded)
    (hne : discarded ≠ drawn)
    (hrest :
      ReachesExchange (exchangeHand before discarded drawn) after distance) :
    ReachesExchange before after (distance + 1) := by
  apply ReachesExchange.step
    (mentsuHandTargetExchange_handStep target before discarded drawn
      hdrawn hdiscarded hne)
  exact hrest

lemma exchangeHand_fixedMelds
    (before : Hand) (discarded drawn : Tile) :
    (exchangeHand before discarded drawn).fixedMelds = before.fixedMelds := by
  rfl

def mentsuHandTargetOfState
    (state : MentsuHandSearchState) : Option (Multiset Tile) :=
  state.pair.map fun pair =>
    mentsuHandTarget pair state.meldHistory.reverse

lemma mentsuHandTargetOfState_eq_some_iff
    (state : MentsuHandSearchState) (target : Multiset Tile) :
    mentsuHandTargetOfState state = some target ↔
      ∃ pair, state.pair = some pair ∧
        target = mentsuHandTarget pair state.meldHistory.reverse := by
  constructor
  · intro htarget
    cases hpair : state.pair with
    | none =>
        simp [mentsuHandTargetOfState, hpair] at htarget
    | some pair =>
        refine ⟨pair, rfl, ?_⟩
        simpa [mentsuHandTargetOfState, hpair] using htarget.symm
  · rintro ⟨pair, hpair, rfl⟩
    rw [mentsuHandTargetOfState, hpair]
    rfl

/-- The number of copies of each tile still required by a target. -/
def targetDeficit (hand : Hand) (target : Multiset Tile) : Nat :=
  ∑ tile : Tile, (target.count tile - hand.counts tile)

lemma exists_lt_of_sum_eq_of_ne
    (current target : TileCounts)
    (hsum : (∑ tile : Tile, current tile) =
      ∑ tile : Tile, target tile)
    (hne : current ≠ target) :
    ∃ tile, current tile < target tile := by
  by_contra hexists
  push_neg at hexists
  have hle : ∀ tile, target tile ≤ current tile := by
    intro tile
    exact hexists tile
  have heq :
      ∀ tile ∈ (Finset.univ : Finset Tile), target tile = current tile := by
    apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := target) (g := current) (fun tile _ => hle tile)).mp
    exact hsum.symm
  apply hne
  funext tile
  exact (heq tile (Finset.mem_univ tile)).symm

lemma exists_target_exchange_tiles
    (before : Hand) (target : TileCounts)
    (hsum : (∑ tile : Tile, before.counts tile) =
      ∑ tile : Tile, target tile)
    (hne : before.counts ≠ target) :
    ∃ discarded drawn,
      target drawn > before.counts drawn ∧
      before.counts discarded > target discarded ∧
      discarded ≠ drawn := by
  obtain ⟨drawn, hdrawn⟩ :=
    exists_lt_of_sum_eq_of_ne before.counts target hsum hne
  obtain ⟨discarded, hdiscarded⟩ :=
    exists_lt_of_sum_eq_of_ne target before.counts hsum.symm
      (Ne.symm hne)
  refine ⟨discarded, drawn, hdrawn, hdiscarded, ?_⟩
  intro heq
  subst discarded
  omega

lemma targetExchange_exists_of_equal_sum
    (before : Hand) (target : TileCounts)
    (hsum : (∑ tile : Tile, before.counts tile) =
      ∑ tile : Tile, target tile)
    (hne : before.counts ≠ target) :
    ∃ after, TargetExchange target before after := by
  obtain ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles⟩ :=
    exists_target_exchange_tiles before target hsum hne
  refine ⟨exchangeHand before discarded drawn, ?_⟩
  exact ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles, rfl⟩

lemma exchangeCounts_sum
    (before : Hand) (discarded drawn : Tile)
    (hne : discarded ≠ drawn) (hdiscarded : before.counts discarded > 0) :
    (∑ tile : Tile, exchangeCounts before discarded drawn tile) =
      ∑ tile : Tile, before.counts tile := by
  have hstep := exchangeCounts_step before discarded drawn hne hdiscarded
  have hfun :
      (fun tile =>
        exchangeCounts before discarded drawn tile +
          (if tile = discarded then 1 else 0)) =
      (fun tile =>
        before.counts tile + (if tile = drawn then 1 else 0)) :=
    funext hstep
  have hsum := congrArg (fun f : TileCounts => ∑ tile, f tile) hfun
  have hsum' :
      (∑ tile, exchangeCounts before discarded drawn tile) + 1 =
        (∑ tile, before.counts tile) + 1 := by
    simpa [Finset.sum_add_distrib, hne, Ne.symm hne] using hsum
  omega

lemma countDeficit_exchange
    (target : TileCounts) (before : Hand) (discarded drawn : Tile)
    (hdrawn : target drawn > before.counts drawn)
    (hdiscarded : before.counts discarded > target discarded)
    (hne : discarded ≠ drawn) :
    countDeficit (exchangeHand before discarded drawn).counts target =
      countDeficit before.counts target - 1 := by
  let deficit : Tile → Nat := fun tile => target tile - before.counts tile
  let afterDeficit : Tile → Nat :=
    fun tile => target tile - (exchangeHand before discarded drawn).counts tile
  have hdrawn' :
      afterDeficit drawn = deficit drawn - 1 := by
    change target drawn - exchangeCounts before discarded drawn drawn =
      target drawn - before.counts drawn - 1
    exact deficit_after_drawing target before discarded drawn hne hdrawn
  have hdiscarded' :
      afterDeficit discarded = deficit discarded := by
    change target discarded - exchangeCounts before discarded drawn discarded =
      target discarded - before.counts discarded
    exact deficit_after_discarding target before discarded drawn hne hdiscarded
  have hother (tile : Tile) (htileDiscarded : tile ≠ discarded)
      (htileDrawn : tile ≠ drawn) :
      afterDeficit tile = deficit tile := by
    change target tile - exchangeCounts before discarded drawn tile =
      target tile - before.counts tile
    exact deficit_unchanged target before discarded drawn tile
      htileDiscarded htileDrawn
  have hdiscarded_zero : deficit discarded = 0 := by
    dsimp [deficit]
    omega
  have hdrawn_deficit :
      deficit drawn = target drawn - before.counts drawn := by
    rfl
  have hsum :
      (∑ tile : Tile, afterDeficit tile) =
        (∑ tile : Tile, deficit tile) - 1 := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset Tile)
      afterDeficit (Finset.mem_univ drawn)]
    rw [← Finset.sum_erase_add (Finset.univ.erase drawn)
      afterDeficit (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ discarded⟩)]
    rw [← Finset.sum_erase_add (Finset.univ : Finset Tile)
      deficit (Finset.mem_univ drawn)]
    rw [← Finset.sum_erase_add (Finset.univ.erase drawn)
      deficit (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ discarded⟩)]
    have hrest :
        (∑ tile ∈ (Finset.univ.erase drawn).erase discarded, afterDeficit tile) =
          ∑ tile ∈ (Finset.univ.erase drawn).erase discarded, deficit tile := by
      apply Finset.sum_congr rfl
      intro tile htile
      exact hother tile
        (Finset.mem_erase.mp htile).1
        (Finset.mem_erase.mp (Finset.mem_erase.mp htile).2).1
    rw [hrest, hdiscarded', hdrawn', hdiscarded_zero]
    rw [hdrawn_deficit]
    omega
  change (∑ tile : Tile, afterDeficit tile) =
    (∑ tile : Tile, deficit tile) - 1
  exact hsum

lemma countDeficit_handStep_le
    (before after : Hand) (target : TileCounts)
    (hstep : HandStep before after) :
    countDeficit before.counts target ≤
      countDeficit after.counts target + 1 := by
  have finish (drawn : Tile)
      (hpoint : ∀ tile,
        target tile - before.counts tile ≤
          target tile - after.counts tile +
            (if tile = drawn then 1 else 0)) :
      countDeficit before.counts target ≤
        countDeficit after.counts target + 1 := by
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun tile _ => hpoint tile)
    calc
      countDeficit before.counts target =
          ∑ tile : Tile, (target tile - before.counts tile) := rfl
      _ ≤ ∑ tile : Tile,
          (target tile - after.counts tile +
            (if tile = drawn then 1 else 0)) := hsum
      _ = countDeficit after.counts target + 1 := by
        simp [countDeficit, Finset.sum_add_distrib]
  rcases hstep.2 with ⟨drawn, _, hcounts⟩ |
    ⟨discarded, drawn, hne, hpositive, hcounts⟩
  · apply finish drawn
    intro tile
    have hcount := hcounts tile
    by_cases hdrawn : tile = drawn
    · subst tile
      simp at hcount
      simp
      omega
    · simp [hdrawn] at hcount
      simp [hdrawn]
      omega
  · apply finish drawn
    intro tile
    by_cases hdiscarded : tile = discarded
    · subst tile
      have hcount := hcounts discarded
      simp [hne] at hcount
      simp [hne]
      omega
    · by_cases hdrawn : tile = drawn
      · subst tile
        have hcount := hcounts drawn
        simp [hne, Ne.symm hne] at hcount
        simp [hne, Ne.symm hne]
        omega
      · have hcount := hcounts tile
        simp [hdiscarded, hdrawn] at hcount
        simp [hdrawn]
        omega

lemma exists_complete_mentsuHand_with_deficit_le
    (before : Hand) (distance : Nat)
    (hreach : ReachesCompletion Complete .mentsuHand before distance) :
    ∃ after,
      Complete .mentsuHand after ∧
        after.fixedMelds = before.fixedMelds ∧
        countDeficit before.counts after.counts ≤ distance := by
  induction distance generalizing before with
  | zero =>
      cases hreach with
      | done hcomplete =>
          exact ⟨before, hcomplete, rfl, by simp [countDeficit]⟩
  | succ distance ih =>
      cases hreach with
      | @step hand next distance hstep hrest =>
          obtain ⟨after, hcomplete, hfixed, hbound⟩ :=
            ih next hrest
          refine ⟨after, hcomplete, ?_, ?_⟩
          · exact hfixed.trans hstep.1.symm
          have hstepBound :=
            countDeficit_handStep_le before next after.counts hstep
          omega

def targetHand (before : Hand) (target : TileCounts) : Hand :=
  { counts := target
    fixedMelds := before.fixedMelds }

def countsOfTiles (tiles : Multiset Tile) : TileCounts :=
  fun tile => tiles.count tile

lemma countDeficit_draw
    (before : Hand) (target : TileCounts) (drawn : Tile)
    (hdrawn : target drawn > before.counts drawn) :
    countDeficit
        (fun tile =>
          before.counts tile + (if tile = drawn then 1 else 0))
        target + 1 =
      countDeficit before.counts target := by
  let deficit : Tile → Nat :=
    fun tile => target tile - before.counts tile
  let afterDeficit : Tile → Nat :=
    fun tile =>
      target tile -
        (before.counts tile + (if tile = drawn then 1 else 0))
  have hdrawn' : afterDeficit drawn + 1 = deficit drawn := by
    simp [afterDeficit, deficit]
    omega
  have hother (tile : Tile) (htile : tile ≠ drawn) :
      afterDeficit tile = deficit tile := by
    simp [afterDeficit, deficit, htile]
  have hpoint (tile : Tile) :
      afterDeficit tile + (if tile = drawn then 1 else 0) =
        deficit tile := by
    by_cases htile : tile = drawn
    · subst tile
      simpa using hdrawn'
    · simp [htile, hother tile htile]
  have hsum :
      (∑ tile : Tile, afterDeficit tile) + 1 =
        ∑ tile : Tile, deficit tile := by
    calc
      (∑ tile : Tile, afterDeficit tile) + 1 =
          ∑ tile : Tile,
            (afterDeficit tile + (if tile = drawn then 1 else 0)) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ tile : Tile, deficit tile := by
        apply Finset.sum_congr rfl
        intro tile _
        exact hpoint tile
  change (∑ tile : Tile, afterDeficit tile) + 1 =
    ∑ tile : Tile, deficit tile
  exact hsum

lemma targetHand_hasTiles_countsOfTiles
    (before : Hand) (tiles : Multiset Tile) :
    HasTiles (targetHand before (countsOfTiles tiles)) tiles := by
  intro tile
  rfl

lemma countsOfTiles_sum_eq_card (tiles : Multiset Tile) :
    (∑ tile : Tile, countsOfTiles tiles tile) = tiles.card := by
  induction tiles using Multiset.induction_on with
  | empty =>
      simp [countsOfTiles]
  | @cons tile tiles ih =>
      simp [countsOfTiles, ih, Finset.sum_add_distrib]

lemma reachesExchange_targetHand_of_equal_sum
    (before : Hand) (target : TileCounts)
    (hsum : (∑ tile : Tile, before.counts tile) =
      ∑ tile : Tile, target tile) :
    ∃ distance,
      distance = countDeficit before.counts target ∧
      ReachesExchange before (targetHand before target) distance := by
  have aux : ∀ d : Nat, ∀ current : Hand,
      (∑ tile : Tile, current.counts tile) =
        ∑ tile : Tile, target tile →
      countDeficit current.counts target = d →
      ∃ distance,
        distance = d ∧
        ReachesExchange current (targetHand current target) distance := by
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih current hsumCurrent hmeasure
    by_cases hd : d = 0
    · have hsumzero :
          (∑ tile : Tile, (target tile - current.counts tile)) = 0 := by
        simpa [countDeficit, hd] using hmeasure
      have hzero :
          ∀ tile ∈ (Finset.univ : Finset Tile),
            target tile - current.counts tile = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg
          (fun tile _ => Nat.zero_le _)).mp
        exact hsumzero
      have hle : ∀ tile, target tile ≤ current.counts tile := by
        intro tile
        have hzeroTile := hzero tile (Finset.mem_univ tile)
        omega
      have heq :
          ∀ tile ∈ (Finset.univ : Finset Tile),
            target tile = current.counts tile := by
        apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
          (f := target) (g := current.counts)
          (fun tile _ => hle tile)).mp
        exact hsumCurrent.symm
      have hcounts : target = current.counts := by
        funext tile
        exact heq tile (Finset.mem_univ tile)
      subst hcounts
      refine ⟨0, ?_, ReachesExchange.done⟩
      simp [countDeficit] at hmeasure
      omega
    · have hpositive : 0 < d := Nat.pos_of_ne_zero hd
      have hne : current.counts ≠ target := by
        intro hcounts
        subst hcounts
        apply hd
        simpa [countDeficit] using hmeasure.symm
      obtain ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles⟩ :=
        exists_target_exchange_tiles current target hsumCurrent hne
      let next := exchangeHand current discarded drawn
      have hsumAfter :
          (∑ tile : Tile, next.counts tile) =
            ∑ tile : Tile, target tile := by
        change (∑ tile : Tile, exchangeCounts current discarded drawn tile) =
          ∑ tile : Tile, target tile
        rw [exchangeCounts_sum current discarded drawn hneTiles
          (by omega)]
        exact hsumCurrent
      have hdefAfterEq :
          countDeficit next.counts target = d - 1 := by
        dsimp [next]
        rw [countDeficit_exchange target current discarded drawn
          hdrawn hdiscarded hneTiles, hmeasure]
      have hdefAfter : countDeficit next.counts target < d := by
        omega
      obtain ⟨distance, hdistanceRest, hrest⟩ := ih
        (countDeficit next.counts target) hdefAfter next
        hsumAfter rfl
      refine ⟨distance + 1, ?_, ?_⟩
      · omega
      · apply ReachesExchange.step
        · exact mentsuHandTargetExchange_handStep target current discarded drawn
            hdrawn hdiscarded hneTiles
        · simpa [next, targetHand, exchangeHand] using hrest
  exact aux (countDeficit before.counts target) before hsum rfl

lemma complete_mentsuHand_targetHand
    (before : Hand) (target : TileCounts)
    (pair : Tile) (melds : List Meld)
    (hvalid : ValidCounts (targetHand before target))
    (hmelds : melds.length + before.fixedMelds = 4)
    (htiles :
      HasTiles (targetHand before target)
        (pairTiles pair + meldsTiles melds)) :
    Complete .mentsuHand (targetHand before target) := by
  exact ⟨hvalid, pair, melds, hmelds, htiles⟩

lemma reachesCompletion_mentsuHand_of_equal_sum
    (before : Hand) (target : TileCounts)
    (pair : Tile) (melds : List Meld)
    (hsum : (∑ tile : Tile, before.counts tile) =
      ∑ tile : Tile, target tile)
    (hvalid : ValidCounts (targetHand before target))
    (hmelds : melds.length + before.fixedMelds = 4)
    (htiles :
      HasTiles (targetHand before target)
        (pairTiles pair + meldsTiles melds)) :
    ReachesCompletion Complete .mentsuHand before
      (countDeficit before.counts target) := by
  obtain ⟨distance, hdistance, hexchange⟩ :=
    reachesExchange_targetHand_of_equal_sum before target hsum
  have hcomplete :
      Complete .mentsuHand (targetHand before target) :=
    complete_mentsuHand_targetHand before target pair melds
      hvalid hmelds htiles
  have hdone :
      ReachesCompletion Complete .mentsuHand
        (targetHand before target) 0 :=
    ReachesCompletion.done hcomplete
  simpa only [Nat.add_zero, hdistance] using
    ReachesExchange.toReachesCompletion hexchange hdone

lemma reachesCompletion_mentsuHand_of_one_more_target_tile
    (before : Hand) (target : TileCounts)
    (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, target tile) =
        (∑ tile : Tile, before.counts tile) + 1)
    (hbeforeValid : ValidCounts before)
    (hvalid : ValidCounts (targetHand before target))
    (hmelds : melds.length + before.fixedMelds = 4)
    (htiles :
      HasTiles (targetHand before target)
        (pairTiles pair + meldsTiles melds)) :
    ∃ distance,
      distance = countDeficit before.counts target ∧
      ReachesCompletion Complete .mentsuHand before distance := by
  have hdrawnExists : ∃ drawn, before.counts drawn < target drawn := by
    by_contra hnone
    push_neg at hnone
    have hle : ∀ tile, target tile ≤ before.counts tile := by
      intro tile
      exact hnone tile
    have hsumLe :=
      Finset.sum_le_sum (s := Finset.univ)
        (fun tile _ => hle tile)
    omega
  obtain ⟨drawn, hdrawn⟩ := hdrawnExists
  let next : Hand :=
    { counts := fun tile =>
        before.counts tile + (if tile = drawn then 1 else 0)
      fixedMelds := before.fixedMelds }
  have hnextValid : ValidCounts next := by
    intro tile
    by_cases htile : tile = drawn
    · subst tile
      have htarget := hvalid drawn
      change next.counts drawn ≤ 4
      simp [next]
      change target drawn ≤ 4 at htarget
      omega
    · have hbefore := hbeforeValid tile
      simpa [next, htile] using hbefore
  have hstep : HandStep before next := by
    refine ⟨rfl, Or.inl ⟨drawn, hnextValid, ?_⟩⟩
    intro tile
    rfl
  have hsumNext :
      (∑ tile : Tile, next.counts tile) =
        ∑ tile : Tile, target tile := by
    calc
      (∑ tile : Tile, next.counts tile) =
          (∑ tile : Tile, before.counts tile) + 1 := by
        simp [next, Finset.sum_add_distrib]
      _ = ∑ tile : Tile, target tile := by omega
  have hvalidNext : ValidCounts (targetHand next target) := by
    change ValidCounts (targetHand before target)
    exact hvalid
  have hmeldsNext : melds.length + next.fixedMelds = 4 := by
    change melds.length + before.fixedMelds = 4
    exact hmelds
  have htilesNext :
      HasTiles (targetHand next target)
        (pairTiles pair + meldsTiles melds) := by
    change HasTiles (targetHand before target)
      (pairTiles pair + meldsTiles melds)
    exact htiles
  have hcomplete :
      Complete .mentsuHand (targetHand next target) :=
    complete_mentsuHand_targetHand next target pair melds
      hvalidNext hmeldsNext htilesNext
  have hdone :
      ReachesCompletion Complete .mentsuHand
        (targetHand next target) 0 :=
    ReachesCompletion.done hcomplete
  obtain ⟨distance, hdistance, hexchange⟩ :=
    reachesExchange_targetHand_of_equal_sum next target hsumNext
  have hrest :
      ReachesCompletion Complete .mentsuHand next distance := by
    simpa using ReachesExchange.toReachesCompletion hexchange hdone
  have hdeficitNext :
      countDeficit next.counts target + 1 =
        countDeficit before.counts target := by
    change countDeficit
      (fun tile =>
        before.counts tile + (if tile = drawn then 1 else 0))
      target + 1 =
        countDeficit before.counts target
    exact countDeficit_draw before target drawn hdrawn
  have hdistanceTotal :
      distance + 1 = countDeficit before.counts target := by
    rw [hdistance]
    exact hdeficitNext
  exact ⟨distance + 1, hdistanceTotal,
    ReachesCompletion.step hstep hrest⟩

/-
## 5. ブロック分解

ブロック分解は、雀頭・通常の面子・ターツを記録します。これは、
制約付き探索が発見すべき数学的な証人です。この章では選択列の集計と
順序不変性を証明し、牌の枚数制限を破らずにターツを完成できることを示します。
-/

/-- A target has the required number of concealed melds for a hand. -/
def HasMentsuHandMeldCount (hand : Hand) (melds : List Meld) : Prop :=
  melds.length + hand.fixedMelds = 4

/-- A mentsu-hand-form decomposition before completing its taatsu blocks. -/
structure MentsuHandBlockDecomposition (hand : Hand) where
  pair : Tile
  melds : List Meld
  taatsus : List Taatsu
  blocks : melds.length + taatsus.length + hand.fixedMelds = 4
  targetWithinHand :
    ∀ tile,
      (mentsuHandTargetWithTaatsu pair melds taatsus).count tile ≤ hand.counts tile
  completionCopyLimit :
    ∀ tile,
      (mentsuHandTargetWithTaatsu pair melds taatsus +
        taatsuCompletionTiles taatsus).count tile ≤ 4

def mentsuHandChoiceTiles : List MentsuHandChoice → Multiset Tile
  | [] => 0
  | choice :: choices =>
      choiceTiles choice + mentsuHandChoiceTiles choices

def mentsuHandChoiceMeldCount : List MentsuHandChoice → Nat
  | [] => 0
  | choice :: choices =>
      (if choiceUsesMeld choice = true then 1 else 0) +
        mentsuHandChoiceMeldCount choices

def mentsuHandChoiceTaatsuCount : List MentsuHandChoice → Nat
  | [] => 0
  | choice :: choices =>
      (if choiceUsesTaatsu choice = true then 1 else 0) +
        mentsuHandChoiceTaatsuCount choices

def mentsuHandChoiceTaatsus : List MentsuHandChoice → List Taatsu
  | [] => []
  | .taatsu taatsu :: choices =>
      taatsu :: mentsuHandChoiceTaatsus choices
  | _ :: choices =>
      mentsuHandChoiceTaatsus choices

/-- Multiplicity-aware inclusion of choice columns.

Unlike `List.Sublist`, this relation does not impose an order on the selected
choices. It is the intermediate relation needed when a column is regrouped by
tile kind: repeated equal choices remain repeated, so a plain set inclusion is
not sufficient.
-/
def MentsuHandChoiceSubmultiset
    (subset superset : List MentsuHandChoice) : Prop :=
  (subset : Multiset MentsuHandChoice) ≤ superset

lemma MentsuHandChoiceSubmultiset.refl
    (choices : List MentsuHandChoice) :
    MentsuHandChoiceSubmultiset choices choices :=
  le_rfl

lemma MentsuHandChoiceSubmultiset.trans
    {left middle right : List MentsuHandChoice}
    (hleft : MentsuHandChoiceSubmultiset left middle)
    (hright : MentsuHandChoiceSubmultiset middle right) :
    MentsuHandChoiceSubmultiset left right :=
  le_trans hleft hright

lemma MentsuHandChoiceSubmultiset.of_perm
    {subset subset' superset : List MentsuHandChoice}
    (hperm : subset.Perm subset')
    (hsub : MentsuHandChoiceSubmultiset subset superset) :
    MentsuHandChoiceSubmultiset subset' superset := by
  have hsubset : (subset : Multiset MentsuHandChoice) =
      (subset' : Multiset MentsuHandChoice) :=
    Multiset.coe_eq_coe.mpr hperm
  simpa [MentsuHandChoiceSubmultiset, hsubset] using hsub

lemma MentsuHandChoiceSubmultiset.mem
    {subset superset : List MentsuHandChoice}
    (hsub : MentsuHandChoiceSubmultiset subset superset)
    {choice : MentsuHandChoice}
    (hchoice : choice ∈ subset) :
    choice ∈ superset :=
  Multiset.mem_of_le hsub hchoice

lemma MentsuHandChoiceSubmultiset.of_sublist
    {subset superset : List MentsuHandChoice}
    (hsub : List.Sublist subset superset) :
    MentsuHandChoiceSubmultiset subset superset := by
  induction hsub with
  | slnil =>
      exact bot_le
  | cons choice hsub ih =>
      simp only [MentsuHandChoiceSubmultiset] at ih ⊢
      exact ih.trans (Multiset.le_add_left
        _ ({choice} : Multiset MentsuHandChoice))
  | cons_cons choice hsub ih =>
      simp only [MentsuHandChoiceSubmultiset] at ih ⊢
      exact add_le_add
        (show ({choice} : Multiset MentsuHandChoice) ≤ {choice} from le_rfl)
        ih

lemma mentsuHandChoicesForTile_submultiset
    (tile : Tile) (choices : List MentsuHandChoice) :
    MentsuHandChoiceSubmultiset
      (mentsuHandChoicesForTile tile choices) choices :=
  MentsuHandChoiceSubmultiset.of_sublist
    (mentsuHandChoicesForTile_sublist tile choices)

lemma MentsuHandChoiceSubmultiset.append_left
    (left right : List MentsuHandChoice) :
    MentsuHandChoiceSubmultiset left (left ++ right) := by
  change (left : Multiset MentsuHandChoice) ≤
    (left : Multiset MentsuHandChoice) + right
  exact Multiset.le_add_right _ _

lemma MentsuHandChoiceSubmultiset.append_right
    (left right : List MentsuHandChoice) :
    MentsuHandChoiceSubmultiset right (left ++ right) := by
  change (right : Multiset MentsuHandChoice) ≤
    (left : Multiset MentsuHandChoice) + right
  exact Multiset.le_add_left _ _

lemma MentsuHandChoiceSubmultiset.append
    {left left' right right' : List MentsuHandChoice}
    (hleft : MentsuHandChoiceSubmultiset left left')
    (hright : MentsuHandChoiceSubmultiset right right') :
    MentsuHandChoiceSubmultiset (left ++ right) (left' ++ right') := by
  change (left ++ right : Multiset MentsuHandChoice) ≤
    (left' ++ right' : Multiset MentsuHandChoice)
  change (left : Multiset MentsuHandChoice) + right ≤
    (left' : Multiset MentsuHandChoice) + right'
  exact add_le_add hleft hright

lemma mentsuHandChoiceTaatsus_of_perm
    {choices choices' : List MentsuHandChoice}
    (hperm : List.Perm choices choices') :
    List.Perm (mentsuHandChoiceTaatsus choices)
      (mentsuHandChoiceTaatsus choices') := by
  induction hperm with
  | nil =>
      exact .nil
  | cons choice hperm ih =>
      cases choice <;>
        simp only [mentsuHandChoiceTaatsus, List.Perm.cons, ih]
  | swap choice choice' choices =>
      cases choice <;> cases choice' <;>
        simp only [mentsuHandChoiceTaatsus] <;>
        try rfl
      apply List.Perm.swap
  | trans hperm hperm' ih ih' =>
      exact ih.trans ih'

lemma mentsuHandChoiceTaatsus_append
    (choices choices' : List MentsuHandChoice) :
    mentsuHandChoiceTaatsus (choices ++ choices') =
      mentsuHandChoiceTaatsus choices ++ mentsuHandChoiceTaatsus choices' := by
  induction choices with
  | nil => rfl
  | cons choice choices ih =>
      cases choice <;>
        simp only [List.cons_append, mentsuHandChoiceTaatsus, ih]

lemma mentsuHandChoiceTaatsus_sublist_of_sublist
    {subset choices : List MentsuHandChoice}
    (hsub : List.Sublist subset choices) :
    List.Sublist (mentsuHandChoiceTaatsus subset)
      (mentsuHandChoiceTaatsus choices) := by
  induction hsub with
  | slnil =>
      exact .slnil
  | cons choice hsub ih =>
      cases choice with
      | skip | pair | meld =>
          simp only [mentsuHandChoiceTaatsus]
          exact ih
      | taatsu taatsu =>
          simp only [mentsuHandChoiceTaatsus]
          exact .cons _ ih
  | cons_cons choice hsub ih =>
      cases choice with
      | skip | pair | meld =>
          simp only [mentsuHandChoiceTaatsus]
          exact ih
      | taatsu taatsu =>
          simp only [mentsuHandChoiceTaatsus]
          exact .cons₂ taatsu ih

lemma mentsuHandChoiceTaatsus_sublist_append
    (choices choices' : List MentsuHandChoice) :
    List.Sublist (mentsuHandChoiceTaatsus choices)
      (mentsuHandChoiceTaatsus (choices ++ choices')) := by
  rw [mentsuHandChoiceTaatsus_append]
  induction mentsuHandChoiceTaatsus choices with
  | nil =>
      simp
  | cons taatsu taatsus ih =>
      exact List.Sublist.cons₂ taatsu ih

lemma mentsuHandChoiceMeldCount_append
    (left right : List MentsuHandChoice) :
    mentsuHandChoiceMeldCount (left ++ right) =
      mentsuHandChoiceMeldCount left +
        mentsuHandChoiceMeldCount right := by
  induction left with
  | nil =>
      simp [mentsuHandChoiceMeldCount]
  | cons choice left ih =>
      simp [mentsuHandChoiceMeldCount, ih, Nat.add_assoc]

lemma mentsuHandChoiceTaatsuCount_append
    (left right : List MentsuHandChoice) :
    mentsuHandChoiceTaatsuCount (left ++ right) =
      mentsuHandChoiceTaatsuCount left +
        mentsuHandChoiceTaatsuCount right := by
  induction left with
  | nil =>
      simp [mentsuHandChoiceTaatsuCount]
  | cons choice left ih =>
      simp [mentsuHandChoiceTaatsuCount, ih, Nat.add_assoc]

lemma mentsuHandChoiceTiles_append
    (left right : List MentsuHandChoice) :
    mentsuHandChoiceTiles (left ++ right) =
      mentsuHandChoiceTiles left + mentsuHandChoiceTiles right := by
  induction left with
  | nil =>
      simp [mentsuHandChoiceTiles]
  | cons choice left ih =>
      simp [mentsuHandChoiceTiles, ih, Multiset.add_assoc]

lemma mentsuHandChoiceTiles_of_perm
    {choices choices' : List MentsuHandChoice}
    (hperm : List.Perm choices choices') :
    mentsuHandChoiceTiles choices =
      mentsuHandChoiceTiles choices' := by
  induction hperm with
  | nil =>
      rfl
  | cons choice hperm ih =>
      simp [mentsuHandChoiceTiles, ih]
  | swap choice choice' choices =>
      simp [mentsuHandChoiceTiles, add_comm, add_left_comm, add_assoc]
  | trans hperm hperm' ih ih' =>
      exact ih.trans ih'

lemma mentsuHandChoiceMeldCount_of_perm
    {choices choices' : List MentsuHandChoice}
    (hperm : List.Perm choices choices') :
    mentsuHandChoiceMeldCount choices =
      mentsuHandChoiceMeldCount choices' := by
  induction hperm with
  | nil =>
      rfl
  | cons choice hperm ih =>
      simp [mentsuHandChoiceMeldCount, ih]
  | swap choice choice' choices =>
      simp [mentsuHandChoiceMeldCount, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc]
  | trans hperm hperm' ih ih' =>
      exact ih.trans ih'

lemma mentsuHandChoiceTaatsuCount_of_perm
    {choices choices' : List MentsuHandChoice}
    (hperm : List.Perm choices choices') :
    mentsuHandChoiceTaatsuCount choices =
      mentsuHandChoiceTaatsuCount choices' := by
  induction hperm with
  | nil =>
      rfl
  | cons choice hperm ih =>
      simp [mentsuHandChoiceTaatsuCount, ih]
  | swap choice choice' choices =>
      simp [mentsuHandChoiceTaatsuCount, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc]
  | trans hperm hperm' ih ih' =>
      exact ih.trans ih'

def MentsuHandBlockDecomposition.blockChoices
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    List MentsuHandChoice :=
  .pair decomposition.pair ::
    decomposition.melds.map MentsuHandChoice.meld ++
      decomposition.taatsus.map MentsuHandChoice.taatsu

lemma MentsuHandBlockDecomposition.blockChoices_length
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    decomposition.blockChoices.length =
      1 + decomposition.melds.length + decomposition.taatsus.length := by
  simp [MentsuHandBlockDecomposition.blockChoices]
  omega

lemma MentsuHandBlockDecomposition.blockChoices_meldCount
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    mentsuHandChoiceMeldCount decomposition.blockChoices =
      decomposition.melds.length := by
  have aux : ∀ melds : List Meld,
      mentsuHandChoiceMeldCount (melds.map MentsuHandChoice.meld) =
        melds.length := by
    intro melds
    induction melds with
    | nil =>
        simp [mentsuHandChoiceMeldCount]
    | cons meld melds ih =>
        simp [mentsuHandChoiceMeldCount, choiceUsesMeld, ih, Nat.add_comm]
  have auxZero : ∀ taatsus : List Taatsu,
      mentsuHandChoiceMeldCount (taatsus.map MentsuHandChoice.taatsu) = 0 := by
    intro taatsus
    induction taatsus with
    | nil =>
        rfl
    | cons taatsu taatsus ih =>
        simp [mentsuHandChoiceMeldCount, choiceUsesMeld, ih]
  simp [MentsuHandBlockDecomposition.blockChoices,
    mentsuHandChoiceMeldCount, choiceUsesMeld,
    mentsuHandChoiceMeldCount_append, aux, auxZero, Nat.add_comm] <;> omega

lemma MentsuHandBlockDecomposition.blockChoices_taatsuCount
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    mentsuHandChoiceTaatsuCount decomposition.blockChoices =
      decomposition.taatsus.length := by
  have aux : ∀ taatsus : List Taatsu,
      mentsuHandChoiceTaatsuCount (taatsus.map MentsuHandChoice.taatsu) =
        taatsus.length := by
    intro taatsus
    induction taatsus with
    | nil =>
        simp [mentsuHandChoiceTaatsuCount]
    | cons taatsu taatsus ih =>
        simp [mentsuHandChoiceTaatsuCount, choiceUsesTaatsu, ih, Nat.add_comm]
  have auxZero : ∀ melds : List Meld,
      mentsuHandChoiceTaatsuCount (melds.map MentsuHandChoice.meld) = 0 := by
    intro melds
    induction melds with
    | nil =>
        rfl
    | cons meld melds ih =>
        simp [mentsuHandChoiceTaatsuCount, choiceUsesTaatsu, ih]
  simp [MentsuHandBlockDecomposition.blockChoices,
    mentsuHandChoiceTaatsuCount, choiceUsesTaatsu,
    mentsuHandChoiceTaatsuCount_append, aux, auxZero, Nat.add_comm] <;> omega

lemma MentsuHandBlockDecomposition.blockChoices_tail_not_pair
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand)
    (choice : MentsuHandChoice)
    (hchoice :
      choice ∈
        decomposition.melds.map MentsuHandChoice.meld ++
          decomposition.taatsus.map MentsuHandChoice.taatsu) :
    choiceUsesPair choice = false := by
  simp only [List.mem_append, List.mem_map] at hchoice
  rcases hchoice with hmeld | htaatsu
  · rcases hmeld with ⟨meld, _, rfl⟩
    rfl
  · rcases htaatsu with ⟨taatsu, _, rfl⟩
    rfl

lemma MentsuHandBlockDecomposition.blockChoices_mem_all
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    ∀ choice, choice ∈ decomposition.blockChoices →
      choice ∈ allMentsuHandChoices := by
  intro choice hchoice
  unfold MentsuHandBlockDecomposition.blockChoices at hchoice
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hchoice
  rcases hchoice with (hpair | hmeld) | htaatsu
  · rw [hpair]
    exact mentsuHandChoice_mem_all _
  · rcases hmeld with ⟨meld, _, hmeld⟩
    rw [← hmeld]
    exact mentsuHandChoice_mem_all _
  · rcases htaatsu with ⟨taatsu, _, htaatsu⟩
    rw [← htaatsu]
    exact mentsuHandChoice_mem_all _

lemma MentsuHandBlockDecomposition.blockChoices_ne_skip
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand)
    {choice : MentsuHandChoice}
    (hchoice : choice ∈ decomposition.blockChoices) :
    choice ≠ .skip := by
  unfold MentsuHandBlockDecomposition.blockChoices at hchoice
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hchoice
  rcases hchoice with (rfl | ⟨meld, _, rfl⟩) | ⟨taatsu, _, rfl⟩
  · simp
  · simp
  · simp

lemma mentsuHandChoiceTiles_map_meld
    (melds : List Meld) :
    mentsuHandChoiceTiles (melds.map MentsuHandChoice.meld) =
      meldsTiles melds := by
  induction melds with
  | nil =>
      rfl
  | cons meld melds ih =>
      simp [mentsuHandChoiceTiles, choiceTiles, meldsTiles, ih]

lemma mentsuHandChoiceTiles_map_taatsu
    (taatsus : List Taatsu) :
    mentsuHandChoiceTiles (taatsus.map MentsuHandChoice.taatsu) =
      taatsuHistoryTiles taatsus := by
  induction taatsus with
  | nil =>
      rfl
  | cons taatsu taatsus ih =>
      simp [mentsuHandChoiceTiles, choiceTiles, taatsuHistoryTiles, ih]

lemma mentsuHandChoiceTaatsus_map_taatsu
   (taatsus : List Taatsu) :
   mentsuHandChoiceTaatsus (taatsus.map MentsuHandChoice.taatsu) =
     taatsus := by
  induction taatsus with
  | nil =>
     rfl
  | cons taatsu taatsus ih =>
     simp [mentsuHandChoiceTaatsus, ih]

lemma MentsuHandBlockDecomposition.blockChoices_taatsus
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    mentsuHandChoiceTaatsus decomposition.blockChoices =
     decomposition.taatsus := by
  have hmelds : ∀ melds : List Meld,
     mentsuHandChoiceTaatsus (melds.map MentsuHandChoice.meld) = [] := by
    intro melds
    induction melds with
    | nil =>
       rfl
    | cons meld melds ih =>
       simp [ih, mentsuHandChoiceTaatsus]
  unfold MentsuHandBlockDecomposition.blockChoices
  simp only [mentsuHandChoiceTaatsus, mentsuHandChoiceTaatsus_append,
    hmelds, List.nil_append, mentsuHandChoiceTaatsus_map_taatsu]

lemma MentsuHandBlockDecomposition.blockChoices_tiles
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    mentsuHandChoiceTiles decomposition.blockChoices =
      mentsuHandTargetWithTaatsu decomposition.pair decomposition.melds
        decomposition.taatsus := by
  unfold MentsuHandBlockDecomposition.blockChoices
  simp [mentsuHandChoiceTiles, choiceTiles, List.map_append,
    mentsuHandChoiceTiles_append,
    mentsuHandChoiceTiles_map_meld, mentsuHandChoiceTiles_map_taatsu,
    mentsuHandTargetWithTaatsu, mentsuHandTarget]
  ac_rfl

lemma mentsuHandChoiceTiles_count_le_of_sublist
    {subset choices : List MentsuHandChoice}
    (hsub : List.Sublist subset choices) :
    ∀ tile,
      (mentsuHandChoiceTiles subset).count tile ≤
        (mentsuHandChoiceTiles choices).count tile := by
  induction hsub with
  | slnil =>
      simp
  | cons choice hsub ih =>
      intro tile
      simp only [mentsuHandChoiceTiles, Multiset.count_add]
      exact (ih tile).trans (Nat.le_add_left _ _)
  | cons_cons choice hsub ih =>
      intro tile
      simp only [mentsuHandChoiceTiles, Multiset.count_add]
      have htail := ih tile
      omega

lemma mentsuHandChoiceMeldCount_le_of_sublist
    {subset choices : List MentsuHandChoice}
    (hsub : List.Sublist subset choices) :
    mentsuHandChoiceMeldCount subset ≤
      mentsuHandChoiceMeldCount choices := by
  induction hsub with
  | slnil =>
      simp [mentsuHandChoiceMeldCount]
  | cons choice hsub ih =>
      simp only [mentsuHandChoiceMeldCount] at ih ⊢
      omega
  | cons_cons choice hsub ih =>
      simp only [mentsuHandChoiceMeldCount] at ih ⊢
      omega

lemma mentsuHandChoiceTaatsuCount_le_of_sublist
    {subset choices : List MentsuHandChoice}
    (hsub : List.Sublist subset choices) :
    mentsuHandChoiceTaatsuCount subset ≤
      mentsuHandChoiceTaatsuCount choices := by
  induction hsub with
  | slnil =>
      simp [mentsuHandChoiceTaatsuCount]
  | cons choice hsub ih =>
      simp only [mentsuHandChoiceTaatsuCount] at ih ⊢
      omega
  | cons_cons choice hsub ih =>
      simp only [mentsuHandChoiceTaatsuCount] at ih ⊢
      omega

def MentsuHandBlockDecomposition.completedTarget
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    Multiset Tile :=
  mentsuHandTargetWithTaatsu decomposition.pair decomposition.melds
      decomposition.taatsus +
    taatsuCompletionTiles decomposition.taatsus

lemma MentsuHandBlockDecomposition.completedTarget_eq
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    decomposition.completedTarget =
      pairTiles decomposition.pair +
        meldsTiles
          (decomposition.melds ++
            taatsuCompletionMelds decomposition.taatsus) := by
  unfold MentsuHandBlockDecomposition.completedTarget
    mentsuHandTargetWithTaatsu mentsuHandTarget
  rw [meldsTiles_append]
  rw [← taatsuHistoryTiles_add_completionTiles]
  ac_rfl

lemma MentsuHandBlockDecomposition.validCounts_completedTarget
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    ValidCounts
      (targetHand hand (countsOfTiles decomposition.completedTarget)) := by
  intro tile
  exact decomposition.completionCopyLimit tile

lemma MentsuHandBlockDecomposition.completedMeldCount
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    (decomposition.melds ++
      taatsuCompletionMelds decomposition.taatsus).length +
        hand.fixedMelds = 4 := by
  rw [List.length_append, taatsuCompletionMelds_length]
  have hblocks := decomposition.blocks
  omega

def completedTargetForState (state : MentsuHandSearchState) (pair : Tile) :
    Multiset Tile :=
  pairTiles pair + meldsTiles (completedMeldsForState state)

def CompletionRespectsCopyLimit (state : MentsuHandSearchState) : Prop :=
  ∀ tile,
    (state.used + taatsuCompletionTiles state.taatsuHistory.reverse).count tile ≤ 4

lemma completionRespectsCopyLimit_of_history_perm
    (state : MentsuHandSearchState) (taatsus : List Taatsu)
    (hperm : List.Perm state.taatsuHistory.reverse taatsus)
    (hcopy : CompletionRespectsCopyLimit state) :
    ∀ tile,
      (state.used + taatsuCompletionTiles taatsus).count tile ≤ 4 := by
  intro tile
  rw [← taatsuCompletionTiles_of_perm hperm]
  exact hcopy tile

lemma MentsuHandBlockDecomposition.completion_respects_of_perm
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand)
    {state : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hperm : List.Perm choices decomposition.blockChoices)
    (hused : state.used = mentsuHandChoiceTiles choices)
    (hhistory :
      state.taatsuHistory.reverse =
        mentsuHandChoiceTaatsus choices) :
    CompletionRespectsCopyLimit state := by
  intro tile
  rw [hused]
  have husedPerm :
      mentsuHandChoiceTiles choices =
        mentsuHandChoiceTiles decomposition.blockChoices :=
    mentsuHandChoiceTiles_of_perm hperm
  rw [husedPerm]
  have hfull :
      (mentsuHandChoiceTiles decomposition.blockChoices +
        taatsuCompletionTiles decomposition.taatsus).count tile ≤ 4 := by
    rw [decomposition.blockChoices_tiles]
    exact decomposition.completionCopyLimit tile
  have htaatsuPerm :
      List.Perm
        (mentsuHandChoiceTaatsus choices)
        decomposition.taatsus := by
    rw [← decomposition.blockChoices_taatsus]
    exact mentsuHandChoiceTaatsus_of_perm hperm
  rw [hhistory, taatsuCompletionTiles_of_perm htaatsuPerm]
  rw [Multiset.count_add] at hfull ⊢
  exact hfull

/-
## 6. 牌の枚数制限付き走査

通常の遷移系に、同一牌は 4 枚までという制約を加えます。
同じ牌種を共有する複数ブロックを扱うため、各牌種の位置で複数選択を
連続して適用できるバッチ走査と、牌種ごとにグループ化した走査を定義します。
-/

def ValidMentsuHandChoiceWithCopyLimit
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice) : Prop :=
  ∃ hvalid : ValidMentsuHandChoice hand state choice,
    CompletionRespectsCopyLimit
      (applyMentsuHandChoice hand state choice hvalid)

lemma validMentsuHandChoiceWithCopyLimit_of
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand state choice hvalid)) :
    ValidMentsuHandChoiceWithCopyLimit hand state choice :=
  ⟨hvalid, hcopy⟩

def NextMentsuHandStateWithCopyLimit
    (hand : Hand) (state next : MentsuHandSearchState) : Prop :=
  ∃ choice, choice ∈ allMentsuHandChoices ∧
    ∃ hvalid : ValidMentsuHandChoice hand state choice,
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand state choice hvalid) ∧
      next = applyMentsuHandChoice hand state choice hvalid

lemma nextMentsuHandStateWithCopyLimit_of_choice
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hchoice : choice ∈ allMentsuHandChoices)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand state choice hvalid)) :
    NextMentsuHandStateWithCopyLimit hand state
      (applyMentsuHandChoice hand state choice hvalid) :=
  ⟨choice, hchoice, hvalid, hcopy, rfl⟩

noncomputable def copyLimitChoices
    (hand : Hand) (state : MentsuHandSearchState) : Finset MentsuHandChoice :=
  by
    classical
    exact allMentsuHandChoices.filter
      (fun choice =>
        ∃ hvalid : ValidMentsuHandChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuHandChoice hand state choice hvalid))

lemma mem_copyLimitChoices_iff
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice) :
    choice ∈ copyLimitChoices hand state ↔
      choice ∈ allMentsuHandChoices ∧
        ∃ hvalid : ValidMentsuHandChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuHandChoice hand state choice hvalid) := by
  classical
  change choice ∈ allMentsuHandChoices.filter _ ↔ _
  rw [Finset.mem_filter]

lemma nextMentsuHandStateWithCopyLimit_iff
    (hand : Hand) (state next : MentsuHandSearchState) :
    NextMentsuHandStateWithCopyLimit hand state next ↔
      ∃ choice, choice ∈ copyLimitChoices hand state ∧
        ∃ hvalid : ValidMentsuHandChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuHandChoice hand state choice hvalid) ∧
          next = applyMentsuHandChoice hand state choice hvalid := by
  classical
  constructor
  · rintro ⟨choice, hchoice, hvalid, hcopy, rfl⟩
    refine ⟨choice, ?_, hvalid, hcopy, rfl⟩
    change choice ∈ allMentsuHandChoices.filter _
    exact Finset.mem_filter.mpr ⟨hchoice, ⟨hvalid, hcopy⟩⟩
  · rintro ⟨choice, hchoice, hvalid, hcopy, rfl⟩
    change choice ∈ allMentsuHandChoices.filter _ at hchoice
    exact ⟨choice, (Finset.mem_filter.mp hchoice).1,
      hvalid, hcopy, rfl⟩

/-- Several blocks may be applied at one tile position before the scan advances.

The list is built by appending the newly applied choice, matching the forward
choice paths used below.
-/
inductive AppliesMentsuHandChoiceBatch (hand : Hand) (tile : Tile) :
    MentsuHandSearchState → List MentsuHandChoice →
      MentsuHandSearchState → Prop
  | nil (state : MentsuHandSearchState) :
      AppliesMentsuHandChoiceBatch hand tile state [] state
  | cons (state middle final : MentsuHandSearchState)
      (choices : List MentsuHandChoice) (choice : MentsuHandChoice)
      (htail :
        AppliesMentsuHandChoiceBatch hand tile state choices middle)
      (hchoice : choice ∈ allMentsuHandChoices)
      (htile : tile ∈ choiceTiles choice)
      (hvalid : ValidMentsuHandChoice hand middle choice)
      (hcopy :
        CompletionRespectsCopyLimit
          (applyMentsuHandChoice hand middle choice hvalid)) :
      AppliesMentsuHandChoiceBatch hand tile state
        (choices ++ [choice])
        (applyMentsuHandChoice hand middle choice hvalid)

lemma AppliesMentsuHandChoiceBatch.append
    {hand : Hand} {tile : Tile}
    {state middle final : MentsuHandSearchState}
    {choicesBefore choicesAfter : List MentsuHandChoice}
    (hbefore :
      AppliesMentsuHandChoiceBatch hand tile
        state choicesBefore middle)
    (hafter :
      AppliesMentsuHandChoiceBatch hand tile
        middle choicesAfter final) :
    AppliesMentsuHandChoiceBatch hand tile state
      (choicesBefore ++ choicesAfter) final := by
  induction hafter generalizing state choicesBefore with
  | nil =>
      simpa using hbefore
  | @cons state middle choices choice htail hchoice htile hvalid hcopy ih =>
      have hmiddle :=
        ih hbefore
      rw [← List.append_assoc]
      exact .cons _ _ (applyMentsuHandChoice hand _ choice hvalid)
        (choicesBefore ++ choices) choice
        hmiddle hchoice htile hvalid hcopy

/-- A tile-order scan whose step may apply a batch of choices at one tile. -/
inductive AppliesMentsuHandTileBatchScan (hand : Hand) :
    List Tile → MentsuHandSearchState → List MentsuHandChoice →
      MentsuHandSearchState → Prop
  | nil (state : MentsuHandSearchState) :
      AppliesMentsuHandTileBatchScan hand [] state [] state
  | step (tile : Tile) (tiles : List Tile)
      (state middle final : MentsuHandSearchState)
      (batchChoices choices : List MentsuHandChoice)
      (hbatch :
        AppliesMentsuHandChoiceBatch hand tile state batchChoices middle)
      (htail :
        AppliesMentsuHandTileBatchScan hand tiles middle choices final) :
      AppliesMentsuHandTileBatchScan hand (tile :: tiles) state
        (batchChoices ++ choices) final

lemma AppliesMentsuHandTileBatchScan.append
    {hand : Hand} {before rest : List Tile}
    {start middle final : MentsuHandSearchState}
    {choicesBefore choicesAfter : List MentsuHandChoice}
    (hbefore :
      AppliesMentsuHandTileBatchScan hand before
        start choicesBefore middle)
    (htail :
      AppliesMentsuHandTileBatchScan hand rest
        middle choicesAfter final) :
    AppliesMentsuHandTileBatchScan hand (before ++ rest)
      start (choicesBefore ++ choicesAfter) final := by
  induction before generalizing start middle choicesBefore with
  | nil =>
      cases hbefore
      simpa using htail
  | cons tile tiles ih =>
      cases hbefore with
      | step =>
          rename_i middle' batchChoices' choices' hbatch htail'
          simpa [List.append_assoc] using
            (.step tile (tiles ++ rest) start middle' final
              batchChoices' (choices' ++ choicesAfter) hbatch
              (ih htail' htail))

lemma AppliesMentsuHandTileBatchScan.single
    {hand : Hand} {tile : Tile}
    {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hbatch :
      AppliesMentsuHandChoiceBatch hand tile state choices final) :
    AppliesMentsuHandTileBatchScan hand [tile] state choices final :=
  by
    convert
      (AppliesMentsuHandTileBatchScan.step
        tile [] state final final choices [] hbatch (.nil final))
        using 1 <;> simp

/-- Batch traversal driven by representative groups.

The source column is carried separately from the tile-order scan. Each step
consumes exactly the choices whose representative is the current tile and
recurses on the remaining source column. The base case therefore requires the
remaining column to be empty.
-/
inductive AppliesMentsuHandGroupedTileBatches (hand : Hand) :
    List Tile → List MentsuHandChoice → MentsuHandSearchState →
      MentsuHandSearchState → Prop
  | nil (state : MentsuHandSearchState) :
      AppliesMentsuHandGroupedTileBatches hand [] [] state state
  | step (tile : Tile) (tiles : List Tile)
      (source : List MentsuHandChoice)
      (state middle final : MentsuHandSearchState)
      (hbatch :
        AppliesMentsuHandChoiceBatch hand tile state
          (mentsuHandChoicesForTile tile source) middle)
      (htail :
        AppliesMentsuHandGroupedTileBatches hand tiles
          (mentsuHandChoicesWithoutTile tile source) middle final) :
      AppliesMentsuHandGroupedTileBatches hand (tile :: tiles)
        source state final

lemma AppliesMentsuHandGroupedTileBatches.to_scan
    {hand : Hand} {tiles : List Tile}
    {choices : List MentsuHandChoice}
    {state final : MentsuHandSearchState}
    (hgrouped :
      AppliesMentsuHandGroupedTileBatches hand tiles choices state final) :
    AppliesMentsuHandTileBatchScan hand tiles state
      (mentsuHandChoicesGroupedByTiles tiles choices) final := by
  induction hgrouped with
  | nil state =>
      simpa [mentsuHandChoicesGroupedByTiles] using
        (AppliesMentsuHandTileBatchScan.nil state)
  | @step tile tiles source state middle final hbatch htail ih =>
      simpa [mentsuHandChoicesGroupedByTiles] using
        (AppliesMentsuHandTileBatchScan.step
          tile tiles state middle final
          (mentsuHandChoicesForTile tile source)
          (mentsuHandChoicesGroupedByTiles tiles
            (mentsuHandChoicesWithoutTile tile source))
          hbatch ih)

lemma nextMentsuHandStateWithCopyLimit_copyLimit
    (hand : Hand) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandStateWithCopyLimit hand state next) :
    CompletionRespectsCopyLimit next := by
  rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
  exact hcopy

def reachableWithinWithCopyLimit
    (hand : Hand) : Nat → MentsuHandSearchState → Prop
  | 0, state => state = initialMentsuHandState
  | fuel + 1, state =>
      ∃ previous,
        reachableWithinWithCopyLimit hand fuel previous ∧
        NextMentsuHandStateWithCopyLimit hand previous state

lemma initialMentsuHandState_copyLimit :
    CompletionRespectsCopyLimit initialMentsuHandState := by
  intro tile
  simp [CompletionRespectsCopyLimit, initialMentsuHandState,
    taatsuCompletionTiles]

lemma reachableWithinWithCopyLimit_copyLimit
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    CompletionRespectsCopyLimit state := by
  induction fuel generalizing state with
  | zero =>
      rw [hreachable]
      exact initialMentsuHandState_copyLimit
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      exact nextMentsuHandStateWithCopyLimit_copyLimit hand previous state hnext

lemma reachableWithinWithCopyLimit_append_choice
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (choice : MentsuHandChoice)
    (hreachable : reachableWithinWithCopyLimit hand fuel state)
    (hchoice : choice ∈ allMentsuHandChoices)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand state choice hvalid)) :
    reachableWithinWithCopyLimit hand (fuel + 1)
      (applyMentsuHandChoice hand state choice hvalid) :=
  ⟨state, hreachable,
    nextMentsuHandStateWithCopyLimit_of_choice
      hand state choice hchoice hvalid hcopy⟩

lemma reachableWithinWithCopyLimit_melds_le_four
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    state.melds ≤ 4 := by
  induction fuel generalizing state with
  | zero =>
      subst state
      simp [initialMentsuHandState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
      have hbound := hvalid.2.1
      simp only [applyMentsuHandChoice] at hbound ⊢
      omega

lemma reachableWithinWithCopyLimit_used_subset
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    ∀ tile, state.used.count tile ≤ hand.counts tile := by
  induction fuel generalizing state with
  | zero =>
      intro tile
      subst state
      simp [initialMentsuHandState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      intro tile
      rcases hnext with ⟨choice, _, hvalid, _, rfl⟩
      exact hvalid.1 tile

lemma reachableWithinWithCopyLimit_taatsu_le_four
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    state.taatsu ≤ 4 := by
  induction fuel generalizing state with
  | zero =>
      subst state
      simp [initialMentsuHandState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
      have hbound := hvalid.2.2.1
      simp only [applyMentsuHandChoice] at hbound ⊢
      omega

def MentsuHandChoiceStateMatches
    (state : MentsuHandSearchState)
    (choices : List MentsuHandChoice) : Prop :=
  state.used = mentsuHandChoiceTiles choices ∧
    state.melds = mentsuHandChoiceMeldCount choices ∧
    state.taatsu = mentsuHandChoiceTaatsuCount choices

lemma mentsuHandChoiceStateMatches_of_perm
    {state : MentsuHandSearchState}
    {choices choices' : List MentsuHandChoice}
    (hperm : List.Perm choices choices')
    (hmatches : MentsuHandChoiceStateMatches state choices) :
    MentsuHandChoiceStateMatches state choices' := by
  have htiles := mentsuHandChoiceTiles_of_perm hperm
  have hmelds := mentsuHandChoiceMeldCount_of_perm hperm
  have htaatsus := mentsuHandChoiceTaatsuCount_of_perm hperm
  exact ⟨hmatches.1.trans htiles, hmatches.2.1.trans hmelds,
    hmatches.2.2.trans htaatsus⟩

lemma mentsuHandChoiceStateMatches_of_groupedByTiles
    {state : MentsuHandSearchState}
    {tiles : List Tile} {choices : List MentsuHandChoice}
    (hrep :
      ∀ choice, choice ∈ choices →
        ∃ tile, tile ∈ tiles ∧
          mentsuHandChoiceRepresentative choice = some tile)
    (hmatches : MentsuHandChoiceStateMatches state choices) :
    MentsuHandChoiceStateMatches state
      (mentsuHandChoicesGroupedByTiles tiles choices ++
        mentsuHandChoicesWithoutTileForTiles tiles choices) := by
  have hperm :=
    mentsuHandChoicesGroupedByTiles_perm_append hrep
  exact mentsuHandChoiceStateMatches_of_perm hperm.symm hmatches

inductive AppliesMentsuHandChoicesForwardWithCopyLimit (hand : Hand) :
    MentsuHandSearchState → List MentsuHandChoice →
      MentsuHandSearchState → Prop
  | nil (state : MentsuHandSearchState) :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand state [] state
  | snoc (state middle : MentsuHandSearchState)
      (choices : List MentsuHandChoice) (choice : MentsuHandChoice)
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit hand state choices middle)
      (hchoice : choice ∈ allMentsuHandChoices)
      (hvalid : ValidMentsuHandChoice hand middle choice)
      (hcopy :
        CompletionRespectsCopyLimit
          (applyMentsuHandChoice hand middle choice hvalid)) :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand state
        (choices ++ [choice])
        (applyMentsuHandChoice hand middle choice hvalid)

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.append
    {hand : Hand}
    {state middle final : MentsuHandSearchState}
    {choicesBefore choicesAfter : List MentsuHandChoice}
    (hbefore :
      AppliesMentsuHandChoicesForwardWithCopyLimit
        hand state choicesBefore middle)
    (hafter :
      AppliesMentsuHandChoicesForwardWithCopyLimit
        hand middle choicesAfter final) :
    AppliesMentsuHandChoicesForwardWithCopyLimit
      hand state (choicesBefore ++ choicesAfter) final := by
  induction hafter generalizing state choicesBefore with
  | nil =>
      simpa using hbefore
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
      have hmiddle :=
        ih hbefore
      rw [← List.append_assoc]
      exact .snoc _ _ (choicesBefore ++ choices) choice
        hmiddle hchoice hvalid hcopy

lemma AppliesMentsuHandChoiceBatch.of_forward
    {hand : Hand} {tile : Tile}
    {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand
        state choices final)
    (htile :
      ∀ choice, choice ∈ choices → tile ∈ choiceTiles choice) :
    AppliesMentsuHandChoiceBatch hand tile state choices final := by
  induction hpath generalizing tile with
  | nil =>
      exact .nil _
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
      have htail :=
        ih (fun candidate hcandidate =>
          htile candidate (by
            exact List.mem_append_left [choice] hcandidate))
      have hchoiceTile :
          tile ∈ choiceTiles choice :=
        htile choice (by simp)
      exact .cons _ _ (applyMentsuHandChoice hand middle choice hvalid)
        choices choice htail hchoice hchoiceTile hvalid hcopy

lemma AppliesMentsuHandChoiceBatch.of_forward_for_representative_tile
    {hand : Hand} {tile : Tile}
    {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand
        state choices final)
    (hchoices :
      ∀ choice, choice ∈ choices →
        mentsuHandChoiceRepresentative choice = some tile) :
    AppliesMentsuHandChoiceBatch hand tile state choices final :=
  AppliesMentsuHandChoiceBatch.of_forward hpath
    (fun choice hchoice =>
      mentsuHandChoiceRepresentative_mem
        (hchoices choice hchoice))

lemma AppliesMentsuHandChoiceBatch.of_forward_for_tile_filter
    {hand : Hand} {tile : Tile}
    {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand
        state (mentsuHandChoicesForTile tile choices) final) :
    AppliesMentsuHandChoiceBatch hand tile state
      (mentsuHandChoicesForTile tile choices) final :=
  AppliesMentsuHandChoiceBatch.of_forward_for_representative_tile
    hpath
    (fun choice hchoice =>
      mentsuHandChoicesForTile_representative hchoice)

lemma AppliesMentsuHandGroupedTileBatches.step_of_forward
    {hand : Hand} {tile : Tile} {tiles : List Tile}
    {source : List MentsuHandChoice}
    {state middle final : MentsuHandSearchState}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand
        state (mentsuHandChoicesForTile tile source) middle)
    (htail :
      AppliesMentsuHandGroupedTileBatches hand tiles
        (mentsuHandChoicesWithoutTile tile source) middle final) :
    AppliesMentsuHandGroupedTileBatches hand (tile :: tiles)
      source state final :=
  .step tile tiles source state middle final
    (AppliesMentsuHandChoiceBatch.of_forward_for_tile_filter hpath)
    htail

lemma reachableWithinWithCopyLimit_of_forward_choice_path
    {hand : Hand} {final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand
        initialMentsuHandState choices final) :
    reachableWithinWithCopyLimit hand choices.length final := by
  induction hpath with
  | nil =>
      rfl
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
      have hnext :=
        reachableWithinWithCopyLimit_append_choice
          hand choices.length middle choice ih hchoice hvalid hcopy
      simpa [List.length_append] using hnext

lemma applyMentsuHandChoice.state_matches_append_single
    {hand : Hand} {state : MentsuHandSearchState}
    {choices : List MentsuHandChoice} (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hmatches : MentsuHandChoiceStateMatches state choices) :
    MentsuHandChoiceStateMatches
      (applyMentsuHandChoice hand state choice hvalid)
      (choices ++ [choice]) := by
  rcases hmatches with ⟨hused, hmelds, htaatsu⟩
  cases choice <;>
    simp [MentsuHandChoiceStateMatches, applyMentsuHandChoice,
      mentsuHandChoiceTiles, mentsuHandChoiceMeldCount,
      mentsuHandChoiceTaatsuCount, hused, hmelds, htaatsu,
      mentsuHandChoiceTiles_append,
      mentsuHandChoiceMeldCount_append,
      mentsuHandChoiceTaatsuCount_append, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] <;> ac_rfl

lemma AppliesMentsuHandChoiceBatch.state_matches_append
    {hand : Hand} {tile : Tile}
    {state final : MentsuHandSearchState}
    {pre choices : List MentsuHandChoice}
    (hbatch :
      AppliesMentsuHandChoiceBatch hand tile state choices final)
    (hmatches : MentsuHandChoiceStateMatches state pre) :
    MentsuHandChoiceStateMatches final (pre ++ choices) := by
  induction hbatch generalizing pre with
  | nil =>
      simpa using hmatches
  | @cons state middle choices choice htail hchoice htile hvalid hcopy ih =>
      have hstate :
          MentsuHandChoiceStateMatches state (pre ++ choices) :=
        ih hmatches
      have hfinal :=
        applyMentsuHandChoice.state_matches_append_single
          choice hvalid hstate
      simpa [List.append_assoc] using hfinal

lemma AppliesMentsuHandChoiceBatch.state_matches_from_initial
    {hand : Hand} {tile : Tile}
    {state : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hbatch :
      AppliesMentsuHandChoiceBatch hand tile
        initialMentsuHandState choices state) :
    MentsuHandChoiceStateMatches state choices :=
  hbatch.state_matches_append (pre := [])
    (by
      simp [MentsuHandChoiceStateMatches, initialMentsuHandState,
        mentsuHandChoiceTiles, mentsuHandChoiceMeldCount,
        mentsuHandChoiceTaatsuCount])

lemma AppliesMentsuHandTileBatchScan.state_matches_append
    {hand : Hand}
    {tiles : List Tile}
    {state final : MentsuHandSearchState}
    {pre choices : List MentsuHandChoice}
    (hscan :
      AppliesMentsuHandTileBatchScan hand tiles state choices final)
    (hmatches : MentsuHandChoiceStateMatches state pre) :
    MentsuHandChoiceStateMatches final (pre ++ choices) := by
  induction hscan generalizing pre with
  | nil =>
      simpa using hmatches
  | @step tile tiles start middle final batchChoices choices hbatch htail ih =>
      have hmiddle :=
        AppliesMentsuHandChoiceBatch.state_matches_append
          hbatch hmatches
      have hfinal := ih hmiddle
      simpa [List.append_assoc] using hfinal

lemma applyMentsuHandChoice.taatsuHistory_reverse_append_single
    {hand : Hand} {state : MentsuHandSearchState}
    {choices : List MentsuHandChoice} (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hhistory :
      state.taatsuHistory.reverse =
        mentsuHandChoiceTaatsus choices) :
    (applyMentsuHandChoice hand state choice hvalid).taatsuHistory.reverse =
      mentsuHandChoiceTaatsus (choices ++ [choice]) := by
  cases choice <;>
    simp [applyMentsuHandChoice, mentsuHandChoiceTaatsus,
      mentsuHandChoiceTaatsus_append, hhistory, List.reverse_append]

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.state_matches_append
    {hand : Hand}
    {state final : MentsuHandSearchState}
    {pre choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit
        hand state choices final)
    (hmatches : MentsuHandChoiceStateMatches state pre) :
    MentsuHandChoiceStateMatches final (pre ++ choices) := by
  induction hpath generalizing pre with
  | nil =>
      simpa using hmatches
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
      have hmiddle :=
        ih hmatches
      have hfinal :=
        applyMentsuHandChoice.state_matches_append_single
          choice hvalid hmiddle
      simpa [List.append_assoc] using hfinal

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.taatsuHistory_reverse_append
    {hand : Hand}
    {state final : MentsuHandSearchState}
    {pre choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit
        hand state choices final)
    (hhistory :
      state.taatsuHistory.reverse =
        mentsuHandChoiceTaatsus pre) :
    final.taatsuHistory.reverse =
      mentsuHandChoiceTaatsus (pre ++ choices) := by
  induction hpath generalizing pre with
  | nil =>
      simpa using hhistory
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
      have hmiddle := ih hhistory
      have hfinal :=
        applyMentsuHandChoice.taatsuHistory_reverse_append_single
          choice hvalid hmiddle
      simpa [List.append_assoc] using hfinal

lemma AppliesMentsuHandChoiceBatch.taatsuHistory_reverse_append
    {hand : Hand} {tile : Tile}
    {state final : MentsuHandSearchState}
    {pre choices : List MentsuHandChoice}
    (hbatch :
      AppliesMentsuHandChoiceBatch hand tile state choices final)
    (hhistory :
      state.taatsuHistory.reverse =
        mentsuHandChoiceTaatsus pre) :
    final.taatsuHistory.reverse =
      mentsuHandChoiceTaatsus (pre ++ choices) := by
  induction hbatch generalizing pre with
  | nil =>
      simpa using hhistory
  | @cons state middle choices choice htail hchoice htile hvalid hcopy ih =>
      have hstate :
          state.taatsuHistory.reverse =
            mentsuHandChoiceTaatsus (pre ++ choices) :=
        ih hhistory
      have hfinal :=
        applyMentsuHandChoice.taatsuHistory_reverse_append_single
          choice hvalid hstate
      simpa [List.append_assoc] using hfinal

lemma AppliesMentsuHandChoiceBatch.taatsuHistory_reverse_from_initial
    {hand : Hand} {tile : Tile}
    {state : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hbatch :
      AppliesMentsuHandChoiceBatch hand tile
        initialMentsuHandState choices state) :
    state.taatsuHistory.reverse =
      mentsuHandChoiceTaatsus choices :=
  hbatch.taatsuHistory_reverse_append (pre := []) (by
    simp [initialMentsuHandState, mentsuHandChoiceTaatsus])

lemma AppliesMentsuHandTileBatchScan.taatsuHistory_reverse_append
    {hand : Hand}
    {tiles : List Tile}
    {state final : MentsuHandSearchState}
    {pre choices : List MentsuHandChoice}
    (hscan :
      AppliesMentsuHandTileBatchScan hand tiles state choices final)
    (hhistory :
      state.taatsuHistory.reverse =
        mentsuHandChoiceTaatsus pre) :
    final.taatsuHistory.reverse =
      mentsuHandChoiceTaatsus (pre ++ choices) := by
  induction hscan generalizing pre with
  | nil =>
      simpa using hhistory
  | @step tile tiles start middle final batchChoices choices hbatch htail ih =>
      have hmiddle :=
        AppliesMentsuHandChoiceBatch.taatsuHistory_reverse_append
          hbatch hhistory
      have hfinal := ih hmiddle
      simpa [List.append_assoc] using hfinal

lemma reachableWithinWithCopyLimit_of_choice_batch
    {hand : Hand} {tile : Tile}
    {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (fuel : Nat)
    (hreachable :
      reachableWithinWithCopyLimit hand fuel state)
    (hbatch :
      AppliesMentsuHandChoiceBatch hand tile state choices final) :
    reachableWithinWithCopyLimit hand
      (fuel + choices.length) final := by
  induction hbatch generalizing fuel with
  | nil =>
      simpa using hreachable
  | @cons state middle choices choice htail hchoice htile hvalid hcopy ih =>
      have hstate :
          reachableWithinWithCopyLimit hand
            (fuel + choices.length) state :=
        ih fuel hreachable
      have hnext :=
        reachableWithinWithCopyLimit_append_choice
          hand (fuel + choices.length) state choice
          hstate hchoice hvalid hcopy
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hnext

lemma reachableWithinWithCopyLimit_of_tile_batch_scan
    {hand : Hand}
    {tiles : List Tile}
    {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (fuel : Nat)
    (hreachable :
      reachableWithinWithCopyLimit hand fuel state)
    (hscan :
      AppliesMentsuHandTileBatchScan hand tiles state choices final) :
    reachableWithinWithCopyLimit hand
      (fuel + choices.length) final := by
  induction hscan generalizing fuel with
  | nil =>
      simpa using hreachable
  | @step tile tiles start middle final batchChoices choices hbatch htail ih =>
      have hmiddle :=
        reachableWithinWithCopyLimit_of_choice_batch
          fuel hreachable hbatch
      have hfinal :=
        ih (fuel + batchChoices.length) hmiddle
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hfinal

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.state_matches_from_initial
    {hand : Hand} {final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand
        initialMentsuHandState choices final) :
    MentsuHandChoiceStateMatches final choices := by
  induction hpath with
  | nil =>
      simp [MentsuHandChoiceStateMatches, initialMentsuHandState,
        mentsuHandChoiceTiles, mentsuHandChoiceMeldCount,
        mentsuHandChoiceTaatsuCount]
  | @snoc state middle choices hpath hchoice hvalid hcopy ih =>
      exact applyMentsuHandChoice.state_matches_append_single
        _ hvalid ih

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.taatsuHistory_reverse_from_initial
    {hand : Hand} {final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand
        initialMentsuHandState choices final) :
    final.taatsuHistory.reverse =
      mentsuHandChoiceTaatsus choices := by
  induction hpath with
  | nil =>
      rfl
  | @snoc state middle choices hpath hchoice hvalid hcopy ih =>
      exact applyMentsuHandChoice.taatsuHistory_reverse_append_single
        _ hvalid ih

def mentsuHandChoicePairCount : List MentsuHandChoice → Nat
  | [] => 0
  | .pair _ :: choices => mentsuHandChoicePairCount choices + 1
  | _ :: choices => mentsuHandChoicePairCount choices

lemma mentsuHandChoicePairCount_append
      (left right : List MentsuHandChoice) :
      mentsuHandChoicePairCount (left ++ right) =
        mentsuHandChoicePairCount left +
          mentsuHandChoicePairCount right := by
  induction left with
  | nil =>
        simp [mentsuHandChoicePairCount]
  | cons choice left ih =>
        cases choice <;>
          simp [mentsuHandChoicePairCount, ih, Nat.add_assoc] <;> omega

lemma mentsuHandChoicePairCount_of_perm
      {choices choices' : List MentsuHandChoice}
      (hperm : List.Perm choices choices') :
      mentsuHandChoicePairCount choices =
        mentsuHandChoicePairCount choices' := by
  induction hperm with
  | nil =>
        rfl
  | cons choice hperm ih =>
        cases choice <;> simp [mentsuHandChoicePairCount, ih]
  | swap choice choice' choices =>
        cases choice <;> cases choice' <;>
          simp [mentsuHandChoicePairCount, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
  | trans hperm hperm' ih ih' =>
        exact ih.trans ih'

lemma MentsuHandBlockDecomposition.blockChoices_pairCount
      {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
      mentsuHandChoicePairCount decomposition.blockChoices = 1 := by
  have meldsCount (melds : List Meld) :
        mentsuHandChoicePairCount (melds.map MentsuHandChoice.meld) = 0 := by
      induction melds with
      | nil => rfl
      | cons meld melds ih => simpa [mentsuHandChoicePairCount] using ih
  have taatsusCount (taatsus : List Taatsu) :
        mentsuHandChoicePairCount (taatsus.map MentsuHandChoice.taatsu) = 0 := by
      induction taatsus with
      | nil => rfl
      | cons taatsu taatsus ih => simpa [mentsuHandChoicePairCount] using ih
  change mentsuHandChoicePairCount
        (MentsuHandChoice.pair decomposition.pair ::
          (decomposition.melds.map MentsuHandChoice.meld ++
            decomposition.taatsus.map MentsuHandChoice.taatsu)) = 1
  rw [mentsuHandChoicePairCount, mentsuHandChoicePairCount_append,
      meldsCount, taatsusCount]

lemma list_sublist_nil {α : Type} (choices : List α) :
    List.Sublist ([] : List α) choices := by
  induction choices with
  | nil => exact .slnil
  | cons choice choices ih => exact .cons choice ih

lemma list_append_single_sublist {α : Type}
    (before : List α) (choice : α) (after : List α) :
    List.Sublist (before ++ [choice]) (before ++ choice :: after) := by
  induction before with
  | nil =>
      exact .cons_cons choice (list_sublist_nil after)
  | cons head before ih =>
      simpa [List.cons_append] using (List.Sublist.cons_cons head ih)

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.pair_none_of_pairCount_eq_zero
      {hand : Hand} {choices : List MentsuHandChoice}
      {final : MentsuHandSearchState}
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState choices final)
      (hcount : mentsuHandChoicePairCount choices = 0) :
      final.pair.isNone := by
  induction hpath with
  | nil =>
        simp [initialMentsuHandState]
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
        rw [mentsuHandChoicePairCount_append] at hcount
        cases choice with
        | pair tile =>
            simp [mentsuHandChoicePairCount] at hcount
        | skip =>
            have hprefix : mentsuHandChoicePairCount choices = 0 := by
              simpa [mentsuHandChoicePairCount] using hcount
            simpa [applyMentsuHandChoice] using ih hprefix
        | taatsu taatsu =>
            have hprefix : mentsuHandChoicePairCount choices = 0 := by
              simpa [mentsuHandChoicePairCount] using hcount
            simpa [applyMentsuHandChoice] using ih hprefix
        | meld meld =>
            have hprefix : mentsuHandChoicePairCount choices = 0 := by
              simpa [mentsuHandChoicePairCount] using hcount
            simpa [applyMentsuHandChoice] using ih hprefix

lemma MentsuHandBlockDecomposition.forwardPath_of_perm_aux
      {hand : Hand}
      (decomposition : MentsuHandBlockDecomposition hand) :
      ∀ (processed choices : List MentsuHandChoice)
        (state : MentsuHandSearchState),
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState processed state →
        List.Perm (processed ++ choices) decomposition.blockChoices →
        ∃ final,
          AppliesMentsuHandChoicesForwardWithCopyLimit hand state choices final := by
  intro processed choices state hpath hperm
  induction choices generalizing processed state with
  | nil =>
        exact ⟨state, .nil state⟩
  | cons choice choices ih =>
        have hpairTotal :
            mentsuHandChoicePairCount (processed ++ choice :: choices) = 1 := by
          calc
            mentsuHandChoicePairCount (processed ++ choice :: choices) =
                mentsuHandChoicePairCount decomposition.blockChoices :=
              mentsuHandChoicePairCount_of_perm hperm
            _ = 1 := decomposition.blockChoices_pairCount
        have hpairSplit :
            mentsuHandChoicePairCount processed +
              mentsuHandChoicePairCount (choice :: choices) = 1 := by
          rw [← mentsuHandChoicePairCount_append]
          exact hpairTotal
        have hpartial :
            List.Sublist (processed ++ [choice]) (processed ++ choice :: choices) :=
          list_append_single_sublist processed choice choices
        have hmatches := hpath.state_matches_from_initial
        have hpartialTilesLe (tile : Tile) :
            (mentsuHandChoiceTiles (processed ++ [choice])).count tile ≤
              (mentsuHandChoiceTiles decomposition.blockChoices).count tile := by
          have hsubLe :=
            mentsuHandChoiceTiles_count_le_of_sublist hpartial tile
          have hfullTiles :
              mentsuHandChoiceTiles (processed ++ choice :: choices) =
                mentsuHandChoiceTiles decomposition.blockChoices :=
            mentsuHandChoiceTiles_of_perm hperm
          calc
            (mentsuHandChoiceTiles (processed ++ [choice])).count tile ≤
                (mentsuHandChoiceTiles (processed ++ choice :: choices)).count tile :=
              hsubLe
            _ = (mentsuHandChoiceTiles decomposition.blockChoices).count tile :=
              congrArg (fun tiles : Multiset Tile => tiles.count tile) hfullTiles
        have hused :
            ∀ tile, (state.used + choiceTiles choice).count tile ≤
              hand.counts tile := by
          intro tile
          calc
            (state.used + choiceTiles choice).count tile =
                (mentsuHandChoiceTiles (processed ++ [choice])).count tile := by
                  rw [mentsuHandChoiceTiles_append, hmatches.1]
                  simp [mentsuHandChoiceTiles, Multiset.count_add]
            _ ≤ (mentsuHandChoiceTiles decomposition.blockChoices).count tile :=
              hpartialTilesLe tile
            _ = (mentsuHandTargetWithTaatsu decomposition.pair
                decomposition.melds decomposition.taatsus).count tile := by
              rw [decomposition.blockChoices_tiles]
            _ ≤ hand.counts tile := decomposition.targetWithinHand tile
        have hpartialMelds :
            mentsuHandChoiceMeldCount (processed ++ [choice]) =
              mentsuHandChoiceMeldCount processed +
                (if choiceUsesMeld choice = true then 1 else 0) := by
          rw [mentsuHandChoiceMeldCount_append]
          cases choice <;> rfl
        have hpartialTaatsus :
            mentsuHandChoiceTaatsuCount (processed ++ [choice]) =
              mentsuHandChoiceTaatsuCount processed +
                (if choiceUsesTaatsu choice = true then 1 else 0) := by
          rw [mentsuHandChoiceTaatsuCount_append]
          cases choice <;> rfl
        have hfullMelds :
            mentsuHandChoiceMeldCount (processed ++ choice :: choices) =
              decomposition.melds.length := by
          calc
            mentsuHandChoiceMeldCount (processed ++ choice :: choices) =
                mentsuHandChoiceMeldCount decomposition.blockChoices :=
              mentsuHandChoiceMeldCount_of_perm hperm
            _ = decomposition.melds.length :=
              decomposition.blockChoices_meldCount
        have hfullTaatsus :
            mentsuHandChoiceTaatsuCount (processed ++ choice :: choices) =
              decomposition.taatsus.length := by
          calc
            mentsuHandChoiceTaatsuCount (processed ++ choice :: choices) =
                mentsuHandChoiceTaatsuCount decomposition.blockChoices :=
              mentsuHandChoiceTaatsuCount_of_perm hperm
            _ = decomposition.taatsus.length :=
              decomposition.blockChoices_taatsuCount
        have hmelds :
            state.melds + (if choiceUsesMeld choice = true then 1 else 0) ≤ 4 := by
          have hpartialLe :=
            mentsuHandChoiceMeldCount_le_of_sublist hpartial
          have hblocks := decomposition.blocks
          rw [hmatches.2.1, ← hpartialMelds]
          calc
            mentsuHandChoiceMeldCount (processed ++ [choice]) ≤
                mentsuHandChoiceMeldCount (processed ++ choice :: choices) :=
              hpartialLe
            _ = decomposition.melds.length := hfullMelds
            _ ≤ 4 := by omega
        have htaatsu :
            state.taatsu + (if choiceUsesTaatsu choice = true then 1 else 0) ≤ 4 := by
          have hpartialLe :=
            mentsuHandChoiceTaatsuCount_le_of_sublist hpartial
          have hblocks := decomposition.blocks
          rw [hmatches.2.2, ← hpartialTaatsus]
          calc
            mentsuHandChoiceTaatsuCount (processed ++ [choice]) ≤
                mentsuHandChoiceTaatsuCount (processed ++ choice :: choices) :=
              hpartialLe
            _ = decomposition.taatsus.length := hfullTaatsus
            _ ≤ 4 := by omega
        have hpair :
            state.pair.isNone ∨ choiceUsesPair choice = false := by
          cases choice with
          | pair tile =>
              have hprocessed : mentsuHandChoicePairCount processed = 0 := by
                simp [mentsuHandChoicePairCount] at hpairSplit
                omega
              exact Or.inl
                (hpath.pair_none_of_pairCount_eq_zero hprocessed)
          | skip =>
              exact Or.inr rfl
          | taatsu taatsu =>
              exact Or.inr rfl
          | meld meld =>
              exact Or.inr rfl
        have hvalid : ValidMentsuHandChoice hand state choice :=
          ⟨hused, hmelds, htaatsu, hpair⟩
        have hpartialTaatsusSub :
            List.Sublist
              (mentsuHandChoiceTaatsus (processed ++ [choice]))
              (mentsuHandChoiceTaatsus (processed ++ choice :: choices)) :=
          mentsuHandChoiceTaatsus_sublist_of_sublist hpartial
        have htaatsuPerm :
            List.Perm
              (mentsuHandChoiceTaatsus (processed ++ choice :: choices))
              decomposition.taatsus := by
          rw [← decomposition.blockChoices_taatsus]
          exact mentsuHandChoiceTaatsus_of_perm hperm
        have hcompletionLe (tile : Tile) :
            (taatsuCompletionTiles
                (mentsuHandChoiceTaatsus (processed ++ [choice]))).count tile ≤
              (taatsuCompletionTiles decomposition.taatsus).count tile := by
          have hsubLe :=
            taatsuCompletionTiles_count_le_of_sublist hpartialTaatsusSub tile
          calc
            (taatsuCompletionTiles
                (mentsuHandChoiceTaatsus (processed ++ [choice]))).count tile ≤
                (taatsuCompletionTiles
                  (mentsuHandChoiceTaatsus (processed ++ choice :: choices))).count tile :=
              hsubLe
            _ = (taatsuCompletionTiles decomposition.taatsus).count tile := by
              rw [taatsuCompletionTiles_of_perm htaatsuPerm]
        let next := applyMentsuHandChoice hand state choice hvalid
        have hmatchesNext :
            MentsuHandChoiceStateMatches next (processed ++ [choice]) := by
          exact applyMentsuHandChoice.state_matches_append_single
            choice hvalid hmatches
        have hhistoryNext :
            next.taatsuHistory.reverse =
              mentsuHandChoiceTaatsus (processed ++ [choice]) := by
          exact applyMentsuHandChoice.taatsuHistory_reverse_append_single
            choice hvalid (hpath.taatsuHistory_reverse_from_initial)
        have hcopy : CompletionRespectsCopyLimit next := by
          intro tile
          have hfull := decomposition.completionCopyLimit tile
          rw [← decomposition.blockChoices_tiles] at hfull
          have hfullCount :
              (mentsuHandChoiceTiles decomposition.blockChoices).count tile +
                (taatsuCompletionTiles decomposition.taatsus).count tile ≤ 4 := by
            simpa [Multiset.count_add] using hfull
          have hpartialCount :
              (mentsuHandChoiceTiles (processed ++ [choice])).count tile +
                (taatsuCompletionTiles
                  (mentsuHandChoiceTaatsus (processed ++ [choice]))).count tile ≤ 4 :=
            (Nat.add_le_add (hpartialTilesLe tile) (hcompletionLe tile)).trans
              hfullCount
          rw [hmatchesNext.1, hhistoryNext]
          simpa only [Multiset.count_add] using hpartialCount
        have hstep :
            AppliesMentsuHandChoicesForwardWithCopyLimit
              hand state [choice] next := by
          have hmem : choice ∈ processed ++ choice :: choices := by
            apply List.mem_append_right
            simp
          exact .snoc state state [] choice (.nil state)
            (decomposition.blockChoices_mem_all choice
              ((List.Perm.mem_iff hperm).1 hmem))
            hvalid hcopy
        have hpathNext := hpath.append hstep
        have hpermNext :
            ((processed ++ [choice]) ++ choices).Perm
              decomposition.blockChoices := by
          simpa [List.append_assoc] using hperm
        obtain ⟨final, htail⟩ :=
          ih (processed ++ [choice]) next hpathNext hpermNext
        exact ⟨final, hstep.append htail⟩

lemma MentsuHandBlockDecomposition.forwardPath_of_perm
      {hand : Hand}
      (decomposition : MentsuHandBlockDecomposition hand)
      {choices : List MentsuHandChoice}
      (hperm : List.Perm choices decomposition.blockChoices) :
      ∃ final,
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState choices final := by
  exact decomposition.forwardPath_of_perm_aux [] choices
      initialMentsuHandState
      (AppliesMentsuHandChoicesForwardWithCopyLimit.nil
        initialMentsuHandState)
      (by simpa using hperm)

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.uncons
      {hand : Hand} {state final : MentsuHandSearchState}
      {choices : List MentsuHandChoice}
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand state choices final)
      (hne : choices ≠ []) :
      ∃ choice rest middle,
        choices = choice :: rest ∧
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand state [choice] middle ∧
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand middle rest final := by
  induction hpath with
  | nil =>
        exact (hne rfl).elim
  | @snoc middle choices choice hprefix hchoice hvalid hcopy ih =>
        cases choices with
        | nil =>
            refine ⟨choice, [], applyMentsuHandChoice hand middle choice hvalid,
              ?_, .snoc state middle [] choice hprefix hchoice hvalid hcopy,
              .nil _⟩
            simp
        | cons first choices =>
            obtain ⟨head, tail, firstMiddle, hshape, firstPath, restPath⟩ :=
              ih (by simp)
            rcases List.cons.inj hshape with ⟨rfl, rfl⟩
            let lastPath :
                AppliesMentsuHandChoicesForwardWithCopyLimit
                  hand middle [choice]
                  (applyMentsuHandChoice hand middle choice hvalid) :=
              .snoc middle middle [] choice (.nil middle)
                hchoice hvalid hcopy
            refine ⟨first, choices ++ [choice], firstMiddle, ?_,
              firstPath, restPath.append lastPath⟩
            simp [List.cons_append, List.append_assoc]

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.final_eq_of_empty
    {hand : Hand} {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand state choices final)
    (hempty : choices = []) :
    final = state := by
  induction hpath with
  | nil =>
        rfl
  | @snoc middle choices choice hprefix hchoice hvalid hcopy ih =>
        simp at hempty

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.split_append
      {hand : Hand} {state final : MentsuHandSearchState}
      {before after : List MentsuHandChoice}
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand state (before ++ after) final) :
      ∃ split,
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand state before split ∧
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand split after final := by
  induction before generalizing state with
  | nil =>
        exact ⟨state, .nil state, by simpa using hpath⟩
  | cons choice before ih =>
        have hnonempty : (choice :: before) ++ after ≠ [] := by
          simp
        obtain ⟨head, tail, firstMiddle, hshape, hfirst, hrest⟩ :=
          AppliesMentsuHandChoicesForwardWithCopyLimit.uncons
            (by simpa [List.cons_append] using hpath) hnonempty
        rcases List.cons.inj hshape with ⟨rfl, rfl⟩
        obtain ⟨split, hbefore, hafter⟩ := ih hrest
        exact ⟨split, hfirst.append hbefore, hafter⟩

lemma MentsuHandBlockDecomposition.blockChoices_representatives_in_tileOrder
      {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
      ∀ choice, choice ∈ decomposition.blockChoices →
        ∃ tile, tile ∈ mentsuHandTileOrder ∧
          mentsuHandChoiceRepresentative choice = some tile := by
  intro choice hchoice
  have hnotSkip := decomposition.blockChoices_ne_skip hchoice
  cases choice with
  | skip =>
        exact (hnotSkip rfl).elim
  | pair tile =>
        exact ⟨tile, tile_mem_mentsuHandTileOrder tile, rfl⟩
  | taatsu taatsu =>
        cases taatsu with
        | pair tile =>
            exact ⟨tile, tile_mem_mentsuHandTileOrder tile, rfl⟩
        | sequence suit start =>
            exact ⟨Tile.suited suit ⟨start.val, by omega⟩,
              tile_mem_mentsuHandTileOrder _, rfl⟩
  | meld meld =>
        cases meld with
        | triplet tile =>
            exact ⟨tile, tile_mem_mentsuHandTileOrder tile, rfl⟩
        | sequence suit start =>
            exact ⟨Tile.suited suit ⟨start.val, by omega⟩,
              tile_mem_mentsuHandTileOrder _, rfl⟩

lemma AppliesMentsuHandGroupedTileBatches.of_forward_grouping
      {hand : Hand} {tiles : List Tile}
      {source : List MentsuHandChoice}
      {state final : MentsuHandSearchState}
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand state (mentsuHandChoicesGroupedByTiles tiles source) final)
      (hrep :
        ∀ choice, choice ∈ source →
          ∃ tile, tile ∈ tiles ∧
            mentsuHandChoiceRepresentative choice = some tile) :
      AppliesMentsuHandGroupedTileBatches hand tiles source state final := by
  induction tiles generalizing source state with
  | nil =>
        have hsource : source = [] := by
          cases source with
          | nil => rfl
          | cons choice source =>
              obtain ⟨tile, htile, _⟩ := hrep choice (by simp)
              simp at htile
        subst source
        have hpathEmpty :
            AppliesMentsuHandChoicesForwardWithCopyLimit hand state [] final := by
          simpa [mentsuHandChoicesGroupedByTiles] using hpath
        have hfinal :=
          hpathEmpty.final_eq_of_empty rfl
        rw [hfinal]
        exact .nil state
  | cons tile tiles ih =>
        have htailRep :
            ∀ choice, choice ∈ mentsuHandChoicesWithoutTile tile source →
              ∃ nextTile, nextTile ∈ tiles ∧
                mentsuHandChoiceRepresentative choice = some nextTile := by
          intro choice hchoice
          obtain ⟨nextTile, hmem, hrepChoice⟩ :=
            hrep choice (mentsuHandChoicesWithoutTile_mem hchoice)
          have hne :=
            mentsuHandChoicesWithoutTile_representative_ne hchoice
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact (hne hrepChoice).elim
          · exact ⟨nextTile, hmem, hrepChoice⟩
        have hsplit :=
          AppliesMentsuHandChoicesForwardWithCopyLimit.split_append
            (by simpa [mentsuHandChoicesGroupedByTiles] using hpath)
        obtain ⟨middle, hbatchPath, htailPath⟩ := hsplit
        have hbatch :
            AppliesMentsuHandChoiceBatch hand tile state
              (mentsuHandChoicesForTile tile source) middle :=
          AppliesMentsuHandChoiceBatch.of_forward_for_tile_filter hbatchPath
        have htail := ih htailPath htailRep
        exact .step tile tiles source state middle final hbatch htail

lemma MentsuHandBlockDecomposition.forwardPath_groupedByTiles
      {hand : Hand}
      (decomposition : MentsuHandBlockDecomposition hand) :
      ∃ final,
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState
            (mentsuHandChoicesGroupedByTiles
              mentsuHandTileOrder decomposition.blockChoices) final := by
  apply decomposition.forwardPath_of_perm
  exact mentsuHandChoicesGroupedByTiles_perm
      decomposition.blockChoices_representatives_in_tileOrder

lemma MentsuHandBlockDecomposition.blockChoices_pair_choice
      {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand)
      {choice : MentsuHandChoice}
      (hchoice : choice ∈ decomposition.blockChoices)
      (hpair : choiceUsesPair choice = true) :
      choice = .pair decomposition.pair := by
  cases choice with
  | skip =>
        simp [choiceUsesPair] at hpair
  | pair tile =>
        change MentsuHandChoice.pair tile ∈ decomposition.blockChoices at hchoice
        unfold MentsuHandBlockDecomposition.blockChoices at hchoice
        simp only [List.mem_cons, List.mem_append, List.mem_map] at hchoice
        rcases hchoice with hpairChoice | htail
        · simpa using hpairChoice
        · simp at htail
  | taatsu taatsu =>
        simp [choiceUsesPair] at hpair
  | meld meld =>
        simp [choiceUsesPair] at hpair

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.pair_eq_none_or_target
      {hand : Hand} {choices : List MentsuHandChoice}
      {final : MentsuHandSearchState} {pair : Tile}
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState choices final)
      (hpairChoices :
        ∀ choice, choice ∈ choices →
          choiceUsesPair choice = true → choice = .pair pair) :
      final.pair = none ∨ final.pair = some pair := by
  induction hpath with
  | nil =>
        exact Or.inl rfl
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
        have hprefix :
            ∀ candidate, candidate ∈ choices →
              choiceUsesPair candidate = true →
                candidate = .pair pair := by
          intro candidate hmem huses
          apply hpairChoices candidate
          · exact List.mem_append_left [choice] hmem
          · exact huses
        have hprev := ih hprefix
        have hlast :
            choiceUsesPair choice = true → choice = .pair pair := by
          intro huses
          exact hpairChoices choice (by simp) huses
        cases choice with
        | pair tile =>
            have hchoiceEq := hlast rfl
            cases hchoiceEq
            simp [applyMentsuHandChoice]
        | skip =>
            simpa [applyMentsuHandChoice] using hprev
        | taatsu taatsu =>
            simpa [applyMentsuHandChoice] using hprev
        | meld meld =>
            simpa [applyMentsuHandChoice] using hprev

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.pair_isSome_of_pairCount_pos
      {hand : Hand} {choices : List MentsuHandChoice}
      {final : MentsuHandSearchState}
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState choices final)
      (hcount : 0 < mentsuHandChoicePairCount choices) :
      final.pair.isSome := by
  induction hpath with
  | nil =>
        simp [mentsuHandChoicePairCount] at hcount
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
        rw [mentsuHandChoicePairCount_append] at hcount
        cases choice with
        | pair tile =>
            simp [applyMentsuHandChoice]
        | skip =>
            have hprefix : 0 < mentsuHandChoicePairCount choices := by
              simpa [mentsuHandChoicePairCount] using hcount
            simpa [applyMentsuHandChoice] using ih hprefix
        | taatsu taatsu =>
            have hprefix : 0 < mentsuHandChoicePairCount choices := by
              simpa [mentsuHandChoicePairCount] using hcount
            simpa [applyMentsuHandChoice] using ih hprefix
        | meld meld =>
            have hprefix : 0 < mentsuHandChoicePairCount choices := by
              simpa [mentsuHandChoicePairCount] using hcount
            simpa [applyMentsuHandChoice] using ih hprefix

lemma MentsuHandBlockDecomposition.finalState_of_groupedForwardPath
      {hand : Hand}
      (decomposition : MentsuHandBlockDecomposition hand)
      {final : MentsuHandSearchState}
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState
            (mentsuHandChoicesGroupedByTiles
              mentsuHandTileOrder decomposition.blockChoices) final) :
      final.pair = some decomposition.pair ∧
        IsMentsuHandBlockSearchComplete hand final := by
  let choices :=
      mentsuHandChoicesGroupedByTiles
        mentsuHandTileOrder decomposition.blockChoices
  have hperm : List.Perm choices decomposition.blockChoices :=
      mentsuHandChoicesGroupedByTiles_perm
        decomposition.blockChoices_representatives_in_tileOrder
  have hpairChoices :
        ∀ choice, choice ∈ choices →
          choiceUsesPair choice = true →
            choice = .pair decomposition.pair := by
      intro choice hchoice hpair
      exact decomposition.blockChoices_pair_choice
        ((List.Perm.mem_iff hperm).1 hchoice) hpair
  have hpairState := hpath.pair_eq_none_or_target hpairChoices
  have hpairCount : 0 < mentsuHandChoicePairCount choices := by
      rw [mentsuHandChoicePairCount_of_perm hperm,
        decomposition.blockChoices_pairCount]
      omega
  have hpairSome := hpath.pair_isSome_of_pairCount_pos hpairCount
  have hpair : final.pair = some decomposition.pair := by
      rcases hpairState with hnone | hsome
      · simp [hnone] at hpairSome
      · exact hsome
  have hmatches := hpath.state_matches_from_initial
  have hmelds :
        final.melds = decomposition.melds.length := by
      calc
        final.melds = mentsuHandChoiceMeldCount choices := hmatches.2.1
        _ = mentsuHandChoiceMeldCount decomposition.blockChoices :=
          mentsuHandChoiceMeldCount_of_perm hperm
        _ = decomposition.melds.length :=
          decomposition.blockChoices_meldCount
  have htaatsu :
        final.taatsu = decomposition.taatsus.length := by
      calc
        final.taatsu = mentsuHandChoiceTaatsuCount choices := hmatches.2.2
        _ = mentsuHandChoiceTaatsuCount decomposition.blockChoices :=
          mentsuHandChoiceTaatsuCount_of_perm hperm
        _ = decomposition.taatsus.length :=
          decomposition.blockChoices_taatsuCount
  refine ⟨hpair, ?_⟩
  unfold IsMentsuHandBlockSearchComplete
  constructor
  · rw [hmelds, htaatsu]
    exact decomposition.blocks
  · simp [hpair]

lemma MentsuHandBlockDecomposition.exists_groupedForwardPath_complete
      {hand : Hand}
      (decomposition : MentsuHandBlockDecomposition hand) :
      ∃ final,
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState
            (mentsuHandChoicesGroupedByTiles
              mentsuHandTileOrder decomposition.blockChoices) final ∧
        final.pair = some decomposition.pair ∧
        IsMentsuHandBlockSearchComplete hand final := by
  obtain ⟨final, hpath⟩ :=
      decomposition.forwardPath_groupedByTiles
  exact ⟨final, hpath,
      decomposition.finalState_of_groupedForwardPath hpath⟩

lemma MentsuHandBlockDecomposition.exists_tileBatchScan_complete
      {hand : Hand}
      (decomposition : MentsuHandBlockDecomposition hand) :
      ∃ final,
        AppliesMentsuHandTileBatchScan hand mentsuHandTileOrder
          initialMentsuHandState
          (mentsuHandChoicesGroupedByTiles
            mentsuHandTileOrder decomposition.blockChoices) final ∧
        final.pair = some decomposition.pair ∧
        IsMentsuHandBlockSearchComplete hand final := by
  obtain ⟨final, hpath, hpair, hcomplete⟩ :=
      decomposition.exists_groupedForwardPath_complete
  have hgrouped :=
      AppliesMentsuHandGroupedTileBatches.of_forward_grouping hpath
        decomposition.blockChoices_representatives_in_tileOrder
  exact ⟨final, hgrouped.to_scan, hpair, hcomplete⟩

private def reviewExampleEast : Tile :=
  .honor ⟨0, by omega⟩

private def reviewExampleMan1 : Tile :=
  .suited .man ⟨0, by omega⟩

private def reviewExampleMan2 : Tile :=
  .suited .man ⟨1, by omega⟩

private def reviewExampleTaatsu : Taatsu :=
  .sequence .man ⟨0, by omega⟩

private def reviewExampleHand : Hand :=
  { counts := countsOfTiles
      (mentsuHandTargetWithTaatsu reviewExampleEast []
          (List.replicate 4 reviewExampleTaatsu) +
        Multiset.replicate 1 (.suited .pin ⟨8, by omega⟩) +
        Multiset.replicate 1 (.suited .sou ⟨8, by omega⟩) +
        Multiset.replicate 1 (.honor ⟨3, by omega⟩))
    fixedMelds := 0 }

private def reviewExampleDecomposition :
    MentsuHandBlockDecomposition reviewExampleHand :=
  { pair := reviewExampleEast
    melds := []
    taatsus := List.replicate 4 reviewExampleTaatsu
    blocks := by simp [reviewExampleHand]
    targetWithinHand := by
      intro tile
      simp [reviewExampleHand, countsOfTiles, mentsuHandTargetWithTaatsu,
        mentsuHandTarget, Multiset.count_add] <;> omega
    completionCopyLimit := by
      intro tile
      cases tile with
      | suited suit rank =>
        cases suit <;> fin_cases rank <;>
          simp [reviewExampleHand, reviewExampleEast, reviewExampleMan1,
            reviewExampleMan2, reviewExampleTaatsu,
            mentsuHandTargetWithTaatsu, mentsuHandTarget, taatsuHistoryTiles,
              taatsuTiles, taatsuCompletionTiles, taatsuCompletionTile,
              pairTiles, meldsTiles] <;> omega
      | honor rank =>
        fin_cases rank <;>
        simp [reviewExampleHand, reviewExampleEast, reviewExampleMan1,
          reviewExampleMan2, reviewExampleTaatsu,
          mentsuHandTargetWithTaatsu, mentsuHandTarget, taatsuHistoryTiles,
          taatsuTiles, taatsuCompletionTiles, taatsuCompletionTile,
          pairTiles, meldsTiles] <;> omega }

example :
    ∃ final,
      AppliesMentsuHandTileBatchScan reviewExampleHand mentsuHandTileOrder
        initialMentsuHandState
        (mentsuHandChoicesGroupedByTiles
          mentsuHandTileOrder reviewExampleDecomposition.blockChoices) final ∧
      final.pair = some reviewExampleEast ∧
      IsMentsuHandBlockSearchComplete reviewExampleHand final :=
  reviewExampleDecomposition.exists_tileBatchScan_complete

lemma applyMentsuHandChoice_pair_eq_some
    (hand : Hand) (state : MentsuHandSearchState) (tile : Tile)
    (hvalid : ValidMentsuHandChoice hand state (.pair tile))
    (hpair : state.pair = none) :
    (applyMentsuHandChoice hand state (.pair tile) hvalid).pair =
      some tile := by
  simp [applyMentsuHandChoice, hpair]

lemma applyMentsuHandChoice_pair_eq_of_not_pair
    (hand : Hand) (state : MentsuHandSearchState)
    (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (pair : Tile) (hpair : state.pair = some pair)
    (hchoice : choiceUsesPair choice = false) :
    (applyMentsuHandChoice hand state choice hvalid).pair =
      some pair := by
  cases choice with
  | skip | taatsu | meld =>
      simp [applyMentsuHandChoice, hpair]
  | pair tile =>
      simp [choiceUsesPair] at hchoice

lemma nextMentsuHandStateWithCopyLimit_toNext
    (hand : Hand) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandStateWithCopyLimit hand state next) :
    NextMentsuHandState hand state next := by
  rcases hnext with ⟨choice, hchoice, hvalid, _, rfl⟩
  exact ⟨choice, hchoice, hvalid, rfl⟩

lemma reachableWithinWithCopyLimit_to_reachableWithin
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    reachableWithin hand fuel state := by
  induction fuel generalizing state with
  | zero =>
      exact hreachable
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rw [reachableWithin_succ_iff]
      exact ⟨previous, ih previous hprevious,
        nextMentsuHandStateWithCopyLimit_toNext hand previous state hnext⟩

/-
## 7. 探索状態から完成目標へ

制約付き走査を確立した後、ここでは到達した探索状態から妥当な
面子手の完成目標を構成します。また、その面子数・牌数・枚数制限を
取り扱います。これは走査の健全性側の補題であり、走査の全域性や
全13枚手に対する最小値一致は主張しません。
-/

lemma completedTargetForState_eq_used_add_completion
    (state : MentsuHandSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    completedTargetForState state pair =
      stateHistoryTiles state +
        taatsuCompletionTiles state.taatsuHistory.reverse := by
  rw [completedTargetForState, completedMeldsForState_tiles state pair hpair]
  rw [mentsuHandTargetWithTaatsuOfState_eq_stateHistoryTiles state pair hpair]

lemma validCounts_completedTarget_of_copyLimit
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcopy : CompletionRespectsCopyLimit state)
    (pair : Tile) (hpair : state.pair = some pair) :
    ValidCounts
      (targetHand before
        (countsOfTiles (completedTargetForState state pair))) := by
  intro tile
  have htarget := hcopy tile
  change (completedTargetForState state pair).count tile ≤ 4
  rw [completedTargetForState_eq_used_add_completion state pair hpair]
  rw [← reachableWithin_used_eq_historyTiles before fuel state hreachable]
  exact htarget

lemma completedMeldsForState_card (state : MentsuHandSearchState) :
    (meldsTiles (completedMeldsForState state)).card =
      3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  rw [meldsTiles_card, completedMeldsForState_length]

lemma completedTargetForState_card
    (state : MentsuHandSearchState) (pair : Tile) :
    (completedTargetForState state pair).card =
      2 + 3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  unfold completedTargetForState
  rw [Multiset.card_add, pairTiles_card, completedMeldsForState_card]

lemma completedTargetForState_sum
    (state : MentsuHandSearchState) (pair : Tile) :
    (∑ tile : Tile, countsOfTiles (completedTargetForState state pair) tile) =
      2 + 3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  rw [countsOfTiles_sum_eq_card, completedTargetForState_card]

lemma completedTargetForState_sum_of_blockCount
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcount : state.melds + state.taatsu + before.fixedMelds = 4)
    (pair : Tile) :
    (∑ tile : Tile,
      countsOfTiles (completedTargetForState state pair) tile) =
        14 - 3 * before.fixedMelds := by
  have hmelds := reachableWithin_melds_eq_history_length
    before fuel state hreachable
  have htaatsu := reachableWithin_taatsu_eq_history_length
    before fuel state hreachable
  rw [completedTargetForState_sum, ← hmelds, ← htaatsu]
  omega

lemma completedTargetForState_sum_eq_tileCount
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcount : state.melds + state.taatsu + before.fixedMelds = 4)
    (hstanding : tileCount before = 14 - 3 * before.fixedMelds)
    (pair : Tile) :
    (∑ tile : Tile,
      countsOfTiles (completedTargetForState state pair) tile) =
        tileCount before := by
  rw [completedTargetForState_sum_of_blockCount
    before fuel state hreachable hcount pair]
  exact hstanding.symm

lemma complete_mentsuHand_completedTarget
    (before : Hand) (state : MentsuHandSearchState) (pair : Tile)
    (hvalid : ValidCounts
      (targetHand before (countsOfTiles (completedTargetForState state pair))))
    (hmelds : HasMentsuHandMeldCount before (completedMeldsForState state)) :
    Complete .mentsuHand
      (targetHand before (countsOfTiles (completedTargetForState state pair))) := by
  apply complete_mentsuHand_targetHand
  · exact hvalid
  · exact hmelds
  · exact targetHand_hasTiles_countsOfTiles before
      (completedTargetForState state pair)

/-- A target is a valid mentsu-hand-form completion for the standing tiles. -/
/-
## 8. 動的計画法の意味論

有限個の目標 DP とコスト DP を定義します。集合への所属を特徴付ける補題により、
再帰的な Finset の定義を単なるブラックボックスの計算として扱うのではなく、
各 DP 状態が数学的に何を意味するかを説明します。
-/

def IsMentsuHandTarget
    (hand : Hand) (pair : Tile) (melds : List Meld) : Prop :=
  HasMentsuHandMeldCount hand melds ∧
    ∀ tile, hand.counts tile ≤
      (mentsuHandTarget pair melds).count tile

/-- The number of additional tiles needed to realize a mentsuHand target. -/
def mentsuHandTargetDistance
    (hand : Hand) (pair : Tile) (melds : List Meld) : Nat :=
  targetDeficit hand (mentsuHandTarget pair melds)

lemma mentsuHandTargetDistance_eq_countDeficit
    (hand : Hand) (pair : Tile) (melds : List Meld) :
    mentsuHandTargetDistance hand pair melds =
      countDeficit hand.counts
        (countsOfTiles (mentsuHandTarget pair melds)) := by
  rfl

def mentsuHandMeldListsOfLength : Nat → Finset (List Meld)
  | 0 => {[]}
  | length + 1 =>
      Finset.univ.biUnion fun meld =>
        (mentsuHandMeldListsOfLength length).image (meld :: ·)

lemma mem_mentsuHandMeldListsOfLength_iff
    (length : Nat) (melds : List Meld) :
    melds ∈ mentsuHandMeldListsOfLength length ↔ melds.length = length := by
  induction length generalizing melds with
  | zero =>
      simp [mentsuHandMeldListsOfLength]
  | succ length ih =>
      simp only [mentsuHandMeldListsOfLength, Finset.mem_biUnion,
        Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨head, tail, htail, rfl⟩
        have hlength := ih tail |>.1 htail
        simp only [List.length_cons]
        omega
      · intro hlength
        cases melds with
        | nil =>
            simp at hlength
        | cons head tail =>
            simp only [List.length_cons] at hlength
            refine ⟨head, tail, ?_, rfl⟩
            exact ih tail |>.2 (by omega)

def mentsuHandTargetConfigurations (fixedMelds : Nat) :
    Finset (Tile × List Meld) :=
  Finset.univ ×ˢ mentsuHandMeldListsOfLength (4 - fixedMelds)

def validCountsDecidable (hand : Hand) : Decidable (ValidCounts hand) := by
  unfold ValidCounts
  exact Fintype.decidableForallFintype

def validCountsBool (hand : Hand) : Bool :=
  @decide (ValidCounts hand) (validCountsDecidable hand)

lemma validCountsBool_eq_true_iff (hand : Hand) :
    validCountsBool hand = true ↔ ValidCounts hand := by
  simp [validCountsBool]

def validTileMultisetBool (tiles : Multiset Tile) : Bool :=
  validCountsBool
    { counts := countsOfTiles tiles
      fixedMelds := 0 }

lemma validTileMultisetBool_eq_true_iff (tiles : Multiset Tile) :
    validTileMultisetBool tiles = true ↔
      ∀ tile, tiles.count tile ≤ 4 := by
  change validCountsBool
    { counts := countsOfTiles tiles
      fixedMelds := 0 } = true ↔ _
  rw [validCountsBool_eq_true_iff]
  rfl

lemma validTileMultisetBool_add_left
    (tiles extra : Multiset Tile)
    (hvalid : validTileMultisetBool (tiles + extra) = true) :
    validTileMultisetBool tiles = true := by
  apply (validTileMultisetBool_eq_true_iff tiles).2
  intro tile
  have hsum :=
    (validTileMultisetBool_eq_true_iff (tiles + extra)).1 hvalid tile
  have hle : tiles.count tile ≤ (tiles + extra).count tile := by
    simp only [Multiset.count_add]
    omega
  omega

lemma validTileMultisetBool_eq_true_iff_targetHand
    (hand : Hand) (tiles : Multiset Tile) :
    validTileMultisetBool tiles = true ↔
      ValidCounts (targetHand hand (countsOfTiles tiles)) := by
  rw [validTileMultisetBool_eq_true_iff]
  change (∀ tile, tiles.count tile ≤ 4) ↔
    (∀ tile, tiles.count tile ≤ 4)
  rfl

lemma mem_mentsuHandTargetConfigurations_iff
    (fixedMelds : Nat) (hfixed : fixedMelds ≤ 4)
    (pair : Tile) (melds : List Meld) :
    (pair, melds) ∈ mentsuHandTargetConfigurations fixedMelds ↔
      melds.length + fixedMelds = 4 := by
  rw [mentsuHandTargetConfigurations, Finset.mem_product]
  simp only [Finset.mem_univ, true_and,
    mem_mentsuHandMeldListsOfLength_iff]
  omega

def validMentsuHandTargetConfigurations (hand : Hand) :
    Finset (Tile × List Meld) :=
  (mentsuHandTargetConfigurations hand.fixedMelds).filter
    (fun candidate =>
      validCountsBool
        (targetHand hand
          (countsOfTiles
            (mentsuHandTarget candidate.1 candidate.2))) = true)

lemma mem_validMentsuHandTargetConfigurations_iff
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4)
    (pair : Tile) (melds : List Meld) :
    (pair, melds) ∈ validMentsuHandTargetConfigurations hand ↔
      melds.length + hand.fixedMelds = 4 ∧
      ValidCounts
        (targetHand hand
          (countsOfTiles (mentsuHandTarget pair melds))) := by
  classical
  rw [validMentsuHandTargetConfigurations, Finset.mem_filter,
    mem_mentsuHandTargetConfigurations_iff
      hand.fixedMelds hfixed pair melds]
  rw [validCountsBool_eq_true_iff]

def mentsuHandMeldTileStatesDP : Nat → Finset (Multiset Tile)
  | 0 => {0}
  | meldCount + 1 =>
      (Finset.univ.biUnion fun meld =>
        (mentsuHandMeldTileStatesDP meldCount).image
          (fun tiles => meldTiles meld + tiles)).filter
        (fun tiles => validTileMultisetBool tiles = true)

lemma mem_mentsuHandMeldTileStatesDP_iff
    (meldCount : Nat) (tiles : Multiset Tile) :
    tiles ∈ mentsuHandMeldTileStatesDP meldCount ↔
      ∃ melds, melds.length = meldCount ∧
        meldsTiles melds = tiles ∧ validTileMultisetBool tiles = true := by
  induction meldCount generalizing tiles with
  | zero =>
      change tiles ∈ ({0} : Finset (Multiset Tile)) ↔ _
      simp only [Finset.mem_singleton]
      constructor
      · rintro rfl
        refine ⟨[], rfl, rfl, ?_⟩
        apply (validTileMultisetBool_eq_true_iff 0).2
        intro tile
        simp
      · rintro ⟨melds, hlength, htiles, _⟩
        cases melds with
        | nil =>
            simpa [meldsTiles] using htiles.symm
        | cons meld melds =>
            simp at hlength
  | succ meldCount ih =>
      simp only [mentsuHandMeldTileStatesDP, Finset.mem_filter,
        Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨meld, previous, hprevious, heq⟩, hvalid⟩
        obtain ⟨melds, hlength, htiles, _⟩ :=
          (ih previous).mp hprevious
        refine ⟨meld :: melds, ?_, ?_, hvalid⟩
        · simp [hlength]
        · calc
            meldsTiles (meld :: melds) =
                meldTiles meld + meldsTiles melds := rfl
            _ = meldTiles meld + previous := by rw [htiles]
            _ = tiles := heq
      · rintro ⟨melds, hlength, htiles, hvalid⟩
        cases melds with
        | nil =>
            simp at hlength
        | cons meld melds =>
            simp only [List.length_cons] at hlength
            have hvalidFull' := hvalid
            have hvalidFull :
                validTileMultisetBool
                  (meldTiles meld + meldsTiles melds) = true := by
              rw [← htiles] at hvalidFull'
              simpa [meldsTiles] using hvalidFull'
            have htailValid :
                validTileMultisetBool (meldsTiles melds) = true := by
              apply validTileMultisetBool_add_left
                (meldsTiles melds) (meldTiles meld)
              simpa [Multiset.add_comm] using hvalidFull
            have hprevious :
                meldsTiles melds ∈ mentsuHandMeldTileStatesDP meldCount :=
              (ih (meldsTiles melds)).2
                ⟨melds, by omega, rfl, htailValid⟩
            refine ⟨⟨meld, meldsTiles melds, hprevious, ?_⟩, hvalid⟩
            calc
              meldTiles meld + meldsTiles melds =
                  meldsTiles (meld :: melds) := rfl
              _ = tiles := htiles

def mentsuHandTargetTileStatesDP (fixedMelds : Nat) :
    Finset (Multiset Tile) :=
  (Finset.univ.biUnion fun pair =>
    (mentsuHandMeldTileStatesDP (4 - fixedMelds)).image
      (fun meldTiles => pairTiles pair + meldTiles)).filter
    (fun tiles => validTileMultisetBool tiles = true)

lemma mem_mentsuHandTargetTileStatesDP_iff
    (fixedMelds : Nat) (hfixed : fixedMelds ≤ 4)
    (tiles : Multiset Tile) :
    tiles ∈ mentsuHandTargetTileStatesDP fixedMelds ↔
      ∃ pair melds,
        melds.length + fixedMelds = 4 ∧
        mentsuHandTarget pair melds = tiles ∧
        validTileMultisetBool tiles = true := by
  unfold mentsuHandTargetTileStatesDP
  simp only [Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨pair, meldTiles, hmeldTiles, rfl⟩, hvalid⟩
    obtain ⟨melds, hlength, rfl, _⟩ :=
      (mem_mentsuHandMeldTileStatesDP_iff (4 - fixedMelds) meldTiles).mp
        hmeldTiles
    refine ⟨pair, melds, ?_, rfl, hvalid⟩
    omega
  · rintro ⟨pair, melds, hlength, rfl, hvalid⟩
    have hmeldValid :
        validTileMultisetBool (meldsTiles melds) = true := by
      apply validTileMultisetBool_add_left
        (meldsTiles melds) (pairTiles pair)
      simpa [mentsuHandTarget, Multiset.add_comm] using hvalid
    refine ⟨⟨pair, meldsTiles melds, ?_, rfl⟩, hvalid⟩
    · exact (mem_mentsuHandMeldTileStatesDP_iff (4 - fixedMelds)
        (meldsTiles melds)).2
        ⟨melds, by omega, rfl, hmeldValid⟩

def mentsuHandTargetCostStatesDP (hand : Hand) :
    Finset (Multiset Tile × Nat) :=
  (mentsuHandTargetTileStatesDP hand.fixedMelds).image
    (fun tiles =>
      (tiles, countDeficit hand.counts (countsOfTiles tiles)))

lemma mem_mentsuHandTargetCostStatesDP_iff
    (hand : Hand) (state : Multiset Tile × Nat) :
    state ∈ mentsuHandTargetCostStatesDP hand ↔
      state.1 ∈ mentsuHandTargetTileStatesDP hand.fixedMelds ∧
      state.2 = countDeficit hand.counts (countsOfTiles state.1) := by
  unfold mentsuHandTargetCostStatesDP
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨tiles, htiles, heq⟩
    have hfst := congrArg Prod.fst heq
    have hsnd := congrArg Prod.snd heq
    refine ⟨?_, ?_⟩
    · rw [← hfst]
      exact htiles
    · rw [← hfst]
      exact hsnd.symm
  · rintro ⟨htiles, hcost⟩
    refine ⟨state.1, htiles, ?_⟩
    exact Prod.ext rfl hcost.symm

lemma countsOfTiles_add (tiles extra : Multiset Tile) :
    countsOfTiles (tiles + extra) =
      countsOfTiles tiles + countsOfTiles extra := by
  funext tile
  simp [countsOfTiles, Multiset.count_add]

lemma countDeficit_tiles_add_mono
    (current : TileCounts) (tiles extra : Multiset Tile) :
    countDeficit current (countsOfTiles tiles) ≤
      countDeficit current (countsOfTiles (tiles + extra)) := by
  unfold countDeficit
  apply Finset.sum_le_sum
  intro tile _
  rw [countsOfTiles_add]
  simp only [Pi.add_apply]
  omega

lemma countDeficit_add_le_card_of_le
    (current : TileCounts) (tiles extra : Multiset Tile)
    (hbelow : ∀ tile, (countsOfTiles tiles) tile ≤ current tile) :
    countDeficit current (countsOfTiles (tiles + extra)) ≤ extra.card := by
  unfold countDeficit
  calc
    ∑ tile : Tile, (countsOfTiles (tiles + extra) tile - current tile) =
        ∑ tile : Tile,
          (countsOfTiles tiles tile + countsOfTiles extra tile -
            current tile) := by
      apply Finset.sum_congr rfl
      intro tile _
      rw [countsOfTiles_add]
      rfl
    _ ≤ ∑ tile : Tile, countsOfTiles extra tile := by
      apply Finset.sum_le_sum
      intro tile _
      have htile := hbelow tile
      omega
    _ = extra.card := by
      exact countsOfTiles_sum_eq_card extra

/-- Extend a target state and add only the newly incurred deficit. -/
def mentsuHandCostStateAdd (hand : Hand)
    (state : Multiset Tile × Nat) (extra : Multiset Tile) :
    Multiset Tile × Nat :=
  let tiles := state.1 + extra
  (tiles,
    state.2 + (countDeficit hand.counts (countsOfTiles tiles) -
      countDeficit hand.counts (countsOfTiles state.1)))

lemma mentsuHandCostStateAdd_cost
    (hand : Hand) (state : Multiset Tile × Nat) (extra : Multiset Tile)
    (hcost :
      state.2 = countDeficit hand.counts (countsOfTiles state.1)) :
    (mentsuHandCostStateAdd hand state extra).2 =
      countDeficit hand.counts
        (countsOfTiles ((mentsuHandCostStateAdd hand state extra).1)) := by
  unfold mentsuHandCostStateAdd
  dsimp only
  rw [hcost]
  have hmono := countDeficit_tiles_add_mono
    hand.counts state.1 extra
  omega

def mentsuHandMeldCostStatesDP (hand : Hand) (initialTiles : Multiset Tile) :
    Nat → Finset (Multiset Tile × Nat)
  | 0 =>
      Finset.filter
        (fun state => validTileMultisetBool state.1 = true)
        ({(initialTiles,
            countDeficit hand.counts (countsOfTiles initialTiles))} :
          Finset (Multiset Tile × Nat))
  | meldCount + 1 =>
      (Finset.univ.biUnion fun meld =>
        (mentsuHandMeldCostStatesDP hand initialTiles meldCount).image
          (fun state => mentsuHandCostStateAdd hand state (meldTiles meld)))
        |>.filter (fun state => validTileMultisetBool state.1 = true)

lemma mentsuHandMeldCostStatesDP_cost
    (hand : Hand) (initialTiles : Multiset Tile) (meldCount : Nat)
    (state : Multiset Tile × Nat)
    (hstate : state ∈ mentsuHandMeldCostStatesDP hand initialTiles meldCount) :
    state.2 = countDeficit hand.counts (countsOfTiles state.1) := by
  induction meldCount generalizing state with
  | zero =>
      simp only [mentsuHandMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_singleton] at hstate
      rw [hstate.1]
  | succ meldCount ih =>
      simp only [mentsuHandMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image] at hstate
      rcases hstate with ⟨⟨meld, previous, hprevious, heq⟩, _⟩
      have hpreviousCost := ih previous hprevious
      have hnextCost :=
        mentsuHandCostStateAdd_cost hand previous (meldTiles meld)
          hpreviousCost
      calc
        state.2 =
            (mentsuHandCostStateAdd hand previous (meldTiles meld)).2 :=
          (congrArg Prod.snd heq).symm
        _ = countDeficit hand.counts
            (countsOfTiles
              (mentsuHandCostStateAdd hand previous (meldTiles meld)).1) :=
          hnextCost
        _ = countDeficit hand.counts (countsOfTiles state.1) := by
          rw [congrArg Prod.fst heq]

lemma mem_mentsuHandMeldCostStatesDP_iff
    (hand : Hand) (initialTiles : Multiset Tile)
    (meldCount : Nat) (state : Multiset Tile × Nat) :
    state ∈ mentsuHandMeldCostStatesDP hand initialTiles meldCount ↔
      ∃ melds,
        melds.length = meldCount ∧
        meldsTiles melds + initialTiles = state.1 ∧
        state.2 = countDeficit hand.counts (countsOfTiles state.1) ∧
        validTileMultisetBool state.1 = true := by
  induction meldCount generalizing state with
  | zero =>
      simp only [mentsuHandMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, hvalid⟩
        refine ⟨[], rfl, ?_, rfl, hvalid⟩
        simp [meldsTiles]
      · rintro ⟨melds, hlength, htiles, hcost, hvalid⟩
        cases melds with
        | nil =>
            simp only [List.length_nil] at hlength
            simp [meldsTiles] at htiles
            have hstate : state =
                (initialTiles,
                  countDeficit hand.counts (countsOfTiles initialTiles)) := by
              apply Prod.ext
              · exact htiles.symm
              · calc
                  state.2 =
                      countDeficit hand.counts (countsOfTiles state.1) := hcost
                  _ = countDeficit hand.counts
                      (countsOfTiles initialTiles) := by rw [htiles]
            exact ⟨hstate, hvalid⟩
        | cons meld melds =>
            simp at hlength
  | succ meldCount ih =>
      simp only [mentsuHandMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · intro hstate
        rcases hstate with ⟨⟨meld, previous, hprevious, heq⟩, hvalid⟩
        have hpreviousCost :=
          mentsuHandMeldCostStatesDP_cost hand initialTiles meldCount
            previous hprevious
        have hnextCost :=
          mentsuHandCostStateAdd_cost hand previous (meldTiles meld)
            hpreviousCost
        have hcost : state.2 =
            countDeficit hand.counts (countsOfTiles state.1) := by
          calc
            state.2 =
                (mentsuHandCostStateAdd hand previous (meldTiles meld)).2 :=
              (congrArg Prod.snd heq).symm
            _ = countDeficit hand.counts
                (countsOfTiles
                  (mentsuHandCostStateAdd hand previous (meldTiles meld)).1) :=
              hnextCost
            _ = countDeficit hand.counts (countsOfTiles state.1) := by
              rw [congrArg Prod.fst heq]
        obtain ⟨melds, hlength, htiles, _, _⟩ :=
          (ih previous).mp hprevious
        have hfst := congrArg Prod.fst heq
        refine ⟨meld :: melds, by simp [hlength], ?_, hcost, hvalid⟩
        calc
          meldsTiles (meld :: melds) + initialTiles =
              meldTiles meld + (meldsTiles melds + initialTiles) := by
                rw [show meldsTiles (meld :: melds) =
                    meldTiles meld + meldsTiles melds by rfl]
                ac_rfl
          _ = meldTiles meld + previous.1 := by rw [htiles]
          _ = (mentsuHandCostStateAdd hand previous (meldTiles meld)).1 := by
                simp [mentsuHandCostStateAdd, Multiset.add_comm]
          _ = state.1 := hfst
      · rintro ⟨melds, hlength, htiles, hcost, hvalid⟩
        cases melds with
        | nil =>
            simp at hlength
        | cons meld melds =>
            simp only [List.length_cons] at hlength
            have htilesShape :
                meldsTiles (meld :: melds) + initialTiles =
                  (meldsTiles melds + initialTiles) + meldTiles meld := by
              rw [show meldsTiles (meld :: melds) =
                  meldTiles meld + meldsTiles melds by rfl]
              ac_rfl
            have hpreviousValid :
                validTileMultisetBool
                  (meldsTiles melds + initialTiles) = true := by
              apply validTileMultisetBool_add_left
                (meldsTiles melds + initialTiles) (meldTiles meld)
              have hfinalValid := hvalid
              rw [← htiles] at hfinalValid
              rw [htilesShape] at hfinalValid
              exact hfinalValid
            let previous : Multiset Tile × Nat :=
              (meldsTiles melds + initialTiles,
                countDeficit hand.counts
                  (countsOfTiles (meldsTiles melds + initialTiles)))
            have hprevious :
                previous ∈ mentsuHandMeldCostStatesDP hand initialTiles meldCount :=
              (ih previous).2
                ⟨melds, by omega, rfl, rfl, hpreviousValid⟩
            have hnextCost :=
              mentsuHandCostStateAdd_cost hand previous (meldTiles meld) rfl
            have hfirst :
                (mentsuHandCostStateAdd hand previous (meldTiles meld)).1 =
                  state.1 := by
              calc
                (mentsuHandCostStateAdd hand previous (meldTiles meld)).1 =
                    (meldsTiles melds + initialTiles) + meldTiles meld := by
                      simp [mentsuHandCostStateAdd, previous]
                _ = meldsTiles (meld :: melds) + initialTiles :=
                  htilesShape.symm
                _ = state.1 := htiles
            refine ⟨⟨meld, previous, hprevious, ?_⟩, hvalid⟩
            apply Prod.ext
            · exact hfirst
            · calc
                (mentsuHandCostStateAdd hand previous (meldTiles meld)).2 =
                    countDeficit hand.counts
                      (countsOfTiles
                        (mentsuHandCostStateAdd hand previous (meldTiles meld)).1) :=
                  hnextCost
                _ = countDeficit hand.counts
                    (countsOfTiles state.1) := by
                      rw [hfirst]
                _ = state.2 := hcost.symm

def recursiveMentsuHandTargetCostStatesDP (hand : Hand) :
    Finset (Multiset Tile × Nat) :=
  Finset.univ.biUnion fun pair =>
    mentsuHandMeldCostStatesDP hand (pairTiles pair)
      (4 - hand.fixedMelds)

lemma recursiveMentsuHandTargetCostStatesDP_eq
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4) :
    recursiveMentsuHandTargetCostStatesDP hand =
      mentsuHandTargetCostStatesDP hand := by
  ext state
  unfold recursiveMentsuHandTargetCostStatesDP
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  rw [mem_mentsuHandTargetCostStatesDP_iff]
  constructor
  · rintro ⟨pair, hstate⟩
    obtain ⟨melds, hlength, htiles, hcost, hvalid⟩ :=
      (mem_mentsuHandMeldCostStatesDP_iff hand (pairTiles pair)
        (4 - hand.fixedMelds) state).mp hstate
    have htargetLength : melds.length + hand.fixedMelds = 4 := by
      omega
    have htarget :
        mentsuHandTarget pair melds = state.1 := by
      rw [mentsuHandTarget]
      calc
        pairTiles pair + meldsTiles melds =
            meldsTiles melds + pairTiles pair := by ac_rfl
        _ = state.1 := htiles
    have htilesTarget :
        state.1 ∈ mentsuHandTargetTileStatesDP hand.fixedMelds :=
      (mem_mentsuHandTargetTileStatesDP_iff hand.fixedMelds hfixed
        state.1).2
        ⟨pair, melds, htargetLength, htarget, hvalid⟩
    exact ⟨htilesTarget, hcost⟩
  · rintro ⟨htiles, hcost⟩
    obtain ⟨pair, melds, hlength, htarget, hvalid⟩ :=
      (mem_mentsuHandTargetTileStatesDP_iff hand.fixedMelds hfixed
        state.1).mp htiles
    refine ⟨pair, ?_⟩
    apply (mem_mentsuHandMeldCostStatesDP_iff hand (pairTiles pair)
      (4 - hand.fixedMelds) state).2
    refine ⟨melds, ?_, ?_, hcost, ?_⟩
    · omega
    · rw [← htarget, mentsuHandTarget]
      ac_rfl
    · exact hvalid

/-
## 9. 最小目標距離と形シャンテン数

妥当な目標距離の最小値を、ここでシャンテン数の仕様に結び付けます。
中心となる解釈は、距離 `d` の目標が形シャンテン数 `d - 1` に対応することです。
-/

def validMentsuHandTargetDistances (hand : Hand) :
    Finset Nat :=
  (recursiveMentsuHandTargetCostStatesDP hand).image Prod.snd

lemma mentsuHandTargetCostDistances_eq_tileDistances
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4) :
    validMentsuHandTargetDistances hand =
      (mentsuHandTargetTileStatesDP hand.fixedMelds).image
        (fun tiles => countDeficit hand.counts (countsOfTiles tiles)) := by
  unfold validMentsuHandTargetDistances
  rw [recursiveMentsuHandTargetCostStatesDP_eq hand hfixed]
  ext distance
  simp [mentsuHandTargetCostStatesDP, Finset.image_image]

/-- Exhaustive target-state search; equal tile multisets are deduplicated at each meld count. -/
def mentsuHandTargetMinimumSearch (hand : Hand) : Option Int :=
  let distances := validMentsuHandTargetDistances hand
  if h : distances.Nonempty then
    some ((distances.min' h : Int) - 1)
  else
    none

lemma mem_validMentsuHandTargetDistances_iff
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4) (distance : Nat) :
    distance ∈ validMentsuHandTargetDistances hand ↔
      ∃ pair melds,
        melds.length + hand.fixedMelds = 4 ∧
        ValidCounts
          (targetHand hand
            (countsOfTiles (mentsuHandTarget pair melds))) ∧
        mentsuHandTargetDistance hand pair melds = distance := by
  classical
  rw [mentsuHandTargetCostDistances_eq_tileDistances hand hfixed]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨tiles, htiles, hdistance⟩
    obtain ⟨pair, melds, hmelds, htarget, hcopy⟩ :=
      (mem_mentsuHandTargetTileStatesDP_iff
        hand.fixedMelds hfixed tiles).mp htiles
    refine ⟨pair, melds, hmelds, ?_, ?_⟩
    · rw [← htarget] at hcopy
      exact (validTileMultisetBool_eq_true_iff_targetHand
        hand (mentsuHandTarget pair melds)).mp hcopy
    · rw [← htarget] at hdistance
      rw [mentsuHandTargetDistance_eq_countDeficit]
      exact hdistance
  · rintro ⟨pair, melds, hmelds, hvalid, hdistance⟩
    let tiles := mentsuHandTarget pair melds
    have hcopy :
        validTileMultisetBool tiles = true :=
      (validTileMultisetBool_eq_true_iff_targetHand hand tiles).mpr hvalid
    have htiles :
        tiles ∈ mentsuHandTargetTileStatesDP hand.fixedMelds :=
      (mem_mentsuHandTargetTileStatesDP_iff
        hand.fixedMelds hfixed tiles).mpr
        ⟨pair, melds, hmelds, rfl, hcopy⟩
    refine ⟨tiles, htiles, ?_⟩
    rw [mentsuHandTargetDistance_eq_countDeficit] at hdistance
    exact hdistance

lemma exists_min_validMentsuHandTargetDistance
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4)
    (hcandidate :
      ∃ pair melds,
        melds.length + hand.fixedMelds = 4 ∧
        ValidCounts
          (targetHand hand
            (countsOfTiles (mentsuHandTarget pair melds)))) :
    ∃ distance, distance ∈ validMentsuHandTargetDistances hand ∧
      ∀ otherDistance,
        otherDistance ∈ validMentsuHandTargetDistances hand →
          distance ≤ otherDistance := by
  classical
  let distances := validMentsuHandTargetDistances hand
  have hnonempty : distances.Nonempty := by
    obtain ⟨pair, melds, hmelds, hvalid⟩ := hcandidate
    refine ⟨mentsuHandTargetDistance hand pair melds, ?_⟩
    exact (mem_validMentsuHandTargetDistances_iff
      hand hfixed (mentsuHandTargetDistance hand pair melds)).2
      ⟨pair, melds, hmelds, hvalid, rfl⟩
  let distance := distances.min' hnonempty
  refine ⟨distance, ?_, ?_⟩
  · change distance ∈ distances
    exact Finset.min'_mem distances hnonempty
  · intro otherDistance hother
    exact Finset.min'_le distances otherDistance hother

lemma exists_mentsuHandTarget_distance_le_of_reachesCompletion
    (before : Hand) (distance : Nat)
    (hreach : ReachesCompletion Complete .mentsuHand before distance) :
    ∃ pair melds,
      melds.length + before.fixedMelds = 4 ∧
        ValidCounts
          (targetHand before
            (countsOfTiles (mentsuHandTarget pair melds))) ∧
        mentsuHandTargetDistance before pair melds ≤ distance := by
  obtain ⟨after, hcomplete, hfixed, hdeficit⟩ :=
    exists_complete_mentsuHand_with_deficit_le before distance hreach
  rcases hcomplete with ⟨hvalidAfter, pair, melds, hmelds, htiles⟩
  have hcounts :
      after.counts =
        countsOfTiles (mentsuHandTarget pair melds) := by
    funext tile
    change after.counts tile =
      (mentsuHandTarget pair melds).count tile
    exact htiles tile
  have hvalidTarget :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))) := by
    intro tile
    change (countsOfTiles (mentsuHandTarget pair melds)) tile ≤ 4
    rw [← hcounts]
    exact hvalidAfter tile
  refine ⟨pair, melds, ?_, hvalidTarget, ?_⟩
  · rw [← hfixed]
    exact hmelds
  · rw [mentsuHandTargetDistance_eq_countDeficit]
    simpa [hcounts] using hdeficit

lemma no_shorter_mentsuHand_completion_of_minimal_mentsuHandTargetDistance
    (before : Hand) (pair : Tile) (melds : List Meld)
    (distance : Nat)
    (hdistance : mentsuHandTargetDistance before pair melds = distance)
    (hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
          mentsuHandTargetDistance before pair melds ≤
            mentsuHandTargetDistance before otherPair otherMelds) :
    ∀ smaller : Nat, smaller < distance →
      ¬ ReachesCompletion Complete .mentsuHand before smaller := by
  intro smaller hsmaller hreach
  obtain ⟨otherPair, otherMelds, hmelds, hvalid, hotherDistance⟩ :=
    exists_mentsuHandTarget_distance_le_of_reachesCompletion
      before smaller hreach
  have hminimal := hminimalTarget otherPair otherMelds hmelds hvalid
  omega

lemma mentsuHandTargetDistance_eq_zero_iff
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile) :
    mentsuHandTargetDistance hand pair melds = 0 ↔
      hand.counts = countsOfTiles (mentsuHandTarget pair melds) := by
  constructor
  · intro hdistance
    have hdeficit :
        countDeficit hand.counts
          (countsOfTiles (mentsuHandTarget pair melds)) = 0 := by
      rw [← mentsuHandTargetDistance_eq_countDeficit]
      exact hdistance
    have hzero :
        ∀ tile ∈ (Finset.univ : Finset Tile),
          (countsOfTiles (mentsuHandTarget pair melds)) tile -
              hand.counts tile = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (fun tile _ => Nat.zero_le _)).mp
      exact hdeficit
    have hle :
        ∀ tile, (countsOfTiles (mentsuHandTarget pair melds)) tile ≤
          hand.counts tile := by
      intro tile
      have hzeroTile := hzero tile (Finset.mem_univ tile)
      omega
    apply funext
    intro tile
    have heq :
        ∀ tile ∈ (Finset.univ : Finset Tile),
          (countsOfTiles (mentsuHandTarget pair melds)) tile =
            hand.counts tile := by
      apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
        (f := countsOfTiles (mentsuHandTarget pair melds))
        (g := hand.counts)
        (fun tile _ => hle tile)).mp
      exact hsum.symm
    exact (heq tile (Finset.mem_univ tile)).symm
  · intro hcounts
    rw [mentsuHandTargetDistance_eq_countDeficit]
    simp [countDeficit, hcounts]

lemma mentsuHandTargetDistance_pos_iff
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile) :
    0 < mentsuHandTargetDistance hand pair melds ↔
      hand.counts ≠ countsOfTiles (mentsuHandTarget pair melds) := by
  constructor
  · intro hpos hcounts
    have hzero : mentsuHandTargetDistance hand pair melds = 0 :=
      (mentsuHandTargetDistance_eq_zero_iff hand pair melds hsum).mpr hcounts
    omega
  · intro hne
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hne
        ((mentsuHandTargetDistance_eq_zero_iff hand pair melds hsum).mp hzero))

lemma mentsuHandTargetDistance_exchange
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (discarded drawn : Tile)
    (hdrawn :
      (mentsuHandTarget pair melds).count drawn > hand.counts drawn)
    (hdiscarded :
      hand.counts discarded >
        (mentsuHandTarget pair melds).count discarded)
    (hne : discarded ≠ drawn) :
    mentsuHandTargetDistance
        (exchangeHand hand discarded drawn) pair melds =
      mentsuHandTargetDistance hand pair melds - 1 := by
  rw [mentsuHandTargetDistance_eq_countDeficit,
    mentsuHandTargetDistance_eq_countDeficit]
  exact countDeficit_exchange
    (countsOfTiles (mentsuHandTarget pair melds))
    hand discarded drawn hdrawn hdiscarded hne

lemma exists_mentsuHandTarget_exchange
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hne :
      hand.counts ≠ countsOfTiles (mentsuHandTarget pair melds)) :
    ∃ discarded drawn,
      (mentsuHandTarget pair melds).count drawn > hand.counts drawn ∧
      hand.counts discarded >
        (mentsuHandTarget pair melds).count discarded ∧
      discarded ≠ drawn ∧
      mentsuHandTargetDistance
          (exchangeHand hand discarded drawn) pair melds =
        mentsuHandTargetDistance hand pair melds - 1 := by
  obtain ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles⟩ :=
    exists_target_exchange_tiles hand
      (countsOfTiles (mentsuHandTarget pair melds)) hsum hne
  refine ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles, ?_⟩
  exact mentsuHandTargetDistance_exchange
    hand pair melds discarded drawn hdrawn hdiscarded hneTiles

lemma exists_mentsuHandTarget_exchange_of_pos
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hpos : 0 < mentsuHandTargetDistance hand pair melds) :
    ∃ discarded drawn,
      (mentsuHandTarget pair melds).count drawn > hand.counts drawn ∧
      hand.counts discarded >
        (mentsuHandTarget pair melds).count discarded ∧
      discarded ≠ drawn ∧
      mentsuHandTargetDistance
          (exchangeHand hand discarded drawn) pair melds =
        mentsuHandTargetDistance hand pair melds - 1 := by
  apply exists_mentsuHandTarget_exchange hand pair melds hsum
  exact (mentsuHandTargetDistance_pos_iff hand pair melds hsum).mp hpos

lemma reachesCompletion_mentsuHand_of_mentsuHandTarget
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    ReachesCompletion Complete .mentsuHand before
      (mentsuHandTargetDistance before pair melds) := by
  rw [mentsuHandTargetDistance_eq_countDeficit]
  apply reachesCompletion_mentsuHand_of_equal_sum
    before
    (countsOfTiles (mentsuHandTarget pair melds))
    pair melds hsum hvalid hmelds
  exact targetHand_hasTiles_countsOfTiles before
    (mentsuHandTarget pair melds)

set_option maxHeartbeats 1000000 in
lemma reachesCompletion_mentsuHand_of_blockDecomposition
    (hand : Hand) (h13 : IsThirteenTileHand hand)
    (decomposition : MentsuHandBlockDecomposition hand) :
    ∃ distance : Nat, distance ≤ 4 ∧
      ReachesCompletion Complete .mentsuHand hand distance := by
  let melds :=
    decomposition.melds ++
      taatsuCompletionMelds decomposition.taatsus
  have hmelds : melds.length + hand.fixedMelds = 4 := by
    dsimp [melds]
    exact decomposition.completedMeldCount
  have htarget :
      mentsuHandTarget decomposition.pair melds =
        decomposition.completedTarget := by
    rw [MentsuHandBlockDecomposition.completedTarget_eq]
    rfl
  have hsumTarget :
      (∑ tile : Tile, (mentsuHandTarget decomposition.pair melds).count tile) =
        (∑ tile : Tile, hand.counts tile) + 1 := by
    calc
      (∑ tile : Tile,
          (mentsuHandTarget decomposition.pair melds).count tile) =
          decomposition.completedTarget.card := by
        change
          (∑ tile : Tile,
            countsOfTiles (mentsuHandTarget decomposition.pair melds) tile) =
            decomposition.completedTarget.card
        rw [htarget, countsOfTiles_sum_eq_card]
      _ = 14 := by
        have hbase :
            (mentsuHandTargetWithTaatsu decomposition.pair
              decomposition.melds decomposition.taatsus).card =
              2 + 3 * decomposition.melds.length +
                2 * decomposition.taatsus.length := by
          have htaatsu :
              (taatsuHistoryTiles decomposition.taatsus).card =
                2 * decomposition.taatsus.length := by
            induction decomposition.taatsus with
            | nil =>
                rfl
            | cons taatsu taatsus ih =>
                cases taatsu <;>
                  simp [taatsuHistoryTiles, taatsuTiles, pairTiles, ih,
                    Multiset.card_add] <;> omega
          unfold mentsuHandTargetWithTaatsu mentsuHandTarget
          rw [Multiset.card_add, Multiset.card_add, pairTiles_card,
            meldsTiles_card, htaatsu]
        have hextra :
            (taatsuCompletionTiles decomposition.taatsus).card =
              decomposition.taatsus.length :=
          taatsuCompletionTiles_card decomposition.taatsus
        have hblocks := decomposition.blocks
        have hfixed := h13.1
        have htargetCard : decomposition.completedTarget.card = 14 := by
          change
            (mentsuHandTargetWithTaatsu decomposition.pair
              decomposition.melds decomposition.taatsus +
              taatsuCompletionTiles decomposition.taatsus).card = 14
          rw [Multiset.card_add, hbase,
            taatsuCompletionTiles_card decomposition.taatsus]
          omega
        exact htargetCard
      _ = (∑ tile : Tile, hand.counts tile) + 1 := by
        have hcount := h13.2.1
        rw [show (∑ tile : Tile, hand.counts tile) = tileCount hand from rfl]
        omega
  have hdistance :
      mentsuHandTargetDistance hand decomposition.pair melds ≤ 4 := by
    rw [mentsuHandTargetDistance_eq_countDeficit, htarget]
    change countDeficit hand.counts
      (countsOfTiles
        (mentsuHandTargetWithTaatsu decomposition.pair
          decomposition.melds decomposition.taatsus +
          taatsuCompletionTiles decomposition.taatsus)) ≤ 4
    have hbound := countDeficit_add_le_card_of_le
      hand.counts
      (mentsuHandTargetWithTaatsu decomposition.pair
        decomposition.melds decomposition.taatsus)
      (taatsuCompletionTiles decomposition.taatsus)
      decomposition.targetWithinHand
    have hblocks := decomposition.blocks
    have hfixed := h13.1
    calc
      countDeficit hand.counts
          (countsOfTiles
            (mentsuHandTargetWithTaatsu decomposition.pair
              decomposition.melds decomposition.taatsus +
              taatsuCompletionTiles decomposition.taatsus)) ≤
          (taatsuCompletionTiles decomposition.taatsus).card := hbound
      _ = decomposition.taatsus.length :=
        taatsuCompletionTiles_card decomposition.taatsus
      _ ≤ 4 := by omega
  have hreach :=
    reachesCompletion_mentsuHand_of_one_more_target_tile
      hand (countsOfTiles (mentsuHandTarget decomposition.pair melds))
      decomposition.pair melds hsumTarget h13.2.2
      (by
        rw [htarget]
        exact decomposition.validCounts_completedTarget)
      hmelds
      (targetHand_hasTiles_countsOfTiles hand
        (mentsuHandTarget decomposition.pair melds))
  rcases hreach with ⟨distance, hdistanceEq, hreach⟩
  exact ⟨distance, by rw [hdistanceEq]; exact hdistance, hreach⟩

lemma complete_mentsuHand_of_mentsuHandTarget_distance_zero
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuHandTargetDistance before pair melds = 0)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    Complete .mentsuHand before := by
  have hdeficit :
      countDeficit before.counts
        (countsOfTiles (mentsuHandTarget pair melds)) = 0 := by
    rw [← mentsuHandTargetDistance_eq_countDeficit]
    exact hdistance
  have hzero :
      ∀ tile ∈ (Finset.univ : Finset Tile),
        (countsOfTiles (mentsuHandTarget pair melds)) tile -
            before.counts tile = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (fun tile _ => Nat.zero_le _)).mp
    exact hdeficit
  have hle :
      ∀ tile, (countsOfTiles (mentsuHandTarget pair melds)) tile ≤
        before.counts tile := by
    intro tile
    have hzeroTile := hzero tile (Finset.mem_univ tile)
    omega
  have heq :
      ∀ tile ∈ (Finset.univ : Finset Tile),
        (countsOfTiles (mentsuHandTarget pair melds)) tile =
          before.counts tile := by
    apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := countsOfTiles (mentsuHandTarget pair melds))
      (g := before.counts)
      (fun tile _ => hle tile)).mp
    exact hsum.symm
  have hcounts :
      countsOfTiles (mentsuHandTarget pair melds) = before.counts := by
    funext tile
    exact heq tile (Finset.mem_univ tile)
  have hcomplete :
      Complete .mentsuHand
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))) := by
    exact complete_mentsuHand_targetHand before
      (countsOfTiles (mentsuHandTarget pair melds)) pair melds
      hvalid hmelds
      (targetHand_hasTiles_countsOfTiles before
        (mentsuHandTarget pair melds))
  simpa [targetHand, hcounts] using hcomplete

set_option maxHeartbeats 1000000 in
lemma reachesCompletion_mentsuHand_of_mentsuHandTarget_distance_one
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuHandTargetDistance before pair melds = 1)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    ReachesCompletion Complete .mentsuHand before 1 := by
  obtain ⟨discarded, drawn, hdrawn, hdiscarded, hne, hdistanceNext⟩ :=
    exists_mentsuHandTarget_exchange_of_pos
      before pair melds hsum (by omega)
  have hsumNext :
      (∑ tile : Tile, (exchangeHand before discarded drawn).counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile := by
    have hsumExchange :
        (∑ tile : Tile, (exchangeHand before discarded drawn).counts tile) =
          ∑ tile : Tile, before.counts tile := by
      change
        (∑ tile : Tile,
          exchangeCounts before discarded drawn tile) =
          ∑ tile : Tile, before.counts tile
      exact exchangeCounts_sum before discarded drawn hne (by omega)
    exact hsumExchange.trans hsum
  have hvalidNext :
      ValidCounts
        (targetHand (exchangeHand before discarded drawn)
          (countsOfTiles (mentsuHandTarget pair melds))) := by
    change
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds)))
    exact hvalid
  have hmeldsNext :
      melds.length + (exchangeHand before discarded drawn).fixedMelds = 4 := by
    change melds.length + before.fixedMelds = 4
    exact hmelds
  have hcomplete :
      Complete .mentsuHand (exchangeHand before discarded drawn) := by
    have hzeroNext :
        mentsuHandTargetDistance
            (exchangeHand before discarded drawn) pair melds = 0 := by
      omega
    have hcountsNext :
        (exchangeHand before discarded drawn).counts =
          countsOfTiles (mentsuHandTarget pair melds) :=
      (mentsuHandTargetDistance_eq_zero_iff
        (exchangeHand before discarded drawn) pair melds hsumNext).mp
        hzeroNext
    have htargetComplete :
        Complete .mentsuHand
          (targetHand (exchangeHand before discarded drawn)
            (countsOfTiles (mentsuHandTarget pair melds))) :=
      complete_mentsuHand_targetHand
        (exchangeHand before discarded drawn)
        (countsOfTiles (mentsuHandTarget pair melds))
        pair melds hvalidNext hmeldsNext
        (targetHand_hasTiles_countsOfTiles
          (exchangeHand before discarded drawn)
          (mentsuHandTarget pair melds))
    have hhand :
        exchangeHand before discarded drawn =
          targetHand (exchangeHand before discarded drawn)
            (countsOfTiles (mentsuHandTarget pair melds)) := by
      cases hnext : exchangeHand before discarded drawn with
      | mk counts fixed =>
          simp only [targetHand, hnext]
          simpa [hnext] using
            congrArg
              (fun counts : TileCounts =>
                ({ counts := counts, fixedMelds := fixed } : Hand))
              hcountsNext
    rw [hhand]
    exact htargetComplete
  apply ReachesCompletion.step
  · exact mentsuHandTargetExchange_handStep
      (countsOfTiles (mentsuHandTarget pair melds))
      before discarded drawn hdrawn hdiscarded hne
  · exact ReachesCompletion.done hcomplete

set_option maxHeartbeats 1000000 in
lemma reachesCompletion_mentsuHand_of_mentsuHandTarget_distance
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuHandTargetDistance before pair melds = distance)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    ReachesCompletion Complete .mentsuHand before distance := by
  induction distance generalizing before with
  | zero =>
      have hcomplete : Complete .mentsuHand before := by
        exact complete_mentsuHand_of_mentsuHandTarget_distance_zero
          before pair melds hdistance hsum hvalid hmelds
      exact ReachesCompletion.done hcomplete
  | succ distance ih =>
      obtain ⟨discarded, drawn, hdrawn, hdiscarded, hne, hdistanceNext⟩ :=
        exists_mentsuHandTarget_exchange_of_pos
          before pair melds hsum (by omega)
      have hsumNext :
          (∑ tile : Tile,
            (exchangeHand before discarded drawn).counts tile) =
            ∑ tile : Tile, (mentsuHandTarget pair melds).count tile := by
        have hsumExchange :
            (∑ tile : Tile,
              (exchangeHand before discarded drawn).counts tile) =
              ∑ tile : Tile, before.counts tile := by
          change
            (∑ tile : Tile,
              exchangeCounts before discarded drawn tile) =
              ∑ tile : Tile, before.counts tile
          exact exchangeCounts_sum before discarded drawn hne (by omega)
        exact hsumExchange.trans hsum
      have hvalidNext :
          ValidCounts
            (targetHand (exchangeHand before discarded drawn)
              (countsOfTiles (mentsuHandTarget pair melds))) := by
        change
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget pair melds)))
        exact hvalid
      have hmeldsNext :
          melds.length + (exchangeHand before discarded drawn).fixedMelds = 4 := by
        change melds.length + before.fixedMelds = 4
        exact hmelds
      have hdistanceNext' :
          mentsuHandTargetDistance
              (exchangeHand before discarded drawn) pair melds = distance := by
        omega
      have hrest :=
        ih (exchangeHand before discarded drawn)
          hdistanceNext' hsumNext hvalidNext hmeldsNext
      apply ReachesCompletion.step
      · exact mentsuHandTargetExchange_handStep
          (countsOfTiles (mentsuHandTarget pair melds))
          before discarded drawn hdrawn hdiscarded hne
      · exact hrest

lemma isShapeShanten_mentsuHand_of_mentsuHandTarget_distance
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuHandTargetDistance before pair melds = distance)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4)
    (hminimal :
      ∀ smaller : Nat, smaller < distance →
        ¬ ReachesCompletion Complete .mentsuHand before smaller) :
    IsShapeShanten before .mentsuHand ((distance : Int) - 1) := by
  have hreaches :
      ReachesCompletion Complete .mentsuHand before distance :=
    reachesCompletion_mentsuHand_of_mentsuHandTarget_distance
      distance before pair melds hdistance hsum hvalid hmelds
  refine ⟨trivial, distance, ?_, hreaches, hminimal⟩
  omega

lemma isShapeShanten_mentsuHand_of_minimal_mentsuHandTargetDistance
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuHandTargetDistance before pair melds = distance)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4)
    (hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
          mentsuHandTargetDistance before pair melds ≤
            mentsuHandTargetDistance before otherPair otherMelds) :
    IsShapeShanten before .mentsuHand ((distance : Int) - 1) := by
  apply isShapeShanten_mentsuHand_of_mentsuHandTarget_distance
    distance before pair melds hdistance hsum hvalid hmelds
  exact no_shorter_mentsuHand_completion_of_minimal_mentsuHandTargetDistance
    before pair melds distance hdistance hminimalTarget

lemma isShapeShanten_mentsuHand_of_minimal_mentsuHandTargetDistance_one_more
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuHandTargetDistance before pair melds = distance)
    (hsum :
      (∑ tile : Tile,
        countsOfTiles (mentsuHandTarget pair melds) tile) =
        (∑ tile : Tile, before.counts tile) + 1)
    (hbeforeValid : ValidCounts before)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4)
    (hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
          mentsuHandTargetDistance before pair melds ≤
            mentsuHandTargetDistance before otherPair otherMelds) :
    IsShapeShanten before .mentsuHand ((distance : Int) - 1) := by
  obtain ⟨reachedDistance, htargetDistance, hreach⟩ :=
    reachesCompletion_mentsuHand_of_one_more_target_tile
      before (countsOfTiles (mentsuHandTarget pair melds))
      pair melds hsum hbeforeValid hvalid hmelds
      (targetHand_hasTiles_countsOfTiles before
        (mentsuHandTarget pair melds))
  have hreachDistance :
      reachedDistance = distance := by
    calc
      reachedDistance =
          countDeficit before.counts
            (countsOfTiles (mentsuHandTarget pair melds)) :=
        htargetDistance
      _ = mentsuHandTargetDistance before pair melds :=
        (mentsuHandTargetDistance_eq_countDeficit before pair melds).symm
      _ = distance := hdistance
  have hreaches :
      ReachesCompletion Complete .mentsuHand before distance := by
    rw [← hreachDistance]
    exact hreach
  have hminimal :=
    no_shorter_mentsuHand_completion_of_minimal_mentsuHandTargetDistance
      before pair melds distance hdistance hminimalTarget
  refine ⟨trivial, distance, ?_, hreaches, hminimal⟩
  omega

private lemma nat_find_le_of_mem
    (predicate : Nat → Prop) [DecidablePred predicate]
    (hexists : ∃ n, predicate n)
    {value : Nat} (hvalue : predicate value) :
    Nat.find hexists ≤ value :=
  Nat.find_min' hexists hvalue

set_option maxHeartbeats 1000000 in
lemma exists_isShapeShanten_mentsuHand_of_valid_mentsuHandTarget
    (before : Hand)
    (hcandidate :
      ∃ pair melds,
        melds.length + before.fixedMelds = 4 ∧
          (∑ tile : Tile, before.counts tile) =
            ∑ tile : Tile, (mentsuHandTarget pair melds).count tile ∧
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget pair melds)))) :
    ∃ value : Int, IsShapeShanten before .mentsuHand value := by
  classical
  let candidateDistance : Nat → Prop := fun distance =>
    ∃ pair melds,
      melds.length + before.fixedMelds = 4 ∧
        (∑ tile : Tile, before.counts tile) =
          ∑ tile : Tile, (mentsuHandTarget pair melds).count tile ∧
        ValidCounts
          (targetHand before
            (countsOfTiles (mentsuHandTarget pair melds))) ∧
        mentsuHandTargetDistance before pair melds = distance
  have hexists : ∃ distance, candidateDistance distance := by
    obtain ⟨pair, melds, hmelds, hsum, hvalid⟩ := hcandidate
    exact ⟨mentsuHandTargetDistance before pair melds,
      pair, melds, hmelds, hsum, hvalid, rfl⟩
  let distance := Nat.find hexists
  obtain ⟨pair, melds, hmelds, hsum, hvalid, hdistance⟩ :=
    Nat.find_spec hexists
  have hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
          mentsuHandTargetDistance before pair melds ≤
            mentsuHandTargetDistance before otherPair otherMelds := by
    intro otherPair otherMelds hotherMelds hotherValid
    have hlength : melds.length = otherMelds.length := by omega
    have hsumOther :
        (∑ tile : Tile, before.counts tile) =
          ∑ tile : Tile, (mentsuHandTarget otherPair otherMelds).count tile := by
      calc
        (∑ tile : Tile, before.counts tile) =
            ∑ tile : Tile, (mentsuHandTarget pair melds).count tile := hsum
        _ = (mentsuHandTarget pair melds).card := by
          simpa [countsOfTiles] using
            (countsOfTiles_sum_eq_card (mentsuHandTarget pair melds))
        _ = (mentsuHandTarget otherPair otherMelds).card := by
          simp [mentsuHandTarget, Multiset.card_add, pairTiles_card,
            meldsTiles_card, hlength]
        _ = ∑ tile : Tile, (mentsuHandTarget otherPair otherMelds).count tile := by
          symm
          simpa [countsOfTiles] using
            (countsOfTiles_sum_eq_card (mentsuHandTarget otherPair otherMelds))
    have hotherCandidate :
        candidateDistance (mentsuHandTargetDistance before otherPair otherMelds) :=
      ⟨otherPair, otherMelds, hotherMelds, hsumOther, hotherValid, rfl⟩
    calc
      mentsuHandTargetDistance before pair melds = distance := hdistance
      _ ≤ mentsuHandTargetDistance before otherPair otherMelds := by
        change Nat.find hexists ≤
          mentsuHandTargetDistance before otherPair otherMelds
        exact nat_find_le_of_mem candidateDistance hexists hotherCandidate
  have hshape :
      IsShapeShanten before .mentsuHand ((distance : Int) - 1) :=
    isShapeShanten_mentsuHand_of_minimal_mentsuHandTargetDistance
      distance before pair melds hdistance hsum hvalid hmelds hminimalTarget
  exact ⟨(distance : Int) - 1, hshape⟩

set_option maxHeartbeats 1000000 in
lemma exists_isShapeShanten_mentsuHand_of_valid_mentsuHandTarget_one_more
    (before : Hand) (hbeforeValid : ValidCounts before)
    (hcandidate :
      ∃ pair melds,
        melds.length + before.fixedMelds = 4 ∧
          (∑ tile : Tile,
            countsOfTiles (mentsuHandTarget pair melds) tile) =
            (∑ tile : Tile, before.counts tile) + 1 ∧
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget pair melds)))) :
    ∃ value : Int, IsShapeShanten before .mentsuHand value := by
  classical
  let candidateDistance : Nat → Prop := fun distance =>
    ∃ pair melds,
      melds.length + before.fixedMelds = 4 ∧
        (∑ tile : Tile,
          countsOfTiles (mentsuHandTarget pair melds) tile) =
          (∑ tile : Tile, before.counts tile) + 1 ∧
        ValidCounts
          (targetHand before
            (countsOfTiles (mentsuHandTarget pair melds))) ∧
        mentsuHandTargetDistance before pair melds = distance
  have hexists : ∃ distance, candidateDistance distance := by
    obtain ⟨pair, melds, hmelds, hsum, hvalid⟩ := hcandidate
    exact ⟨mentsuHandTargetDistance before pair melds,
      pair, melds, hmelds, hsum, hvalid, rfl⟩
  let distance := Nat.find hexists
  obtain ⟨pair, melds, hmelds, hsum, hvalid, hdistance⟩ :=
    Nat.find_spec hexists
  have hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
          mentsuHandTargetDistance before pair melds ≤
            mentsuHandTargetDistance before otherPair otherMelds := by
    intro otherPair otherMelds hotherMelds hotherValid
    have hlength : melds.length = otherMelds.length := by omega
    have hsumOther :
        (∑ tile : Tile,
          countsOfTiles (mentsuHandTarget otherPair otherMelds) tile) =
          (∑ tile : Tile, before.counts tile) + 1 := by
      calc
        (∑ tile : Tile,
            countsOfTiles (mentsuHandTarget otherPair otherMelds) tile) =
            (mentsuHandTarget otherPair otherMelds).card := by
          simpa [countsOfTiles] using
            (countsOfTiles_sum_eq_card (mentsuHandTarget otherPair otherMelds))
        _ = (mentsuHandTarget pair melds).card := by
          simp [mentsuHandTarget, Multiset.card_add, pairTiles_card,
            meldsTiles_card, hlength]
        _ = ∑ tile : Tile,
            countsOfTiles (mentsuHandTarget pair melds) tile := by
          symm
          simpa [countsOfTiles] using
            (countsOfTiles_sum_eq_card (mentsuHandTarget pair melds))
        _ = (∑ tile : Tile, before.counts tile) + 1 := hsum
    have hotherCandidate :
        candidateDistance (mentsuHandTargetDistance before otherPair otherMelds) :=
      ⟨otherPair, otherMelds, hotherMelds, hsumOther, hotherValid, rfl⟩
    calc
      mentsuHandTargetDistance before pair melds = distance := hdistance
      _ ≤ mentsuHandTargetDistance before otherPair otherMelds := by
        change Nat.find hexists ≤
          mentsuHandTargetDistance before otherPair otherMelds
        exact nat_find_le_of_mem candidateDistance hexists hotherCandidate
  have hshape :
      IsShapeShanten before .mentsuHand ((distance : Int) - 1) :=
    isShapeShanten_mentsuHand_of_minimal_mentsuHandTargetDistance_one_more
      distance before pair melds hdistance hsum hbeforeValid
      hvalid hmelds hminimalTarget
  exact ⟨(distance : Int) - 1, hshape⟩

lemma sum_countsOfTiles_mentsuHandTarget_of_thirteen_tile_count
    (hand : Hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (pair : Tile) (melds : List Meld)
    (hmelds : melds.length + hand.fixedMelds = 4) :
    (∑ tile : Tile, countsOfTiles (mentsuHandTarget pair melds) tile) =
      (∑ tile : Tile, hand.counts tile) + 1 := by
  calc
    _ = (mentsuHandTarget pair melds).card := by
      exact countsOfTiles_sum_eq_card (mentsuHandTarget pair melds)
    _ = 2 + 3 * melds.length := by
      simp [mentsuHandTarget, Multiset.card_add, pairTiles_card,
        meldsTiles_card]
    _ = tileCount hand + 1 := by omega
    _ = (∑ tile : Tile, hand.counts tile) + 1 := by rfl

set_option maxHeartbeats 1000000 in
lemma exists_mentsuHandTarget_reaching_isShapeShanten_distance
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (value : Int) (hshape : IsShapeShanten hand .mentsuHand value) :
    ∃ distance : Nat, ∃ pair melds,
      (distance : Int) = value + 1 ∧
      melds.length + hand.fixedMelds = 4 ∧
      ValidCounts
        (targetHand hand
          (countsOfTiles (mentsuHandTarget pair melds))) ∧
      mentsuHandTargetDistance hand pair melds = distance ∧
      ReachesCompletion Complete .mentsuHand hand distance := by
  rcases hshape with ⟨_, distance, hvalue, hreach, hminimal⟩
  obtain ⟨pair, melds, hmelds, hvalid, hdistanceLE⟩ :=
    exists_mentsuHandTarget_distance_le_of_reachesCompletion
      hand distance hreach
  have hsum :=
    sum_countsOfTiles_mentsuHandTarget_of_thirteen_tile_count
      hand hstanding pair melds hmelds
  obtain ⟨targetDistance, htargetDistance, htargetReach⟩ :=
    reachesCompletion_mentsuHand_of_one_more_target_tile
      hand (countsOfTiles (mentsuHandTarget pair melds)) pair melds
      hsum hbeforeValid hvalid hmelds
      (targetHand_hasTiles_countsOfTiles hand
        (mentsuHandTarget pair melds))
  have hreachDistance :
      targetDistance = mentsuHandTargetDistance hand pair melds := by
    calc
      targetDistance =
          countDeficit hand.counts
            (countsOfTiles (mentsuHandTarget pair melds)) :=
        htargetDistance
      _ = mentsuHandTargetDistance hand pair melds :=
        (mentsuHandTargetDistance_eq_countDeficit hand pair melds).symm
  have htargetLE : targetDistance ≤ distance := by
    calc
      targetDistance = mentsuHandTargetDistance hand pair melds :=
        hreachDistance
      _ ≤ distance := hdistanceLE
  have hdistanceLEtarget : distance ≤ targetDistance := by
    by_contra hnot
    have hshorter : targetDistance < distance := by omega
    exact hminimal targetDistance hshorter htargetReach
  have htargetDistanceEq : mentsuHandTargetDistance hand pair melds = distance := by
    omega
  have htargetDistanceEqNat : targetDistance = distance := by
    calc
      targetDistance = mentsuHandTargetDistance hand pair melds :=
        hreachDistance
      _ = distance := htargetDistanceEq
  refine ⟨distance, pair, melds, hvalue, hmelds, hvalid,
    htargetDistanceEq, ?_⟩
  rw [← htargetDistanceEqNat]
  exact htargetReach

set_option maxHeartbeats 1000000 in
lemma exists_minimal_mentsuHandTarget_of_isShapeShanten_mentsuHand
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (value : Int) (hshape : IsShapeShanten hand .mentsuHand value) :
    ∃ distance : Nat, ∃ pair melds,
      (distance : Int) = value + 1 ∧
      melds.length + hand.fixedMelds = 4 ∧
      ValidCounts
        (targetHand hand
          (countsOfTiles (mentsuHandTarget pair melds))) ∧
      mentsuHandTargetDistance hand pair melds = distance ∧
      ReachesCompletion Complete .mentsuHand hand distance ∧
      ∀ otherPair otherMelds,
        otherMelds.length + hand.fixedMelds = 4 →
        ValidCounts
          (targetHand hand
            (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
        mentsuHandTargetDistance hand pair melds ≤
          mentsuHandTargetDistance hand otherPair otherMelds := by
  obtain ⟨distance, pair, melds, hvalue, hmelds, hvalid,
      hdistance, hreach⟩ :=
    exists_mentsuHandTarget_reaching_isShapeShanten_distance
      hand hbeforeValid hstanding value hshape
  rcases hshape with ⟨_, actualDistance, hactualValue, _, hminimal⟩
  have hdistanceEq : distance = actualDistance := by omega
  refine ⟨distance, pair, melds, hvalue, hmelds, hvalid,
    hdistance, hreach, ?_⟩
  intro otherPair otherMelds hotherMelds hotherValid
  have hsumOther :=
    sum_countsOfTiles_mentsuHandTarget_of_thirteen_tile_count
      hand hstanding otherPair otherMelds hotherMelds
  obtain ⟨otherDistance, hotherDistance, hotherReach⟩ :=
    reachesCompletion_mentsuHand_of_one_more_target_tile
      hand (countsOfTiles (mentsuHandTarget otherPair otherMelds))
      otherPair otherMelds hsumOther hbeforeValid hotherValid
      hotherMelds
      (targetHand_hasTiles_countsOfTiles hand
        (mentsuHandTarget otherPair otherMelds))
  have hotherDistanceEq :
      otherDistance =
        mentsuHandTargetDistance hand otherPair otherMelds := by
    calc
      otherDistance =
          countDeficit hand.counts
            (countsOfTiles (mentsuHandTarget otherPair otherMelds)) :=
        hotherDistance
      _ = mentsuHandTargetDistance hand otherPair otherMelds :=
        (mentsuHandTargetDistance_eq_countDeficit hand otherPair otherMelds).symm
  by_contra hnotMinimal
  have hshorter : otherDistance < actualDistance := by
    omega
  exact hminimal otherDistance hshorter hotherReach

lemma isShapeShanten_mentsuHand_iff_exists_minimal_mentsuHandTarget
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (value : Int) :
    IsShapeShanten hand .mentsuHand value ↔
      ∃ distance : Nat, ∃ pair melds,
        (distance : Int) = value + 1 ∧
        melds.length + hand.fixedMelds = 4 ∧
        (∑ tile : Tile,
          countsOfTiles (mentsuHandTarget pair melds) tile) =
          (∑ tile : Tile, hand.counts tile) + 1 ∧
        ValidCounts
          (targetHand hand
            (countsOfTiles (mentsuHandTarget pair melds))) ∧
        mentsuHandTargetDistance hand pair melds = distance ∧
        ∀ otherPair otherMelds,
          otherMelds.length + hand.fixedMelds = 4 →
          ValidCounts
            (targetHand hand
              (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
          mentsuHandTargetDistance hand pair melds ≤
            mentsuHandTargetDistance hand otherPair otherMelds := by
  constructor
  · intro hshape
    obtain ⟨distance, pair, melds, hvalue, hmelds, hvalid,
        hdistance, _, hminimal⟩ :=
      exists_minimal_mentsuHandTarget_of_isShapeShanten_mentsuHand
        hand hbeforeValid hstanding value hshape
    have hsum :=
      sum_countsOfTiles_mentsuHandTarget_of_thirteen_tile_count
        hand hstanding pair melds hmelds
    exact ⟨distance, pair, melds, hvalue, hmelds, hsum, hvalid,
      hdistance, hminimal⟩
  · rintro ⟨distance, pair, melds, hvalue, hmelds, hsum,
      hvalid, hdistance, hminimal⟩
    have hshape :
        IsShapeShanten hand .mentsuHand ((distance : Int) - 1) :=
      isShapeShanten_mentsuHand_of_minimal_mentsuHandTargetDistance_one_more
        distance hand pair melds hdistance hsum hbeforeValid
        hvalid hmelds hminimal
    have hvalueEq : (distance : Int) - 1 = value := by omega
    exact hvalueEq ▸ hshape

private def canonicalMentsuHandPair : Tile :=
  .honor ⟨0, by omega⟩

private def canonicalMentsuHandMelds : Nat → List Meld
  | 0 =>
      [ .sequence .man ⟨0, by omega⟩
      , .sequence .pin ⟨0, by omega⟩
      , .sequence .sou ⟨0, by omega⟩
      , .triplet (.honor ⟨1, by omega⟩) ]
  | 1 =>
      [ .sequence .man ⟨0, by omega⟩
      , .sequence .pin ⟨0, by omega⟩
      , .sequence .sou ⟨0, by omega⟩ ]
  | 2 =>
      [ .sequence .man ⟨0, by omega⟩
      , .sequence .pin ⟨0, by omega⟩ ]
  | 3 => [ .sequence .man ⟨0, by omega⟩ ]
  | _ => []

private lemma canonicalMentsuHandMelds_length
    (fixedMelds : Nat) (hfixed : fixedMelds ≤ 4) :
    (canonicalMentsuHandMelds fixedMelds).length + fixedMelds = 4 := by
  have hcases :
      fixedMelds = 0 ∨ fixedMelds = 1 ∨ fixedMelds = 2 ∨
        fixedMelds = 3 ∨ fixedMelds = 4 := by omega
  rcases hcases with h | h | h | h | h
  all_goals subst fixedMelds <;> simp [canonicalMentsuHandMelds]

private lemma canonicalMentsuHandTarget_validCounts
    (fixedMelds : Nat) (hfixed : fixedMelds ≤ 4) :
    ∀ tile,
      (mentsuHandTarget canonicalMentsuHandPair
        (canonicalMentsuHandMelds fixedMelds)).count tile ≤ 4 := by
  intro tile
  have hcases :
      fixedMelds = 0 ∨ fixedMelds = 1 ∨ fixedMelds = 2 ∨
        fixedMelds = 3 ∨ fixedMelds = 4 := by omega
  rcases hcases with h | h | h | h | h
  all_goals subst fixedMelds
  all_goals
    cases tile with
    | suited suit rank =>
        cases suit <;> fin_cases rank <;>
          simp [canonicalMentsuHandPair, canonicalMentsuHandMelds,
            mentsuHandTarget, pairTiles, meldsTiles, meldTiles]
    | honor rank =>
        fin_cases rank <;>
          simp [canonicalMentsuHandPair, canonicalMentsuHandMelds,
            mentsuHandTarget, pairTiles, meldsTiles, meldTiles]

set_option maxHeartbeats 1000000 in
lemma exists_mentsuHandShanten_as_min_validTargetDistance
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13) :
    ∃ distance,
      distance ∈ validMentsuHandTargetDistances hand ∧
      (∀ otherDistance,
        otherDistance ∈ validMentsuHandTargetDistances hand →
          distance ≤ otherDistance) ∧
      IsShapeShanten hand .mentsuHand ((distance : Int) - 1) := by
  have hfixed : hand.fixedMelds ≤ 4 := by omega
  have hmelds :=
    canonicalMentsuHandMelds_length hand.fixedMelds hfixed
  have hvalid :
      ValidCounts
        (targetHand hand
          (countsOfTiles
            (mentsuHandTarget canonicalMentsuHandPair
              (canonicalMentsuHandMelds hand.fixedMelds)))) := by
    intro tile
    change
      (mentsuHandTarget canonicalMentsuHandPair
        (canonicalMentsuHandMelds hand.fixedMelds)).count tile ≤ 4
    exact canonicalMentsuHandTarget_validCounts
      hand.fixedMelds hfixed tile
  obtain ⟨distance, hdistanceMem, hminimalDistance⟩ :=
    exists_min_validMentsuHandTargetDistance hand hfixed
      ⟨canonicalMentsuHandPair, canonicalMentsuHandMelds hand.fixedMelds,
        hmelds, hvalid⟩
  obtain ⟨pair, melds, htargetMelds, htargetValid, htargetDistance⟩ :=
    (mem_validMentsuHandTargetDistances_iff
      hand hfixed distance).mp hdistanceMem
  have hsum :=
    sum_countsOfTiles_mentsuHandTarget_of_thirteen_tile_count
      hand hstanding pair melds htargetMelds
  have hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + hand.fixedMelds = 4 →
          ValidCounts
            (targetHand hand
              (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
          mentsuHandTargetDistance hand pair melds ≤
            mentsuHandTargetDistance hand otherPair otherMelds := by
    intro otherPair otherMelds hotherMelds hotherValid
    have hotherDistanceMem :
        mentsuHandTargetDistance hand otherPair otherMelds ∈
          validMentsuHandTargetDistances hand :=
      (mem_validMentsuHandTargetDistances_iff
        hand hfixed
        (mentsuHandTargetDistance hand otherPair otherMelds)).mpr
        ⟨otherPair, otherMelds, hotherMelds, hotherValid, rfl⟩
    calc
      mentsuHandTargetDistance hand pair melds = distance :=
        htargetDistance
      _ ≤ mentsuHandTargetDistance hand otherPair otherMelds :=
        hminimalDistance _ hotherDistanceMem
  have hshape :
      IsShapeShanten hand .mentsuHand ((distance : Int) - 1) :=
    isShapeShanten_mentsuHand_of_minimal_mentsuHandTargetDistance_one_more
      distance hand pair melds htargetDistance hsum hbeforeValid
      htargetValid htargetMelds hminimalTarget
  exact ⟨distance, hdistanceMem, hminimalDistance, hshape⟩

lemma mentsuHandTargetMinimumSearch_eq_some_iff
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (value : Int) :
    mentsuHandTargetMinimumSearch hand = some value ↔
      IsShapeShanten hand .mentsuHand value := by
  obtain ⟨distance, hmem, hminimal, hshape⟩ :=
    exists_mentsuHandShanten_as_min_validTargetDistance
      hand hbeforeValid hstanding
  let distances := validMentsuHandTargetDistances hand
  have hnonempty : distances.Nonempty := ⟨distance, hmem⟩
  have hdistance :
      distances.min' hnonempty = distance := by
    apply Nat.le_antisymm
    · exact Finset.min'_le distances distance hmem
    · exact hminimal _ (Finset.min'_mem distances hnonempty)
  have hsearch :
      mentsuHandTargetMinimumSearch hand =
        some ((distance : Int) - 1) := by
    simp [mentsuHandTargetMinimumSearch, distances, hnonempty, hdistance]
  constructor
  · intro hresult
    have hvalues :
        some ((distance : Int) - 1) = some value :=
      hsearch.symm.trans hresult
    have hvalue : (distance : Int) - 1 = value :=
      Option.some.inj hvalues
    exact hvalue ▸ hshape
  · intro hvalue
    have heq :
        ((distance : Int) - 1) = value :=
      isShapeShanten_unique hshape hvalue
    rw [hsearch, heq]

lemma mentsuHandTargetMinimumSearch_eq_some_iff_of_thirteenTileHand
    (hand : Hand) (hthirteen : IsThirteenTileHand hand) (value : Int) :
    mentsuHandTargetMinimumSearch hand = some value ↔
      IsShapeShanten hand .mentsuHand value := by
  rcases hthirteen with ⟨hfixed, hcount, hvalid⟩
  apply mentsuHandTargetMinimumSearch_eq_some_iff hand hvalid
  rw [hfixed, hcount]

lemma exists_isShapeShanten_mentsuHand_of_valid_thirteen_tile_count
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13) :
    ∃ value : Int, IsShapeShanten hand .mentsuHand value := by
  obtain ⟨distance, _, _, hshape⟩ :=
    exists_mentsuHandShanten_as_min_validTargetDistance
      hand hbeforeValid hstanding
  exact ⟨(distance : Int) - 1, hshape⟩

lemma exists_isShapeShanten_mentsuHand_of_thirteenTileHand
    (hand : Hand) (hthirteen : IsThirteenTileHand hand) :
    ∃ value : Int, IsShapeShanten hand .mentsuHand value := by
  rcases hthirteen with ⟨hfixed, hcount, hvalid⟩
  apply exists_isShapeShanten_mentsuHand_of_valid_thirteen_tile_count
    hand hvalid
  rw [hfixed, hcount]

lemma exists_isOverallShanten_of_thirteenTileHand
    (hand : Hand) (hthirteen : IsThirteenTileHand hand) :
    ∃ value : Int, IsOverallShanten hand value := by
  obtain ⟨mentsuHandValue, hmentsuHand⟩ :=
    exists_isShapeShanten_mentsuHand_of_thirteenTileHand hand hthirteen
  have hmentsuHandOption :
      ShapeShanten hand .mentsuHand = some mentsuHandValue :=
    (shapeShanten_eq_some_iff).2 hmentsuHand
  unfold IsOverallShanten OverallShanten
  rw [hmentsuHandOption]
  cases hseven : ShapeShanten hand .sevenPairs <;>
    cases horphans : ShapeShanten hand .thirteenOrphans <;>
      simp [minOption, hseven, horphans]

lemma MentsuHandBlockDecomposition.exists_isShapeShanten
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand)
    (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13) :
    ∃ value : Int, IsShapeShanten hand .mentsuHand value := by
  let melds :=
    decomposition.melds ++
      taatsuCompletionMelds decomposition.taatsus
  have htarget :
      mentsuHandTarget decomposition.pair melds =
        decomposition.completedTarget := by
    rw [MentsuHandBlockDecomposition.completedTarget_eq]
    rfl
  have hmelds :
      melds.length + hand.fixedMelds = 4 := by
    dsimp [melds]
    exact decomposition.completedMeldCount
  have htargetCard :
      (mentsuHandTarget decomposition.pair melds).card =
        tileCount hand + 1 := by
    rw [htarget, MentsuHandBlockDecomposition.completedTarget_eq]
    simp [Multiset.card_add, pairTiles_card, meldsTiles_card,
      List.length_append, taatsuCompletionMelds_length]
    have hblocks := decomposition.blocks
    omega
  have hsum :
      (∑ tile : Tile,
        countsOfTiles (mentsuHandTarget decomposition.pair melds) tile) =
        (∑ tile : Tile, hand.counts tile) + 1 := by
    calc
      _ = (mentsuHandTarget decomposition.pair melds).card := by
        exact countsOfTiles_sum_eq_card
          (mentsuHandTarget decomposition.pair melds)
      _ = tileCount hand + 1 := htargetCard
      _ = (∑ tile : Tile, hand.counts tile) + 1 := by
        rfl
  have hvalid :
      ValidCounts
        (targetHand hand
          (countsOfTiles (mentsuHandTarget decomposition.pair melds))) := by
    rw [htarget]
    exact decomposition.validCounts_completedTarget
  exact exists_isShapeShanten_mentsuHand_of_valid_mentsuHandTarget_one_more
    hand hbeforeValid
    ⟨decomposition.pair, melds, hmelds, hsum, hvalid⟩

lemma mentsuHandTarget_count_le_stateHistoryTiles
    (state : MentsuHandSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuHandTarget pair state.meldHistory.reverse).count tile ≤
        (stateHistoryTiles state).count tile := by
  intro tile
  simp [mentsuHandTarget, stateHistoryTiles, pairHistoryTiles, hpair,
    Multiset.count_add]

lemma mentsuHandTarget_count_le_used
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuHandTarget pair state.meldHistory.reverse).count tile ≤
        state.used.count tile := by
  intro tile
  rw [reachableWithin_used_eq_historyTiles hand fuel state hreachable]
  exact mentsuHandTarget_count_le_stateHistoryTiles state pair hpair tile

lemma mentsuHandTarget_count_le_hand
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuHandTarget pair state.meldHistory.reverse).count tile ≤
        hand.counts tile := by
  intro tile
  exact le_trans
    (mentsuHandTarget_count_le_used hand fuel state hreachable pair hpair tile)
    (reachableWithin_used_subset hand fuel state hreachable tile)

lemma mentsuHandTarget_hasMeldCount_of_complete
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcomplete : IsMentsuHandSearchComplete hand state) :
    HasMentsuHandMeldCount hand state.meldHistory.reverse := by
  have hlength := reachableWithin_melds_eq_history_length
    hand fuel state hreachable
  rcases hcomplete with ⟨hmelds, _⟩
  unfold HasMentsuHandMeldCount
  simpa [List.length_reverse, hlength] using hmelds

lemma mentsuHandTargetOfState_exists_of_complete
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcomplete : IsMentsuHandSearchComplete hand state) :
    ∃ target, mentsuHandTargetOfState state = some target ∧
      HasMentsuHandMeldCount hand state.meldHistory.reverse := by
  cases hpair : state.pair with
  | none =>
      exfalso
      simpa [hpair] using hcomplete.2
  | some pair =>
      refine ⟨mentsuHandTarget pair state.meldHistory.reverse, ?_, ?_⟩
      · rw [mentsuHandTargetOfState, hpair]
        rfl
      · exact mentsuHandTarget_hasMeldCount_of_complete
          hand fuel state hreachable hcomplete

lemma completedMeldsForState_hasMeldCount
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcount : state.melds + state.taatsu + hand.fixedMelds = 4) :
    HasMentsuHandMeldCount hand (completedMeldsForState state) := by
  have hmelds := reachableWithin_melds_eq_history_length
    hand fuel state hreachable
  have htaatsu := reachableWithin_taatsu_eq_history_length
    hand fuel state hreachable
  unfold HasMentsuHandMeldCount
  rw [completedMeldsForState_length, ← hmelds, ← htaatsu]
  omega

/-
## 10. 制約付き探索からの最終接続

最後の補題では、制約付きブロック探索が成功した場合に完成目標、ひいては形
シャンテン数の証人を取り出します。これは条件付きの健全性接続であり、
任意の13枚手をこの狭い分解へ被覆する完全性や、旧一選択走査との同値を
完結させるものではありません。
-/

lemma complete_mentsuHand_of_blockSearch
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcomplete : IsMentsuHandBlockSearchComplete before state)
    (hvalid : ∀ pair, state.pair = some pair →
      ValidCounts
        (targetHand before
          (countsOfTiles (completedTargetForState state pair)))) :
    ∃ pair,
      Complete .mentsuHand
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      refine ⟨pair, ?_⟩
      apply complete_mentsuHand_completedTarget before state pair
      · exact hvalid pair hstatePair
      · exact completedMeldsForState_hasMeldCount
          before fuel state hreachable hcount

lemma complete_mentsuHand_of_blockSearch_of_copyLimit
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcomplete : IsMentsuHandBlockSearchComplete before state)
    (hcopy : CompletionRespectsCopyLimit state) :
    ∃ pair,
      Complete .mentsuHand
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      refine ⟨pair, ?_⟩
      apply complete_mentsuHand_completedTarget before state pair
      · exact validCounts_completedTarget_of_copyLimit
          before fuel state hreachable hcopy pair hstatePair
      · exact completedMeldsForState_hasMeldCount
          before fuel state hreachable hcount

lemma complete_mentsuHand_of_constrainedBlockSearch
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit before fuel state)
    (hcomplete : IsMentsuHandBlockSearchComplete before state) :
    ∃ pair,
      Complete .mentsuHand
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  exact complete_mentsuHand_of_blockSearch_of_copyLimit
    before fuel state
    (reachableWithinWithCopyLimit_to_reachableWithin
      before fuel state hreachable)
    hcomplete
    (reachableWithinWithCopyLimit_copyLimit before fuel state hreachable)

lemma validMentsuHandTargetDistance_mem_of_constrainedBlockSearch
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit before fuel state)
    (hcomplete : IsMentsuHandBlockSearchComplete before state) :
    ∃ pair melds,
      melds.length + before.fixedMelds = 4 ∧
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))) ∧
      mentsuHandTargetDistance before pair melds ∈
        validMentsuHandTargetDistances before := by
  have hreachable' :
      reachableWithin before fuel state :=
    reachableWithinWithCopyLimit_to_reachableWithin
      before fuel state hreachable
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      let melds := completedMeldsForState state
      have hmelds :
          melds.length + before.fixedMelds = 4 := by
        dsimp [melds]
        exact completedMeldsForState_hasMeldCount
          before fuel state hreachable' hcount
      have htarget :
          mentsuHandTarget pair melds =
            completedTargetForState state pair := by
        rfl
      have hvalid :
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget pair melds))) := by
        rw [htarget]
        exact validCounts_completedTarget_of_copyLimit
          before fuel state hreachable'
          (reachableWithinWithCopyLimit_copyLimit
            before fuel state hreachable)
          pair hstatePair
      refine ⟨pair, melds, hmelds, hvalid, ?_⟩
      apply (mem_validMentsuHandTargetDistances_iff
        before (by omega) (mentsuHandTargetDistance before pair melds)).2
      exact ⟨pair, melds, hmelds, hvalid, rfl⟩

lemma exists_isShapeShanten_mentsuHand_of_constrainedBlockSearch
    (before : Hand) (hbeforeValid : ValidCounts before)
    (hstanding : tileCount before + 3 * before.fixedMelds = 13)
    (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit before fuel state)
    (hcomplete : IsMentsuHandBlockSearchComplete before state) :
    ∃ value : Int, IsShapeShanten before .mentsuHand value := by
  have hreachable' :
      reachableWithin before fuel state :=
    reachableWithinWithCopyLimit_to_reachableWithin
      before fuel state hreachable
  have hcopy :
      CompletionRespectsCopyLimit state :=
    reachableWithinWithCopyLimit_copyLimit before fuel state hreachable
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      let melds := completedMeldsForState state
      have hmelds :
          melds.length + before.fixedMelds = 4 := by
        dsimp [melds]
        exact completedMeldsForState_hasMeldCount
          before fuel state hreachable' hcount
      have htarget :
          mentsuHandTarget pair melds =
            completedTargetForState state pair := by
        rfl
      have hsum' :=
        completedTargetForState_sum_of_blockCount
          before fuel state hreachable' hcount pair
      have hsum :
          (∑ tile : Tile,
            countsOfTiles (mentsuHandTarget pair melds) tile) =
            (∑ tile : Tile, before.counts tile) + 1 := by
        calc
          _ = 14 - 3 * before.fixedMelds := by
            rw [htarget]
            exact hsum'
          _ = tileCount before + 1 := by
            omega
          _ = (∑ tile : Tile, before.counts tile) + 1 := by
            rfl
      have hvalid :
          ValidCounts
            (targetHand before (countsOfTiles (mentsuHandTarget pair melds))) := by
        rw [htarget]
        exact validCounts_completedTarget_of_copyLimit
          before fuel state hreachable' hcopy pair hstatePair
      exact exists_isShapeShanten_mentsuHand_of_valid_mentsuHandTarget_one_more
        before hbeforeValid
        ⟨pair, melds, hmelds, hsum, hvalid⟩

end Shanten
