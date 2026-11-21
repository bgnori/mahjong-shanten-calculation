import Shanten.MentsuHand.Basic
import Mathlib.Data.Finset.Union

/-!
# State

Choice transitions, history invariants, reachability, and the 34-tile order.
-/

namespace Shanten

open MahjongDomain

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

def taatsuCompletionMelds : List Taatsu → List MentsuCandidate
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
      MentsuCandidateList.tiles (taatsuCompletionMelds taatsus) := by
  induction taatsus with
  | nil =>
      rfl
  | cons taatsu taatsus ih =>
      simp only [taatsuHistoryTiles, taatsuCompletionTiles,
        taatsuCompletionMelds, MentsuCandidateList.tiles]
      calc
        _ =
            (taatsuTiles taatsu +
                Multiset.replicate 1 (taatsuCompletionTile taatsu)) +
              (taatsuHistoryTiles taatsus + taatsuCompletionTiles taatsus) := by
                ac_rfl
        _ = MentsuCandidate.tiles (taatsuCompletionMeld taatsu) +
              MentsuCandidateList.tiles (taatsuCompletionMelds taatsus) := by
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
  exact Pair.tiles_card ⟨tile⟩

lemma meldsTiles_card (melds : List MentsuCandidate) :
    (MentsuCandidateList.tiles melds).card = 3 * melds.length := by
  induction melds with
  | nil =>
      rfl
  | cons meld melds ih =>
      change (MentsuCandidate.tiles meld + MentsuCandidateList.tiles melds).card =
        3 * (melds.length + 1)
      rw [Multiset.card_add, MentsuCandidate.tiles_card, ih]
      omega

def completedMeldsForState (state : MentsuHandSearchState) : List MentsuCandidate :=
  state.meldHistory.reverse ++
    taatsuCompletionMelds state.taatsuHistory.reverse

lemma completedMeldsForState_length
    (state : MentsuHandSearchState) :
    (completedMeldsForState state).length =
      state.meldHistory.length + state.taatsuHistory.length := by
  simp [completedMeldsForState, taatsuCompletionMelds_length,
    Nat.add_comm]

lemma meldsTiles_append (left right : List MentsuCandidate) :
    MentsuCandidateList.tiles (left ++ right) = MentsuCandidateList.tiles left + MentsuCandidateList.tiles right := by
  induction left with
  | nil =>
      simp [MentsuCandidateList.tiles]
  | cons meld left ih =>
      change MentsuCandidate.tiles meld + MentsuCandidateList.tiles (left ++ right) =
        (MentsuCandidate.tiles meld + MentsuCandidateList.tiles left) + MentsuCandidateList.tiles right
      rw [ih]
      ac_rfl

def stateHistoryTiles (state : MentsuHandSearchState) : Multiset Tile :=
  pairHistoryTiles state.pair +
    MentsuCandidateList.tiles state.meldHistory.reverse +
    taatsuHistoryTiles state.taatsuHistory.reverse

lemma taatsuHistoryTiles_append_single (history : List Taatsu) (taatsu : Taatsu) :
    taatsuHistoryTiles (history ++ [taatsu]) =
      taatsuHistoryTiles history + taatsuTiles taatsu := by
  induction history with
  | nil => simp [taatsuHistoryTiles]
  | cons head tail ih =>
      simp [taatsuHistoryTiles, ih, Multiset.add_assoc]

lemma meldsTiles_append_single (history : List MentsuCandidate) (meld : MentsuCandidate) :
    MentsuCandidateList.tiles (history ++ [meld]) =
      MentsuCandidateList.tiles history + MentsuCandidate.tiles meld := by
  simpa [MentsuCandidateList.tiles] using meldsTiles_append history [meld]

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
      change state.used + MentsuCandidate.tiles meld = _
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

end Shanten
