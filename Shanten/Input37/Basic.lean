import Shanten.Capacity.Basic

/-!
# Signed aka37 inputs and normalization

Indices 0/10/20 are red fives; 1..9/11..19/21..29 are ordinary
suited tiles; 30..36 are honors. Normalization is linear over integers.
-/

namespace Shanten.Input37

abbrev Counts37 := Fin 37 → Int

structure MeldInput where
  kind : String
  tiles : Counts37

structure Input where
  standing : Counts37
  melds : List MeldInput

def normalizeTile (index : Fin 37) : Tile :=
  if hsuited : index.val < 30 then
    let suit := if index.val < 10 then Suit.man else if index.val < 20 then .pin else .sou
    let rank := index.val % 10
    .suited suit ⟨if rank = 0 then 4 else rank - 1, by
      have : rank < 10 := Nat.mod_lt _ (by decide)
      split <;> omega⟩
  else
    .honor ⟨index.val - 30, by omega⟩

def capacity (index : Fin 37) : Nat :=
  if index.val < 30 then
    if index.val % 10 = 0 then 1 else if index.val % 10 = 5 then 3 else 4
  else 4

def normalIndex : Tile → Fin 37
  | .suited suit rank =>
      ⟨(match suit with | .man => 0 | .pin => 10 | .sou => 20) + rank.val + 1, by
        cases suit <;> simp_all <;> omega⟩
  | .honor rank => ⟨30 + rank.val, by omega⟩

lemma normalizeTile_normalIndex : ∀ tile, normalizeTile (normalIndex tile) = tile := by
  decide

def normalizeCounts (counts : Counts37) (tile : Tile) : Int :=
  ∑ index : Fin 37, if normalizeTile index = tile then counts index else 0

def meldCounts : List MeldInput → Counts37
  | [] => fun _ => 0
  | meld :: rest => fun index => meld.tiles index + meldCounts rest index

def totalCounts (input : Input) : Counts37 :=
  fun index => input.standing index + meldCounts input.melds index

def standingCount (input : Input) : Int :=
  ∑ index, input.standing index

def Nonnegative (counts : Counts37) : Prop :=
  ∀ index, 0 ≤ counts index

instance (counts : Counts37) : Decidable (Nonnegative counts) :=
  Fintype.decidableForallFintype

lemma normalizeCounts_nonneg (h : Nonnegative counts) (tile : Tile) :
    0 ≤ normalizeCounts counts tile := by
  unfold normalizeCounts
  apply Finset.sum_nonneg
  intro index _
  split
  · exact h index
  · omega

lemma normalizeCounts_add (left right : Counts37) (tile : Tile) :
    normalizeCounts (fun index => left index + right index) tile =
      normalizeCounts left tile + normalizeCounts right tile := by
  simp only [normalizeCounts, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  split <;> simp

lemma normalizeCounts_sum (counts : Counts37) :
    (∑ tile : Tile, normalizeCounts counts tile) = ∑ index, counts index := by
  unfold normalizeCounts
  rw [Finset.sum_comm]
  simp

set_option maxRecDepth 4096 in
lemma capacity_fiber :
    ∀ tile : Tile, normalizeCounts (fun index => (capacity index : Int)) tile = 4 := by
  decide

lemma normalizeCounts_le_four
    (hcapacity : ∀ index, counts index ≤ (capacity index : Int)) (tile : Tile) :
    normalizeCounts counts tile ≤ 4 := by
  rw [← capacity_fiber tile]
  unfold normalizeCounts
  apply Finset.sum_le_sum
  intro index _
  split
  · exact hcapacity index
  · omega

def kindMatches (kind : String) : Capacity.FixedMeld → Bool
  | .meld (.sequence _ _) => kind == "chi"
  | .meld (.triplet _) => kind == "pon"
  | .kan _ => kind == "ankan" || kind == "daiminkan" || kind == "kakan"

def MatchesMeld (raw : MeldInput) (target : Capacity.FixedMeld) : Prop :=
  kindMatches raw.kind target = true ∧
    ∀ tile, normalizeCounts raw.tiles tile = (target.tiles.count tile : Int)

instance (raw : MeldInput) (target : Capacity.FixedMeld) :
    Decidable (MatchesMeld raw target) :=
  @instDecidableAnd _ _ inferInstance Fintype.decidableForallFintype

def Valid (input : Input) : Prop :=
  Nonnegative input.standing ∧
    (∀ index : Fin input.melds.length, Nonnegative input.melds[index].tiles) ∧
    (∀ index, totalCounts input index ≤ (capacity index : Int)) ∧
    input.melds.length ≤ 4 ∧
    (standingCount input + 3 * (input.melds.length : Int) = 13 ∨
      standingCount input + 3 * (input.melds.length : Int) = 14) ∧
    ∀ index : Fin input.melds.length, ∃ target, MatchesMeld input.melds[index] target

end Shanten.Input37
