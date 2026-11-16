import Shanten.Exchange

/-!
# Seven pairs / Basic

Tenpai and completion count vectors, tenpai conditions, and target counts.
-/

namespace Shanten

def sevenPairsTenpaiTargetCounts (pairs : Finset Tile) (single : Tile) : TileCounts :=
  fun tile => if tile ∈ pairs then 2 else if tile = single then 1 else 0

def sevenPairsTenpaiTarget (pairs : Finset Tile) (single : Tile) : Hand :=
  { counts := sevenPairsTenpaiTargetCounts pairs single
    fixedMelds := 0 }

/-- A thirteen-tile seven-pairs tenpai shape. -/
def IsSevenPairsTenpai (hand : Hand) : Prop :=
  hand.fixedMelds = 0 ∧
    tileCount hand = 13 ∧
    distinctTileCount hand = 7 ∧
    pairCount hand = 6

lemma isSevenPairsTenpai_of_counts
    (hand : Hand) (h13 : IsThirteenTileHand hand)
    (hdistinct : distinctTileCount hand = 7)
    (hpairs : pairCount hand = 6) :
    IsSevenPairsTenpai hand := by
  exact ⟨h13.1, h13.2.1, hdistinct, hpairs⟩

lemma sevenPairsTenpaiTarget_fixedMelds
    (pairs : Finset Tile) (single : Tile) :
    (sevenPairsTenpaiTarget pairs single).fixedMelds = 0 := by
  rfl

lemma sevenPairsTenpaiTarget_counts_le_four
    (pairs : Finset Tile) (single : Tile) (tile : Tile) :
    (sevenPairsTenpaiTarget pairs single).counts tile ≤ 4 := by
  unfold sevenPairsTenpaiTarget sevenPairsTenpaiTargetCounts
  by_cases hp : tile ∈ pairs <;> by_cases hs : tile = single <;>
    simp [hp, hs] <;> split <;> omega

def sevenPairsCompletionCounts (pairs : Finset Tile) : TileCounts :=
  fun tile => if tile ∈ pairs then 2 else 0

lemma sevenPairsTenpaiTargetCounts_single
    (pairs : Finset Tile) (single : Tile) (hsingle : single ∉ pairs) :
    sevenPairsTenpaiTargetCounts pairs single single = 1 := by
  simp [sevenPairsTenpaiTargetCounts, hsingle]

lemma sevenPairsTenpaiTargetCounts_pair
    (pairs : Finset Tile) (single tile : Tile) (htile : tile ∈ pairs) :
    sevenPairsTenpaiTargetCounts pairs single tile = 2 := by
  simp [sevenPairsTenpaiTargetCounts, htile]

lemma sevenPairsTenpaiTargetCounts_other
    (pairs : Finset Tile) (single tile : Tile)
    (htile : tile ∉ pairs) (hne : tile ≠ single) :
    sevenPairsTenpaiTargetCounts pairs single tile = 0 := by
  simp [sevenPairsTenpaiTargetCounts, htile, hne]

lemma exchangeDistance_eq_target_deficit
    (hand : Hand) (pairs : Finset Tile) (single : Tile) :
    exchangeDistance hand (sevenPairsTenpaiTargetCounts pairs single) =
      ∑ tile : Tile, (sevenPairsTenpaiTargetCounts pairs single tile - hand.counts tile) := by
  simp [exchangeDistance, countDeficit]

end Shanten
