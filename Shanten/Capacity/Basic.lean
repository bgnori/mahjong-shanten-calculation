import Shanten.Exchange

/-!
# Capacity-aware hands

The fixed meld context is immutable. Standing counts reuse the abstract `Hand`,
but validity includes every tile occupied by the fixed melds.
-/

namespace Shanten.Capacity

open MahjongDomain

inductive FixedMeld
  | meld (value : MentsuCandidate)
  | kan (tile : Tile)
  deriving DecidableEq

def FixedMeld.tiles : FixedMeld → Multiset Tile
  | .meld value => MentsuCandidate.tiles value
  | .kan tile => Kan.occupiedTiles tile

def fixedTiles (fixed : List FixedMeld) : Multiset Tile :=
  fixed.foldr (fun meld rest => meld.tiles + rest) 0

def remainingCapacity (fixed : List FixedMeld) : TileCounts :=
  fun tile => 4 - (fixedTiles fixed).count tile

/-- Sum-based validation also rejects an overfull fixed context. -/
def ValidHand (fixed : List FixedMeld) (hand : Hand) : Prop :=
  hand.fixedMelds = fixed.length ∧ fixed.length ≤ 4 ∧
    ∀ tile, hand.counts tile + (fixedTiles fixed).count tile ≤ 4

def IsThirteenTileEquivalentHand (fixed : List FixedMeld) (hand : Hand) : Prop :=
  ValidHand fixed hand ∧ tileCount hand + 3 * fixed.length = 13

def IsFourteenTileEquivalentHand (fixed : List FixedMeld) (hand : Hand) : Prop :=
  ValidHand fixed hand ∧ tileCount hand + 3 * fixed.length = 14

lemma ValidHand.validCounts (hvalid : ValidHand fixed hand) :
    ValidCounts hand := by
  intro tile
  have := hvalid.2.2 tile
  omega

lemma ValidHand.fixed_count_le (hvalid : ValidHand fixed hand) (tile : Tile) :
    (fixedTiles fixed).count tile ≤ 4 := by
  have := hvalid.2.2 tile
  omega

lemma ValidHand.counts_le_capacity (hvalid : ValidHand fixed hand) (tile : Tile) :
    hand.counts tile ≤ remainingCapacity fixed tile := by
  have := hvalid.2.2 tile
  unfold remainingCapacity
  omega

lemma validHand_iff_capacity :
    ValidHand fixed hand ↔
      hand.fixedMelds = fixed.length ∧ fixed.length ≤ 4 ∧
        (∀ tile, (fixedTiles fixed).count tile ≤ 4) ∧
        (∀ tile, hand.counts tile ≤ remainingCapacity fixed tile) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.fixed_count_le, h.counts_le_capacity⟩
  · rintro ⟨hfixed, hlength, hoccupied, hcounts⟩
    refine ⟨hfixed, hlength, fun tile => ?_⟩
    have := hoccupied tile
    have := hcounts tile
    unfold remainingCapacity at *
    omega

lemma validHand_nil_iff :
    ValidHand [] hand ↔ hand.fixedMelds = 0 ∧ ValidCounts hand := by
  simp [ValidHand, fixedTiles, ValidCounts]

def drawHand (hand : Hand) (drawn : Tile) : Hand :=
  { counts := fun tile => hand.counts tile + (if tile = drawn then 1 else 0)
    fixedMelds := hand.fixedMelds }

lemma ValidHand.draw
    (hvalid : ValidHand fixed hand)
    (hdrawn : hand.counts drawn < remainingCapacity fixed drawn) :
    ValidHand fixed (drawHand hand drawn) := by
  refine ⟨hvalid.1, hvalid.2.1, fun tile => ?_⟩
  by_cases htile : tile = drawn
  · subst tile
    have := hvalid.fixed_count_le drawn
    simp only [drawHand, ite_true]
    unfold remainingCapacity at hdrawn
    omega
  · simpa [drawHand, htile] using hvalid.2.2 tile

lemma ValidHand.exchange
    (hvalid : ValidHand fixed hand)
    (hne : discarded ≠ drawn) (hdiscarded : 0 < hand.counts discarded)
    (hdrawn : hand.counts drawn < remainingCapacity fixed drawn) :
    ValidHand fixed (exchangeHand hand discarded drawn) := by
  refine ⟨hvalid.1, hvalid.2.1, fun tile => ?_⟩
  change exchangeCounts hand discarded drawn tile + (fixedTiles fixed).count tile ≤ 4
  by_cases htileDrawn : tile = drawn
  · subst tile
    rw [exchangeCounts_drawn hand discarded drawn hne]
    have := hvalid.fixed_count_le drawn
    unfold remainingCapacity at hdrawn
    omega
  · by_cases htileDiscarded : tile = discarded
    · subst tile
      rw [exchangeCounts_discarded hand discarded drawn hne hdiscarded]
      have := hvalid.2.2 discarded
      omega
    · rw [exchangeCounts_other hand discarded drawn tile htileDiscarded htileDrawn]
      exact hvalid.2.2 tile

end Shanten.Capacity
