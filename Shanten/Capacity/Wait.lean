import Shanten.Capacity.Specification

namespace Shanten.Capacity

open MahjongDomain

def IsFixedContextWait (fixed : List FixedMeld) (hand : Hand) (tile : Tile) : Prop :=
  hand.counts tile < remainingCapacity fixed tile ∧
    Complete fixed .mentsuHand (drawHand hand tile)

theorem completeTileCount
    (hcomplete : Complete fixed .mentsuHand hand) :
    tileCount hand = 2 + 3 * (4 - fixed.length) := by
  obtain ⟨hvalid, hshape⟩ := hcomplete
  obtain ⟨_, pair, melds, hlength, htiles⟩ := hshape
  have hcounts : hand.counts = TileCounts.ofMultiset
      (pairTiles pair + MentsuCandidateList.tiles melds) := by
    funext tile
    exact htiles tile
  rw [tileCount, hcounts, TileCounts.ofMultiset_sum_eq_card, Multiset.card_add, pairTiles,
    Pair.tiles_card, MentsuCandidateList.tiles_card]
  have hfixed : hand.fixedMelds = fixed.length := hvalid.1
  have hmelds : melds.length + fixed.length = 4 := by
    rw [← hfixed]
    exact hlength
  have hbound : fixed.length ≤ 4 := hvalid.2.1
  have hmelds' : melds.length = 4 - fixed.length := by omega
  rw [hmelds']

theorem notCompleteAtThirteen
    (h13 : IsThirteenTileEquivalentHand fixed hand) :
    ¬ Complete fixed .mentsuHand hand := by
  intro hcomplete
  have hcount := completeTileCount hcomplete
  have hfixed : fixed.length ≤ 4 := h13.1.2.1
  have hsize := h13.2
  omega

theorem handStepTileCount
    (hstep : Shanten.HandStep before after) :
    tileCount after = tileCount before + 1 ∨ tileCount after = tileCount before := by
  rcases hstep.2 with ⟨drawn, _, hcounts⟩ |
    ⟨discarded, drawn, hne, _, _, hcounts⟩
  · left
    unfold tileCount
    have hcountsEq : after.counts =
        fun tile => before.counts tile + (if tile = drawn then 1 else 0) :=
      funext hcounts
    rw [hcountsEq]
    simp [Finset.sum_add_distrib]
  · right
    unfold tileCount
    have hcountsEq :
        (fun tile => after.counts tile + (if tile = discarded then 1 else 0)) =
        (fun tile => before.counts tile + (if tile = drawn then 1 else 0)) :=
      funext hcounts
    have hsum := congrArg (fun counts : Tile → Nat => ∑ tile, counts tile) hcountsEq
    simp [Finset.sum_add_distrib] at hsum
    exact hsum

theorem isShapeShanten_zero_iff_exists_fixedContextWait
    (h13 : IsThirteenTileEquivalentHand fixed hand) :
    IsShapeShanten fixed hand .mentsuHand 0 ↔
      ∃ tile, IsFixedContextWait fixed hand tile := by
  constructor
  · rintro ⟨_, distance, hdistance, hreach, _⟩
    have hdistance' : distance = 1 := by omega
    subst distance
    obtain ⟨next, hstep, hcomplete⟩ :=
      (reachesCompletion_one_iff (fixed := fixed) (shape := .mentsuHand)
        (hand := hand)).mp hreach
    have hafter : tileCount next = tileCount hand + 1 := by
      have hcount := completeTileCount hcomplete
      have hstepCount := handStepTileCount hstep.toAbstract
      have hsize := h13.2
      have hbound := h13.1.2.1
      omega
    rcases hstep.toAbstract.2 with draw | exchange
    · obtain ⟨tile, _, hcounts⟩ := draw
      have hnext : next = drawHand hand tile := by
        cases next with
      | mk nextBase fixedMelds =>
          cases nextBase with
          | mk nextCounts =>
              cases hand with
              | mk handBase handFixed =>
                  cases handBase with
                  | mk handCounts =>
                      simp only [
                        Shanten.Hand.mk.injEq,
                        MahjongDomain.Hand.mk.injEq,
                        drawHand
                      ]
                      constructor
                      · funext kind
                        exact hcounts kind
                      · exact hstep.toAbstract.1.symm
      subst next
      have hcapacity := hcomplete.1.counts_le_capacity tile
      simp [drawHand] at hcapacity
      have hdrawn : hand.counts tile < remainingCapacity fixed tile := by
        omega
      exact ⟨tile, hdrawn, hcomplete⟩
    · obtain ⟨discarded, drawn, hne, _, _, hcounts⟩ := exchange
      have hsame : tileCount next = tileCount hand := by
        unfold tileCount
        have hcountsEq :
            (fun tile => next.counts tile + (if tile = discarded then 1 else 0)) =
            (fun tile => hand.counts tile + (if tile = drawn then 1 else 0)) :=
          funext hcounts
        have hsum := congrArg
          (fun counts : Tile → Nat => ∑ tile, counts tile) hcountsEq
        simp [Finset.sum_add_distrib] at hsum
        exact hsum
      omega
  · rintro ⟨tile, hwait⟩
    have hstep : HandStep fixed hand (drawHand hand tile) :=
      drawHand_step h13.1 hwait.1
    refine ⟨trivial, 1, by omega,
      (reachesCompletion_one_iff (fixed := fixed) (shape := .mentsuHand)
        (hand := hand)).mpr ⟨drawHand hand tile, hstep, hwait.2⟩, ?_⟩
    intro smaller hsmaller hreach
    have hzero : smaller = 0 := by omega
    subst smaller
    exact notCompleteAtThirteen h13 (reachesCompletion_zero_iff.mp hreach)

end Shanten.Capacity
