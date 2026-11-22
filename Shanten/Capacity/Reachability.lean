import Shanten.Capacity.Specification

namespace Shanten.Capacity

open MahjongDomain

lemma handStep_of_targetExchange
    (hstep : Shanten.TargetExchange target before after)
    (hvalid : ValidHand fixed before)
    (htarget : ∀ tile, target tile + (fixedTiles fixed).count tile ≤ 4) :
    HandStep fixed before after := by
  obtain ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩ := hstep
  apply exchangeHand_step hvalid hne (by omega)
  have := htarget drawn
  change target drawn + (fixedTiles fixed).count drawn ≤ copiesPerTile at this
  unfold remainingCapacity
  omega

lemma reachesHand_of_targetExchanges
    (hreach : Shanten.ReachesTargetExchange target before after distance)
    (hvalid : ValidHand fixed before)
    (htarget : ∀ tile, target tile + (fixedTiles fixed).count tile ≤ 4) :
    ReachesHand fixed before after distance := by
  induction hreach with
  | done => exact .done hvalid
  | step hstep _ ih =>
      have hlegal := handStep_of_targetExchange hstep hvalid htarget
      exact .step hlegal (ih hlegal.validHand)

lemma reachesHand_targetHand_of_equal_sum
    (hsum : (∑ tile : Tile, before.counts tile) = ∑ tile : Tile, target tile)
    (hvalid : ValidHand fixed before)
    (htarget : ∀ tile, target tile + (fixedTiles fixed).count tile ≤ 4) :
    ReachesHand fixed before (targetHand before target)
      (countDeficit before.counts target) := by
  obtain ⟨distance, hdistance, hreach⟩ :=
    Shanten.reachesTargetExchange_targetHand_of_equal_sum before target hsum
  rw [← hdistance]
  exact reachesHand_of_targetExchanges hreach hvalid htarget

lemma ReachesHand.deficit_le (hreach : ReachesHand fixed before after distance) :
    countDeficit before.counts after.counts ≤ distance := by
  induction hreach with
  | done _ => simp [countDeficit]
  | @step before next after distance hstep _ ih =>
      have := countDeficit_handStep_le before next after.counts hstep.toAbstract
      omega

/-- A capacity-valid target with one extra tile is reachable at its exact deficit. -/
lemma reachesCompletion_of_one_more_target_tile
    (hsum : (∑ tile : Tile, target tile) =
      (∑ tile : Tile, before.counts tile) + 1)
    (hvalid : ValidHand fixed before)
    (hcomplete : Complete fixed shape (targetHand before target)) :
    ReachesCompletion fixed shape before (countDeficit before.counts target) := by
  have hdrawnExists : ∃ drawn, before.counts drawn < target drawn := by
    by_contra hnone
    push Not at hnone
    have := Finset.sum_le_sum (s := Finset.univ) (fun tile _ => hnone tile)
    omega
  obtain ⟨drawn, hdrawn⟩ := hdrawnExists
  have hspace : before.counts drawn < remainingCapacity fixed drawn := by
    have := hcomplete.1.counts_le_capacity drawn
    exact lt_of_lt_of_le hdrawn this
  let next := drawHand before drawn
  have hstep : HandStep fixed before next := drawHand_step hvalid hspace
  have hsumNext : (∑ tile : Tile, next.counts tile) = ∑ tile : Tile, target tile := by
    simpa [next, drawHand, Finset.sum_add_distrib] using hsum.symm
  have hrest := reachesHand_targetHand_of_equal_sum hsumNext hstep.validHand
    (show ∀ tile, target tile + (fixedTiles fixed).count tile ≤ 4 from hcomplete.1.2.2)
  have hdeficit : countDeficit next.counts target + 1 =
      countDeficit before.counts target :=
    countDeficit_draw before target drawn hdrawn
  refine ⟨targetHand before target, ?_, hcomplete⟩
  rw [← hdeficit]
  exact .step hstep hrest

end Shanten.Capacity
