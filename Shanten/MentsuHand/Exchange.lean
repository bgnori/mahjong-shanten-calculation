import Shanten.MentsuHand.Targets

/-!
# Exchange

Tile deficits, exchanges, and realization of a fixed completion target.
-/

namespace Shanten

open MahjongDomain

/-- The number of copies of each tile still required by a target. -/
def targetDeficit (hand : Hand) (target : Multiset Tile) : Nat :=
  ∑ tile : Tile, (target.count tile - hand.counts tile)

lemma exists_complete_mentsuHand_with_deficit_le
    (before : Hand) (distance : Nat)
    (hreach : ReachesCompletion Complete .mentsuHand before distance) :
    ∃ after,
      Complete .mentsuHand after ∧
        after.fixedMelds = before.fixedMelds ∧
        countDeficit before.counts after.counts ≤ distance := by
  exact exists_complete_with_deficit_le hreach

lemma complete_mentsuHand_targetHand
    (before : Hand) (target : TileCounts)
    (pair : Tile) (melds : List MentsuCandidate)
    (hvalid : ValidCounts (targetHand before target))
    (hmelds : melds.length + before.fixedMelds = 4)
    (htiles :
      HasTiles (targetHand before target)
        (pairTiles pair + meldsTiles melds)) :
    Complete .mentsuHand (targetHand before target) := by
  exact ⟨hvalid, pair, melds, hmelds, htiles⟩

lemma reachesCompletion_mentsuHand_of_equal_sum
    (before : Hand) (target : TileCounts)
    (pair : Tile) (melds : List MentsuCandidate)
    (hsum : (∑ tile : Tile, before.counts tile) =
      ∑ tile : Tile, target tile)
    (hvalid : ValidCounts (targetHand before target))
    (hmelds : melds.length + before.fixedMelds = 4)
    (htiles :
      HasTiles (targetHand before target)
        (pairTiles pair + meldsTiles melds))
    (hbeforeValid : ValidCounts before) :
    ReachesCompletion Complete .mentsuHand before
      (countDeficit before.counts target) := by
  obtain ⟨distance, hdistance, hexchange⟩ :=
    reachesHand_targetHand_of_equal_sum before target hsum hbeforeValid hvalid
  have hcomplete :
      Complete .mentsuHand (targetHand before target) :=
    complete_mentsuHand_targetHand before target pair melds
      hvalid hmelds htiles
  have hdone :
      ReachesCompletion Complete .mentsuHand
        (targetHand before target) 0 :=
    ReachesCompletion.done hcomplete
  simpa only [Nat.add_zero, hdistance] using
    ReachesHand.toReachesCompletion hexchange hdone

lemma reachesCompletion_mentsuHand_of_one_more_target_tile
    (before : Hand) (target : TileCounts)
    (pair : Tile) (melds : List MentsuCandidate)
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
  exact ⟨_, rfl, reachesCompletion_of_one_more_target_tile before target hsum
    hbeforeValid (complete_mentsuHand_targetHand before target pair melds
      hvalid hmelds htiles)⟩

end Shanten
