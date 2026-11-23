module

public import Shanten.MentsuHand.Search.TargetDP

@[expose] public section

/-!
# Search / Minimum

Minimum target distances and lower bounds on completion paths.
-/

namespace Shanten

open MahjongDomain

def validMentsuHandTargetDistances (hand : Hand) :
    Finset Nat :=
  (recursiveMentsuHandTargetCostStatesDP hand).image Prod.snd

lemma mentsuHandTargetCostDistances_eq_tileDistances
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4) :
    validMentsuHandTargetDistances hand =
      (mentsuHandTargetTileStatesDP hand.fixedMelds).image
        (fun tiles => countDeficit hand.counts (TileCounts.ofMultiset tiles)) := by
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
            (TileCounts.ofMultiset (mentsuHandTarget pair melds))) ∧
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
            (TileCounts.ofMultiset (mentsuHandTarget pair melds)))) :
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
            (TileCounts.ofMultiset (mentsuHandTarget pair melds))) ∧
        mentsuHandTargetDistance before pair melds ≤ distance := by
  obtain ⟨after, hcomplete, hfixed, hdeficit⟩ :=
    exists_complete_mentsuHand_with_deficit_le before distance hreach
  rcases hcomplete with ⟨hvalidAfter, pair, melds, hmelds, htiles⟩
  have hcounts :
      after.counts =
        TileCounts.ofMultiset (mentsuHandTarget pair melds) := by
    funext tile
    change after.counts tile =
      (mentsuHandTarget pair melds).count tile
    exact htiles tile
  have hvalidTarget :
      ValidCounts
        (targetHand before
          (TileCounts.ofMultiset (mentsuHandTarget pair melds))) := by
    intro tile
    change (TileCounts.ofMultiset (mentsuHandTarget pair melds)) tile ≤ 4
    rw [← hcounts]
    exact hvalidAfter tile
  refine ⟨pair, melds, ?_, hvalidTarget, ?_⟩
  · rw [← hfixed]
    exact hmelds
  · rw [mentsuHandTargetDistance_eq_countDeficit]
    simpa [hcounts] using hdeficit

lemma no_shorter_mentsuHand_completion_of_minimal_mentsuHandTargetDistance
    (before : Hand) (pair : Tile) (melds : List MentsuCandidate)
    (distance : Nat)
    (hdistance : mentsuHandTargetDistance before pair melds = distance)
    (hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (TileCounts.ofMultiset (mentsuHandTarget otherPair otherMelds))) →
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

end Shanten
