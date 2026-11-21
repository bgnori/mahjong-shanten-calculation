import Shanten.MentsuHand.Search.Reachability

/-!
# Search / Correctness

Characterizing mathematical shanten by minimal valid target distance.
-/

namespace Shanten

open MahjongDomain

lemma isShapeShanten_mentsuHand_of_minimal_mentsuHandTargetDistance
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List MentsuCandidate)
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
            mentsuHandTargetDistance before otherPair otherMelds)
    (hbeforeValid : ValidCounts before) :
    IsShapeShanten before .mentsuHand ((distance : Int) - 1) := by
  apply isShapeShanten_mentsuHand_of_mentsuHandTarget_distance
    distance before pair melds hdistance hsum hvalid hmelds
  · exact no_shorter_mentsuHand_completion_of_minimal_mentsuHandTargetDistance
      before pair melds distance hdistance hminimalTarget
  · exact hbeforeValid

lemma isShapeShanten_mentsuHand_of_minimal_mentsuHandTargetDistance_one_more
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List MentsuCandidate)
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
    (before : Hand) (hbeforeValid : ValidCounts before)
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
      distance before pair melds hdistance hsum hvalid hmelds hminimalTarget hbeforeValid
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
    (pair : Tile) (melds : List MentsuCandidate)
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

end Shanten
