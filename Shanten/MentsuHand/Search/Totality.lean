import Shanten.MentsuHand.Search.Correctness
import Mathlib.Tactic.FinCases

/-!
# Search / Totality

Existence, uniqueness, and specification correctness for all valid 13-tile-equivalent hands.
-/

namespace Shanten

open MahjongDomain

private def canonicalMentsuHandPair : Tile :=
  .honor ⟨0, by omega⟩

private def canonicalMentsuHandMelds : Nat → List MentsuCandidate
  | 0 =>
      [ .shuntsu ⟨.man, ⟨0, by omega⟩⟩
      , .shuntsu ⟨.pin, ⟨0, by omega⟩⟩
      , .shuntsu ⟨.sou, ⟨0, by omega⟩⟩
      , .koutsu (.honor ⟨1, by omega⟩) ]
  | 1 =>
      [ .shuntsu ⟨.man, ⟨0, by omega⟩⟩
      , .shuntsu ⟨.pin, ⟨0, by omega⟩⟩
      , .shuntsu ⟨.sou, ⟨0, by omega⟩⟩ ]
  | 2 =>
      [ .shuntsu ⟨.man, ⟨0, by omega⟩⟩
      , .shuntsu ⟨.pin, ⟨0, by omega⟩⟩ ]
  | 3 => [ .shuntsu ⟨.man, ⟨0, by omega⟩⟩ ]
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
            mentsuHandTarget, pairTiles, Pair.tiles, MentsuCandidateList.tiles, MentsuCandidate.tiles,
            Pair.orderedTiles, MentsuCandidate.orderedTiles, Shuntsu.orderedTiles,
            ShuntsuStart.firstRank, ShuntsuStart.middleRank, ShuntsuStart.lastRank]
    | honor rank =>
        fin_cases rank <;>
          simp [canonicalMentsuHandPair, canonicalMentsuHandMelds,
            mentsuHandTarget, pairTiles, Pair.tiles, MentsuCandidateList.tiles, MentsuCandidate.tiles,
            Pair.orderedTiles, MentsuCandidate.orderedTiles, Shuntsu.orderedTiles,
            ShuntsuStart.firstRank, ShuntsuStart.middleRank, ShuntsuStart.lastRank]

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
          (TileCounts.ofMultiset
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
              (TileCounts.ofMultiset (mentsuHandTarget otherPair otherMelds))) →
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
        TileCounts.ofMultiset (mentsuHandTarget decomposition.pair melds) tile) =
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
          (TileCounts.ofMultiset (mentsuHandTarget decomposition.pair melds))) := by
    rw [htarget]
    exact decomposition.validCounts_completedTarget
  exact exists_isShapeShanten_mentsuHand_of_valid_mentsuHandTarget_one_more
    hand hbeforeValid
    ⟨decomposition.pair, melds, hmelds, hsum, hvalid⟩

end Shanten
