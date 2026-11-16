import Shanten.MentsuHand.Scan.Grouping
import Shanten.MentsuHand.Search.BlockSearch

/-!
# Examples

Regression proofs for repeated blocks, missing heads, isolated tiles, and copy limits.
-/

namespace Shanten

private def reviewExampleEast : Tile :=
  .honor ⟨0, by omega⟩

private def reviewExampleMan1 : Tile :=
  .suited .man ⟨0, by omega⟩

private def reviewExampleMan2 : Tile :=
  .suited .man ⟨1, by omega⟩

private def reviewCopyLimitNorth : Tile :=
  .honor ⟨3, by omega⟩

private def reviewCopyLimitHand : Hand :=
  { counts := fun tile =>
      if tile = reviewExampleEast ∨ tile = .honor ⟨1, by omega⟩ ∨
        tile = .honor ⟨2, by omega⟩ then 4
      else if tile = reviewCopyLimitNorth then 1 else 0
    fixedMelds := 0 }

private lemma reviewCopyLimitHand_thirteen : IsThirteenTileHand reviewCopyLimitHand := by
  unfold IsThirteenTileHand ValidCounts
  decide

private lemma reviewCopyLimitHand_fifth_invalid :
    ¬ ValidCounts
      (exchangeHand reviewCopyLimitHand reviewCopyLimitNorth reviewExampleEast) := by
  intro hvalid
  have hcount := hvalid reviewExampleEast
  change exchangeCounts reviewCopyLimitHand reviewCopyLimitNorth
    reviewExampleEast reviewExampleEast ≤ 4 at hcount
  rw [exchangeCounts_drawn _ _ _ (by decide)] at hcount
  change 4 + 1 ≤ 4 at hcount
  omega

example : ¬ HandStep reviewCopyLimitHand
    (exchangeHand reviewCopyLimitHand reviewCopyLimitNorth reviewExampleEast) := by
  intro hstep
  exact reviewCopyLimitHand_fifth_invalid hstep.validCounts

example : ¬ ReachesHand reviewCopyLimitHand
    (exchangeHand reviewCopyLimitHand reviewCopyLimitNorth reviewExampleEast) distance := by
  intro hreach
  exact reviewCopyLimitHand_fifth_invalid
    (hreach.validCounts reviewCopyLimitHand_thirteen.2.2)

example :
    let next := exchangeHand reviewCopyLimitHand reviewExampleEast reviewCopyLimitNorth
    HandStep reviewCopyLimitHand next ∧
      HandStep next (exchangeHand next reviewCopyLimitNorth reviewExampleEast) := by
  dsimp only
  have hstep := exchangeHand_step reviewCopyLimitHand reviewExampleEast
    reviewCopyLimitNorth (by decide) (by decide)
    reviewCopyLimitHand_thirteen.2.2 (by decide)
  exact ⟨hstep, exchangeHand_step _ _ _ (by decide) (by decide)
    hstep.validCounts (by decide)⟩

private def reviewExampleTaatsu : Taatsu :=
  .sequence .man ⟨0, by omega⟩

private def reviewExampleHand : Hand :=
  { counts := countsOfTiles
      (mentsuHandTargetWithTaatsu reviewExampleEast []
          (List.replicate 4 reviewExampleTaatsu) +
        Multiset.replicate 1 (.suited .pin ⟨8, by omega⟩) +
        Multiset.replicate 1 (.suited .sou ⟨8, by omega⟩) +
        Multiset.replicate 1 (.honor ⟨3, by omega⟩))
    fixedMelds := 0 }

private def reviewExampleDecomposition :
    MentsuHandBlockDecomposition reviewExampleHand :=
  { pair := reviewExampleEast
    melds := []
    taatsus := List.replicate 4 reviewExampleTaatsu
    blocks := by simp [reviewExampleHand]
    targetWithinHand := by
      intro tile
      simp [reviewExampleHand, countsOfTiles, mentsuHandTargetWithTaatsu,
        mentsuHandTarget, Multiset.count_add] <;> omega
    completionCopyLimit := by
      intro tile
      cases tile with
      | suited suit rank =>
        cases suit <;> fin_cases rank <;>
          simp [reviewExampleHand, reviewExampleEast, reviewExampleMan1,
            reviewExampleMan2, reviewExampleTaatsu,
            mentsuHandTargetWithTaatsu, mentsuHandTarget, taatsuHistoryTiles,
              taatsuTiles, taatsuCompletionTiles, taatsuCompletionTile,
              pairTiles, meldsTiles] <;> omega
      | honor rank =>
        fin_cases rank <;>
        simp [reviewExampleHand, reviewExampleEast, reviewExampleMan1,
          reviewExampleMan2, reviewExampleTaatsu,
          mentsuHandTargetWithTaatsu, mentsuHandTarget, taatsuHistoryTiles,
          taatsuTiles, taatsuCompletionTiles, taatsuCompletionTile,
          pairTiles, meldsTiles] <;> omega }

example :
    ∃ final,
      AppliesMentsuHandTileBatchScan reviewExampleHand mentsuHandTileOrder
        initialMentsuHandState
        (mentsuHandChoicesGroupedByTiles
          mentsuHandTileOrder reviewExampleDecomposition.blockChoices) final ∧
      final.pair = some reviewExampleEast ∧
      IsMentsuHandBlockSearchComplete reviewExampleHand final :=
  reviewExampleDecomposition.exists_tileBatchScan_complete

/-! Regression cases for hands not covered by the old decomposition premise. -/

private def isolatedMentsuHand : Hand :=
  { counts := fun tile => if tile ∈ kokushiKinds then 1 else 0
    fixedMelds := 0 }

private lemma isolatedMentsuHand_thirteen : IsThirteenTileHand isolatedMentsuHand := by
  refine ⟨rfl, ?_, ?_⟩
  · change (∑ tile : Tile, if tile ∈ kokushiKinds then 1 else 0) = 13
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
    decide
  · intro tile
    change (if tile ∈ kokushiKinds then 1 else 0) ≤ 4
    split <;> omega

example : ¬ Nonempty (MentsuHandBlockDecomposition isolatedMentsuHand) := by
  rintro ⟨decomposition⟩
  have hcount := decomposition.targetWithinHand decomposition.pair
  have hone : isolatedMentsuHand.counts decomposition.pair ≤ 1 := by
    change (if decomposition.pair ∈ kokushiKinds then 1 else 0) ≤ 1
    split <;> omega
  simp only [mentsuHandTargetWithTaatsu, mentsuHandTarget, Multiset.count_add,
    pairTiles, Multiset.count_replicate_self] at hcount
  omega

example :
    ∃! value : Int,
      generalMentsuHandMinimumSearch isolatedMentsuHand = some value ∧
      IsShapeShanten isolatedMentsuHand .mentsuHand value :=
  generalMentsuHandMinimumSearch_exists_unique isolatedMentsuHand
    isolatedMentsuHand_thirteen.2.2 (by
      have hcount := isolatedMentsuHand_thirteen.2.1
      simpa [isolatedMentsuHand] using hcount)

example :
    let head := generalMentsuHandAddBlock isolatedMentsuHand initialGeneralMentsuHandState
      (pairTiles (.suited .man ⟨4, by omega⟩))
    let meld := generalMentsuHandAddBlock isolatedMentsuHand head
      (meldTiles (.sequence .man ⟨3, by omega⟩))
    head.used.card = 0 ∧ head.missing = 2 ∧
      meld.used.card = 0 ∧ meld.missing = 5 := by
  decide

private def missingHeadMentsuHand : Hand :=
  { counts := fun tile => if tile = .honor ⟨0, by omega⟩ then 1 else 0
    fixedMelds := 4 }

set_option maxRecDepth 4096 in
example : generalMentsuHandMinimumSearch missingHeadMentsuHand = some 0 := by
  decide

private def gappedMentsuHand : Hand :=
  { counts := fun tile =>
      if tile = .suited .man ⟨0, by omega⟩ ∨
        tile = .suited .man ⟨2, by omega⟩ then 1 else 0
    fixedMelds := 0 }

example :
    let state := generalMentsuHandAddBlock gappedMentsuHand initialGeneralMentsuHandState
      (meldTiles (.sequence .man ⟨0, by omega⟩))
    state.used.card = 2 ∧ state.missing = 1 := by
  decide

example :
    let first := generalMentsuHandAddBlock gappedMentsuHand initialGeneralMentsuHandState
      (meldTiles (.sequence .man ⟨0, by omega⟩))
    let second := generalMentsuHandAddBlock gappedMentsuHand first
      (meldTiles (.sequence .man ⟨0, by omega⟩))
    second.used.card = 2 ∧ second.missing = 4 := by
  decide

example :
    let first := generalMentsuHandAddBlock missingHeadMentsuHand initialGeneralMentsuHandState
      (pairTiles (.honor ⟨0, by omega⟩))
    let second := generalMentsuHandAddBlock missingHeadMentsuHand first
      (meldTiles (.triplet (.honor ⟨0, by omega⟩)))
    validTileMultisetBool second.completed = false := by
  decide

end Shanten
