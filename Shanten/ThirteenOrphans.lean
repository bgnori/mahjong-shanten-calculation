import Shanten.Exchange
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FinCases

/-!
# Thirteen orphans

Every valid thirteen-tile hand can complete in at most fourteen steps.
A hand containing only middle tiles needs all fourteen steps, so the maximum
shape-specific shanten number is thirteen.
-/

namespace Shanten

lemma orphanKinds_eq_kokushiKinds : orphanKinds = kokushiKinds := by
  ext tile
  cases tile with
  | suited suit rank =>
      cases suit <;> fin_cases rank <;> simp [orphanKinds, kokushiKinds]
  | honor rank =>
      fin_cases rank <;> simp [orphanKinds, kokushiKinds]

lemma orphanKinds_card : orphanKinds.card = 13 := by
  rw [orphanKinds_eq_kokushiKinds]
  decide

lemma orphanTiles_count (tile : Tile) :
    orphanTiles.count tile = if tile ∈ orphanKinds then 1 else 0 := by
  simpa [orphanTiles] using
    (Multiset.count_eq_of_nodup (a := tile) orphanKinds.nodup)

lemma orphanTiles_card : orphanTiles.card = 13 := by
  simpa [orphanTiles] using orphanKinds_card

lemma thirteenOrphans_completion_tileCount
    (hcomplete : Complete .thirteenOrphans hand) :
    tileCount hand = 14 := by
  obtain ⟨_, _, pair, _, hcounts⟩ := hcomplete
  unfold HasTiles at hcounts
  change (∑ tile : Tile, hand.counts tile) = 14
  simp_rw [hcounts]
  change (∑ tile : Tile,
    countsOfTiles (orphanTiles + Multiset.replicate 1 pair) tile) = 14
  rw [countsOfTiles_sum_eq_card, Multiset.card_add, orphanTiles_card]
  simp

lemma complete_thirteenOrphans_targetHand
    (hand : Hand) (pair : Tile)
    (hfixed : hand.fixedMelds = 0) (hpair : pair ∈ orphanKinds) :
    Complete .thirteenOrphans
      (targetHand hand (countsOfTiles
        (orphanTiles + Multiset.replicate 1 pair))) := by
  refine ⟨?_, hfixed, pair, hpair, ?_⟩
  · intro tile
    change (orphanTiles + Multiset.replicate 1 pair).count tile ≤ 4
    rw [Multiset.count_add, orphanTiles_count]
    by_cases horphan : tile ∈ orphanKinds <;>
      by_cases htile : tile = pair <;>
      simp [horphan, htile, hpair]
  · exact targetHand_hasTiles_countsOfTiles hand _

lemma reaches_thirteenOrphans_completion
    (hand : Hand) (h13 : IsThirteenTileHand hand) :
    ∃ distance : Nat, distance ≤ 14 ∧
      ReachesCompletion Complete .thirteenOrphans hand distance := by
  let pair : Tile := .honor ⟨0, by omega⟩
  let target := countsOfTiles (orphanTiles + Multiset.replicate 1 pair)
  have hpair : pair ∈ orphanKinds := by
    simp only [orphanKinds, Finset.mem_filter, Finset.mem_univ, true_and]
    trivial
  have hcomplete := complete_thirteenOrphans_targetHand hand pair h13.1 hpair
  have htargetCount : (∑ tile : Tile, target tile) = 14 := by
    change tileCount (targetHand hand target) = 14
    exact thirteenOrphans_completion_tileCount hcomplete
  have hsum : (∑ tile : Tile, target tile) =
      (∑ tile : Tile, hand.counts tile) + 1 := by
    have := h13.2.1
    change (∑ tile : Tile, hand.counts tile) = 13 at this
    omega
  refine ⟨countDeficit hand.counts target, ?_,
    reachesCompletion_of_one_more_target_tile hand target hsum h13.2.2 hcomplete⟩
  exact (Finset.sum_le_sum (s := Finset.univ)
    (fun tile _ => Nat.sub_le (target tile) (hand.counts tile))).trans
      htargetCount.le

/-- The specification's shanten value, not just the closed form, is at most 13. -/
theorem thirteenOrphansShanten_le_thirteen
    (h13 : IsThirteenTileHand hand)
    (hvalue : IsShapeShanten hand .thirteenOrphans value) :
    value ≤ 13 := by
  obtain ⟨bound, hbound, hreach⟩ := reaches_thirteenOrphans_completion hand h13
  obtain ⟨_, distance, hvalue, _, hminimal⟩ := hvalue
  have : distance ≤ bound := by
    by_contra h
    exact hminimal bound (by omega) hreach
  omega

theorem thirteenOrphansShanten_exists
    (h13 : IsThirteenTileHand hand) :
    ∃ value : Int, IsShapeShanten hand .thirteenOrphans value ∧ value ≤ 13 := by
  classical
  obtain ⟨bound, _, hreach⟩ := reaches_thirteenOrphans_completion hand h13
  have hexists : ∃ distance, ReachesCompletion Complete .thirteenOrphans hand distance :=
    ⟨bound, hreach⟩
  have hvalue : IsShapeShanten hand .thirteenOrphans ((Nat.find hexists : Int) - 1) :=
    ⟨h13.1, Nat.find hexists, by omega, Nat.find_spec hexists,
      fun smaller hsmaller => Nat.find_min hexists hsmaller⟩
  exact ⟨_, hvalue, thirteenOrphansShanten_le_thirteen h13 hvalue⟩

lemma kokushiWorstCase_isThirteenTileHand : IsThirteenTileHand kokushiWorstCase := by
  refine ⟨rfl, ?_, ?_⟩
  · decide
  · intro tile
    change (if tile ∈ _ then 1 else 0) ≤ 4
    split <;> omega

lemma kokushiWorstCase_no_orphans :
    ∀ tile ∈ orphanKinds, kokushiWorstCase.counts tile = 0 := by
  rw [orphanKinds_eq_kokushiKinds]
  decide

lemma kokushiWorstCase_completion_distance_ge_fourteen
    (hreach : ReachesCompletion Complete .thirteenOrphans kokushiWorstCase distance) :
    14 ≤ distance := by
  obtain ⟨after, hcomplete, _, hbound⟩ := exists_complete_with_deficit_le hreach
  have hcount := thirteenOrphans_completion_tileCount hcomplete
  obtain ⟨_, _, pair, hpair, htiles⟩ := hcomplete
  have hdeficit : countDeficit kokushiWorstCase.counts after.counts = 14 := by
    calc
      countDeficit kokushiWorstCase.counts after.counts = tileCount after := by
        apply Finset.sum_congr rfl
        intro tile _
        by_cases horphan : tile ∈ orphanKinds
        · rw [kokushiWorstCase_no_orphans tile horphan, Nat.sub_zero]
        · have hne : tile ≠ pair := by
            intro heq
            exact horphan (heq ▸ hpair)
          have hzero : after.counts tile = 0 := by
            rw [htiles, Multiset.count_add, orphanTiles_count]
            simp [horphan, hne]
          simp [hzero]
      _ = 14 := hcount
  omega

/-- The valid middle-tile example attains the upper bound in the specification. -/
theorem kokushiWorstCase_isShapeShanten :
    IsShapeShanten kokushiWorstCase .thirteenOrphans 13 := by
  obtain ⟨distance, hbound, hreach⟩ :=
    reaches_thirteenOrphans_completion kokushiWorstCase
      kokushiWorstCase_isThirteenTileHand
  have hlower := kokushiWorstCase_completion_distance_ge_fourteen hreach
  have hdistance : distance = 14 := by omega
  refine ⟨rfl, distance, by omega, hreach, ?_⟩
  intro smaller hsmaller hsmall
  have := kokushiWorstCase_completion_distance_ge_fourteen hsmall
  omega

theorem kokushiWorstCase_shapeShanten :
    ShapeShanten kokushiWorstCase .thirteenOrphans = some 13 :=
  shapeShanten_eq_some_iff.mpr kokushiWorstCase_isShapeShanten

/-- Thirteen is an attained maximum on valid concealed thirteen-tile hands. -/
theorem thirteenOrphansShanten_maximum :
    (∀ hand value, IsThirteenTileHand hand →
      IsShapeShanten hand .thirteenOrphans value → value ≤ 13) ∧
    (∃ hand, IsThirteenTileHand hand ∧
      IsShapeShanten hand .thirteenOrphans 13) :=
  ⟨fun _ _ h13 hvalue => thirteenOrphansShanten_le_thirteen h13 hvalue,
    kokushiWorstCase, kokushiWorstCase_isThirteenTileHand,
    kokushiWorstCase_isShapeShanten⟩

end Shanten
