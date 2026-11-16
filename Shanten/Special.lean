import Shanten.SevenPairs.Completion
import Shanten.SevenPairs.Counting
import Shanten.ThirteenOrphans

/-!
# Computable special-shape formulas

The formulas are realized by optimal completion targets, for both thirteen-
and fourteen-tile concealed hands. No enumeration of seven-kind subsets is needed.
-/

namespace Shanten

private theorem isShapeShanten_of_minimum_deficit
    (hvalid : ValidCounts hand)
    (hsize : tileCount hand = 13 ∨ tileCount hand = 14)
    (happlicable : Applicable shape hand)
    (hcomplete : Complete shape (targetHand hand target))
    (htotal : (∑ tile : Tile, target tile) = 14)
    (hvalue : (countDeficit hand.counts target : Int) = value + 1)
    (hlower : ∀ after, Complete shape after →
      countDeficit hand.counts target ≤ countDeficit hand.counts after.counts) :
    IsShapeShanten hand shape value := by
  have hreach : ReachesCompletion Complete shape hand (countDeficit hand.counts target) := by
    rcases hsize with h13 | h14
    · exact reachesCompletion_of_one_more_target_tile hand target
        (htotal.trans (congrArg (fun n : Nat => n + 1) h13).symm)
        hvalid hcomplete
    · obtain ⟨distance, hdistance, hpath⟩ :=
        reachesHand_targetHand_of_equal_sum hand target
          (h14.trans htotal.symm)
          hvalid hcomplete.validCounts
      rw [← hdistance]
      exact hpath.toReachesCompletion (.done hcomplete)
  refine ⟨happlicable, _, hvalue, hreach, ?_⟩
  intro smaller hsmaller hsmall
  obtain ⟨after, ha, _, hb⟩ := exists_complete_with_deficit_le hsmall
  have := hlower after ha
  omega

lemma sevenPairs_deficit_accounting (hand : Hand) (pairs : Finset Tile) :
    countDeficit hand.counts (sevenPairsCompletionCounts pairs) +
      (pairs.filter fun tile => 0 < hand.counts tile).card +
      (pairs.filter fun tile => 2 ≤ hand.counts tile).card = 2 * pairs.card := by
  have hdeficit : countDeficit hand.counts (sevenPairsCompletionCounts pairs) =
      ∑ tile ∈ pairs, (2 - hand.counts tile) := by
    simp only [countDeficit, sevenPairsCompletionCounts, ite_sub, Nat.zero_sub]
    simp
  rw [hdeficit]
  calc
    _ = ∑ tile ∈ pairs, ((2 - hand.counts tile) +
        (if 0 < hand.counts tile then 1 else 0) +
        (if 2 ≤ hand.counts tile then 1 else 0)) := by
      simp [Finset.sum_add_distrib]
    _ = ∑ _tile ∈ pairs, 2 := by
      apply Finset.sum_congr rfl
      intro tile _
      split <;> split <;> omega
    _ = 2 * pairs.card := by simp [Nat.mul_comm]

private lemma pairCount_le_seven (hsize : tileCount hand ≤ 14) :
    pairCount hand ≤ 7 := by
  have := two_mul_pairCount_le_tileCount hand
  omega

private lemma exists_optimal_sevenPairs_target
    (hpairs : pairCount hand ≤ 7) :
    ∃ pairs : Finset Tile, pairs.card = 7 ∧
      (pairs.filter fun tile => 2 ≤ hand.counts tile).card = pairCount hand ∧
      (pairs.filter fun tile => 0 < hand.counts tile).card =
        min (distinctTileCount hand) 7 := by
  let paired := Finset.univ.filter fun tile => 2 ≤ hand.counts tile
  let present := presentTiles hand
  have hsub : paired ⊆ present := by
    intro tile ht
    simp only [paired, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    simp only [present, presentTiles, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hpcard : paired.card ≤ 7 := hpairs
  by_cases hmany : 7 ≤ present.card
  · obtain ⟨pairs, hpaired, hpresent, hcard⟩ :=
      Finset.exists_subsuperset_card_eq hsub hpcard hmany
    refine ⟨pairs, hcard, ?_, ?_⟩
    · have heq : (pairs.filter fun tile => 2 ≤ hand.counts tile) = paired := by
        ext tile
        simp only [Finset.mem_filter, paired, Finset.mem_univ, true_and]
        exact ⟨And.right, fun ht => ⟨hpaired (by simpa [paired] using ht), ht⟩⟩
      rw [heq]
      rfl
    · have heq : (pairs.filter fun tile => 0 < hand.counts tile) = pairs := by
        apply Finset.filter_eq_self.mpr
        intro tile ht
        simpa [present, presentTiles] using hpresent ht
      rw [heq, hcard]
      exact (Nat.min_eq_right hmany).symm
  · have henough : 7 ≤ (Finset.univ : Finset Tile).card := by decide
    obtain ⟨pairs, hpresent, _, hcard⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.subset_univ present)
        (by omega : present.card ≤ 7) henough
    refine ⟨pairs, hcard, ?_, ?_⟩
    · have heq : (pairs.filter fun tile => 2 ≤ hand.counts tile) = paired := by
        ext tile
        simp only [Finset.mem_filter, paired, Finset.mem_univ, true_and]
        exact ⟨And.right, fun ht =>
          ⟨hpresent (hsub (by simpa [paired] using ht)), ht⟩⟩
      rw [heq]
      rfl
    · have heq : (pairs.filter fun tile => 0 < hand.counts tile) = present := by
        ext tile
        simp only [Finset.mem_filter, present, presentTiles, Finset.mem_univ, true_and]
        exact ⟨And.right, fun ht => ⟨hpresent (by simpa [present, presentTiles] using ht), ht⟩⟩
      rw [heq]
      have hdistinct : distinctTileCount hand ≤ 7 := by
        change present.card ≤ 7
        omega
      exact (Nat.min_eq_left hdistinct).symm

theorem sevenPairsShanten_isShapeShanten
    (hfixed : hand.fixedMelds = 0) (hvalid : ValidCounts hand)
    (hsize : tileCount hand = 13 ∨ tileCount hand = 14) :
    IsShapeShanten hand .sevenPairs (sevenPairsShanten hand) := by
  have hpair := pairCount_le_seven (hand := hand) (by rcases hsize with h | h <;> omega)
  obtain ⟨pairs, hcard, hpairs, hpresent⟩ :=
    exists_optimal_sevenPairs_target hpair
  have haccount := sevenPairs_deficit_accounting hand pairs
  have hcomplete : Complete .sevenPairs
      (targetHand hand (sevenPairsCompletionCounts pairs)) :=
    complete_sevenPairs_of_counts pairs _ hfixed hcard (fun _ => rfl)
  have htotal : (∑ tile : Tile, sevenPairsCompletionCounts pairs tile) = 14 := by
    simp [sevenPairsCompletionCounts, hcard]
  apply isShapeShanten_of_minimum_deficit hvalid hsize
    (show Applicable .sevenPairs hand from hfixed) hcomplete htotal
  · rw [hpairs, hpresent, hcard] at haccount
    unfold sevenPairsShanten
    omega
  · intro after hafter
    obtain ⟨_, _, other, hother, htiles⟩ := hafter
    have hcounts : after.counts = sevenPairsCompletionCounts other := by
      funext tile
      simpa [sevenPairsCompletionCounts, multiset_count_fold_pairTiles] using htiles tile
    rw [hcounts]
    have hotherAccount := sevenPairs_deficit_accounting hand other
    have hbpair : (other.filter fun tile => 2 ≤ hand.counts tile).card ≤
        pairCount hand := by
      apply Finset.card_le_card
      intro tile ht
      simpa [pairCount] using (Finset.mem_filter.mp ht).2
    have hbdistinct : (other.filter fun tile => 0 < hand.counts tile).card ≤
        distinctTileCount hand := by
      apply Finset.card_le_card
      intro tile ht
      simpa [distinctTileCount] using (Finset.mem_filter.mp ht).2
    have hbcard := Finset.card_filter_le (s := other) (p := fun tile => 0 < hand.counts tile)
    rw [hpairs, hpresent, hcard] at haccount
    omega

lemma kokushi_deficit_accounting (hand : Hand) (pair : Tile)
    (hpair : pair ∈ orphanKinds) :
    countDeficit hand.counts
        (countsOfTiles (orphanTiles + Multiset.replicate 1 pair)) +
      kokushiDistinctCount hand + (if 2 ≤ hand.counts pair then 1 else 0) = 14 := by
  have hpair' : pair ∈ kokushiKinds := by rwa [← orphanKinds_eq_kokushiKinds]
  have hpoint : ∀ tile,
      (orphanTiles + Multiset.replicate 1 pair).count tile - hand.counts tile =
        (if tile ∈ kokushiKinds then 1 - hand.counts tile else 0) +
        (if tile = pair then (if 2 ≤ hand.counts pair then 0 else 1) else 0) := by
    intro tile
    rw [Multiset.count_add, orphanTiles_count, orphanKinds_eq_kokushiKinds]
    by_cases heq : tile = pair
    · subst tile
      simp only [hpair', ite_true, Multiset.count_replicate_self]
      split <;> omega
    · simp [heq, ite_sub]
  have hdeficit : countDeficit hand.counts
        (countsOfTiles (orphanTiles + Multiset.replicate 1 pair)) =
      (∑ tile ∈ kokushiKinds, (1 - hand.counts tile)) +
        (if 2 ≤ hand.counts pair then 0 else 1) := by
    simp only [countDeficit, countsOfTiles, hpoint, Finset.sum_add_distrib]
    simp
  have hmissing : (∑ tile ∈ kokushiKinds, (1 - hand.counts tile)) +
      kokushiDistinctCount hand = 13 := by
    calc
      _ = ∑ tile ∈ kokushiKinds,
          ((1 - hand.counts tile) + (if 0 < hand.counts tile then 1 else 0)) := by
        simp [kokushiDistinctCount, Finset.sum_add_distrib]
      _ = ∑ _tile ∈ kokushiKinds, 1 := by
        apply Finset.sum_congr rfl
        intro tile _
        split <;> omega
      _ = 13 := by rw [← orphanKinds_eq_kokushiKinds]; simp [orphanKinds_card]
  rw [hdeficit]
  split <;> omega

theorem kokushiShanten_isShapeShanten
    (hfixed : hand.fixedMelds = 0) (hvalid : ValidCounts hand)
    (hsize : tileCount hand = 13 ∨ tileCount hand = 14) :
    IsShapeShanten hand .thirteenOrphans (kokushiShanten hand) := by
  have hchoose : ∃ pair, pair ∈ orphanKinds ∧
      (if 2 ≤ hand.counts pair then 1 else 0) =
        (if 0 < kokushiPairCount hand then 1 else 0) := by
    by_cases hpair : 0 < kokushiPairCount hand
    · obtain ⟨pair, hp⟩ := Finset.card_pos.mp hpair
      obtain ⟨horphan, hcount⟩ := Finset.mem_filter.mp hp
      exact ⟨pair, by rwa [orphanKinds_eq_kokushiKinds], by simp [hcount, hpair]⟩
    · let pair : Tile := .honor ⟨0, by omega⟩
      have horphan : pair ∈ orphanKinds := by simp [pair, orphanKinds]
      have hcount : ¬ 2 ≤ hand.counts pair := by
        intro hc
        have : 0 < kokushiPairCount hand := Finset.card_pos.mpr
          ⟨pair, Finset.mem_filter.mpr
            ⟨by rwa [← orphanKinds_eq_kokushiKinds], hc⟩⟩
        exact hpair this
      exact ⟨pair, horphan, by simp [hcount, hpair]⟩
  obtain ⟨pair, hpair, hbest⟩ := hchoose
  have hcomplete := complete_thirteenOrphans_targetHand hand pair hfixed hpair
  have htotal : (∑ tile : Tile,
      countsOfTiles (orphanTiles + Multiset.replicate 1 pair) tile) = 14 := by
    rw [countsOfTiles_sum_eq_card, Multiset.card_add, orphanTiles_card]
    simp
  have haccount := kokushi_deficit_accounting hand pair hpair
  apply isShapeShanten_of_minimum_deficit hvalid hsize
    (show Applicable .thirteenOrphans hand from hfixed) hcomplete htotal
  · rw [hbest] at haccount
    unfold kokushiShanten
    split <;> simp_all <;> omega
  · intro after hafter
    obtain ⟨_, _, other, hother, htiles⟩ := hafter
    have hcounts : after.counts =
        countsOfTiles (orphanTiles + Multiset.replicate 1 other) :=
      funext htiles
    rw [hcounts]
    have hotherAccount := kokushi_deficit_accounting hand other hother
    have hle : (if 2 ≤ hand.counts other then 1 else 0) ≤
        (if 0 < kokushiPairCount hand then 1 else 0) := by
      split
      next hc =>
        have hp : 0 < kokushiPairCount hand := Finset.card_pos.mpr
          ⟨other, Finset.mem_filter.mpr
            ⟨by rwa [← orphanKinds_eq_kokushiKinds], hc⟩⟩
        simp [hp]
      next => omega
    rw [hbest] at haccount
    omega

end Shanten
