import Shanten.SevenPairs.Exchange.Basic
import Shanten.SevenPairs.Counting

/-!
# Seven pairs / Exchange / Pair making

One-step exchanges that turn a singleton into a pair without removing tile kinds.
-/

namespace Shanten

lemma PairMakingExchange.isThirteenTileHand
    (h13 : IsThirteenTileHand before)
    (h : PairMakingExchange before after) :
    IsThirteenTileHand after := by
  rcases h with ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩
  rcases h13 with ⟨hfixed, hcount, hmax⟩
  refine ⟨?_, ?_, ?_⟩
  · change before.fixedMelds = 0
    exact hfixed
  · have hstep := exchangeCounts_step before discarded drawn hne (by
      unfold IsPairPreservingDiscard at hdiscarded
      omega)
    have hfun :
        (fun tile =>
          exchangeCounts before discarded drawn tile +
            (if tile = discarded then 1 else 0)) =
        (fun tile =>
          before.counts tile + (if tile = drawn then 1 else 0)) :=
      funext hstep
    have hsum := congrArg (fun f : TileCounts => ∑ tile, f tile) hfun
    have hsum' :
        (∑ tile, exchangeCounts before discarded drawn tile) + 1 =
          (∑ tile, before.counts tile) + 1 := by
      simpa [Finset.sum_add_distrib, hne, Ne.symm hne] using hsum
    have hsum_eq :
        (∑ tile, exchangeCounts before discarded drawn tile) =
          ∑ tile, before.counts tile := by
      omega
    change (∑ tile, exchangeCounts before discarded drawn tile) = 13
    rw [hsum_eq]
    exact hcount
  · intro tile
    by_cases hdrawn' : tile = drawn
    · subst tile
      change exchangeCounts before discarded drawn drawn ≤ 4
      rw [exchangeCounts_drawn]
      · omega
      · exact hne
    · by_cases hdiscarded' : tile = discarded
      · subst tile
        unfold IsPairPreservingDiscard at hdiscarded
        change exchangeCounts before discarded drawn discarded ≤ 4
        have hbefore := hmax discarded
        rw [exchangeCounts_discarded]
        · omega
        · exact hne
        · omega
      · change exchangeCounts before discarded drawn tile ≤ 4
        rw [exchangeCounts_other]
        · exact hmax tile
        · exact hdiscarded'
        · exact hdrawn'

lemma PairMakingExchange.handStep
    (h : PairMakingExchange before after) (hvalid : ValidCounts before) :
    HandStep before after := by
  rcases h with ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩
  exact exchangeHand_step before discarded drawn hne (by
    unfold IsPairPreservingDiscard at hdiscarded
    omega) hvalid (by omega)

lemma PairMakingExchange.filter_conditions
    (h : PairMakingExchange before after) :
    ∃ discarded drawn,
      before.counts drawn = 1 ∧
        2 ≤ after.counts drawn ∧
        2 ≤ after.counts discarded ∧
        discarded ≠ drawn := by
  rcases h with ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩
  refine ⟨discarded, drawn, hdrawn, ?_, ?_, hne⟩
  · change 2 ≤ exchangeCounts before discarded drawn drawn
    rw [exchangeCounts_drawn]
    · omega
    · exact hne
  · unfold IsPairPreservingDiscard at hdiscarded
    change 2 ≤ exchangeCounts before discarded drawn discarded
    rw [exchangeCounts_discarded]
    · omega
    · exact hne
    · omega

lemma exists_pairMakingExchange
    (hand : Hand) (h13 : IsThirteenTileHand hand)
    (hdistinct : distinctTileCount hand = 7)
    (hpairs : pairCount hand < 6) :
    ∃ next, PairMakingExchange hand next := by
  obtain ⟨drawn, hdrawn⟩ :=
    exists_singleton_kind_of_seven_kinds_lt_six_pairs hand hdistinct hpairs
  obtain ⟨discarded, hdiscarded⟩ :=
    exists_surplus_kind_for_pairMaking hand h13.2.1 hdistinct hpairs
  have hne : discarded ≠ drawn := by
    intro heq
    subst heq
    omega
  refine ⟨exchangeHand hand discarded drawn, ?_⟩
  exact ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩

lemma distinctTileCount_pairMakingExchange
    (h : PairMakingExchange before after) :
    distinctTileCount after = distinctTileCount before := by
  classical
  rcases h with ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩
  unfold distinctTileCount
  apply Eq.symm
  apply card_filter_eq_of_iff
  intro tile
  by_cases hdrawn' : tile = drawn
  · subst tile
    change (0 < before.counts drawn ↔
      0 < exchangeCounts before discarded drawn drawn)
    rw [exchangeCounts_drawn]
    · omega
    · exact hne
  · by_cases hdiscarded' : tile = discarded
    · subst tile
      unfold IsPairPreservingDiscard at hdiscarded
      change (0 < before.counts discarded ↔
        0 < exchangeCounts before discarded drawn discarded)
      rw [exchangeCounts_discarded]
      · omega
      · exact hne
      · omega
    · change (0 < before.counts tile ↔
      0 < exchangeCounts before discarded drawn tile)
      rw [exchangeCounts_other]
      · exact hdiscarded'
      · exact hdrawn'

lemma pairCount_pairMakingExchange
    (h : PairMakingExchange before after) :
    pairCount after = pairCount before + 1 := by
  classical
  rcases h with ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩
  unfold pairCount
  apply card_filter_eq_add_one_of
    (p := fun tile => 2 ≤ before.counts tile)
    (q := fun tile => 2 ≤ (exchangeHand before discarded drawn).counts tile)
    drawn
  · omega
  · change 2 ≤ exchangeCounts before discarded drawn drawn
    rw [exchangeCounts_drawn]
    · omega
    · exact hne
  · intro tile htile
    by_cases hdiscarded' : tile = discarded
    · subst tile
      unfold IsPairPreservingDiscard at hdiscarded
      change (2 ≤ before.counts discarded ↔
        2 ≤ exchangeCounts before discarded drawn discarded)
      rw [exchangeCounts_discarded]
      · omega
      · exact hne
      · omega
    · change (2 ≤ before.counts tile ↔
      2 ≤ exchangeCounts before discarded drawn tile)
      rw [exchangeCounts_other]
      · exact hdiscarded'
      · exact htile

end Shanten
