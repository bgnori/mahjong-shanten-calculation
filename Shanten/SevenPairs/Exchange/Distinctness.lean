import Shanten.SevenPairs.Exchange.Basic
import Shanten.SevenPairs.Counting

/-!
# Seven pairs / Exchange / Distinctness

One-step exchanges that add a tile kind while preserving every existing pair.
-/

namespace Shanten

open MahjongDomain

lemma DistinctnessExchange.isThirteenTileHand
    (h13 : IsThirteenTileHand before)
    (h : DistinctnessExchange before after) :
    IsThirteenTileHand after := by
  rcases h with ⟨discarded, drawn, hdiscarded, hdrawn, hne, rfl⟩
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
      unfold IsAbsentTileKind at hdrawn
      change exchangeCounts before discarded drawn drawn ≤ 4
      rw [exchangeCounts_drawn]
      · omega
      · exact hne
    · by_cases hdiscarded' : tile = discarded
      · subst tile
        unfold IsPairPreservingDiscard at hdiscarded
        change exchangeCounts before discarded drawn discarded ≤ 4
        have hbefore := hmax discarded
        change before.counts discarded ≤ 4 at hbefore
        rw [exchangeCounts_discarded]
        · omega
        · exact hne
        · omega
      · change exchangeCounts before discarded drawn tile ≤ 4
        rw [exchangeCounts_other]
        · exact hmax tile
        · exact hdiscarded'
        · exact hdrawn'

lemma exists_distinctnessExchange
    (hand : Hand) (h13 : IsThirteenTileHand hand)
    (hdistinct : distinctTileCount hand < 7) :
    ∃ next, DistinctnessExchange hand next := by
  obtain ⟨discarded, hdiscarded⟩ :=
    exists_surplus_tile_kind hand h13.2.1 hdistinct
  obtain ⟨drawn, hdrawn⟩ := exists_missing_tile_kind hand hdistinct
  have hne : discarded ≠ drawn := by
    intro heq
    subst heq
    omega
  refine ⟨exchangeHand hand discarded drawn, ?_⟩
  exact ⟨discarded, drawn, hdiscarded, hdrawn, hne, rfl⟩

lemma DistinctnessExchange.handStep
    (h : DistinctnessExchange before after) (hvalid : ValidCounts before) :
    HandStep before after := by
  rcases h with ⟨discarded, drawn, hdiscarded, hdrawn, hne, rfl⟩
  exact exchangeHand_step before discarded drawn hne (by
    unfold IsPairPreservingDiscard at hdiscarded
    omega) hvalid (by unfold IsAbsentTileKind at hdrawn; omega)

lemma DistinctnessExchange.filter_conditions
    (h : DistinctnessExchange before after) :
    ∃ discarded drawn,
      before.counts drawn = 0 ∧
        0 < after.counts drawn ∧
        2 ≤ after.counts discarded ∧
        discarded ≠ drawn := by
  rcases h with ⟨discarded, drawn, hdiscarded, hdrawn, hne, rfl⟩
  refine ⟨discarded, drawn, ?_, ?_, ?_, hne⟩
  · exact hdrawn
  · unfold IsAbsentTileKind at hdrawn
    change 0 < exchangeCounts before discarded drawn drawn
    rw [exchangeCounts_drawn]
    · omega
    · exact hne
  · unfold IsPairPreservingDiscard at hdiscarded
    change 2 ≤ exchangeCounts before discarded drawn discarded
    rw [exchangeCounts_discarded]
    · omega
    · exact hne
    · omega

lemma distinctTileCount_distinctnessExchange
    (h : DistinctnessExchange before after) :
    distinctTileCount after = distinctTileCount before + 1 := by
  classical
  rcases h with ⟨discarded, drawn, hdiscarded, hdrawn, hne, rfl⟩
  unfold distinctTileCount
  apply card_filter_eq_add_one_of
    (p := fun tile => 0 < before.counts tile)
    (q := fun tile => 0 < (exchangeHand before discarded drawn).counts tile)
    drawn
  · unfold IsAbsentTileKind at hdrawn
    simp [hdrawn]
  · change 0 < exchangeCounts before discarded drawn drawn
    rw [exchangeCounts_drawn]
    · omega
    · exact hne
  · intro tile htile
    by_cases hdiscard : tile = discarded
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
      · exact hdiscard
      · exact htile

lemma pairCount_distinctnessExchange
    (h : DistinctnessExchange before after) :
    pairCount after = pairCount before := by
  classical
  rcases h with ⟨discarded, drawn, hdiscarded, hdrawn, hne, rfl⟩
  unfold pairCount
  apply Eq.symm
  apply card_filter_eq_of_iff
  intro tile
  by_cases hdrawn' : tile = drawn
  · subst tile
    unfold IsAbsentTileKind at hdrawn
    change (2 ≤ before.counts drawn ↔
      2 ≤ exchangeCounts before discarded drawn drawn)
    rw [exchangeCounts_drawn]
    · omega
    · exact hne
  · by_cases hdiscarded' : tile = discarded
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
      · exact hdrawn'

end Shanten
