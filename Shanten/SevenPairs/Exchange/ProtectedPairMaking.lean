import Shanten.SevenPairs.Exchange.Basic
import Shanten.SevenPairs.Counting

/-!
# Seven pairs / Exchange / Protected pair making

Choosing seven protected kinds and making pairs while maintaining their invariants.
-/

namespace Shanten

open MahjongDomain

/-- Every protected pair-making exchange from valid counts is an ordinary hand step. -/
lemma ProtectedPairMakingExchange.handStep
        (h : ProtectedPairMakingExchange protectedTiles before after)
        (hvalid : ValidCounts before) :
        HandStep before after := by
  rcases h with ⟨discarded, drawn, hprotected, hdrawn, hdiscarded, hne, rfl⟩
  refine exchangeHand_step before discarded drawn hne ?_ hvalid (by omega)
  rcases hdiscarded with hsurplus | ⟨hsingleton, _⟩
  · omega
  · omega

lemma ProtectedPairMakingExchange.isThirteenTileHand
    (h13 : IsThirteenTileHand before)
    (h : ProtectedPairMakingExchange protectedTiles before after) :
    IsThirteenTileHand after := by
  rcases h with
    ⟨discarded, drawn, hprotected, hdrawn, hdiscarded, hne, rfl⟩
  rcases h13 with ⟨hfixed, hcount, hmax⟩
  have hpositive : before.counts discarded > 0 := by
    rcases hdiscarded with hsurplus | ⟨hsingleton, _⟩
    · omega
    · omega
  refine ⟨?_, ?_, ?_⟩
  · change before.fixedMelds = 0
    exact hfixed
  · have hstep :=
      exchangeCounts_step before discarded drawn hne hpositive
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
        change exchangeCounts before discarded drawn discarded ≤ 4
        rcases hdiscarded with hsurplus | ⟨hsingleton, _⟩
        · have hbefore := hmax discarded
          rw [exchangeCounts_discarded before discarded drawn hne hpositive]
          omega
        · rw [exchangeCounts_discarded before discarded drawn hne hpositive]
          omega
      · change exchangeCounts before discarded drawn tile ≤ 4
        rw [exchangeCounts_other before discarded drawn tile hdiscarded' hdrawn']
        exact hmax tile

lemma pairCount_protectedPairMakingExchange
    (h : ProtectedPairMakingExchange protectedTiles before after) :
    pairCount after = pairCount before + 1 := by
  classical
  rcases h with ⟨discarded, drawn, hprotected, hdrawn, hdiscarded, hne, rfl⟩
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
      change (2 ≤ before.counts discarded ↔
      2 ≤ exchangeCounts before discarded drawn discarded)
      rw [exchangeCounts_discarded]
      · rcases hdiscarded with hsurplus | ⟨hsingleton, _⟩
        · constructor <;> omega
        · constructor <;> omega
      · exact hne
      · rcases hdiscarded with hsurplus | ⟨hsingleton, _⟩
        · omega
        · omega
    · change (2 ≤ before.counts tile ↔
      2 ≤ exchangeCounts before discarded drawn tile)
      rw [exchangeCounts_other]
      · exact hdiscarded'
      · exact htile

lemma protectedTiles_positive_after_protectedPairMakingExchange
    (hpositive : ∀ tile, tile ∈ protectedTiles → 0 < before.counts tile)
    (h : ProtectedPairMakingExchange protectedTiles before after) :
    ∀ tile, tile ∈ protectedTiles → 0 < after.counts tile := by
  intro tile htile
  rcases h with ⟨discarded, drawn, hdrawn, hdrawnCount,
    hdiscarded, hne, rfl⟩
  by_cases htileDrawn : tile = drawn
  · subst tile
    change 0 < exchangeCounts before discarded drawn drawn
    rw [exchangeCounts_drawn]
    · omega
    · exact hne
  by_cases htileDiscarded : tile = discarded
  · subst tile
    change 0 < exchangeCounts before discarded drawn discarded
    rw [exchangeCounts_discarded]
    · rcases hdiscarded with hsurplus | ⟨hsingleton, _⟩
      · omega
      · exact False.elim (‹discarded ∉ protectedTiles› htile)
    · exact hne
    · exact hpositive discarded (by assumption)
  · change 0 < exchangeCounts before discarded drawn tile
    rw [exchangeCounts_other]
    · exact hpositive tile htile
    · exact htileDiscarded
    · exact htileDrawn

/-- Invariants used while a fixed set of seven kinds is used for pairing. -/
def ProtectedPairingInvariant
    (protectedTiles : Finset Tile) (hand : Hand) : Prop :=
  (∀ tile, tile ∈ protectedTiles → 0 < hand.counts tile) ∧
    (∀ tile, 2 ≤ hand.counts tile → tile ∈ protectedTiles)

lemma exists_protectedTiles
    (hand : Hand) (hdistinct : 7 ≤ distinctTileCount hand)
    (hpairs : pairCount hand < 6) :
    ∃ protectedTiles : Finset Tile,
      protectedTiles.card = 7 ∧
        ProtectedPairingInvariant protectedTiles hand := by
  classical
  let pairs : Finset Tile :=
    Finset.univ.filter (fun tile => 2 ≤ hand.counts tile)
  let present : Finset Tile :=
    Finset.univ.filter (fun tile => 0 < hand.counts tile)
  have hpairsCard : pairs.card = pairCount hand := by
    rfl
  have hpresentCard : present.card = distinctTileCount hand := by
    rfl
  have hpairsSubset : pairs ⊆ present := by
    intro tile htile
    simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at htile
    simp only [present, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hdiffCard :
      (present \ pairs).card = present.card - pairs.card := by
    exact Finset.card_sdiff_of_subset hpairsSubset
  have hextraCard : 7 - pairs.card ≤ (present \ pairs).card := by
    rw [hdiffCard, hpresentCard, hpairsCard]
    omega
  obtain ⟨extra, hextraSubset, hextra⟩ :=
    Finset.exists_subset_card_eq hextraCard
  let protectedTiles := pairs ∪ extra
  have hdisjoint : Disjoint pairs extra := by
    rw [Finset.disjoint_left]
    intro tile hpair hextra'
    have hdiff' : tile ∈ present \ pairs :=
      hextraSubset hextra'
    exact (Finset.mem_sdiff.mp hdiff').2 hpair
  have hprotectedCard : protectedTiles.card = 7 := by
    change (pairs ∪ extra).card = 7
    rw [Finset.card_union_of_disjoint hdisjoint]
    rw [hextra, hpairsCard]
    omega
  refine ⟨protectedTiles, hprotectedCard, ?_⟩
  constructor
  · intro tile htile
    rcases Finset.mem_union.mp (show tile ∈ pairs ∪ extra from htile) with
      hpair | hextra'
    · simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hpair
      omega
    · have hdiff' : tile ∈ present \ pairs :=
        hextraSubset hextra'
      have hpresent' := (Finset.mem_sdiff.mp hdiff').1
      simp only [present, Finset.mem_filter, Finset.mem_univ, true_and] at hpresent'
      exact hpresent'
  · intro tile htile
    apply Finset.mem_union_left
    simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact htile

lemma protectedPairingInvariant_after_protectedPairMakingExchange
    (hprotected : ProtectedPairingInvariant protectedTiles before)
    (h : ProtectedPairMakingExchange protectedTiles before after) :
    ProtectedPairingInvariant protectedTiles after := by
  constructor
  · exact protectedTiles_positive_after_protectedPairMakingExchange
      hprotected.1 h
  · intro tile hpair
    rcases h with ⟨discarded, drawn, hdrawn, hdrawnCount,
      hdiscarded, hne, rfl⟩
    by_cases htileDrawn : tile = drawn
    · subst tile
      exact hdrawn
    · by_cases htileDiscarded : tile = discarded
      · subst tile
        rcases hdiscarded with hsurplus | ⟨hsingleton, houtside⟩
        · exact hprotected.2 discarded (by omega)
        · have hpair' : 2 ≤ exchangeCounts before discarded drawn discarded := hpair
          rw [exchangeCounts_discarded] at hpair'
          · omega
          · exact hne
          · omega
      · have hunchanged :
          exchangeCounts before discarded drawn tile = before.counts tile := by
          exact exchangeCounts_other before discarded drawn tile
            htileDiscarded htileDrawn
        have hbefore : 2 ≤ before.counts tile := by
          rw [← hunchanged]
          exact hpair
        exact hprotected.2 tile hbefore

lemma exists_protectedPairMakingExchange
    (protectedTiles : Finset Tile) (hand : Hand)
    (h13 : IsThirteenTileHand hand)
    (hcard : protectedTiles.card = 7)
    (hprotected : ProtectedPairingInvariant protectedTiles hand)
    (hpairs : pairCount hand < 6) :
    ∃ next,
      ProtectedPairMakingExchange protectedTiles hand next ∧
        ProtectedPairingInvariant protectedTiles next := by
  classical
  have hdrawn : ∃ drawn, drawn ∈ protectedTiles ∧ hand.counts drawn = 1 := by
    by_contra hnone
    push Not at hnone
    have hpairSubset : protectedTiles ⊆
        Finset.univ.filter (fun tile => 2 ≤ hand.counts tile) := by
      intro tile htile
      have hpositive := hprotected.1 tile htile
      have hnot := hnone tile htile
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hcardle :
        protectedTiles.card ≤
          (Finset.univ.filter (fun tile => 2 ≤ hand.counts tile)).card :=
      Finset.card_le_card hpairSubset
    have : 7 ≤ pairCount hand := by
      rw [hcard] at hcardle
      exact hcardle
    omega
  obtain ⟨drawn, hdrawnProtected, hdrawnCount⟩ := hdrawn
  by_cases hsurplus : ∃ discarded, 3 ≤ hand.counts discarded
  · obtain ⟨discarded, hdiscarded⟩ := hsurplus
    have hne : discarded ≠ drawn := by
      intro heq
      subst heq
      omega
    let next := exchangeHand hand discarded drawn
    have hstep : ProtectedPairMakingExchange protectedTiles hand next := by
      exact ⟨discarded, drawn, hdrawnProtected, hdrawnCount,
        Or.inl hdiscarded, hne, rfl⟩
    exact ⟨next, hstep,
      protectedPairingInvariant_after_protectedPairMakingExchange
        hprotected hstep⟩
  · push Not at hsurplus
    have hsmall : ∀ tile, hand.counts tile ≤ 2 := by
      intro tile
      have hnot := hsurplus tile
      omega
    have hbound := tileCount_le_distinct_add_pairCount hand hsmall
    have hdistinct : 8 ≤ distinctTileCount hand := by
      have hcount := h13.2.1
      omega
    let present : Finset Tile :=
      Finset.univ.filter (fun tile => 0 < hand.counts tile)
    have hpresentCard : present.card = distinctTileCount hand := by
      rfl
    have hexternal : ∃ discarded, discarded ∈ present ∧
        discarded ∉ protectedTiles := by
      by_contra hnone
      push Not at hnone
      have hsubset : present ⊆ protectedTiles := by
        intro tile htile
        exact hnone tile htile
      have hcardle := Finset.card_le_card hsubset
      rw [hpresentCard, hcard] at hcardle
      omega
    obtain ⟨discarded, hdiscardedPresent, hdiscardedOutside⟩ := hexternal
    have hdiscardedPositive :
        0 < hand.counts discarded := by
      simpa [present] using hdiscardedPresent
    have hdiscardedNotPair : ¬ 2 ≤ hand.counts discarded := by
      intro hpair
      exact hdiscardedOutside (hprotected.2 discarded hpair)
    have hdiscardedSingleton : hand.counts discarded = 1 := by
      omega
    have hne : discarded ≠ drawn := by
      intro heq
      subst heq
      exact hdiscardedOutside hdrawnProtected
    let next := exchangeHand hand discarded drawn
    have hstep : ProtectedPairMakingExchange protectedTiles hand next := by
      exact ⟨discarded, drawn, hdrawnProtected, hdrawnCount,
        Or.inr ⟨hdiscardedSingleton, hdiscardedOutside⟩, hne, rfl⟩
    exact ⟨next, hstep,
      protectedPairingInvariant_after_protectedPairMakingExchange
        hprotected hstep⟩

end Shanten
