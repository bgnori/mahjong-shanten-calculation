import Shanten.Capacity.Fourteen

namespace Shanten.Capacity

open MahjongDomain

def discardHand (hand : Hand) (discarded : Tile) : Hand :=
  { counts := fun tile => hand.counts tile - (if tile = discarded then 1 else 0)
    fixedMelds := hand.fixedMelds }

lemma ValidHand.discard (hvalid : ValidHand fixed hand) :
    ValidHand fixed (discardHand hand discarded) := by
  refine ⟨hvalid.1, hvalid.2.1, fun tile => ?_⟩
  have := hvalid.2.2 tile
  change hand.counts tile - (if tile = discarded then 1 else 0) +
    (fixedTiles fixed).count tile ≤ 4
  omega

lemma discardHand_tileCount (hpositive : 0 < hand.counts discarded) :
    tileCount (discardHand hand discarded) + 1 = tileCount hand := by
  have hpoint : ∀ tile,
      (discardHand hand discarded).counts tile + (if tile = discarded then 1 else 0) =
        hand.counts tile := by
    intro tile
    by_cases htile : tile = discarded
    · subst tile
      simp only [discardHand, ite_true]
      omega
    · simp [discardHand, htile]
  have hsum := congrArg (fun counts : TileCounts => ∑ tile, counts tile) (funext hpoint)
  simpa [tileCount, Finset.sum_add_distrib] using hsum

lemma IsFourteenTileEquivalentHand.discard
    (h14 : IsFourteenTileEquivalentHand fixed hand)
    (hpositive : 0 < hand.counts discarded) :
    IsThirteenTileEquivalentHand fixed (discardHand hand discarded) := by
  exact ⟨h14.1.discard, by have := discardHand_tileCount hpositive; have := h14.2; omega⟩

lemma countDeficit_le_discard :
    countDeficit hand.counts target ≤
      countDeficit (discardHand hand discarded).counts target := by
  apply Finset.sum_le_sum
  intro tile _
  change target tile - hand.counts tile ≤
    target tile - (hand.counts tile - (if tile = discarded then 1 else 0))
  omega

lemma countDeficit_discard_of_surplus (hsurplus : target discarded < hand.counts discarded) :
    countDeficit (discardHand hand discarded).counts target =
      countDeficit hand.counts target := by
  apply Finset.sum_congr rfl
  intro tile _
  by_cases htile : tile = discarded
  · subst tile
    change target discarded - (hand.counts discarded - (if discarded = discarded then 1 else 0)) =
      target discarded - hand.counts discarded
    simp only [ite_true]
    omega
  · simp [discardHand, htile]

private lemma search_le_target
    (hvalid : ValidHand fixed hand)
    (hsize : tileCount hand + 3 * fixed.length = 13 ∨
      tileCount hand + 3 * fixed.length = 14)
    (hresult : generalMentsuHandMinimumSearch fixed hand = some value)
    (hlength : melds.length + hand.fixedMelds = 4)
    (hcapacity : ValidHand fixed
      (targetHand hand (TileCounts.ofMultiset (mentsuHandTarget pair melds)))) :
    value ≤ (countDeficit hand.counts (TileCounts.ofMultiset (mentsuHandTarget pair melds)) : Int) - 1 := by
  obtain ⟨state, _, hminimum, _, hminimal⟩ :=
    exists_optimal_state_of_size hvalid hsize (generalMentsuHandStates_nonempty hvalid)
  have hstate := (mem_generalMentsuHandStates_iff hvalid _).mpr
    ⟨pair, melds, hlength, hcapacity, rfl⟩
  have hbound := hminimal _ hstate
  have heq := Option.some.inj (hminimum.symm.trans hresult)
  change state.missing ≤ countDeficit hand.counts
    (TileCounts.ofMultiset (mentsuHandTarget pair melds)) at hbound
  omega

theorem search_le_discard_search (h14 : IsFourteenTileEquivalentHand fixed hand)
    (hresult : generalMentsuHandMinimumSearch fixed hand = some value)
    (hpositive : 0 < hand.counts discarded)
    (hdiscard : generalMentsuHandMinimumSearch fixed (discardHand hand discarded) = some other) :
    value ≤ other := by
  have h13 := h14.discard hpositive
  obtain ⟨state, hstate, hminimum, _, _⟩ := generalMentsuHandMinimumSearch_optimal h13
  obtain ⟨pair, melds, hlength, hcapacity, rfl⟩ :=
    (mem_generalMentsuHandStates_iff h13.1 state).mp hstate
  have hbound := search_le_target h14.1 (Or.inr h14.2) hresult hlength hcapacity
  have hmono := countDeficit_le_discard (hand := hand) (discarded := discarded)
    (target := TileCounts.ofMultiset (mentsuHandTarget pair melds))
  have heq := Option.some.inj (hminimum.symm.trans hdiscard)
  change (countDeficit (discardHand hand discarded).counts
    (TileCounts.ofMultiset (mentsuHandTarget pair melds)) : Int) - 1 = other at heq
  omega

/-- Every noncomplete fourteen-tile hand has an attaining legal discard. -/
theorem exists_discard_search_eq (h14 : IsFourteenTileEquivalentHand fixed hand)
    (hnotComplete : ¬ Complete fixed .mentsuHand hand)
    (hresult : generalMentsuHandMinimumSearch fixed hand = some value) :
    ∃ discarded, 0 < hand.counts discarded ∧
      generalMentsuHandMinimumSearch fixed (discardHand hand discarded) = some value := by
  obtain ⟨state, hstate, hminimum, hshape, _⟩ :=
    generalMentsuHandMinimumSearch_optimal_of_fourteen h14
  obtain ⟨pair, melds, hlength, hcapacity, rfl⟩ :=
    (mem_generalMentsuHandStates_iff h14.1 state).mp hstate
  let target := TileCounts.ofMultiset (mentsuHandTarget pair melds)
  have hsum : (∑ tile : Tile, hand.counts tile) = ∑ tile : Tile, target tile := by
    rw [countsOfTiles_sum_eq_card]
    change tileCount hand = (pairTiles pair + MentsuCandidateList.tiles melds).card
    rw [Multiset.card_add, pairTiles_card, meldsTiles_card]
    have := h14.1.1
    have := h14.2
    omega
  have hne : hand.counts ≠ target := by
    intro heq
    apply hnotComplete
    refine ⟨h14.1, h14.1.validCounts, pair, melds, hlength, ?_⟩
    intro tile
    exact congrFun heq tile
  obtain ⟨discarded, drawn, _, hsurplus, _⟩ :=
    exists_target_exchange_tiles hand target hsum hne
  have hpositive : 0 < hand.counts discarded := by omega
  have h13 := h14.discard hpositive
  obtain ⟨other, ⟨hother, _⟩, _⟩ := generalMentsuHandMinimumSearch_exists_unique h13
  have hlower := search_le_discard_search h14 hresult hpositive hother
  have hupper := search_le_target h13.1 (Or.inl h13.2) hother hlength hcapacity
  have hdeficit := countDeficit_discard_of_surplus hsurplus
  have heq := Option.some.inj (hminimum.symm.trans hresult)
  change (countDeficit hand.counts target : Int) - 1 = value at heq
  change other ≤ (countDeficit (discardHand hand discarded).counts target : Int) - 1 at hupper
  rw [hdeficit] at hupper
  have : other = value := by omega
  exact ⟨discarded, hpositive, this ▸ hother⟩

/-- Legal discards paired with their thirteen-tile search result. -/
def discardSearchResults (fixed : List FixedMeld) (hand : Hand) : Finset (Tile × Int) :=
  (presentTiles hand).biUnion fun discarded =>
    ((generalMentsuHandMinimumSearch fixed (discardHand hand discarded)).toFinset).image
      (fun value => (discarded, value))

lemma mem_discardSearchResults_iff :
    (discarded, value) ∈ discardSearchResults fixed hand ↔
      0 < hand.counts discarded ∧
        generalMentsuHandMinimumSearch fixed (discardHand hand discarded) = some value := by
  simp [discardSearchResults, presentTiles, Option.mem_toFinset]

def minimumDiscardSearch (fixed : List FixedMeld) (hand : Hand) : Option Int :=
  let values := (discardSearchResults fixed hand).image Prod.snd
  if h : values.Nonempty then some (values.min' h) else none

theorem generalMentsuHandMinimumSearch_eq_minimumDiscardSearch
    (h14 : IsFourteenTileEquivalentHand fixed hand)
    (hnotComplete : ¬ Complete fixed .mentsuHand hand) :
    generalMentsuHandMinimumSearch fixed hand = minimumDiscardSearch fixed hand := by
  obtain ⟨value, ⟨hresult, _⟩, _⟩ :=
    generalMentsuHandMinimumSearch_exists_unique_of_fourteen h14
  obtain ⟨discarded, hpositive, hdiscard⟩ := exists_discard_search_eq h14 hnotComplete hresult
  let values := (discardSearchResults fixed hand).image Prod.snd
  have hmem : value ∈ values :=
    Finset.mem_image.mpr ⟨(discarded, value),
      mem_discardSearchResults_iff.mpr ⟨hpositive, hdiscard⟩, rfl⟩
  have hnonempty : values.Nonempty := ⟨value, hmem⟩
  have hmin : values.min' hnonempty = value := by
    apply le_antisymm
    · exact Finset.min'_le values _ hmem
    · obtain ⟨⟨tile, other⟩, hother, heq⟩ :=
        Finset.mem_image.mp (Finset.min'_mem values hnonempty)
      obtain ⟨hpresent, hotherSearch⟩ := mem_discardSearchResults_iff.mp hother
      simpa only [Prod.snd] using
        heq ▸ search_le_discard_search h14 hresult hpresent hotherSearch
  simp [hresult, minimumDiscardSearch, values, hnonempty, hmin]

/-- Best legal discards; completion should be checked before using this set. -/
def optimalDiscards (fixed : List FixedMeld) (hand : Hand) : Finset Tile :=
  ((discardSearchResults fixed hand).filter
    (fun candidate => minimumDiscardSearch fixed hand = some candidate.2)).image Prod.fst

theorem mem_optimalDiscards_iff
    (h14 : IsFourteenTileEquivalentHand fixed hand)
    (hnotComplete : ¬ Complete fixed .mentsuHand hand)
    (hresult : generalMentsuHandMinimumSearch fixed hand = some value) :
    discarded ∈ optimalDiscards fixed hand ↔
      0 < hand.counts discarded ∧
        generalMentsuHandMinimumSearch fixed (discardHand hand discarded) = some value := by
  have hmin : minimumDiscardSearch fixed hand = some value :=
    (generalMentsuHandMinimumSearch_eq_minimumDiscardSearch h14 hnotComplete).symm.trans hresult
  simp [optimalDiscards, hmin, mem_discardSearchResults_iff]

theorem optimalDiscards_nonempty
    (h14 : IsFourteenTileEquivalentHand fixed hand)
    (hnotComplete : ¬ Complete fixed .mentsuHand hand) :
    (optimalDiscards fixed hand).Nonempty := by
  obtain ⟨value, ⟨hresult, _⟩, _⟩ :=
    generalMentsuHandMinimumSearch_exists_unique_of_fourteen h14
  obtain ⟨discarded, hpositive, hdiscard⟩ := exists_discard_search_eq h14 hnotComplete hresult
  exact ⟨discarded, (mem_optimalDiscards_iff h14 hnotComplete hresult).mpr
    ⟨hpositive, hdiscard⟩⟩

end Shanten.Capacity
