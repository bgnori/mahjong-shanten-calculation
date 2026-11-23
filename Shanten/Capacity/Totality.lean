module

public import Shanten.Capacity.Search

@[expose] public section

namespace Shanten.Capacity

open MahjongDomain

private def honorKind : FixedMeld → Option (Fin 7)
  | .meld (.koutsu (.honor rank)) | .kan (.honor rank) => some rank
  | _ => none

private def occupiedHonors (fixed : List FixedMeld) : Finset (Fin 7) :=
  (fixed.filterMap honorKind).toFinset

private lemma occupiedHonors_card_le (fixed : List FixedMeld) :
    (occupiedHonors fixed).card ≤ fixed.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

private lemma honor_count_zero (meld : FixedMeld) (rank : Fin 7)
    (hfree : honorKind meld ≠ some rank) :
    meld.tiles.count (.honor rank) = 0 := by
  cases meld with
  | meld value =>
      cases value with
      | koutsu tile =>
          cases tile <;> simp_all [honorKind, FixedMeld.tiles, MentsuCandidate.tiles,
            MentsuCandidate.orderedTiles, eq_comm]
      | shuntsu sequence =>
          simp [FixedMeld.tiles, MentsuCandidate.tiles, MentsuCandidate.orderedTiles,
            Shuntsu.orderedTiles]
  | kan tile =>
      cases tile <;> simp_all [honorKind, FixedMeld.tiles, Kan.occupiedTiles, eq_comm]

private lemma fixedTiles_honor_count_zero (hfree : rank ∉ occupiedHonors fixed) :
    (fixedTiles fixed).count (.honor rank) = 0 := by
  have hpoint : ∀ meld ∈ fixed, honorKind meld ≠ some rank := by
    intro meld hmem heq
    apply hfree
    simp only [occupiedHonors, List.mem_toFinset, List.mem_filterMap]
    exact ⟨meld, hmem, heq⟩
  clear hfree
  induction fixed with
  | nil => simp [fixedTiles]
  | cons meld rest ih =>
      have hhead := honor_count_zero meld rank (hpoint meld (by simp))
      have htail := ih (fun other hmem => hpoint other (by simp [hmem]))
      simpa [fixedTiles, Multiset.count_add, hhead] using htail

private lemma triplet_list_counts (kinds : List Tile) (tile : Tile) :
    (MentsuCandidateList.tiles (kinds.map MentsuCandidate.koutsu)).count tile = 3 * kinds.count tile := by
  induction kinds with
  | nil => simp [MentsuCandidateList.tiles]
  | cons head tail ih =>
      change (Multiset.replicate 3 head + MentsuCandidateList.tiles (tail.map MentsuCandidate.koutsu)).count tile =
        3 * (head :: tail).count tile
      rw [Multiset.count_add, ih, Multiset.count_replicate]
      by_cases heq : head = tile
      · subst head
        simp [Nat.mul_add, Nat.add_comm]
      · simp [heq]

private lemma triplet_finset_counts (kinds : Finset Tile) (tile : Tile) :
    (MentsuCandidateList.tiles (kinds.toList.map MentsuCandidate.koutsu)).count tile =
      if tile ∈ kinds then 3 else 0 := by
  rw [triplet_list_counts]
  by_cases hmem : tile ∈ kinds
  · rw [List.count_eq_one_of_mem kinds.nodup_toList (Finset.mem_toList.mpr hmem)]
    simp [hmem]
  · rw [List.count_eq_zero.mpr (by simpa using hmem)]
    simp [hmem]

/-- Every fixed context leaves enough unused honor kinds for distinct triplets and a pair. -/
lemma exists_complete_target (hvalid : ValidHand fixed hand) :
    ∃ pair melds,
      melds.length + hand.fixedMelds = 4 ∧
      ValidHand fixed (targetHand hand (TileCounts.ofMultiset (mentsuHandTarget pair melds))) := by
  let available := (Finset.univ \ occupiedHonors fixed).image Tile.honor
  have hcard : available.card = 7 - (occupiedHonors fixed).card := by
    dsimp [available]
    rw [Finset.card_image_of_injective _ (fun _ _ h => Tile.honor.inj h)]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  have henough : 5 - fixed.length ≤ available.card := by
    have := occupiedHonors_card_le fixed
    rw [hcard]
    omega
  obtain ⟨chosen, hsubset, hchosen⟩ := Finset.exists_subset_card_eq henough
  have hnonempty : chosen.Nonempty := Finset.card_pos.mp (by
    have := hvalid.2.1
    omega)
  obtain ⟨pair, hpair⟩ := hnonempty
  let kinds := chosen.erase pair
  let melds := kinds.toList.map MentsuCandidate.koutsu
  refine ⟨pair, melds, ?_, hvalid.1, hvalid.2.1, fun tile => ?_⟩
  · dsimp [melds, kinds]
    rw [List.length_map, Finset.length_toList, Finset.card_erase_of_mem hpair, hchosen]
    have := hvalid.1
    have := hvalid.2.1
    omega
  · change (mentsuHandTarget pair melds).count tile + (fixedTiles fixed).count tile ≤ 4
    have hcount : (MentsuCandidateList.tiles melds).count tile =
        if tile ∈ kinds then 3 else 0 := triplet_finset_counts kinds tile
    simp only [mentsuHandTarget, Multiset.count_add, hcount,
      pairTiles, Pair.tiles_eq_replicate, Multiset.count_replicate]
    by_cases hmem : tile ∈ chosen
    · obtain ⟨rank, hrank, rfl⟩ := Finset.mem_image.mp (hsubset hmem)
      have hfree := (Finset.mem_sdiff.mp hrank).2
      rw [fixedTiles_honor_count_zero hfree]
      by_cases heq : Tile.honor rank = pair
      · subst pair
        simp [kinds]
      · simp [kinds, heq, Ne.symm heq, hmem]
    · have hne : tile ≠ pair := by
        intro heq
        exact hmem (heq ▸ hpair)
      have hkind : tile ∉ kinds := by
        exact fun h => hmem (Finset.mem_of_mem_erase h)
      simpa [hne, Ne.symm hne, hkind] using hvalid.fixed_count_le tile

lemma generalMentsuHandStates_nonempty (hvalid : ValidHand fixed hand) :
    (generalMentsuHandStates fixed hand).Nonempty := by
  obtain ⟨pair, melds, hlength, htarget⟩ := exists_complete_target hvalid
  exact ⟨generalMentsuHandStateFor hand (mentsuHandTarget pair melds),
    (mem_generalMentsuHandStates_iff hvalid _).mpr ⟨pair, melds, hlength, htarget, rfl⟩⟩

theorem generalMentsuHandMinimumSearch_eq_some_iff
    (h13 : IsThirteenTileEquivalentHand fixed hand) (value : Int) :
    generalMentsuHandMinimumSearch fixed hand = some value ↔
      IsShapeShanten fixed hand .mentsuHand value := by
  obtain ⟨state, _, hresult, hshape, _⟩ :=
    exists_optimal_state h13 (generalMentsuHandStates_nonempty h13.1)
  constructor
  · intro hvalue
    have heq := Option.some.inj (hresult.symm.trans hvalue)
    exact heq ▸ hshape
  · intro hvalue
    rw [hresult, isShapeShanten_unique hshape hvalue]

theorem generalMentsuHandMinimumSearch_exists_unique
    (h13 : IsThirteenTileEquivalentHand fixed hand) :
    ∃! value : Int,
      generalMentsuHandMinimumSearch fixed hand = some value ∧
      IsShapeShanten fixed hand .mentsuHand value := by
  obtain ⟨state, _, hresult, hshape, _⟩ :=
    exists_optimal_state h13 (generalMentsuHandStates_nonempty h13.1)
  exact ⟨_, ⟨hresult, hshape⟩, fun _ hother => isShapeShanten_unique hother.2 hshape⟩

theorem generalMentsuHandMinimumSearch_optimal
    (h13 : IsThirteenTileEquivalentHand fixed hand) :
    ∃ state ∈ generalMentsuHandStates fixed hand,
      generalMentsuHandMinimumSearch fixed hand = some ((state.missing : Int) - 1) ∧
      IsShapeShanten fixed hand .mentsuHand ((state.missing : Int) - 1) ∧
      ∀ other ∈ generalMentsuHandStates fixed hand, state.missing ≤ other.missing :=
  exists_optimal_state h13 (generalMentsuHandStates_nonempty h13.1)

theorem generalMentsuHandMinimumSearch_nil
    (h13 : IsThirteenTileEquivalentHand [] hand) :
    generalMentsuHandMinimumSearch [] hand = Shanten.generalMentsuHandMinimumSearch hand := by
  obtain ⟨value, ⟨hresult, hshape⟩, _⟩ := generalMentsuHandMinimumSearch_exists_unique h13
  have hstanding : tileCount hand + 3 * hand.fixedMelds = 13 := by
    rw [h13.1.1]
    exact h13.2
  have habstract := (Shanten.generalMentsuHandMinimumSearch_eq_some_iff
    hand h13.1.validCounts hstanding value).mpr ((isShapeShanten_nil_iff h13.1).mp hshape)
  rw [hresult, habstract]

end Shanten.Capacity
