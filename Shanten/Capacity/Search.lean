import Shanten.Capacity.Reachability
import Shanten.MentsuHand.Search.BlockSearch

namespace Shanten.Capacity

/-- Reuse block consumption and costs, retaining only targets that fit the fixed context. -/
def generalMentsuHandStates (fixed : List FixedMeld) (hand : Hand) :
    Finset GeneralMentsuHandState :=
  (Shanten.generalMentsuHandStates hand).filter
    (fun state => validTileMultisetBool (state.completed + fixedTiles fixed) = true)

def generalMentsuHandDistances (fixed : List FixedMeld) (hand : Hand) : Finset Nat :=
  (generalMentsuHandStates fixed hand).image GeneralMentsuHandState.missing

def generalMentsuHandMinimumSearch (fixed : List FixedMeld) (hand : Hand) : Option Int :=
  let distances := generalMentsuHandDistances fixed hand
  if h : distances.Nonempty then
    some ((distances.min' h : Int) - 1)
  else
    none

lemma validTarget_iff (hvalid : ValidHand fixed hand) (tiles : Multiset Tile) :
    validTileMultisetBool (tiles + fixedTiles fixed) = true ↔
      ValidHand fixed (targetHand hand (countsOfTiles tiles)) := by
  rw [validTileMultisetBool_eq_true_iff]
  simp only [ValidHand, targetHand, countsOfTiles, hvalid.1, hvalid.2.1,
    true_and, Multiset.count_add]

lemma mem_generalMentsuHandStates_iff (hvalid : ValidHand fixed hand)
    (state : GeneralMentsuHandState) :
    state ∈ generalMentsuHandStates fixed hand ↔
      ∃ pair melds,
        melds.length + hand.fixedMelds = 4 ∧
        ValidHand fixed (targetHand hand (countsOfTiles (mentsuHandTarget pair melds))) ∧
        state = generalMentsuHandStateFor hand (mentsuHandTarget pair melds) := by
  have hfixed : hand.fixedMelds ≤ 4 := hvalid.1 ▸ hvalid.2.1
  rw [generalMentsuHandStates, Finset.mem_filter,
    Shanten.mem_generalMentsuHandStates_iff hand hfixed state]
  constructor
  · rintro ⟨⟨pair, melds, hlength, _, rfl⟩, hcapacity⟩
    exact ⟨pair, melds, hlength, (validTarget_iff hvalid _).mp hcapacity, rfl⟩
  · rintro ⟨pair, melds, hlength, hcapacity, rfl⟩
    exact ⟨⟨pair, melds, hlength, hcapacity.validCounts, rfl⟩,
      (validTarget_iff hvalid _).mpr hcapacity⟩

lemma generalMentsuHandStates_invariants (hvalid : ValidHand fixed hand)
    (hstate : state ∈ generalMentsuHandStates fixed hand) :
    state.used ≤ mentsuHandSupply hand ∧
      state.used ≤ state.completed ∧
      (∀ tile, state.completed.count tile + (fixedTiles fixed).count tile ≤ 4) ∧
      state.used.card + state.missing = state.completed.card := by
  obtain ⟨pair, melds, _, hcapacity, rfl⟩ :=
    (mem_generalMentsuHandStates_iff hvalid state).mp hstate
  exact ⟨generalMentsuHandStateFor_used_le hand _, Multiset.inter_le_left,
    hcapacity.2.2, generalMentsuHandStateFor_accounting hand _⟩

lemma generalMentsuHandState_reaches_of_size (hvalid : ValidHand fixed hand)
    (hsize : tileCount hand + 3 * fixed.length = 13 ∨
      tileCount hand + 3 * fixed.length = 14)
    (hstate : state ∈ generalMentsuHandStates fixed hand) :
    ReachesCompletion fixed .mentsuHand hand state.missing := by
  obtain ⟨pair, melds, hlength, hcapacity, rfl⟩ :=
    (mem_generalMentsuHandStates_iff hvalid state).mp hstate
  have hcomplete : Complete fixed .mentsuHand
      (targetHand hand (countsOfTiles (mentsuHandTarget pair melds))) :=
    ⟨hcapacity, complete_mentsuHand_targetHand hand _ pair melds
      hcapacity.validCounts hlength (targetHand_hasTiles_countsOfTiles hand _)⟩
  rcases hsize with h13 | h14
  · have hstanding : tileCount hand + 3 * hand.fixedMelds = 13 := by
      rw [hvalid.1]
      exact h13
    exact reachesCompletion_of_one_more_target_tile
      (sum_countsOfTiles_mentsuHandTarget_of_thirteen_tile_count
        hand hstanding pair melds hlength) hvalid hcomplete
  · have hsum : (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, countsOfTiles (mentsuHandTarget pair melds) tile := by
      rw [countsOfTiles_sum_eq_card]
      change tileCount hand = (pairTiles pair + meldsTiles melds).card
      rw [Multiset.card_add, pairTiles_card, meldsTiles_card]
      have := hvalid.1
      omega
    exact ⟨_, reachesHand_targetHand_of_equal_sum hsum hvalid hcapacity.2.2, hcomplete⟩

lemma generalMentsuHandState_reaches (h13 : IsThirteenTileEquivalentHand fixed hand)
    (hstate : state ∈ generalMentsuHandStates fixed hand) :
    ReachesCompletion fixed .mentsuHand hand state.missing :=
  generalMentsuHandState_reaches_of_size h13.1 (Or.inl h13.2) hstate

lemma exists_state_of_reachesCompletion (hvalid : ValidHand fixed hand)
    (hreach : ReachesCompletion fixed .mentsuHand hand distance) :
    ∃ state ∈ generalMentsuHandStates fixed hand, state.missing ≤ distance := by
  obtain ⟨after, hpath, hcapacity, _, pair, melds, hlength, htiles⟩ := hreach
  have hcounts : countsOfTiles (mentsuHandTarget pair melds) = after.counts :=
    funext (fun tile => (htiles tile).symm)
  have hmelds : melds.length + hand.fixedMelds = 4 := by
    have := hvalid.1
    have := hcapacity.1
    omega
  have htarget : ValidHand fixed
      (targetHand hand (countsOfTiles (mentsuHandTarget pair melds))) := by
    refine ⟨hvalid.1, hvalid.2.1, fun tile => ?_⟩
    change countsOfTiles (mentsuHandTarget pair melds) tile +
      (fixedTiles fixed).count tile ≤ 4
    rw [hcounts]
    exact hcapacity.2.2 tile
  refine ⟨generalMentsuHandStateFor hand (mentsuHandTarget pair melds),
    (mem_generalMentsuHandStates_iff hvalid _).mpr
      ⟨pair, melds, hmelds, htarget, rfl⟩, ?_⟩
  change countDeficit hand.counts (countsOfTiles (mentsuHandTarget pair melds)) ≤ distance
  rw [hcounts]
  exact hpath.deficit_le

lemma exists_optimal_state_of_size (hvalid : ValidHand fixed hand)
    (hsize : tileCount hand + 3 * fixed.length = 13 ∨
      tileCount hand + 3 * fixed.length = 14)
    (hnonempty : (generalMentsuHandStates fixed hand).Nonempty) :
    ∃ state ∈ generalMentsuHandStates fixed hand,
      generalMentsuHandMinimumSearch fixed hand = some ((state.missing : Int) - 1) ∧
      IsShapeShanten fixed hand .mentsuHand ((state.missing : Int) - 1) ∧
      ∀ other ∈ generalMentsuHandStates fixed hand, state.missing ≤ other.missing := by
  let distances := generalMentsuHandDistances fixed hand
  have hdistances : distances.Nonempty := Finset.Nonempty.image hnonempty _
  obtain ⟨state, hstate, hminimum⟩ :=
    Finset.mem_image.mp (Finset.min'_mem distances hdistances)
  have hminimal : ∀ other ∈ generalMentsuHandStates fixed hand,
      state.missing ≤ other.missing := by
    intro other hother
    rw [hminimum]
    exact Finset.min'_le distances _ (Finset.mem_image.mpr ⟨other, hother, rfl⟩)
  have hshape : IsShapeShanten fixed hand .mentsuHand ((state.missing : Int) - 1) := by
    refine ⟨trivial, state.missing, by omega,
      generalMentsuHandState_reaches_of_size hvalid hsize hstate, ?_⟩
    intro smaller hsmaller hreach
    obtain ⟨other, hother, hbound⟩ := exists_state_of_reachesCompletion hvalid hreach
    have := hminimal other hother
    omega
  refine ⟨state, hstate, ?_, hshape, hminimal⟩
  simp [generalMentsuHandMinimumSearch, distances, hdistances, ← hminimum]

lemma exists_optimal_state (h13 : IsThirteenTileEquivalentHand fixed hand)
    (hnonempty : (generalMentsuHandStates fixed hand).Nonempty) :
    ∃ state ∈ generalMentsuHandStates fixed hand,
      generalMentsuHandMinimumSearch fixed hand = some ((state.missing : Int) - 1) ∧
      IsShapeShanten fixed hand .mentsuHand ((state.missing : Int) - 1) ∧
      ∀ other ∈ generalMentsuHandStates fixed hand, state.missing ≤ other.missing :=
  exists_optimal_state_of_size h13.1 (Or.inl h13.2) hnonempty

end Shanten.Capacity
