module

public import Shanten.MentsuHand.Search.Totality
public import Mathlib.Data.Multiset.UnionInter

@[expose] public section

/-!
# Search / BlockSearch

Completed-block search with hand-tile consumption and missing-tile costs.
-/

namespace Shanten

open MahjongDomain

def mentsuHandSupply (hand : Hand) : Multiset Tile :=
  ∑ tile : Tile, Multiset.replicate (hand.counts tile) tile

@[simp]
lemma mentsuHandSupply_count (hand : Hand) (tile : Tile) :
    (mentsuHandSupply hand).count tile = hand.counts tile := by
  simp [mentsuHandSupply, Multiset.count_sum', Multiset.count_replicate]

@[ext]
structure GeneralMentsuHandState where
  completed : Multiset Tile
  used : Multiset Tile
  missing : Nat
  deriving DecidableEq

def initialGeneralMentsuHandState : GeneralMentsuHandState :=
  ⟨0, 0, 0⟩

/-- Consume only remaining copies; missing blocks and a missing head are allowed. -/
def generalMentsuHandAddBlock (hand : Hand)
    (state : GeneralMentsuHandState) (block : Multiset Tile) :
    GeneralMentsuHandState :=
  let remaining := mentsuHandSupply hand - state.used
  { completed := state.completed + block
    used := state.used + block ∩ remaining
    missing := state.missing + (block - remaining).card }

def generalMentsuHandStateFor (hand : Hand) (tiles : Multiset Tile) :
    GeneralMentsuHandState :=
  { completed := tiles
    used := tiles ∩ mentsuHandSupply hand
    missing := countDeficit hand.counts (TileCounts.ofMultiset tiles) }

lemma generalMentsuHandStateFor_zero (hand : Hand) :
    generalMentsuHandStateFor hand 0 = initialGeneralMentsuHandState := by
  simp [generalMentsuHandStateFor, initialGeneralMentsuHandState,
    countDeficit, TileCounts.ofMultiset]

lemma generalMentsuHandAddBlock_stateFor
    (hand : Hand) (tiles block : Multiset Tile) :
    generalMentsuHandAddBlock hand (generalMentsuHandStateFor hand tiles) block =
      generalMentsuHandStateFor hand (tiles + block) := by
  apply GeneralMentsuHandState.ext
  · rfl
  · apply Multiset.ext.mpr
    intro tile
    simp only [generalMentsuHandAddBlock, generalMentsuHandStateFor,
      Multiset.count_add, Multiset.count_inter, Multiset.count_sub,
      mentsuHandSupply_count]
    omega
  · change countDeficit hand.counts (TileCounts.ofMultiset tiles) +
        (block - (mentsuHandSupply hand - tiles ∩ mentsuHandSupply hand)).card =
      countDeficit hand.counts (TileCounts.ofMultiset (tiles + block))
    rw [← TileCounts.ofMultiset_sum_eq_card]
    unfold countDeficit
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro tile _
    simp only [TileCounts.ofMultiset, Multiset.count_add, Multiset.count_sub,
      Multiset.count_inter, mentsuHandSupply_count]
    omega

lemma generalMentsuHandStateFor_used_le (hand : Hand) (tiles : Multiset Tile) :
    (generalMentsuHandStateFor hand tiles).used ≤ mentsuHandSupply hand :=
  Multiset.inter_le_right

/-- The retained tiles and the missing tiles account for the entire target. -/
lemma generalMentsuHandStateFor_accounting
    (hand : Hand) (tiles : Multiset Tile) :
    (generalMentsuHandStateFor hand tiles).used.card +
      (generalMentsuHandStateFor hand tiles).missing = tiles.card := by
  change (tiles ∩ mentsuHandSupply hand).card +
    countDeficit hand.counts (TileCounts.ofMultiset tiles) = tiles.card
  rw [← TileCounts.ofMultiset_sum_eq_card, ← TileCounts.ofMultiset_sum_eq_card tiles]
  unfold countDeficit
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro tile _
  simp only [TileCounts.ofMultiset, Multiset.count_inter, mentsuHandSupply_count]
  omega

def generalMentsuHandMeldStates (hand : Hand) (initialTiles : Multiset Tile) :
    Nat → Finset GeneralMentsuHandState
  | 0 =>
      ({generalMentsuHandAddBlock hand initialGeneralMentsuHandState initialTiles} :
        Finset GeneralMentsuHandState)
        |>.filter (fun state => validTileMultisetBool state.completed = true)
  | count + 1 =>
      (Finset.univ.biUnion fun meld =>
        (generalMentsuHandMeldStates hand initialTiles count).image
          (fun state => generalMentsuHandAddBlock hand state (MentsuCandidate.tiles meld)))
        |>.filter (fun state => validTileMultisetBool state.completed = true)

def generalMentsuHandStates (hand : Hand) : Finset GeneralMentsuHandState :=
  Finset.univ.biUnion fun pair =>
    generalMentsuHandMeldStates hand (pairTiles pair) (4 - hand.fixedMelds)

def generalMentsuHandDistances (hand : Hand) : Finset Nat :=
  (generalMentsuHandStates hand).image GeneralMentsuHandState.missing

def generalMentsuHandMinimumSearch (hand : Hand) : Option Int :=
  let distances := generalMentsuHandDistances hand
  if h : distances.Nonempty then
    some ((distances.min' h : Int) - 1)
  else
    none

lemma generalMentsuHandAddBlock_initial (hand : Hand) (block : Multiset Tile) :
    generalMentsuHandAddBlock hand initialGeneralMentsuHandState block =
      generalMentsuHandStateFor hand block := by
  simpa [generalMentsuHandStateFor_zero] using
    generalMentsuHandAddBlock_stateFor hand 0 block

lemma mem_generalMentsuHandMeldStates_iff
    (hand : Hand) (initialTiles : Multiset Tile) (count : Nat)
    (state : GeneralMentsuHandState) :
    state ∈ generalMentsuHandMeldStates hand initialTiles count ↔
      ∃ costState ∈ mentsuHandMeldCostStatesDP hand initialTiles count,
        generalMentsuHandStateFor hand costState.1 = state := by
  induction count generalizing state with
  | zero =>
      simp only [generalMentsuHandMeldStates, mentsuHandMeldCostStatesDP,
        generalMentsuHandAddBlock_initial, Finset.mem_filter,
        Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, hvalid⟩
        exact ⟨_, ⟨rfl, hvalid⟩, rfl⟩
      · rintro ⟨_, ⟨rfl, hvalid⟩, rfl⟩
        exact ⟨rfl, hvalid⟩
  | succ count ih =>
      constructor
      · intro hstate
        simp only [generalMentsuHandMeldStates, Finset.mem_filter,
          Finset.mem_biUnion, Finset.mem_univ, true_and,
          Finset.mem_image] at hstate
        obtain ⟨⟨meld, previous, hprevious, rfl⟩, hvalid⟩ := hstate
        obtain ⟨costState, hcostState, rfl⟩ := (ih previous).mp hprevious
        refine ⟨mentsuHandCostStateAdd hand costState (MentsuCandidate.tiles meld), ?_, ?_⟩
        · simp only [mentsuHandMeldCostStatesDP, Finset.mem_filter,
            Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
          exact ⟨⟨meld, costState, hcostState, rfl⟩, hvalid⟩
        · exact (generalMentsuHandAddBlock_stateFor hand _ _).symm
      · rintro ⟨costState, hcostState, rfl⟩
        simp only [mentsuHandMeldCostStatesDP, Finset.mem_filter,
          Finset.mem_biUnion, Finset.mem_univ, true_and,
          Finset.mem_image] at hcostState
        obtain ⟨⟨meld, previous, hprevious, rfl⟩, hvalid⟩ := hcostState
        simp only [generalMentsuHandMeldStates, Finset.mem_filter,
          Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
        refine ⟨⟨meld, generalMentsuHandStateFor hand previous.1,
          (ih _).mpr ⟨previous, hprevious, rfl⟩,
          generalMentsuHandAddBlock_stateFor hand _ _⟩, hvalid⟩

lemma mem_generalMentsuHandStates_iff_costState
    (hand : Hand) (state : GeneralMentsuHandState) :
    state ∈ generalMentsuHandStates hand ↔
      ∃ costState ∈ recursiveMentsuHandTargetCostStatesDP hand,
        generalMentsuHandStateFor hand costState.1 = state := by
  simp only [generalMentsuHandStates, recursiveMentsuHandTargetCostStatesDP,
    Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_generalMentsuHandMeldStates_iff]
  constructor
  · rintro ⟨pair, costState, hmem, rfl⟩
    exact ⟨costState, ⟨pair, hmem⟩, rfl⟩
  · rintro ⟨costState, ⟨pair, hmem⟩, rfl⟩
    exact ⟨pair, costState, hmem, rfl⟩

lemma generalMentsuHandDistances_eq (hand : Hand) :
    generalMentsuHandDistances hand = validMentsuHandTargetDistances hand := by
  ext distance
  simp only [generalMentsuHandDistances, validMentsuHandTargetDistances,
    Finset.mem_image, mem_generalMentsuHandStates_iff_costState]
  constructor
  · rintro ⟨state, ⟨costState, hmem, rfl⟩, hdistance⟩
    obtain ⟨pair, hpair⟩ := Finset.mem_biUnion.mp hmem
    have hcost := mentsuHandMeldCostStatesDP_cost hand (pairTiles pair)
      (4 - hand.fixedMelds) costState hpair.2
    exact ⟨costState, hmem, hcost.trans hdistance⟩
  · rintro ⟨costState, hmem, rfl⟩
    obtain ⟨pair, hpair⟩ := Finset.mem_biUnion.mp hmem
    have hcost := mentsuHandMeldCostStatesDP_cost hand (pairTiles pair)
      (4 - hand.fixedMelds) costState hpair.2
    exact ⟨generalMentsuHandStateFor hand costState.1,
      ⟨costState, hmem, rfl⟩, hcost.symm⟩

/-- Soundness and coverage include targets with no pre-existing blocks in the hand. -/
lemma mem_generalMentsuHandStates_iff
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4)
    (state : GeneralMentsuHandState) :
    state ∈ generalMentsuHandStates hand ↔
      ∃ pair melds,
        melds.length + hand.fixedMelds = 4 ∧
        ValidCounts (targetHand hand (TileCounts.ofMultiset (mentsuHandTarget pair melds))) ∧
        state = generalMentsuHandStateFor hand (mentsuHandTarget pair melds) := by
  rw [mem_generalMentsuHandStates_iff_costState,
    recursiveMentsuHandTargetCostStatesDP_eq hand hfixed]
  constructor
  · rintro ⟨costState, hmem, rfl⟩
    obtain ⟨htiles, _⟩ := (mem_mentsuHandTargetCostStatesDP_iff hand costState).mp hmem
    obtain ⟨pair, melds, hlength, htarget, hvalid⟩ :=
      (mem_mentsuHandTargetTileStatesDP_iff hand.fixedMelds hfixed costState.1).mp htiles
    refine ⟨pair, melds, hlength, ?_, ?_⟩
    · apply (validTileMultisetBool_eq_true_iff_targetHand hand _).mp
      simpa [htarget] using hvalid
    · rw [htarget]
  · rintro ⟨pair, melds, hlength, hvalid, rfl⟩
    let tiles := mentsuHandTarget pair melds
    refine ⟨(tiles, countDeficit hand.counts (TileCounts.ofMultiset tiles)), ?_, rfl⟩
    apply (mem_mentsuHandTargetCostStatesDP_iff hand _).mpr
    refine ⟨?_, rfl⟩
    apply (mem_mentsuHandTargetTileStatesDP_iff hand.fixedMelds hfixed tiles).mpr
    exact ⟨pair, melds, hlength, rfl,
      (validTileMultisetBool_eq_true_iff_targetHand hand tiles).mpr hvalid⟩

lemma generalMentsuHandStates_invariants
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4)
    (state : GeneralMentsuHandState) (hstate : state ∈ generalMentsuHandStates hand) :
    state.used ≤ mentsuHandSupply hand ∧
      state.used ≤ state.completed ∧
      (∀ tile, state.completed.count tile ≤ 4) ∧
      state.used.card + state.missing = state.completed.card := by
  obtain ⟨pair, melds, _, hvalid, rfl⟩ :=
    (mem_generalMentsuHandStates_iff hand hfixed state).mp hstate
  exact ⟨generalMentsuHandStateFor_used_le hand _,
    Multiset.inter_le_left, hvalid,
    generalMentsuHandStateFor_accounting hand _⟩

lemma generalMentsuHandMinimumSearch_eq_targetMinimumSearch (hand : Hand) :
    generalMentsuHandMinimumSearch hand = mentsuHandTargetMinimumSearch hand := by
  simp only [generalMentsuHandMinimumSearch, mentsuHandTargetMinimumSearch,
    generalMentsuHandDistances_eq]

theorem generalMentsuHandMinimumSearch_eq_some_iff
    (hand : Hand) (hvalid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13) (value : Int) :
    generalMentsuHandMinimumSearch hand = some value ↔
      IsShapeShanten hand .mentsuHand value := by
  rw [generalMentsuHandMinimumSearch_eq_targetMinimumSearch]
  exact mentsuHandTargetMinimumSearch_eq_some_iff hand hvalid hstanding value

/-- Every valid thirteen-tile-equivalent hand has exactly one correct result. -/
theorem generalMentsuHandMinimumSearch_exists_unique
    (hand : Hand) (hvalid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13) :
    ∃! value : Int,
      generalMentsuHandMinimumSearch hand = some value ∧
      IsShapeShanten hand .mentsuHand value := by
  obtain ⟨value, hshape⟩ :=
    exists_isShapeShanten_mentsuHand_of_valid_thirteen_tile_count hand hvalid hstanding
  refine ⟨value, ⟨?_, hshape⟩, ?_⟩
  · exact (generalMentsuHandMinimumSearch_eq_some_iff hand hvalid hstanding value).mpr hshape
  · intro other hother
    exact isShapeShanten_unique hother.2 hshape

/-- The minimum is attained by an actual block-search state, not just a specification witness. -/
theorem generalMentsuHandMinimumSearch_optimal
    (hand : Hand) (hvalid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13) :
    ∃ state ∈ generalMentsuHandStates hand,
      generalMentsuHandMinimumSearch hand = some ((state.missing : Int) - 1) ∧
      IsShapeShanten hand .mentsuHand ((state.missing : Int) - 1) ∧
      ∀ other ∈ generalMentsuHandStates hand, state.missing ≤ other.missing := by
  obtain ⟨distance, hmem, hminimal, hshape⟩ :=
    exists_mentsuHandShanten_as_min_validTargetDistance hand hvalid hstanding
  rw [← generalMentsuHandDistances_eq] at hmem hminimal
  obtain ⟨state, hstate, rfl⟩ := Finset.mem_image.mp hmem
  refine ⟨state, hstate, ?_, hshape, ?_⟩
  · exact (generalMentsuHandMinimumSearch_eq_some_iff hand hvalid hstanding _).mpr hshape
  · intro other hother
    exact hminimal _ (Finset.mem_image.mpr ⟨other, hother, rfl⟩)

end Shanten
