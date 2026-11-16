import Shanten.Capacity.Specification

namespace Shanten.Capacity.Examples

def east : Tile := .honor ⟨0, by omega⟩
def south : Tile := .honor ⟨1, by omega⟩
def white : Tile := .honor ⟨4, by omega⟩

def sequences : List FixedMeld :=
  [ .meld (.sequence .man ⟨0, by omega⟩)
  , .meld (.sequence .pin ⟨0, by omega⟩)
  , .meld (.sequence .sou ⟨0, by omega⟩) ]

def fixedA : List FixedMeld := .meld (.triplet east) :: sequences
def fixedB : List FixedMeld := .meld (.triplet south) :: sequences

def standing : Hand :=
  { counts := fun tile => if tile = east then 1 else 0
    fixedMelds := 4 }

theorem inputA_valid : IsThirteenTileEquivalentHand fixedA standing := by
  unfold IsThirteenTileEquivalentHand ValidHand
  decide

theorem inputB_valid : IsThirteenTileEquivalentHand fixedB standing := by
  unfold IsThirteenTileEquivalentHand ValidHand
  decide

example : remainingCapacity fixedA east = 1 ∧ remainingCapacity fixedB east = 4 := by
  decide

example : ¬ HandStep fixedA standing (drawHand standing east) := by
  intro hstep
  exact (by unfold ValidHand; decide :
    ¬ ValidHand fixedA (drawHand standing east)) hstep.validHand

example : ¬ HandStep fixedA (drawHand standing white)
    (exchangeHand (drawHand standing white) white east) := by
  intro hstep
  exact (by unfold ValidHand; decide :
    ¬ ValidHand fixedA (exchangeHand (drawHand standing white) white east))
    hstep.validHand

private lemma not_complete (fixed : List FixedMeld) (hlength : fixed.length = 4) :
    ¬ Complete fixed .mentsuHand standing := by
  intro hcomplete
  obtain ⟨_, pair, htiles⟩ :=
    (complete_mentsuHand_iff_of_four_fixed hlength).mp hcomplete
  have hcount := htiles pair
  simp only [pairTiles, Multiset.count_replicate_self] at hcount
  change (if pair = east then 1 else 0) = 2 at hcount
  split at hcount <;> omega

private lemma one_step_pair_is_east
    (hstep : Shanten.HandStep standing after) (htiles : HasTiles after (pairTiles pair)) :
    pair = east := by
  by_contra hne
  have hpair := htiles pair
  simp only [pairTiles, Multiset.count_replicate_self] at hpair
  have hbefore : standing.counts pair = 0 := by simp [standing, hne]
  rcases hstep.2 with ⟨drawn, _, hcounts⟩ |
    ⟨discarded, drawn, _, _, _, hcounts⟩
  · have := hcounts pair
    split at this <;> omega
  · have := hcounts pair
    split at this <;> split at this <;> omega

private lemma inputA_no_one_step :
    ¬ ReachesCompletion fixedA .mentsuHand standing 1 := by
  intro hreach
  obtain ⟨next, hstep, hcomplete⟩ := reachesCompletion_one_iff.mp hreach
  obtain ⟨hvalid, pair, htiles⟩ :=
    (complete_mentsuHand_iff_of_four_fixed (by decide : fixedA.length = 4)).mp hcomplete
  have hpair := one_step_pair_is_east hstep.toAbstract htiles
  subst pair
  have hcount := htiles east
  simp only [pairTiles, Multiset.count_replicate_self] at hcount
  have hcapacity := hvalid.2.2 east
  have hfixed : (fixedTiles fixedA).count east = 3 := by decide
  omega

theorem inputA_shanten : IsShapeShanten fixedA standing .mentsuHand 1 := by
  let next := exchangeHand standing east white
  let target := drawHand next white
  have hstep : HandStep fixedA standing next :=
    exchangeHand_step inputA_valid.1 (by decide) (by decide) (by decide)
  have hdraw : HandStep fixedA next target :=
    drawHand_step hstep.validHand (by decide)
  have hcomplete : Complete fixedA .mentsuHand target :=
    (complete_mentsuHand_iff_of_four_fixed (by decide)).mpr
      ⟨hdraw.validHand, white, by unfold HasTiles; decide⟩
  refine ⟨trivial, 2, by omega,
    ⟨target, .step hstep (.step hdraw (.done hcomplete.1)), hcomplete⟩, ?_⟩
  intro smaller hsmaller
  have hcases : smaller = 0 ∨ smaller = 1 := by omega
  rcases hcases with rfl | rfl
  · intro hreach
    exact not_complete fixedA (by decide) (reachesCompletion_zero_iff.mp hreach)
  · exact inputA_no_one_step

theorem inputB_shanten : IsShapeShanten fixedB standing .mentsuHand 0 := by
  let target := drawHand standing east
  have hdraw : HandStep fixedB standing target :=
    drawHand_step inputB_valid.1 (by decide)
  have hcomplete : Complete fixedB .mentsuHand target :=
    (complete_mentsuHand_iff_of_four_fixed (by decide)).mpr
      ⟨hdraw.validHand, east, by unfold HasTiles; decide⟩
  refine ⟨trivial, 1, by omega, reachesCompletion_one_iff.mpr
    ⟨target, hdraw, hcomplete⟩, ?_⟩
  intro smaller hsmaller hreach
  have : smaller = 0 := by omega
  subst smaller
  exact not_complete fixedB (by decide) (reachesCompletion_zero_iff.mp hreach)

def fixedKan : List FixedMeld := .kan east :: sequences

example : fixedKan.length = 4 ∧ remainingCapacity fixedKan east = 0 := by
  decide

example : ¬ ValidHand fixedKan standing := by
  unfold ValidHand
  decide

example : IsThirteenTileEquivalentHand fixedKan
    { counts := fun tile => if tile = white then 1 else 0, fixedMelds := 4 } := by
  unfold IsThirteenTileEquivalentHand ValidHand
  decide

example : ¬ ValidHand (List.replicate 2 (.kan east))
    { counts := fun _ => 0, fixedMelds := 2 } := by
  unfold ValidHand
  decide

end Shanten.Capacity.Examples
