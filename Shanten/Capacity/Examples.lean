import Shanten.Capacity.Discard
import Shanten.Capacity.Special
import Shanten.Capacity.Overall
import Shanten.Capacity.Wait

namespace Shanten.Capacity.Examples

open MahjongDomain

def east : Tile := .honor ⟨0, by omega⟩
def south : Tile := .honor ⟨1, by omega⟩
def white : Tile := .honor ⟨4, by omega⟩

def sequences : List FixedMeld :=
  [ .meld (.shuntsu ⟨.man, ⟨0, by omega⟩⟩)
  , .meld (.shuntsu ⟨.pin, ⟨0, by omega⟩⟩)
  , .meld (.shuntsu ⟨.sou, ⟨0, by omega⟩⟩) ]

def fixedA : List FixedMeld := .meld (.koutsu east) :: sequences
def fixedB : List FixedMeld := .meld (.koutsu south) :: sequences

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
  simp only [pairTiles, Pair.tiles_eq_replicate, Multiset.count_replicate_self] at hcount
  change (if pair = east then 1 else 0) = 2 at hcount
  split at hcount <;> omega

private lemma one_step_pair_is_east
    (hstep : Shanten.HandStep standing after) (htiles : HasTiles after (pairTiles pair)) :
    pair = east := by
  by_contra hne
  have hpair := htiles pair
  simp only [pairTiles, Pair.tiles_eq_replicate, Multiset.count_replicate_self] at hpair
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
  simp only [pairTiles, Pair.tiles_eq_replicate, Multiset.count_replicate_self] at hcount
  have hcapacity := hvalid.2.2 east
  change next.counts east + (fixedTiles fixedA).count east ≤ 4 at hcapacity
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

example : ¬ ∃ tile, IsFixedContextWait fixedA standing tile := by
  intro wait
  have zero := (isShapeShanten_zero_iff_exists_fixedContextWait inputA_valid).mpr wait
  have equal := isShapeShanten_unique inputA_shanten zero
  omega

example : ∃ tile, IsFixedContextWait fixedB standing tile :=
  (isShapeShanten_zero_iff_exists_fixedContextWait inputB_valid).mp inputB_shanten

private def man1 : Tile := .suited .man 0

private def threeMeldStanding : Hand :=
  { counts := fun tile => if tile = man1 then 3 else if tile = east then 1 else 0
    fixedMelds := 3 }

private def threeMeldFixedA : List FixedMeld :=
  [.meld (.koutsu east), .meld (.shuntsu ⟨.pin, 0⟩), .meld (.shuntsu ⟨.sou, 0⟩)]

private def threeMeldFixedB : List FixedMeld :=
  [.meld (.koutsu south), .meld (.shuntsu ⟨.pin, 0⟩), .meld (.shuntsu ⟨.sou, 0⟩)]

example : IsThirteenTileEquivalentHand threeMeldFixedA threeMeldStanding := by
  unfold IsThirteenTileEquivalentHand ValidHand
  decide

example : ¬ IsFixedContextWait threeMeldFixedA threeMeldStanding east := by
  intro wait
  have : ¬ threeMeldStanding.counts east < remainingCapacity threeMeldFixedA east := by decide
  exact this wait.1

private theorem threeMeldFixedB_wait : IsFixedContextWait threeMeldFixedB threeMeldStanding east := by
  have valid : ValidHand threeMeldFixedB (drawHand threeMeldStanding east) := by
    unfold ValidHand
    decide
  refine ⟨by decide, valid, valid.validCounts, east, [.koutsu man1], by decide, ?_⟩
  unfold HasTiles
  decide

example : IsShapeShanten threeMeldFixedB threeMeldStanding .mentsuHand 0 := by
  have valid : IsThirteenTileEquivalentHand threeMeldFixedB threeMeldStanding := by
    unfold IsThirteenTileEquivalentHand ValidHand
    decide
  exact (isShapeShanten_zero_iff_exists_fixedContextWait valid).mpr ⟨east, threeMeldFixedB_wait⟩

set_option maxRecDepth 4096 in
theorem inputA_search : generalMentsuHandMinimumSearch fixedA standing = some 1 := by
  decide

set_option maxRecDepth 4096 in
theorem inputB_search : generalMentsuHandMinimumSearch fixedB standing = some 0 := by
  decide

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

set_option maxRecDepth 4096 in
example : generalMentsuHandMinimumSearch fixedKan
    { counts := fun tile => if tile = white then 1 else 0, fixedMelds := 4 } = some 0 := by
  decide

example : ¬ ValidHand (List.replicate 2 (.kan east))
    { counts := fun _ => 0, fixedMelds := 2 } := by
  unfold ValidHand
  decide

def fourteenStanding : Hand := drawHand standing white

private lemma fourteenA_valid : IsFourteenTileEquivalentHand fixedA fourteenStanding := by
  unfold IsFourteenTileEquivalentHand ValidHand
  decide

private lemma fourteenB_valid : IsFourteenTileEquivalentHand fixedB fourteenStanding := by
  unfold IsFourteenTileEquivalentHand ValidHand
  decide

set_option maxRecDepth 4096 in
theorem fourteenA_search :
    generalMentsuHandMinimumSearch fixedA fourteenStanding = some 0 ∧
      minimumDiscardSearch fixedA fourteenStanding = some 0 ∧
      optimalDiscards fixedA fourteenStanding = {east} := by
  decide

set_option maxRecDepth 4096 in
theorem fourteenB_search :
    generalMentsuHandMinimumSearch fixedB fourteenStanding = some 0 ∧
      optimalDiscards fixedB fourteenStanding = {east, white} := by
  decide

example : IsShapeShanten fixedA fourteenStanding .mentsuHand 0 :=
  (generalMentsuHandMinimumSearch_eq_some_iff_of_fourteen fourteenA_valid 0).mp
    fourteenA_search.1

example : IsShapeShanten fixedB fourteenStanding .mentsuHand 0 :=
  (generalMentsuHandMinimumSearch_eq_some_iff_of_fourteen fourteenB_valid 0).mp
    fourteenB_search.1

set_option maxRecDepth 4096 in
theorem fourteenComplete_search :
    generalMentsuHandMinimumSearch fixedB (drawHand standing east) = some (-1) ∧
      minimumDiscardSearch fixedB (drawHand standing east) = some 0 := by
  decide

set_option maxRecDepth 4096 in
example :
    (south, 0) ∉ discardSearchResults fixedA fourteenStanding := by
  decide

def blockedFixed : List FixedMeld :=
  [ .meld (.koutsu east), .meld (.koutsu south)
  , .meld (.shuntsu ⟨.man, ⟨0, by omega⟩⟩), .meld (.shuntsu ⟨.pin, ⟨0, by omega⟩⟩) ]

set_option maxRecDepth 4096 in
theorem fourteenBlocked_search :
    let hand := drawHand standing south
    IsFourteenTileEquivalentHand blockedFixed hand ∧
      generalMentsuHandMinimumSearch blockedFixed hand = some 1 ∧
      minimumDiscardSearch blockedFixed hand = some 1 ∧
      optimalDiscards blockedFixed hand = {east, south} := by
  unfold IsFourteenTileEquivalentHand ValidHand
  decide

set_option maxRecDepth 4096 in
example :
    let hand := drawHand (discardHand fourteenStanding east) white
    IsFourteenTileEquivalentHand fixedKan hand ∧
      generalMentsuHandMinimumSearch fixedKan hand = some (-1) := by
  unfold IsFourteenTileEquivalentHand ValidHand
  decide

def sevenPairsReady : Hand :=
  { counts := fun tile => match tile with
      | .honor rank => if rank.val = 6 then 1 else 2
      | .suited _ _ => 0
    fixedMelds := 0 }

def sevenPairsQuads : Hand :=
  { counts := fun tile => match tile with
      | .honor rank => if rank.val < 3 then 4 else if rank.val = 3 then 1 else 0
      | .suited _ _ => 0
    fixedMelds := 0 }

example :
    pairCount sevenPairsQuads = 3 ∧
      Pair.remainingCounts sevenPairsQuads.counts ⟨east⟩ east = 2 ∧
      remainingCapacity fixedKan east = 0 := by
  decide

example :
    Pair.remainingCounts (fun tile => if tile = east then 3 else 0) ⟨east⟩ east = 1 := by
  decide

theorem sevenPairsFormula_search :
    IsThirteenTileEquivalentHand [] sevenPairsReady ∧
      sevenPairsSearch sevenPairsReady = some 0 ∧
      IsFourteenTileEquivalentHand [] (drawHand sevenPairsReady (.honor ⟨6, by omega⟩)) ∧
      sevenPairsSearch (drawHand sevenPairsReady (.honor ⟨6, by omega⟩)) = some (-1) := by
  unfold IsThirteenTileEquivalentHand IsFourteenTileEquivalentHand ValidHand
  decide

theorem sevenPairsQuads_search :
    IsThirteenTileEquivalentHand [] sevenPairsQuads ∧
      sevenPairsSearch sevenPairsQuads = some 6 ∧
      IsFourteenTileEquivalentHand [] (drawHand sevenPairsQuads (.honor ⟨3, by omega⟩)) ∧
      sevenPairsSearch (drawHand sevenPairsQuads (.honor ⟨3, by omega⟩)) = some 5 := by
  unfold IsThirteenTileEquivalentHand IsFourteenTileEquivalentHand ValidHand
  decide

example : IsShapeShanten [] sevenPairsQuads .sevenPairs 6 :=
  (sevenPairsSearch_eq_some_iff sevenPairsQuads_search.1.1
    (Or.inl sevenPairsQuads_search.1.2)).mp sevenPairsQuads_search.2.1

example : IsShapeShanten [] (drawHand sevenPairsQuads (.honor ⟨3, by omega⟩))
    .sevenPairs 5 :=
  (sevenPairsSearch_eq_some_iff sevenPairsQuads_search.2.2.1.1
    (Or.inr sevenPairsQuads_search.2.2.1.2)).mp sevenPairsQuads_search.2.2.2

def kokushiReady : Hand :=
  { counts := fun tile => if tile ∈ orphanKinds then 1 else 0
    fixedMelds := 0 }

def kokushiTriple : Hand :=
  { counts := fun tile =>
      if tile = east then 3
      else if tile ∈ orphanKinds ∧ tile ≠ south then 1 else 0
    fixedMelds := 0 }

def kokushiNonOrphanPair : Hand :=
  { counts := fun tile =>
      if tile = .suited .man ⟨1, by omega⟩ then 2
      else if tile ∈ orphanKinds ∧ tile ≠ east ∧ tile ≠ south then 1 else 0
    fixedMelds := 0 }

theorem kokushiFormula_search :
    IsThirteenTileEquivalentHand [] kokushiReady ∧
      thirteenOrphansSearch kokushiReady = some 0 ∧
      IsFourteenTileEquivalentHand [] (drawHand kokushiReady east) ∧
      thirteenOrphansSearch (drawHand kokushiReady east) = some (-1) ∧
      IsFourteenTileEquivalentHand [] kokushiTriple ∧
      thirteenOrphansSearch kokushiTriple = some 0 := by
  unfold IsThirteenTileEquivalentHand IsFourteenTileEquivalentHand ValidHand
  decide

theorem kokushiNonOrphanPair_search :
    IsThirteenTileEquivalentHand [] kokushiNonOrphanPair ∧
      thirteenOrphansSearch kokushiNonOrphanPair = some 2 ∧
      thirteenOrphansSearch kokushiWorstCase = some 13 ∧
      IsFourteenTileEquivalentHand []
        (drawHand kokushiWorstCase (.suited .man ⟨1, by omega⟩)) ∧
      thirteenOrphansSearch
        (drawHand kokushiWorstCase (.suited .man ⟨1, by omega⟩)) = some 13 := by
  unfold IsThirteenTileEquivalentHand IsFourteenTileEquivalentHand ValidHand
  decide

example : IsShapeShanten [] kokushiNonOrphanPair .thirteenOrphans 2 :=
  (thirteenOrphansSearch_eq_some_iff kokushiNonOrphanPair_search.1.1
    (Or.inl kokushiNonOrphanPair_search.1.2)).mp kokushiNonOrphanPair_search.2.1

example : IsShapeShanten [] (drawHand kokushiReady east) .thirteenOrphans (-1) :=
  (thirteenOrphansSearch_eq_some_iff kokushiFormula_search.2.2.1.1
    (Or.inr kokushiFormula_search.2.2.1.2)).mp kokushiFormula_search.2.2.2.1

def specialKanStanding : Hand :=
  { counts := fun tile =>
      if tile = south ∨ tile = .honor ⟨2, by omega⟩ then 4
      else if tile = .honor ⟨3, by omega⟩ then 2 else 0
    fixedMelds := 1 }

example :
    sevenPairsSearch standing = none ∧ thirteenOrphansSearch standing = none ∧
      IsThirteenTileEquivalentHand [.kan east] specialKanStanding ∧
      sevenPairsSearch specialKanStanding = none ∧
      thirteenOrphansSearch specialKanStanding = none := by
  unfold IsThirteenTileEquivalentHand ValidHand
  decide

theorem overallFixed_search :
    overallMinimumSearch fixedA standing = some 1 ∧
      overallMinimumSearch fixedB standing = some 0 ∧
      overallMinimumSearch blockedFixed (drawHand standing south) = some 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [overallMinimumSearch_of_fixed (by decide : standing.fixedMelds ≠ 0)]
    exact inputA_search
  · rw [overallMinimumSearch_of_fixed (by decide : standing.fixedMelds ≠ 0)]
    exact inputB_search
  · rw [overallMinimumSearch_of_fixed
      (by decide : (drawHand standing south).fixedMelds ≠ 0)]
    exact fourteenBlocked_search.2.1

def overallMentsuComplete : Hand :=
  { counts := fun tile => match tile with
      | .honor rank => if rank.val < 4 then 3 else if rank.val = 4 then 2 else 0
      | .suited _ _ => 0
    fixedMelds := 0 }

theorem overallMentsuComplete_search :
    IsFourteenTileEquivalentHand [] overallMentsuComplete ∧
      sevenPairsSearch overallMentsuComplete = some 3 ∧
      thirteenOrphansSearch overallMentsuComplete = some 7 ∧
      overallMinimumSearch [] overallMentsuComplete = some (-1) := by
  have hvalid : IsFourteenTileEquivalentHand [] overallMentsuComplete := by
    unfold IsFourteenTileEquivalentHand ValidHand
    decide
  refine ⟨hvalid, by decide, by decide, ?_⟩
  apply (overallMinimumSearch_eq_neg_one_iff hvalid.1 (Or.inr hvalid.2)).mpr
  refine ⟨.mentsuHand, hvalid.1, hvalid.1.validCounts, white,
    [ .koutsu east, .koutsu south, .koutsu (.honor ⟨2, by omega⟩),
      .koutsu (.honor ⟨3, by omega⟩) ], by decide, ?_⟩
  unfold HasTiles
  decide

theorem overallSpecialComplete_search :
    overallMinimumSearch [] (drawHand sevenPairsReady (.honor ⟨6, by omega⟩)) = some (-1) ∧
      thirteenOrphansSearch (drawHand sevenPairsReady (.honor ⟨6, by omega⟩)) = some 5 ∧
      overallMinimumSearch [] (drawHand kokushiReady east) = some (-1) ∧
      sevenPairsSearch (drawHand kokushiReady east) = some 5 := by
  have hseven := sevenPairsFormula_search.2.2.1
  have horphans := kokushiFormula_search.2.2.1
  refine ⟨?_, by decide, ?_, by decide⟩
  · apply (overallMinimumSearch_eq_some_iff hseven.1 (Or.inr hseven.2)).mpr
    exact ⟨⟨.sevenPairs,
      (sevenPairsSearch_eq_some_iff hseven.1 (Or.inr hseven.2)).mp
        sevenPairsFormula_search.2.2.2⟩,
      fun _ _ hother => hother.neg_one_le⟩
  · apply (overallMinimumSearch_eq_some_iff horphans.1 (Or.inr horphans.2)).mpr
    exact ⟨⟨.thirteenOrphans,
      (thirteenOrphansSearch_eq_some_iff horphans.1 (Or.inr horphans.2)).mp
        kokushiFormula_search.2.2.2.1⟩,
      fun _ _ hother => hother.neg_one_le⟩

end Shanten.Capacity.Examples
