import Shanten.Specification
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Shared exchanges

Shape-independent count deficits, tile exchanges, and fixed-target reachability.
-/

namespace Shanten

/-- The number of tiles still missing from a target count vector. -/
def countDeficit (current target : TileCounts) : Nat :=
  ∑ tile : Tile, (target tile - current tile)

private lemma countDeficit_eq_succ_of_pointwise
    (current next target : TileCounts) (drawn : Tile)
    (hpoint : ∀ tile, target tile - current tile =
      target tile - next tile + (if tile = drawn then 1 else 0)) :
    countDeficit current target = countDeficit next target + 1 := by
  unfold countDeficit
  simp_rw [hpoint]
  simp [Finset.sum_add_distrib]

/--
For count vectors with the same total, `countDeficit` is exactly the number
of exchanges needed when each exchange replaces one tile kind by another.
-/
def exchangeDistance (hand : Hand) (target : TileCounts) : Nat :=
  countDeficit hand.counts target

/-- The count vector obtained by drawing `drawn` and discarding `discarded`. -/
def exchangeCounts (hand : Hand) (discarded drawn : Tile) : TileCounts :=
  fun tile =>
    hand.counts tile + (if tile = drawn then 1 else 0) -
      (if tile = discarded then 1 else 0)

def exchangeHand (hand : Hand) (discarded drawn : Tile) : Hand :=
  { counts := exchangeCounts hand discarded drawn
    fixedMelds := hand.fixedMelds }

lemma exchangeCounts_step
    (hand : Hand) (discarded drawn : Tile)
    (hne : discarded ≠ drawn) (hdiscarded : hand.counts discarded > 0) :
    ∀ tile,
      exchangeCounts hand discarded drawn tile +
          (if tile = discarded then 1 else 0) =
        hand.counts tile + (if tile = drawn then 1 else 0) := by
  intro tile
  by_cases hdiscard : tile = discarded
  · subst tile
    simp [exchangeCounts, hne, Ne.symm hne]
    omega
  · by_cases hdrawn : tile = drawn
    · subst tile
      simp [exchangeCounts, hdiscard]
    · simp [exchangeCounts, hdiscard, hdrawn]

lemma exchangeHand_step
    (hand : Hand) (discarded drawn : Tile)
    (hne : discarded ≠ drawn) (hdiscarded : hand.counts discarded > 0) :
    HandStep hand (exchangeHand hand discarded drawn) := by
  refine ⟨rfl, Or.inr ⟨discarded, drawn, hne, hdiscarded, ?_⟩⟩
  exact exchangeCounts_step hand discarded drawn hne hdiscarded

lemma exchangeCounts_drawn
    (hand : Hand) (discarded drawn : Tile) (hne : discarded ≠ drawn) :
    exchangeCounts hand discarded drawn drawn = hand.counts drawn + 1 := by
  simp [exchangeCounts, hne, Ne.symm hne]

lemma exchangeCounts_discarded
    (hand : Hand) (discarded drawn : Tile) (hne : discarded ≠ drawn)
    (hpositive : hand.counts discarded > 0) :
    exchangeCounts hand discarded drawn discarded =
      hand.counts discarded - 1 := by
  simp [exchangeCounts, hne]

lemma exchangeCounts_other
    (hand : Hand) (discarded drawn tile : Tile)
    (hdiscarded : tile ≠ discarded) (hdrawn : tile ≠ drawn) :
    exchangeCounts hand discarded drawn tile = hand.counts tile := by
  simp [exchangeCounts, hdiscarded, hdrawn]

lemma validCounts_exchangeHand
    (hvalid : ValidCounts hand) (hdrawn : hand.counts drawn < 4)
    (hne : discarded ≠ drawn) (hdiscarded : hand.counts discarded > 0) :
    ValidCounts (exchangeHand hand discarded drawn) := by
  intro tile
  by_cases hdrawn' : tile = drawn
  · subst tile
    change exchangeCounts hand discarded drawn drawn ≤ 4
    rw [exchangeCounts_drawn]
    · omega
    · exact hne
  · by_cases hdiscarded' : tile = discarded
    · subst tile
      change exchangeCounts hand discarded drawn discarded ≤ 4
      rw [exchangeCounts_discarded]
      · have hbefore := hvalid discarded
        omega
      · exact hne
      · exact hdiscarded
    · change exchangeCounts hand discarded drawn tile ≤ 4
      rw [exchangeCounts_other]
      · exact hvalid tile
      · exact hdiscarded'
      · exact hdrawn'

/-- Exactly the given number of draws or exchanges, ending at a fixed hand. -/
inductive ReachesHand : Hand → Hand → Nat → Prop
  | done {hand} : ReachesHand hand hand 0
  | step {hand next target distance} :
      HandStep hand next →
      ReachesHand next target distance →
      ReachesHand hand target (distance + 1)

lemma ReachesHand.append
    (hfirst : ReachesHand before middle distance₁)
    (hsecond : ReachesHand middle after distance₂) :
    ReachesHand before after (distance₁ + distance₂) := by
  induction hfirst with
  | done =>
      simpa using hsecond
  | step hstep hrest ih =>
      have hcombined := ih hsecond
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ReachesHand.step hstep hcombined

lemma ReachesHand.toReachesCompletion
    (hfirst : ReachesHand before middle distance₁)
    (hsecond : ReachesCompletion complete shape middle distance₂) :
    ReachesCompletion complete shape before (distance₁ + distance₂) := by
  induction hfirst with
  | done =>
      simpa using hsecond
  | step hstep hrest ih =>
      have hcombined := ih hsecond
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ReachesCompletion.step hstep hcombined

/--
An exchange directed at a fixed target count vector. The drawn kind is
deficient in the current hand relative to the target, while the discarded
kind is strictly in surplus.
-/
def TargetExchange (target : TileCounts) (before after : Hand) : Prop :=
  ∃ discarded drawn,
    target drawn > before.counts drawn ∧
      before.counts discarded > target discarded ∧
      discarded ≠ drawn ∧
      after = exchangeHand before discarded drawn

lemma TargetExchange.handStep
    (h : TargetExchange target before after) : HandStep before after := by
  rcases h with ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩
  exact exchangeHand_step before discarded drawn hne (by omega)

lemma deficit_after_drawing
    (target : TileCounts) (hand : Hand) (discarded drawn : Tile)
    (hne : discarded ≠ drawn) (hdeficit : hand.counts drawn < target drawn) :
    target drawn - exchangeCounts hand discarded drawn drawn =
      target drawn - hand.counts drawn - 1 := by
  simp [exchangeCounts, hne, Ne.symm hne]
  omega

lemma deficit_after_discarding
    (target : TileCounts) (hand : Hand) (discarded drawn : Tile)
    (hne : discarded ≠ drawn)
    (hsurplus : target discarded < hand.counts discarded) :
    target discarded - exchangeCounts hand discarded drawn discarded =
      target discarded - hand.counts discarded := by
  simp [exchangeCounts, hne]
  omega

lemma deficit_unchanged
    (target : TileCounts) (hand : Hand) (discarded drawn tile : Tile)
    (hdiscarded : tile ≠ discarded) (hdrawn : tile ≠ drawn) :
    target tile - exchangeCounts hand discarded drawn tile =
      target tile - hand.counts tile := by
  simp [exchangeCounts, hdiscarded, hdrawn]

lemma exists_lt_of_sum_eq_of_ne
    (current target : TileCounts)
    (hsum : (∑ tile : Tile, current tile) =
      ∑ tile : Tile, target tile)
    (hne : current ≠ target) :
    ∃ tile, current tile < target tile := by
  by_contra hexists
  push_neg at hexists
  have hle : ∀ tile, target tile ≤ current tile := by
    intro tile
    exact hexists tile
  have heq :
      ∀ tile ∈ (Finset.univ : Finset Tile), target tile = current tile := by
    apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := target) (g := current) (fun tile _ => hle tile)).mp
    exact hsum.symm
  apply hne
  funext tile
  exact (heq tile (Finset.mem_univ tile)).symm

lemma exists_target_exchange_tiles
    (before : Hand) (target : TileCounts)
    (hsum : (∑ tile : Tile, before.counts tile) =
      ∑ tile : Tile, target tile)
    (hne : before.counts ≠ target) :
    ∃ discarded drawn,
      target drawn > before.counts drawn ∧
      before.counts discarded > target discarded ∧
      discarded ≠ drawn := by
  obtain ⟨drawn, hdrawn⟩ :=
    exists_lt_of_sum_eq_of_ne before.counts target hsum hne
  obtain ⟨discarded, hdiscarded⟩ :=
    exists_lt_of_sum_eq_of_ne target before.counts hsum.symm
      (Ne.symm hne)
  refine ⟨discarded, drawn, hdrawn, hdiscarded, ?_⟩
  intro heq
  subst discarded
  omega

lemma targetExchange_exists_of_equal_sum
    (before : Hand) (target : TileCounts)
    (hsum : (∑ tile : Tile, before.counts tile) =
      ∑ tile : Tile, target tile)
    (hne : before.counts ≠ target) :
    ∃ after, TargetExchange target before after := by
  obtain ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles⟩ :=
    exists_target_exchange_tiles before target hsum hne
  refine ⟨exchangeHand before discarded drawn, ?_⟩
  exact ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles, rfl⟩

lemma exchangeCounts_sum
    (before : Hand) (discarded drawn : Tile)
    (hne : discarded ≠ drawn) (hdiscarded : before.counts discarded > 0) :
    (∑ tile : Tile, exchangeCounts before discarded drawn tile) =
      ∑ tile : Tile, before.counts tile := by
  have hstep := exchangeCounts_step before discarded drawn hne hdiscarded
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
  omega

lemma countDeficit_exchange
    (target : TileCounts) (before : Hand) (discarded drawn : Tile)
    (hdrawn : target drawn > before.counts drawn)
    (hdiscarded : before.counts discarded > target discarded)
    (hne : discarded ≠ drawn) :
    countDeficit (exchangeHand before discarded drawn).counts target =
      countDeficit before.counts target - 1 := by
  have hdecrease : countDeficit before.counts target =
      countDeficit (exchangeHand before discarded drawn).counts target + 1 := by
    apply countDeficit_eq_succ_of_pointwise (drawn := drawn)
    intro tile
    change target tile - before.counts tile =
      target tile - exchangeCounts before discarded drawn tile +
        (if tile = drawn then 1 else 0)
    by_cases htileDrawn : tile = drawn
    · subst tile
      rw [deficit_after_drawing target before discarded drawn hne hdrawn]
      simp
      omega
    · simp only [if_neg htileDrawn, Nat.add_zero]
      by_cases htileDiscarded : tile = discarded
      · subst tile
        exact (deficit_after_discarding target before discarded drawn
          hne hdiscarded).symm
      · exact (deficit_unchanged target before discarded drawn tile
          htileDiscarded htileDrawn).symm
  omega

lemma countDeficit_handStep_le
    (before after : Hand) (target : TileCounts)
    (hstep : HandStep before after) :
    countDeficit before.counts target ≤
      countDeficit after.counts target + 1 := by
  have finish (drawn : Tile)
      (hpoint : ∀ tile,
        target tile - before.counts tile ≤
          target tile - after.counts tile +
            (if tile = drawn then 1 else 0)) :
      countDeficit before.counts target ≤
        countDeficit after.counts target + 1 := by
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun tile _ => hpoint tile)
    calc
      countDeficit before.counts target =
          ∑ tile : Tile, (target tile - before.counts tile) := rfl
      _ ≤ ∑ tile : Tile,
          (target tile - after.counts tile +
            (if tile = drawn then 1 else 0)) := hsum
      _ = countDeficit after.counts target + 1 := by
        simp [countDeficit, Finset.sum_add_distrib]
  rcases hstep.2 with ⟨drawn, _, hcounts⟩ |
    ⟨discarded, drawn, hne, hpositive, hcounts⟩
  · apply finish drawn
    intro tile
    have hcount := hcounts tile
    by_cases hdrawn : tile = drawn
    · subst tile
      simp at hcount
      simp
      omega
    · simp [hdrawn] at hcount
      simp [hdrawn]
      omega
  · apply finish drawn
    intro tile
    by_cases hdiscarded : tile = discarded
    · subst tile
      have hcount := hcounts discarded
      simp [hne] at hcount
      simp [hne]
      omega
    · by_cases hdrawn : tile = drawn
      · subst tile
        have hcount := hcounts drawn
        simp [hne, Ne.symm hne] at hcount
        simp [hne, Ne.symm hne]
        omega
      · have hcount := hcounts tile
        simp [hdiscarded, hdrawn] at hcount
        simp [hdrawn]
        omega

def targetHand (before : Hand) (target : TileCounts) : Hand :=
  { counts := target
    fixedMelds := before.fixedMelds }

def countsOfTiles (tiles : Multiset Tile) : TileCounts :=
  fun tile => tiles.count tile

lemma countDeficit_draw
    (before : Hand) (target : TileCounts) (drawn : Tile)
    (hdrawn : target drawn > before.counts drawn) :
    countDeficit
        (fun tile =>
          before.counts tile + (if tile = drawn then 1 else 0))
        target + 1 =
      countDeficit before.counts target := by
  symm
  apply countDeficit_eq_succ_of_pointwise (drawn := drawn)
  intro tile
  by_cases htile : tile = drawn
  · subst tile
    simp
    omega
  · simp [htile]

lemma targetHand_hasTiles_countsOfTiles
    (before : Hand) (tiles : Multiset Tile) :
    HasTiles (targetHand before (countsOfTiles tiles)) tiles := by
  intro tile
  rfl

lemma countsOfTiles_sum_eq_card (tiles : Multiset Tile) :
    (∑ tile : Tile, countsOfTiles tiles tile) = tiles.card := by
  induction tiles using Multiset.induction_on with
  | empty =>
      simp [countsOfTiles]
  | @cons tile tiles ih =>
      simp [countsOfTiles, ih, Finset.sum_add_distrib]

lemma reachesHand_targetHand_of_equal_sum
    (before : Hand) (target : TileCounts)
    (hsum : (∑ tile : Tile, before.counts tile) =
      ∑ tile : Tile, target tile) :
    ∃ distance,
      distance = countDeficit before.counts target ∧
      ReachesHand before (targetHand before target) distance := by
  have aux : ∀ d : Nat, ∀ current : Hand,
      (∑ tile : Tile, current.counts tile) =
        ∑ tile : Tile, target tile →
      countDeficit current.counts target = d →
      ∃ distance,
        distance = d ∧
        ReachesHand current (targetHand current target) distance := by
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih current hsumCurrent hmeasure
    by_cases hd : d = 0
    · have hsumzero :
          (∑ tile : Tile, (target tile - current.counts tile)) = 0 := by
        simpa [countDeficit, hd] using hmeasure
      have hzero :
          ∀ tile ∈ (Finset.univ : Finset Tile),
            target tile - current.counts tile = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg
          (fun tile _ => Nat.zero_le _)).mp
        exact hsumzero
      have hle : ∀ tile, target tile ≤ current.counts tile := by
        intro tile
        have hzeroTile := hzero tile (Finset.mem_univ tile)
        omega
      have heq :
          ∀ tile ∈ (Finset.univ : Finset Tile),
            target tile = current.counts tile := by
        apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
          (f := target) (g := current.counts)
          (fun tile _ => hle tile)).mp
        exact hsumCurrent.symm
      have hcounts : target = current.counts := by
        funext tile
        exact heq tile (Finset.mem_univ tile)
      subst hcounts
      refine ⟨0, ?_, ReachesHand.done⟩
      simp [countDeficit] at hmeasure
      omega
    · have hpositive : 0 < d := Nat.pos_of_ne_zero hd
      have hne : current.counts ≠ target := by
        intro hcounts
        subst hcounts
        apply hd
        simpa [countDeficit] using hmeasure.symm
      obtain ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles⟩ :=
        exists_target_exchange_tiles current target hsumCurrent hne
      let next := exchangeHand current discarded drawn
      have hsumAfter :
          (∑ tile : Tile, next.counts tile) =
            ∑ tile : Tile, target tile := by
        change (∑ tile : Tile, exchangeCounts current discarded drawn tile) =
          ∑ tile : Tile, target tile
        rw [exchangeCounts_sum current discarded drawn hneTiles
          (by omega)]
        exact hsumCurrent
      have hdefAfterEq :
          countDeficit next.counts target = d - 1 := by
        dsimp [next]
        rw [countDeficit_exchange target current discarded drawn
          hdrawn hdiscarded hneTiles, hmeasure]
      have hdefAfter : countDeficit next.counts target < d := by
        omega
      obtain ⟨distance, hdistanceRest, hrest⟩ := ih
        (countDeficit next.counts target) hdefAfter next
        hsumAfter rfl
      refine ⟨distance + 1, ?_, ?_⟩
      · omega
      · apply ReachesHand.step
        · exact exchangeHand_step current discarded drawn hneTiles (by omega)
        · simpa [next, targetHand, exchangeHand] using hrest
  exact aux (countDeficit before.counts target) before hsum rfl

lemma exists_complete_with_deficit_le
    (hreach : ReachesCompletion Complete shape before distance) :
    ∃ after, Complete shape after ∧
      after.fixedMelds = before.fixedMelds ∧
      countDeficit before.counts after.counts ≤ distance := by
  induction hreach with
  | done hcomplete =>
      exact ⟨_, hcomplete, rfl, by simp [countDeficit]⟩
  | @step before next distance hstep hrest ih =>
      obtain ⟨after, hcomplete, hfixed, hbound⟩ := ih
      refine ⟨after, hcomplete, hfixed.trans hstep.1.symm, ?_⟩
      have := countDeficit_handStep_le before next after.counts hstep
      omega

/-- A target with one extra tile is reachable in exactly its count deficit. -/
lemma reachesCompletion_of_one_more_target_tile
    (before : Hand) (target : TileCounts)
    (hsum : (∑ tile : Tile, target tile) =
      (∑ tile : Tile, before.counts tile) + 1)
    (hbeforeValid : ValidCounts before)
    (hcomplete : Complete shape (targetHand before target)) :
    ReachesCompletion Complete shape before
      (countDeficit before.counts target) := by
  have hvalid : ∀ tile, target tile ≤ 4 := hcomplete.validCounts
  have hdrawnExists : ∃ drawn, before.counts drawn < target drawn := by
    by_contra hnone
    push Not at hnone
    have := Finset.sum_le_sum (s := Finset.univ)
      (fun tile _ => hnone tile)
    omega
  obtain ⟨drawn, hdrawn⟩ := hdrawnExists
  let next : Hand :=
    { counts := fun tile =>
        before.counts tile + (if tile = drawn then 1 else 0)
      fixedMelds := before.fixedMelds }
  have hnextValid : ValidCounts next := by
    intro tile
    by_cases htile : tile = drawn
    · subst tile
      have := hvalid drawn
      simp [next]
      omega
    · simpa [next, htile] using hbeforeValid tile
  have hstep : HandStep before next :=
    ⟨rfl, Or.inl ⟨drawn, hnextValid, fun _ => rfl⟩⟩
  have hsumNext : (∑ tile : Tile, next.counts tile) =
      ∑ tile : Tile, target tile := by
    simpa [next, Finset.sum_add_distrib] using hsum.symm
  obtain ⟨distance, hdistance, hexchange⟩ :=
    reachesHand_targetHand_of_equal_sum next target hsumNext
  have hrest : ReachesCompletion Complete shape next distance := by
    simpa using hexchange.toReachesCompletion
      (ReachesCompletion.done (show Complete shape (targetHand next target) from
        hcomplete))
  have hdeficit : distance + 1 = countDeficit before.counts target := by
    rw [hdistance]
    exact countDeficit_draw before target drawn hdrawn
  rw [← hdeficit]
  exact ReachesCompletion.step hstep hrest

end Shanten
