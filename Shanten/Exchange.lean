import Shanten.Specification
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Shared exchanges

Shape-independent count deficits, tile exchanges, and finite step chains.
-/

namespace Shanten

/-- The number of tiles still missing from a target count vector. -/
def countDeficit (current target : TileCounts) : Nat :=
  ∑ tile : Tile, (target tile - current tile)

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

/-- A chain consisting only of draw-and-discard exchanges. -/
inductive ReachesExchange : Hand → Hand → Nat → Prop
  | done {hand} : ReachesExchange hand hand 0
  | step {hand next target distance} :
      HandStep hand next →
      ReachesExchange next target distance →
      ReachesExchange hand target (distance + 1)

lemma ReachesExchange.append
    (hfirst : ReachesExchange before middle distance₁)
    (hsecond : ReachesExchange middle after distance₂) :
    ReachesExchange before after (distance₁ + distance₂) := by
  induction hfirst with
  | done =>
      simpa using hsecond
  | step hstep hrest ih =>
      have hcombined := ih hsecond
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ReachesExchange.step hstep hcombined

lemma ReachesExchange.toReachesCompletion
    (hfirst : ReachesExchange before middle distance₁)
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
An exchange directed at a fixed target count vector.  The drawn kind is
deficient at the target, while the discarded kind is strictly in surplus.
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

end Shanten
