import Shanten.SevenPairs
import Mathlib.Tactic.Convert

namespace Shanten

lemma reaches_sevenPairs_completion
    (hand : Hand) (h13 : IsThirteenTileHand hand) :
    ∃ distance : Nat, distance ≤ 7 ∧
      ReachesCompletion Complete .sevenPairs hand distance := by
  have hdistinct_le : distinctTileCount hand ≤ 13 := by
    have hcount := h13.2.1
    have hpoint : ∀ tile, (if 0 < hand.counts tile then 1 else 0) ≤
        hand.counts tile := by
      intro tile
      by_cases hpositive : 0 < hand.counts tile <;> simp [hpositive] <;>
        omega
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun tile _ => hpoint tile)
    have hbound : distinctTileCount hand ≤ tileCount hand := by
      calc
        distinctTileCount hand =
            ∑ tile : Tile, (if 0 < hand.counts tile then 1 else 0) := by
              simp [distinctTileCount, Finset.sum_filter]
        _ ≤ tileCount hand := hsum
    omega
  have hpairs : pairCount hand ≤ 6 :=
    pairCount_le_six_of_thirteen hand h13
  by_cases hsmall : distinctTileCount hand ≤ 7
  · obtain ⟨middle, hdistinctness, hmiddleDistinct⟩ :=
      reaches_seven_tile_kinds hand h13 hsmall
    have hmiddle13 :=
      ReachesDistinctness.isThirteenTileHand hdistinctness h13
    have hmiddlePairsEq : pairCount middle = pairCount hand :=
      ReachesDistinctness.pairCount hdistinctness rfl
    have hmiddlePairs : pairCount middle ≤ 6 :=
      pairCount_le_six_of_thirteen middle hmiddle13
    obtain ⟨final, hpairing, hfinalPairs⟩ :=
      reaches_six_pairs middle hmiddle13 hmiddleDistinct hmiddlePairs
    have hfinal13 :=
      ReachesPairMaking.isThirteenTileHand hpairing hmiddle13
    have hfinalDistinct :=
      ReachesPairMaking.distinctTileCount hpairing hmiddleDistinct
    have hfinalTenpai :=
      isSevenPairsTenpai_of_counts final hfinal13 hfinalDistinct
        (by simpa using hfinalPairs)
    have hdraw := reachesCompletion_of_sevenPairsTenpai final hfinal13
      hfinalTenpai
    have hexchanges :=
      ReachesDistinctness.toReachesHand hdistinctness
    have hpexchanges :=
      ReachesPairMaking.toReachesHand hpairing
    have hcombined := ReachesHand.append hexchanges hpexchanges
    have hcombined' := ReachesHand.toReachesCompletion hcombined hdraw
    have hlower := seven_le_distinct_add_pairCount_of_thirteen hand h13
    have hlower' : 7 ≤ distinctTileCount hand + pairCount middle := by
      omega
    refine ⟨_, ?_, hcombined'⟩
    omega
  · have hlarge : 7 ≤ distinctTileCount hand := by omega
    by_cases hpairslt : pairCount hand < 6
    · obtain ⟨protectedTiles, hcard, hprotected⟩ :=
        exists_protectedTiles hand hlarge hpairslt
      obtain ⟨final, hpairing, hfinalPairs⟩ :=
        reaches_six_pairs_protected_of_card protectedTiles hand h13
          hcard hprotected hpairs
      have hfinal13 :=
        ReachesProtectedPairMaking.isThirteenTileHand hpairing h13
      have hfinalProtected :=
        ReachesProtectedPairMaking.protectedInvariant hpairing hprotected
      have hfinalDistinct : distinctTileCount final = 7 := by
        have hge : 7 ≤ distinctTileCount final := by
          have hsubset :
              protectedTiles ⊆
                Finset.univ.filter (fun tile => 0 < final.counts tile) := by
            intro tile htile
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hfinalProtected.1 tile htile
          have := Finset.card_le_card hsubset
          simpa [distinctTileCount, hcard] using this
        have hle : distinctTileCount final ≤ 7 := by
          have hbound := distinct_add_pairCount_le_tileCount final
          have hcount := hfinal13.2.1
          rw [hfinalPairs] at hbound
          omega
        omega
      have hfinalTenpai :=
        isSevenPairsTenpai_of_counts final hfinal13 hfinalDistinct
          (by simpa using hfinalPairs)
      have hdraw := reachesCompletion_of_sevenPairsTenpai final hfinal13
        hfinalTenpai
      have hpexchanges :=
        ReachesProtectedPairMaking.toReachesHand hpairing
      have hcombined' := ReachesHand.toReachesCompletion hpexchanges hdraw
      refine ⟨_, ?_, hcombined'⟩
      omega
    · have hpairsEq : pairCount hand = 6 := by omega
      have hdistinctEq : distinctTileCount hand = 7 := by
        have hbound := distinct_add_pairCount_le_tileCount hand
        have hcount := h13.2.1
        rw [hpairsEq] at hbound
        omega
      obtain ⟨final, hpairing, hfinalPairs⟩ :=
        reaches_six_pairs hand h13 hdistinctEq (by omega)
      have hfinal13 :=
        ReachesPairMaking.isThirteenTileHand hpairing h13
      have hfinalDistinct : distinctTileCount final = 7 := by
        exact ReachesPairMaking.distinctTileCount hpairing hdistinctEq
      have hfinalTenpai :=
        isSevenPairsTenpai_of_counts final hfinal13 hfinalDistinct
          (by simpa using hfinalPairs)
      have hdraw := reachesCompletion_of_sevenPairsTenpai final hfinal13
        hfinalTenpai
      have hpexchanges :=
        ReachesPairMaking.toReachesHand hpairing
      have hcombined' := ReachesHand.toReachesCompletion hpexchanges hdraw
      refine ⟨1, by omega, ?_⟩
      convert hcombined' using 1 <;> omega

/--
The maximum shanten number of a thirteen-tile hand is at most six.  For the
seven-pairs argument, the relevant witness is a completion reachable in
distance seven: six exchanges create six pairs, and one final draw creates
the seventh pair.  Since shanten is distance minus one, this gives `6`.

The seven-pairs construction supplies the bound regardless of the other shapes.
-/
theorem overallShanten_le_six_of_thirteenTileHand
    (h13 : IsThirteenTileHand hand)
    (value : Int)
    (hvalue : IsOverallShanten hand value) :
    value ≤ 6 := by
  obtain ⟨bound, hbound, hreachable⟩ :=
    reaches_sevenPairs_completion hand h13
  obtain ⟨sevenPairsValue, hshape, hsevenPairsBound⟩ :=
    exists_isShapeShanten_of_reachesCompletion hreachable h13.1
  have hseven :
      ShapeShanten hand .sevenPairs = some sevenPairsValue :=
    (shapeShanten_eq_some_iff).2 hshape
  have hvalue' : OverallShanten hand = some value := hvalue
  unfold OverallShanten at hvalue'
  cases hmentsuHand : ShapeShanten hand .mentsuHand <;>
    cases hthirteen : ShapeShanten hand .thirteenOrphans <;>
    simp [hseven, hmentsuHand, hthirteen, minOption] at hvalue'
  case none.none =>
    omega
  case none.some =>
    have hle : value ≤ sevenPairsValue := by
      rw [← hvalue']
      exact min_le_left _ _
    omega
  case some.none =>
    have hle : value ≤ sevenPairsValue := by
      rw [← hvalue']
      exact min_le_right _ _
    omega
  case some.some =>
    have hle : value ≤ sevenPairsValue := by
      rw [← hvalue']
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    omega

/--
If a shape has a completion reachable in at most seven steps, then its
shape-specific shanten value is at most six.  This is the common bound used
by the three hand-shape arguments below; it does not use any comparison
between the three shapes.
-/
theorem shapeShanten_le_six_of_completion_bound
    (_happlicable : Applicable shape hand)
    (hbound : ∃ distance : Nat, distance ≤ 7 ∧
      ReachesCompletion Complete shape hand distance)
    (value : Int)
    (hvalue : IsShapeShanten hand shape value) :
    value ≤ 6 := by
  simpa using hvalue.le_of_completion_bound hbound

/--
If a shape has a completion reachable in at most nine steps, then its
shape-specific shanten value is at most eight.  In particular, the bound is
independent of how many fixed melds the hand has: fixed melds are preserved by
`HandStep` and are counted in `Complete .mentsuHand`.
-/
theorem mentsuHandShanten_le_eight_of_completion_bound
    (hand : Hand)
    (hbound : ∃ distance : Nat, distance ≤ 9 ∧
      ReachesCompletion Complete .mentsuHand hand distance)
    (value : Int)
    (hvalue : IsShapeShanten hand .mentsuHand value) :
    value ≤ 8 := by
  simpa using hvalue.le_of_completion_bound hbound

/-- With a fixed meld, only the mentsuHand shape contributes to overall shanten. -/
theorem overallShanten_le_eight_of_fixedMelds
    (hand : Hand)
    (hfixed : 0 < hand.fixedMelds)
    (hbound : ∃ distance : Nat, distance ≤ 9 ∧
      ReachesCompletion Complete .mentsuHand hand distance)
    (value : Int)
    (hvalue : IsOverallShanten hand value) :
    value ≤ 8 := by
  have hseven : ShapeShanten hand .sevenPairs = none := by
    unfold ShapeShanten
    split
    next h =>
      exfalso
      exact (by
        have happ : ¬ Applicable .sevenPairs hand := by
          simp [Applicable, Nat.ne_of_gt hfixed]
        exact happ (Classical.choose_spec h).1)
    next h => rfl
  have hthirteen : ShapeShanten hand .thirteenOrphans = none := by
    unfold ShapeShanten
    split
    next h =>
      exfalso
      exact (by
        have happ : ¬ Applicable .thirteenOrphans hand := by
          simp [Applicable, Nat.ne_of_gt hfixed]
        exact happ (Classical.choose_spec h).1)
    next h => rfl
  have hmentsuHand := hvalue
  unfold IsOverallShanten OverallShanten at hmentsuHand
  rw [hseven, hthirteen] at hmentsuHand
  cases hshape : ShapeShanten hand .mentsuHand with
  | none =>
      simp [hshape, minOption] at hmentsuHand
  | some mentsuHandValue =>
      have hmentsuHandValue :
          IsShapeShanten hand .mentsuHand mentsuHandValue :=
        (shapeShanten_eq_some_iff).1 hshape
      have hle := mentsuHandShanten_le_eight_of_completion_bound
        hand hbound mentsuHandValue hmentsuHandValue
      have hmentsuHand' : some mentsuHandValue = some value := by
        simpa [hshape, minOption] using hmentsuHand
      have heq : mentsuHandValue = value := Option.some.inj hmentsuHand'
      omega

/-- The seven-pairs component of the thirteen-tile upper bound. -/
theorem sevenPairsShanten_le_six_of_completion_bound
    (h13 : IsThirteenTileHand hand)
    (value : Int)
    (hvalue : IsShapeShanten hand .sevenPairs value) :
    value ≤ 6 := by
  apply shapeShanten_le_six_of_completion_bound
    (show Applicable .sevenPairs hand from h13.1)
    (reaches_sevenPairs_completion hand h13) value hvalue

/-- The mentsu-hand-form component of the thirteen-tile upper bound. -/
theorem mentsuHandShanten_le_six_of_completion_bound
    (happlicable : Applicable .mentsuHand hand)
    (hbound : ∃ distance : Nat, distance ≤ 7 ∧
      ReachesCompletion Complete .mentsuHand hand distance)
    (value : Int)
    (hvalue : IsShapeShanten hand .mentsuHand value) :
    value ≤ 6 := by
  apply shapeShanten_le_six_of_completion_bound
    happlicable hbound value hvalue

/-- The thirteen-orphans component of the thirteen-tile upper bound. -/
theorem thirteenOrphansShanten_le_six_of_completion_bound
    (happlicable : Applicable .thirteenOrphans hand)
    (hbound : ∃ distance : Nat, distance ≤ 7 ∧
      ReachesCompletion Complete .thirteenOrphans hand distance)
    (value : Int)
    (hvalue : IsShapeShanten hand .thirteenOrphans value) :
    value ≤ 6 := by
  apply shapeShanten_le_six_of_completion_bound
    happlicable hbound value hvalue

/-- No hand can exceed thirteen shanten for the thirteen-orphans shape. -/
theorem kokushiShanten_le_thirteen (hand : Hand) :
    kokushiShanten hand ≤ 13 := by
  unfold kokushiShanten
  split <;> omega

/-- The middle-tile example has the maximum thirteen-orphans shanten value. -/
theorem kokushiWorstCase_shanten :
    kokushiShanten kokushiWorstCase = 13 := by
  native_decide

end Shanten
