module

public import Shanten.Capacity.Fourteen
public import Shanten.Capacity.SevenPairsAndThirteenOrphans

@[expose] public section

/-!
# Overall capacity-aware calculation

The three existing shape calculators share one dispatch and one minimum.
Validity and thirteen- or fourteen-tile-equivalent size are separate prerequisites.
-/

namespace Shanten.Capacity

def shapeSearch (fixed : List FixedMeld) (hand : Hand) : Shape → Option Int
  | .mentsuHand => generalMentsuHandMinimumSearch fixed hand
  | .sevenPairs => sevenPairsSearch hand
  | .thirteenOrphans => thirteenOrphansSearch hand

def overallMinimumSearch (fixed : List FixedMeld) (hand : Hand) : Option Int :=
  minOption (shapeSearch fixed hand .mentsuHand)
    (minOption (shapeSearch fixed hand .sevenPairs) (shapeSearch fixed hand .thirteenOrphans))

theorem shapeSearch_eq_some_iff
    (hvalid : ValidHand fixed hand)
    (hsize : tileCount hand + 3 * fixed.length = 13 ∨
      tileCount hand + 3 * fixed.length = 14) (shape : Shape) :
    shapeSearch fixed hand shape = some value ↔ IsShapeShanten fixed hand shape value := by
  cases shape with
  | mentsuHand =>
      rcases hsize with h13 | h14
      · exact generalMentsuHandMinimumSearch_eq_some_iff ⟨hvalid, h13⟩ value
      · exact generalMentsuHandMinimumSearch_eq_some_iff_of_fourteen ⟨hvalid, h14⟩ value
  | sevenPairs => exact sevenPairsSearch_eq_some_iff hvalid hsize
  | thirteenOrphans => exact thirteenOrphansSearch_eq_some_iff hvalid hsize

theorem shapeSearch_eq_none_iff
    (hvalid : ValidHand fixed hand)
    (hsize : tileCount hand + 3 * fixed.length = 13 ∨
      tileCount hand + 3 * fixed.length = 14) (shape : Shape) :
    shapeSearch fixed hand shape = none ↔ ¬ Applicable shape hand := by
  cases shape with
  | mentsuHand =>
      obtain ⟨_, _, hresult, _, _⟩ :=
        exists_optimal_state_of_size hvalid hsize (generalMentsuHandStates_nonempty hvalid)
      simp [shapeSearch, hresult, Applicable]
  | sevenPairs => exact sevenPairsSearch_eq_none_iff
  | thirteenOrphans => exact thirteenOrphansSearch_eq_none_iff

private lemma minOption_eq_some_iff (left right : Option Int) :
    minOption left right = some value ↔
      (left = some value ∨ right = some value) ∧
        (∀ other, left = some other → value ≤ other) ∧
        (∀ other, right = some other → value ≤ other) := by
  cases left <;> cases right <;> simp [minOption, min_def] <;> omega

private lemma minimum_shapes_iff (search : Shape → Option Int) :
    minOption (search .mentsuHand)
        (minOption (search .sevenPairs) (search .thirteenOrphans)) = some value ↔
      (∃ shape, search shape = some value) ∧
        ∀ shape other, search shape = some other → value ≤ other := by
  constructor
  · rw [minOption_eq_some_iff]
    rintro ⟨hwitness, hmentsu, hsevenPairsAndOrphans⟩
    have hlower : ∀ shape other, search shape = some other → value ≤ other := by
      intro shape other hother
      cases shape with
      | mentsuHand => exact hmentsu _ hother
      | sevenPairs =>
          cases horphans : search .thirteenOrphans with
          | none => exact hsevenPairsAndOrphans _ (by simp [minOption, hother, horphans])
          | some orphans =>
              have := hsevenPairsAndOrphans (min other orphans)
                (by simp [minOption, hother, horphans])
              exact this.trans (min_le_left _ _)
      | thirteenOrphans =>
          cases hseven : search .sevenPairs with
          | none => exact hsevenPairsAndOrphans _ (by simp [minOption, hother, hseven])
          | some seven =>
              have := hsevenPairsAndOrphans (min seven other)
                (by simp [minOption, hother, hseven])
              exact this.trans (min_le_right _ _)
    refine ⟨?_, hlower⟩
    rcases hwitness with hm | hs
    · exact ⟨.mentsuHand, hm⟩
    · obtain ⟨hseven | horphans, _⟩ := (minOption_eq_some_iff _ _).mp hs
      · exact ⟨.sevenPairs, hseven⟩
      · exact ⟨.thirteenOrphans, horphans⟩
  · rintro ⟨⟨shape, hwitness⟩, hlower⟩
    apply (minOption_eq_some_iff _ _).mpr
    have hsevenPairsAndOrphans : ∀ other,
        minOption (search .sevenPairs) (search .thirteenOrphans) = some other →
          value ≤ other := by
      intro other hother
      obtain ⟨hseven | horphans, _⟩ := (minOption_eq_some_iff _ _).mp hother
      · exact hlower .sevenPairs _ hseven
      · exact hlower .thirteenOrphans _ horphans
    refine ⟨?_, hlower .mentsuHand, hsevenPairsAndOrphans⟩
    cases shape with
    | mentsuHand => exact Or.inl hwitness
    | sevenPairs =>
        exact Or.inr ((minOption_eq_some_iff _ _).mpr
          ⟨Or.inl hwitness, hlower .sevenPairs, hlower .thirteenOrphans⟩)
    | thirteenOrphans =>
        exact Or.inr ((minOption_eq_some_iff _ _).mpr
          ⟨Or.inr hwitness, hlower .sevenPairs, hlower .thirteenOrphans⟩)

theorem overallMinimumSearch_eq_some_iff
    (hvalid : ValidHand fixed hand)
    (hsize : tileCount hand + 3 * fixed.length = 13 ∨
      tileCount hand + 3 * fixed.length = 14) :
    overallMinimumSearch fixed hand = some value ↔ IsOverallShanten fixed hand value := by
  unfold overallMinimumSearch
  rw [minimum_shapes_iff]
  simp_rw [shapeSearch_eq_some_iff hvalid hsize]
  rfl

theorem overallMinimumSearch_exists_unique
    (hvalid : ValidHand fixed hand)
    (hsize : tileCount hand + 3 * fixed.length = 13 ∨
      tileCount hand + 3 * fixed.length = 14) :
    ∃! value : Int, overallMinimumSearch fixed hand = some value ∧
      IsOverallShanten fixed hand value := by
  obtain ⟨_, _, hmentsu, _, _⟩ :=
    exists_optimal_state_of_size hvalid hsize (generalMentsuHandStates_nonempty hvalid)
  have hexists : ∃ value, overallMinimumSearch fixed hand = some value := by
    unfold overallMinimumSearch shapeSearch
    rw [hmentsu]
    cases sevenPairsSearch hand <;> cases thirteenOrphansSearch hand <;>
      simp [minOption]
  obtain ⟨value, hvalue⟩ := hexists
  have hspec := (overallMinimumSearch_eq_some_iff hvalid hsize).mp hvalue
  exact ⟨value, ⟨hvalue, hspec⟩, fun _ h => isOverallShanten_unique h.2 hspec⟩

theorem overallMinimumSearch_of_fixed (hfixed : hand.fixedMelds ≠ 0) :
    overallMinimumSearch fixed hand = generalMentsuHandMinimumSearch fixed hand := by
  cases hresult : generalMentsuHandMinimumSearch fixed hand <;>
    simp [overallMinimumSearch, shapeSearch, sevenPairsSearch, thirteenOrphansSearch,
      hfixed, minOption, hresult]

theorem overallMinimumSearch_neg_one_le
    (hvalid : ValidHand fixed hand)
    (hsize : tileCount hand + 3 * fixed.length = 13 ∨
      tileCount hand + 3 * fixed.length = 14)
    (hresult : overallMinimumSearch fixed hand = some value) :
    -1 ≤ value :=
  ((overallMinimumSearch_eq_some_iff hvalid hsize).mp hresult).neg_one_le

theorem overallMinimumSearch_eq_neg_one_iff
    (hvalid : ValidHand fixed hand)
    (hsize : tileCount hand + 3 * fixed.length = 13 ∨
      tileCount hand + 3 * fixed.length = 14) :
    overallMinimumSearch fixed hand = some (-1) ↔ ∃ shape, Complete fixed shape hand := by
  rw [overallMinimumSearch_eq_some_iff hvalid hsize, isOverallShanten_neg_one_iff]

theorem overallMinimumSearch_nil
    (hvalid : ValidHand [] hand)
    (hsize : tileCount hand = 13 ∨ tileCount hand = 14) :
    overallMinimumSearch [] hand = Shanten.OverallShanten hand := by
  have hsize' : tileCount hand + 3 * ([] : List FixedMeld).length = 13 ∨
      tileCount hand + 3 * ([] : List FixedMeld).length = 14 := by simpa using hsize
  have hshape : ∀ shape, shapeSearch [] hand shape = Shanten.ShapeShanten hand shape := by
    intro shape
    cases hsearch : shapeSearch [] hand shape with
    | some value =>
        have hspec := (shapeSearch_eq_some_iff hvalid hsize' shape).mp hsearch
        exact (Shanten.shapeShanten_eq_some_iff.mpr
          ((isShapeShanten_nil_iff hvalid).mp hspec)).symm
    | none =>
        cases habstract : Shanten.ShapeShanten hand shape with
        | none => rfl
        | some value =>
            have hspec := (isShapeShanten_nil_iff hvalid).mpr
              (Shanten.shapeShanten_eq_some_iff.mp habstract)
            have := (shapeSearch_eq_some_iff hvalid hsize' shape).mpr hspec
            rw [hsearch] at this
            contradiction
  simp only [overallMinimumSearch, Shanten.OverallShanten, hshape]

end Shanten.Capacity
