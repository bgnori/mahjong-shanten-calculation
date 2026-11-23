import Shanten.Capacity.Specification
import Shanten.SevenPairsAndThirteenOrphans

/-!
# Capacity-aware special-shape calculations

Like the mentsu search, these calculators assume separately validated input.
Fixed melds (including kans) make either special shape inapplicable.
-/

namespace Shanten.Capacity

def sevenPairsSearch (hand : Hand) : Option Int :=
  if hand.fixedMelds = 0 then some (sevenPairsShanten hand) else none

def thirteenOrphansSearch (hand : Hand) : Option Int :=
  if hand.fixedMelds = 0 then some (kokushiShanten hand) else none

private theorem sevenPairsOrThirteenOrphansSearch_eq_some_iff
    (hvalid : ValidHand fixed hand)
    (hsize : tileCount hand + 3 * fixed.length = 13 ∨
      tileCount hand + 3 * fixed.length = 14)
    (happlicable : Applicable shape hand ↔ hand.fixedMelds = 0)
    (hformula : hand.fixedMelds = 0 → ValidCounts hand →
      (tileCount hand = 13 ∨ tileCount hand = 14) →
      Shanten.IsShapeShanten hand shape result) :
    (if hand.fixedMelds = 0 then some result else none) = some value ↔
      IsShapeShanten fixed hand shape value := by
  by_cases hfixed : hand.fixedMelds = 0
  · have hnil : fixed = [] := List.length_eq_zero_iff.mp (by have := hvalid.1; omega)
    subst fixed
    have hsize' : tileCount hand = 13 ∨ tileCount hand = 14 := by simpa using hsize
    have hspec := (isShapeShanten_nil_iff hvalid).mpr
      (hformula hfixed hvalid.validCounts hsize')
    simp only [hfixed, ite_true, Option.some.injEq]
    exact ⟨fun heq => heq ▸ hspec, fun h => isShapeShanten_unique hspec h⟩
  · constructor
    · intro h
      simp [hfixed] at h
    · intro h
      exact (hfixed (happlicable.mp h.1)).elim

theorem sevenPairsSearch_eq_some_iff
    (hvalid : ValidHand fixed hand)
    (hsize : tileCount hand + 3 * fixed.length = 13 ∨
      tileCount hand + 3 * fixed.length = 14) :
    sevenPairsSearch hand = some value ↔
      IsShapeShanten fixed hand .sevenPairs value :=
  sevenPairsOrThirteenOrphansSearch_eq_some_iff hvalid hsize Iff.rfl
    sevenPairsShanten_isShapeShanten

theorem thirteenOrphansSearch_eq_some_iff
    (hvalid : ValidHand fixed hand)
    (hsize : tileCount hand + 3 * fixed.length = 13 ∨
      tileCount hand + 3 * fixed.length = 14) :
    thirteenOrphansSearch hand = some value ↔
      IsShapeShanten fixed hand .thirteenOrphans value :=
  sevenPairsOrThirteenOrphansSearch_eq_some_iff hvalid hsize Iff.rfl
    kokushiShanten_isShapeShanten

theorem sevenPairsSearch_eq_none_iff :
    sevenPairsSearch hand = none ↔ ¬ Applicable .sevenPairs hand := by
  simp [sevenPairsSearch, Applicable]

theorem thirteenOrphansSearch_eq_none_iff :
    thirteenOrphansSearch hand = none ↔ ¬ Applicable .thirteenOrphans hand := by
  simp [thirteenOrphansSearch, Applicable]

end Shanten.Capacity
