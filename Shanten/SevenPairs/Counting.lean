module

public import Shanten.Specification
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Seven pairs / Counting

Filtered cardinalities, singleton and surplus witnesses, and thirteen-tile bounds.
-/

namespace Shanten

open MahjongDomain

lemma card_filter_eq_add_one_of
    {α : Type} [Fintype α] [DecidableEq α]
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (a : α) (hpa : ¬ p a) (hqa : q a)
    (hother : ∀ x, x ≠ a → (p x ↔ q x)) :
    (Finset.univ.filter q).card = (Finset.univ.filter p).card + 1 := by
  classical
  have hfilter :
      Finset.univ.filter q = insert a (Finset.univ.filter p) := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [hpa, hqa]
    · rw [Finset.mem_insert]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [hxa, hother x hxa]
  rw [hfilter, Finset.card_insert_of_notMem]
  · simp [hpa]

lemma card_filter_eq_of_iff
    {α : Type} [Fintype α] [DecidableEq α]
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ x, p x ↔ q x) :
    (Finset.univ.filter p).card = (Finset.univ.filter q).card := by
  have hfilter :
      Finset.univ.filter p = Finset.univ.filter q := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h x
  exact congrArg Finset.card hfilter

lemma tileCount_le_distinct_add_pairCount
    (hand : Hand) (hsmall : ∀ tile, hand.counts tile ≤ 2) :
    tileCount hand ≤ distinctTileCount hand + pairCount hand := by
  have hpoint :
      ∀ tile, hand.counts tile ≤
        (if 0 < hand.counts tile then 1 else 0) +
          (if 2 ≤ hand.counts tile then 1 else 0) := by
    intro tile
    by_cases hpositive : 0 < hand.counts tile
    · by_cases hpair : 2 ≤ hand.counts tile
      · simpa [hpositive, hpair] using hsmall tile
      · have hnotpair : ¬ 2 ≤ hand.counts tile := hpair
        simp [hpositive, hpair]
        omega
    · have hzero : hand.counts tile = 0 :=
        Nat.eq_zero_of_not_pos hpositive
      simp [hzero]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun tile _ => hpoint tile)
  calc
    tileCount hand ≤
        ∑ tile : Tile,
          ((if 0 < hand.counts tile then 1 else 0) +
            (if 2 ≤ hand.counts tile then 1 else 0)) := hsum
    _ = distinctTileCount hand + pairCount hand := by
      rw [Finset.sum_add_distrib]
      simp [distinctTileCount, pairCount, Finset.sum_filter,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma exists_singleton_kind_of_seven_kinds_lt_six_pairs
    (hand : Hand) (hdistinct : distinctTileCount hand = 7)
    (hpairs : pairCount hand < 6) :
    ∃ tile, hand.counts tile = 1 := by
  by_contra hnon
  have hno : ∀ tile, hand.counts tile ≠ 1 := by
    intro tile htile
    exact hnon ⟨tile, htile⟩
  have hiff : ∀ tile,
      (0 < hand.counts tile) ↔ 2 ≤ hand.counts tile := by
    intro tile
    constructor
    · intro hpositive
      have hno' := hno tile
      omega
    · intro hpair
      have hno' := hno tile
      omega
  have hcard :
      distinctTileCount hand = pairCount hand := by
    unfold distinctTileCount pairCount
    exact card_filter_eq_of_iff
      (fun tile => 0 < hand.counts tile)
      (fun tile => 2 ≤ hand.counts tile)
      hiff
  omega

lemma exists_singleton_kind_of_seven_kinds_six_pairs
    (hand : Hand) (hdistinct : distinctTileCount hand = 7)
    (hpairs : pairCount hand = 6) :
    ∃ tile, hand.counts tile = 1 := by
  by_contra hnon
  have hno : ∀ tile, hand.counts tile ≠ 1 := by
    intro tile htile
    exact hnon ⟨tile, htile⟩
  have hiff : ∀ tile,
      (0 < hand.counts tile) ↔ 2 ≤ hand.counts tile := by
    intro tile
    constructor
    · intro hpositive
      have hno' := hno tile
      omega
    · intro hpair
      omega
  have hcard :
      distinctTileCount hand = pairCount hand := by
    unfold distinctTileCount pairCount
    exact card_filter_eq_of_iff
      (fun tile => 0 < hand.counts tile)
      (fun tile => 2 ≤ hand.counts tile)
      hiff
  omega

lemma exists_surplus_kind_for_pairMaking
    (hand : Hand) (hcount : tileCount hand = 13)
    (hdistinct : distinctTileCount hand = 7)
    (hpairs : pairCount hand < 6) :
    ∃ tile, 3 ≤ hand.counts tile := by
  by_contra hsurplus
  push Not at hsurplus
  have hsmall : ∀ tile, hand.counts tile ≤ 2 := by
    intro tile
    have hnot := hsurplus tile
    omega
  have hbound := tileCount_le_distinct_add_pairCount hand hsmall
  omega

lemma two_mul_pairCount_le_tileCount (hand : Hand) :
    2 * pairCount hand ≤ tileCount hand := by
  have hpoint : ∀ tile, (if 2 ≤ hand.counts tile then 2 else 0) ≤
      hand.counts tile := by
    intro tile
    by_cases hpair : 2 ≤ hand.counts tile <;> simp [hpair] <;> omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun tile _ => hpoint tile)
  calc
    2 * pairCount hand =
        ∑ tile : Tile, (if 2 ≤ hand.counts tile then 2 else 0) := by
          rw [← Finset.sum_filter]
          simp [pairCount, Nat.mul_comm]
    _ ≤ tileCount hand := hsum

lemma pairCount_le_six_of_thirteen
    (hand : Hand) (h13 : IsThirteenTileHand hand) :
    pairCount hand ≤ 6 := by
  have hbound := two_mul_pairCount_le_tileCount hand
  have hcount := h13.2.1
  omega

lemma distinct_add_pairCount_le_tileCount
    (hand : Hand) :
    distinctTileCount hand + pairCount hand ≤ tileCount hand := by
  have hpoint : ∀ tile,
      (if 0 < hand.counts tile then 1 else 0) +
          (if 2 ≤ hand.counts tile then 1 else 0) ≤ hand.counts tile := by
    intro tile
    by_cases hpositive : 0 < hand.counts tile <;>
      by_cases hpair : 2 ≤ hand.counts tile <;>
      simp [hpositive, hpair] <;> omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun tile _ => hpoint tile)
  calc
    distinctTileCount hand + pairCount hand =
        ∑ tile : Tile,
          ((if 0 < hand.counts tile then 1 else 0) +
            (if 2 ≤ hand.counts tile then 1 else 0)) := by
              simp [distinctTileCount, pairCount, Finset.sum_add_distrib]
    _ ≤ tileCount hand := hsum

lemma seven_le_distinct_add_pairCount_of_thirteen
    (hand : Hand) (h13 : IsThirteenTileHand hand) :
    7 ≤ distinctTileCount hand + pairCount hand := by
  have hpoint : ∀ tile,
      hand.counts tile ≤
        (if 0 < hand.counts tile then 1 else 0) +
          3 * (if 2 ≤ hand.counts tile then 1 else 0) := by
    intro tile
    have hmax := h13.2.2 tile
    by_cases hpositive : 0 < hand.counts tile <;>
      by_cases hpair : 2 ≤ hand.counts tile <;>
      simp [hpositive, hpair] <;> omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun tile _ => hpoint tile)
  have hbound :
      tileCount hand ≤ distinctTileCount hand + 3 * pairCount hand := by
    calc
      tileCount hand ≤
          ∑ tile : Tile,
            ((if 0 < hand.counts tile then 1 else 0) +
              3 * (if 2 ≤ hand.counts tile then 1 else 0)) := hsum
      _ = distinctTileCount hand + 3 * pairCount hand := by
        rw [Finset.sum_add_distrib]
        have hpositive :
            (∑ tile : Tile, (if 0 < hand.counts tile then 1 else 0)) =
              distinctTileCount hand := by
          simp [distinctTileCount, Finset.sum_filter]
        have hpairs :
            (∑ tile : Tile, 3 * (if 2 ≤ hand.counts tile then 1 else 0)) =
              3 * pairCount hand := by
          rw [← Finset.mul_sum]
          rw [← Finset.sum_filter]
          simp [pairCount, Nat.mul_comm]
        rw [hpositive, hpairs]
  have hpair_le_distinct : pairCount hand ≤ distinctTileCount hand := by
    apply Finset.card_le_card
    intro tile htile
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at htile ⊢
    omega
  have hcount := h13.2.1
  omega

end Shanten
