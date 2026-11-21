import Shanten.Capacity.Basic
import Shanten.Specification

namespace Shanten.Capacity

open MahjongDomain

def Complete (fixed : List FixedMeld) (shape : Shape) (hand : Hand) : Prop :=
  ValidHand fixed hand ∧ Shanten.Complete shape hand

theorem Complete.mentsuHand_iff_standardCompletion :
    Complete fixed .mentsuHand hand ↔
      ValidHand fixed hand ∧
        MahjongDomain.StandardCompletion (4 - fixed.length)
          hand.counts := by
  constructor
  · rintro ⟨hvalid, hcomplete⟩
    obtain ⟨_, _, hcompletion⟩ :=
      Shanten.mentsuComplete_iff_standardCompletion hand |>.mp hcomplete
    have hlength : hand.fixedMelds = fixed.length := hvalid.1
    rw [hlength] at hcompletion
    exact ⟨hvalid, hcompletion⟩
  · rintro ⟨hvalid, hcompletion⟩
    have hfixed : hand.fixedMelds = fixed.length := hvalid.1
    have hbound : hand.fixedMelds ≤ 4 := by
      rw [hfixed]
      exact hvalid.2.1
    have hstandard :
        MahjongDomain.StandardCompletion (4 - hand.fixedMelds)
          hand.counts := by
      rw [hfixed]
      exact hcompletion
    exact ⟨hvalid, (Shanten.mentsuComplete_iff_standardCompletion hand).mpr
      ⟨hvalid.validCounts, hbound, hstandard⟩⟩

def HandStep (fixed : List FixedMeld) (before after : Hand) : Prop :=
  ValidHand fixed before ∧ Shanten.HandStep before after ∧ ValidHand fixed after

lemma HandStep.toAbstract (hstep : HandStep fixed before after) :
    Shanten.HandStep before after := hstep.2.1

lemma HandStep.validHand (hstep : HandStep fixed before after) :
    ValidHand fixed after := hstep.2.2

lemma drawHand_step
    (hvalid : ValidHand fixed hand)
    (hdrawn : hand.counts drawn < remainingCapacity fixed drawn) :
    HandStep fixed hand (drawHand hand drawn) := by
  have hafter := hvalid.draw hdrawn
  exact ⟨hvalid, ⟨rfl, Or.inl ⟨drawn, hafter.validCounts, fun _ => rfl⟩⟩, hafter⟩

lemma exchangeHand_step
    (hvalid : ValidHand fixed hand)
    (hne : discarded ≠ drawn) (hdiscarded : 0 < hand.counts discarded)
    (hdrawn : hand.counts drawn < remainingCapacity fixed drawn) :
    HandStep fixed hand (exchangeHand hand discarded drawn) := by
  have hafter := hvalid.exchange hne hdiscarded hdrawn
  have hcapacity : remainingCapacity fixed drawn ≤ 4 := Nat.sub_le _ _
  exact ⟨hvalid, Shanten.exchangeHand_step hand discarded drawn hne hdiscarded
    hvalid.validCounts (by omega), hafter⟩

inductive ReachesHand (fixed : List FixedMeld) : Hand → Hand → Nat → Prop
  | done {hand} : ValidHand fixed hand → ReachesHand fixed hand hand 0
  | step {hand next target distance} :
      HandStep fixed hand next →
      ReachesHand fixed next target distance →
      ReachesHand fixed hand target (distance + 1)

lemma ReachesHand.validHand (hreach : ReachesHand fixed before after distance) :
    ValidHand fixed after := by
  induction hreach with
  | done hvalid => exact hvalid
  | step _ _ ih => exact ih

lemma ReachesHand.toAbstract (hreach : ReachesHand fixed before after distance) :
    Shanten.ReachesHand before after distance := by
  induction hreach with
  | done _ => exact .done
  | step hstep _ ih => exact .step hstep.toAbstract ih

def ReachesCompletion (fixed : List FixedMeld) (shape : Shape)
    (hand : Hand) (distance : Nat) : Prop :=
  ∃ target, ReachesHand fixed hand target distance ∧ Complete fixed shape target

lemma ReachesCompletion.toAbstract
    (hreach : ReachesCompletion fixed shape hand distance) :
    Shanten.ReachesCompletion Shanten.Complete shape hand distance := by
  obtain ⟨target, hpath, hcomplete⟩ := hreach
  simpa using hpath.toAbstract.toReachesCompletion
    (Shanten.ReachesCompletion.done hcomplete.2)

lemma reachesCompletion_zero_iff :
    ReachesCompletion fixed shape hand 0 ↔ Complete fixed shape hand := by
  constructor
  · rintro ⟨_, hpath, hcomplete⟩
    cases hpath
    exact hcomplete
  · intro hcomplete
    exact ⟨hand, .done hcomplete.1, hcomplete⟩

lemma reachesCompletion_one_iff :
    ReachesCompletion fixed shape hand 1 ↔
      ∃ next, HandStep fixed hand next ∧ Complete fixed shape next := by
  constructor
  · rintro ⟨_, hpath, hcomplete⟩
    cases hpath with
    | step hstep hrest =>
        cases hrest
        exact ⟨_, hstep, hcomplete⟩
  · rintro ⟨next, hstep, hcomplete⟩
    exact ⟨next, .step hstep (.done hcomplete.1), hcomplete⟩

def IsShapeShanten (fixed : List FixedMeld)
    (hand : Hand) (shape : Shape) (value : Int) : Prop :=
  Applicable shape hand ∧
    ∃ distance : Nat,
      (distance : Int) = value + 1 ∧
      ReachesCompletion fixed shape hand distance ∧
      ∀ smaller : Nat, smaller < distance →
        ¬ ReachesCompletion fixed shape hand smaller

theorem isShapeShanten_unique
    (h₁ : IsShapeShanten fixed hand shape value₁)
    (h₂ : IsShapeShanten fixed hand shape value₂) :
    value₁ = value₂ := by
  obtain ⟨_, d₁, hv₁, hr₁, hm₁⟩ := h₁
  obtain ⟨_, d₂, hv₂, hr₂, hm₂⟩ := h₂
  have : d₁ = d₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hm₂ d₁ hlt hr₁
    · exact hm₁ d₂ hgt hr₂
  omega

/-- An attained minimum over the applicable shapes, independently of any calculator. -/
def IsOverallShanten (fixed : List FixedMeld) (hand : Hand) (value : Int) : Prop :=
  (∃ shape, IsShapeShanten fixed hand shape value) ∧
    ∀ shape other, IsShapeShanten fixed hand shape other → value ≤ other

theorem isOverallShanten_unique
    (h₁ : IsOverallShanten fixed hand value₁)
    (h₂ : IsOverallShanten fixed hand value₂) :
    value₁ = value₂ := by
  obtain ⟨shape₁, hs₁⟩ := h₁.1
  obtain ⟨shape₂, hs₂⟩ := h₂.1
  exact le_antisymm (h₁.2 shape₂ _ hs₂) (h₂.2 shape₁ _ hs₁)

lemma IsShapeShanten.neg_one_le (hvalue : IsShapeShanten fixed hand shape value) :
    -1 ≤ value := by
  obtain ⟨_, distance, hdistance, _⟩ := hvalue
  omega

lemma Complete.applicable (hcomplete : Complete fixed shape hand) :
    Applicable shape hand := by
  cases shape with
  | mentsuHand => trivial
  | sevenPairs => exact hcomplete.2.2.1
  | thirteenOrphans => exact hcomplete.2.2.1

theorem isShapeShanten_neg_one_iff :
    IsShapeShanten fixed hand shape (-1) ↔ Complete fixed shape hand := by
  constructor
  · rintro ⟨_, distance, hdistance, hreach, _⟩
    have : distance = 0 := by omega
    subst distance
    exact reachesCompletion_zero_iff.mp hreach
  · intro hcomplete
    exact ⟨hcomplete.applicable, 0, by omega, reachesCompletion_zero_iff.mpr hcomplete,
      fun smaller hsmaller => by omega⟩

lemma IsOverallShanten.neg_one_le (hvalue : IsOverallShanten fixed hand value) :
    -1 ≤ value := by
  obtain ⟨shape, hshape⟩ := hvalue.1
  exact hshape.neg_one_le

theorem isOverallShanten_neg_one_iff :
    IsOverallShanten fixed hand (-1) ↔ ∃ shape, Complete fixed shape hand := by
  constructor
  · rintro ⟨⟨shape, hshape⟩, _⟩
    exact ⟨shape, isShapeShanten_neg_one_iff.mp hshape⟩
  · rintro ⟨shape, hshape⟩
    exact ⟨⟨shape, isShapeShanten_neg_one_iff.mpr hshape⟩,
      fun _ _ hother => hother.neg_one_le⟩

/-- Erasing occupied capacity can only make the abstract answer smaller. -/
theorem IsShapeShanten.abstract_le
    (hvalue : IsShapeShanten fixed hand shape value)
    (habstract : Shanten.IsShapeShanten hand shape abstractValue) :
    abstractValue ≤ value := by
  obtain ⟨_, distance, hdistance, hreach, _⟩ := hvalue
  have := habstract.add_one_le_of_reachesCompletion hreach.toAbstract
  omega

lemma handStep_nil_iff (hvalid : ValidHand [] before) :
    HandStep [] before after ↔ Shanten.HandStep before after := by
  constructor
  · exact HandStep.toAbstract
  · intro hstep
    refine ⟨hvalid, hstep, validHand_nil_iff.mpr ⟨?_, hstep.validCounts⟩⟩
    have hfixed := (validHand_nil_iff.mp hvalid).1
    have := hstep.1
    omega

lemma reachesCompletion_nil_iff (hvalid : ValidHand [] hand) :
    ReachesCompletion [] shape hand distance ↔
      Shanten.ReachesCompletion Shanten.Complete shape hand distance := by
  constructor
  · exact ReachesCompletion.toAbstract
  · intro hreach
    induction hreach with
    | done hcomplete =>
        exact reachesCompletion_zero_iff.mpr ⟨hvalid, hcomplete⟩
    | step hstep _ ih =>
        have hcapacityStep := (handStep_nil_iff hvalid).mpr hstep
        obtain ⟨target, hpath, hcomplete⟩ := ih hcapacityStep.validHand
        exact ⟨target, .step hcapacityStep hpath, hcomplete⟩

theorem isShapeShanten_nil_iff (hvalid : ValidHand [] hand) :
    IsShapeShanten [] hand shape value ↔ Shanten.IsShapeShanten hand shape value := by
  unfold IsShapeShanten Shanten.IsShapeShanten
  simp_rw [reachesCompletion_nil_iff hvalid]

lemma complete_mentsuHand_iff_of_four_fixed (hlength : fixed.length = 4) :
    Complete fixed .mentsuHand hand ↔
      ValidHand fixed hand ∧ ∃ pair, HasTiles hand (pairTiles pair) := by
  constructor
  · rintro ⟨hvalid, _, pair, melds, hmelds, htiles⟩
    have hfixed : hand.fixedMelds = 4 := hvalid.1.trans hlength
    have hnil : melds = [] := List.length_eq_zero_iff.mp (by omega)
    subst melds
    exact ⟨hvalid, pair, by simpa [MentsuCandidateList.tiles] using htiles⟩
  · rintro ⟨hvalid, pair, htiles⟩
    have hfixed : hand.fixedMelds = 4 := by
      rw [hvalid.1, hlength]
    exact ⟨hvalid, hvalid.validCounts, pair, [], by simp [hfixed],
      by simpa [MentsuCandidateList.tiles] using htiles⟩

end Shanten.Capacity
