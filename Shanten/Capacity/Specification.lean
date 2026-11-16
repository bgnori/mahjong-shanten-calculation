import Shanten.Capacity.Basic

namespace Shanten.Capacity

def Complete (fixed : List FixedMeld) (shape : Shape) (hand : Hand) : Prop :=
  ValidHand fixed hand ∧ Shanten.Complete shape hand

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
    have hnil : melds = [] := by
      have := hvalid.1
      have : melds.length = 0 := by omega
      exact List.length_eq_zero_iff.mp this
    subst melds
    exact ⟨hvalid, pair, by simpa [meldsTiles] using htiles⟩
  · rintro ⟨hvalid, pair, htiles⟩
    refine ⟨hvalid, hvalid.validCounts, pair, [], ?_, ?_⟩
    · have := hvalid.1
      simp only [List.length_nil]
      omega
    · simpa [meldsTiles] using htiles

end Shanten.Capacity
