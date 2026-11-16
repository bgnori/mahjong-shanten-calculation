import Shanten.Capacity.Totality

namespace Shanten.Capacity

theorem generalMentsuHandMinimumSearch_optimal_of_fourteen
    (h14 : IsFourteenTileEquivalentHand fixed hand) :
    ∃ state ∈ generalMentsuHandStates fixed hand,
      generalMentsuHandMinimumSearch fixed hand = some ((state.missing : Int) - 1) ∧
      IsShapeShanten fixed hand .mentsuHand ((state.missing : Int) - 1) ∧
      ∀ other ∈ generalMentsuHandStates fixed hand, state.missing ≤ other.missing :=
  exists_optimal_state_of_size h14.1 (Or.inr h14.2)
    (generalMentsuHandStates_nonempty h14.1)

theorem generalMentsuHandMinimumSearch_eq_some_iff_of_fourteen
    (h14 : IsFourteenTileEquivalentHand fixed hand) (value : Int) :
    generalMentsuHandMinimumSearch fixed hand = some value ↔
      IsShapeShanten fixed hand .mentsuHand value := by
  obtain ⟨_, _, hresult, hshape, _⟩ := generalMentsuHandMinimumSearch_optimal_of_fourteen h14
  constructor
  · intro hvalue
    exact Option.some.inj (hresult.symm.trans hvalue) ▸ hshape
  · intro hvalue
    rw [hresult, isShapeShanten_unique hshape hvalue]

theorem generalMentsuHandMinimumSearch_exists_unique_of_fourteen
    (h14 : IsFourteenTileEquivalentHand fixed hand) :
    ∃! value : Int,
      generalMentsuHandMinimumSearch fixed hand = some value ∧
      IsShapeShanten fixed hand .mentsuHand value := by
  obtain ⟨_, _, hresult, hshape, _⟩ := generalMentsuHandMinimumSearch_optimal_of_fourteen h14
  exact ⟨_, ⟨hresult, hshape⟩, fun _ hother => isShapeShanten_unique hother.2 hshape⟩

theorem generalMentsuHandMinimumSearch_eq_neg_one_iff
    (h14 : IsFourteenTileEquivalentHand fixed hand) :
    generalMentsuHandMinimumSearch fixed hand = some (-1) ↔
      Complete fixed .mentsuHand hand := by
  rw [generalMentsuHandMinimumSearch_eq_some_iff_of_fourteen h14]
  constructor
  · rintro ⟨_, distance, hdistance, hreach, _⟩
    have : distance = 0 := by omega
    subst distance
    exact reachesCompletion_zero_iff.mp hreach
  · intro hcomplete
    exact ⟨trivial, 0, by omega, reachesCompletion_zero_iff.mpr hcomplete,
      fun smaller hsmaller => by omega⟩

end Shanten.Capacity
