import Shanten.Input37.Correctness

namespace Shanten.Input37.Examples

set_option maxRecDepth 4096

private def counts (entries : List (Fin 37 × Int)) : Counts37 :=
  fun index => (entries.map fun entry => if entry.1 = index then entry.2 else 0).sum

private def produces (input : Input) (fixed : List Capacity.FixedMeld)
    (expected : TileCounts) : Prop :=
  match validateAndNormalize input with
  | .error _ => False
  | .ok normalized => normalized.fixed = fixed ∧
      normalized.hand.fixedMelds = fixed.length ∧
      ∀ tile, normalized.hand.counts tile = expected tile

private instance : Decidable (produces input fixed expected) := by
  unfold produces
  split <;> infer_instance

private def error (input : Input) : Option ValidationError :=
  match validateAndNormalize input with
  | .error reason => some reason
  | .ok _ => none

def redMixture : Input :=
  ⟨counts [(0, 1), (5, 3), (10, 1), (15, 3), (20, 1), (25, 3), (30, 1)], []⟩

theorem red_mixture_normalizes :
    produces redMixture [] (fun tile => match tile with
      | .suited _ rank => if rank.val = 4 then 4 else 0
      | .honor rank => if rank.val = 0 then 1 else 0) := by
  decide

theorem fourteen_normalizes :
    produces
      ⟨fun index => redMixture.standing index + (if index = 36 then 1 else 0), []⟩
      [] (fun tile => match tile with
        | .suited _ rank => if rank.val = 4 then 4 else 0
        | .honor rank => if rank.val = 0 ∨ rank.val = 6 then 1 else 0) := by
  decide

private def standingTen : Counts37 := counts [(30, 4), (31, 4), (32, 2)]

private def normalizedTen : TileCounts :=
  fun tile => match tile with
    | .honor rank => if rank.val < 2 then 4 else if rank.val = 2 then 2 else 0
    | .suited _ _ => 0

theorem melds_normalize :
    produces ⟨standingTen, [⟨"chi", counts [(4, 1), (0, 1), (6, 1)]⟩]⟩
        [.meld (.sequence .man ⟨3, by omega⟩)] normalizedTen ∧
      produces ⟨standingTen, [⟨"pon", counts [(5, 2), (0, 1)]⟩]⟩
        [.meld (.triplet (.suited .man ⟨4, by omega⟩))] normalizedTen ∧
      (∀ kind ∈ ["ankan", "daiminkan", "kakan"],
        produces ⟨standingTen, [⟨kind, counts [(5, 3), (0, 1)]⟩]⟩
          [.kan (.suited .man ⟨4, by omega⟩)] normalizedTen) := by
  decide

theorem physical_capacity_rejections :
    error ⟨counts [(0, 2), (30, 4), (31, 4), (32, 3)], []⟩ =
        some (.capacityExceeded 0) ∧
      error ⟨counts [(5, 4), (30, 4), (31, 4), (32, 1)], []⟩ =
        some (.capacityExceeded 5) ∧
      error ⟨counts [(0, 1), (30, 4), (31, 4), (32, 1)],
        [⟨"pon", counts [(0, 1), (5, 2)]⟩]⟩ = some (.capacityExceeded 0) ∧
      error ⟨counts [(5, 1), (30, 4), (31, 4), (32, 1)],
        [⟨"pon", counts [(5, 3)]⟩]⟩ = some (.capacityExceeded 5) := by
  decide

theorem negative_count_rejections :
    error ⟨counts [(30, -1), (31, 4), (32, 4), (33, 3)],
        [⟨"pon", counts [(30, 3)]⟩]⟩ = some (.negativeStanding 30) ∧
      error ⟨counts [(32, 4), (33, 4), (34, 2)],
        [⟨"pon", counts [(30, -1), (31, 4)]⟩]⟩ = some (.negativeMeld 0 30) := by
  decide

theorem malformed_meld_rejections :
    error ⟨standingTen, [⟨"chi", counts [(8, 1), (9, 1), (11, 1)]⟩]⟩ =
        some (.invalidMeld 0) ∧
      error ⟨standingTen, [⟨"pon", counts [(5, 2)]⟩]⟩ = some (.invalidMeld 0) ∧
      error ⟨standingTen, [⟨"ankan", counts [(5, 3)]⟩]⟩ = some (.invalidMeld 0) ∧
      error ⟨standingTen, [⟨"unknown", counts [(5, 3)]⟩]⟩ = some (.invalidMeld 0) := by
  decide

theorem hand_size_rejections :
    error ⟨counts [(30, 4), (31, 4), (32, 4)], []⟩ = some (.invalidSize 12 0) ∧
      error ⟨fun _ => 0, List.replicate 5 ⟨"pon", fun _ => 0⟩⟩ =
        some (.tooManyMelds 5) := by
  decide

private lemma produces_success (h : produces input fixed expected) :
    ∃ normalized, validateAndNormalize input = .ok normalized := by
  cases hresult : validateAndNormalize input with
  | error reason => simp [produces, hresult] at h
  | ok normalized => exact ⟨normalized, rfl⟩

def redVariant (red : Bool) : Input :=
  ⟨counts [(if red then 0 else 5, 1), (30, 4), (31, 4), (32, 4)], []⟩

theorem red_identity_invariant :
    ∃ left right,
      validateAndNormalize (redVariant true) = .ok left ∧
      validateAndNormalize (redVariant false) = .ok right ∧
      left.fixed = right.fixed ∧ left.hand = right.hand ∧
      Capacity.overallMinimumSearch left.fixed left.hand =
        Capacity.overallMinimumSearch right.fixed right.hand := by
  have hleft : produces (redVariant true) []
      (fun tile => (normalizeCounts (redVariant true).standing tile).toNat) := by
    decide
  have hright : produces (redVariant false) []
      (fun tile => (normalizeCounts (redVariant false).standing tile).toNat) := by
    decide
  obtain ⟨left, hl⟩ := produces_success hleft
  obtain ⟨right, hr⟩ := produces_success hright
  have heq : Equivalent (redVariant true) (redVariant false) := by
    refine ⟨funext (by decide), rfl⟩
  obtain ⟨hfixed, hhand⟩ := normalized_equivalent hl hr heq
  exact ⟨left, right, hl, hr, hfixed, hhand, overall_normalization_invariant hl hr heq⟩

example :
    ∃ normalized, validateAndNormalize redMixture = .ok normalized ∧
      Capacity.ValidHand normalized.fixed normalized.hand ∧
      (tileCount normalized.hand + 3 * normalized.fixed.length = 13 ∨
        tileCount normalized.hand + 3 * normalized.fixed.length = 14) := by
  obtain ⟨normalized, h⟩ := produces_success red_mixture_normalizes
  exact ⟨normalized, h, validateAndNormalize_valid h⟩

end Shanten.Input37.Examples
