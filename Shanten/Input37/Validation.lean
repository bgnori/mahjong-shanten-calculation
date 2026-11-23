module

public import Shanten.Input37.Basic

@[expose] public section

namespace Shanten.Input37

open MahjongDomain

inductive ValidationError
  | negativeStanding (tile : Fin 37)
  | negativeMeld (meldIndex : Nat) (tile : Fin 37)
  | capacityExceeded (tile : Fin 37)
  | tooManyMelds (count : Nat)
  | invalidSize (standing : Int) (meldCount : Nat)
  | invalidMeld (meldIndex : Nat)
  deriving DecidableEq, Repr

structure NormalizedInput where
  fixed : List Capacity.FixedMeld
  hand : Hand

def meldCandidates : List Capacity.FixedMeld :=
  let tiles := (List.finRange 37).map Int37Index.tile
  tiles.map (fun tile => .meld (.koutsu tile)) ++
    ([Suit.man, .pin, .sou].flatMap fun suit =>
      (List.finRange 7).map fun start => .meld (.shuntsu ⟨suit, start⟩)) ++
    tiles.map Capacity.FixedMeld.kan

lemma mem_meldCandidates (target : Capacity.FixedMeld) : target ∈ meldCandidates := by
  cases target with
  | kan tile =>
      simpa [meldCandidates] using
        (show ∃ index, Int37Index.tile index = tile from
          ⟨tile.int37Index, Int37Index.tile_int37Index tile⟩)
  | meld value =>
      cases value with
      | koutsu tile =>
          simpa [meldCandidates] using
            (show ∃ index, Int37Index.tile index = tile from
              ⟨tile.int37Index, Int37Index.tile_int37Index tile⟩)
      | shuntsu sequence =>
          obtain ⟨suit, start⟩ := sequence
          have hsuit : suit ∈ [Suit.man, .pin, .sou] := by cases suit <;> simp
          apply List.mem_append_left
          apply List.mem_append_right
          exact List.mem_flatMap.mpr ⟨suit, hsuit,
            List.mem_map.mpr ⟨start, by simp, rfl⟩⟩

def parseMeld (raw : MeldInput) : Option Capacity.FixedMeld :=
  meldCandidates.find? fun target =>
    decide (MatchesMeld raw target)

lemma parseMeld_some_matches (h : parseMeld raw = some target) :
    MatchesMeld raw target :=
  of_decide_eq_true
    (List.find?_some (p := fun candidate => decide (MatchesMeld raw candidate)) h)

lemma parseMeld_isSome_iff :
    (parseMeld raw).isSome = true ↔ ∃ target, MatchesMeld raw target := by
  simp [parseMeld, List.isSome_find?, mem_meldCandidates]

def normalizedHand (input : Input) (_nonnegative : Nonnegative input.standing) : Hand :=
  { counts := fun tile =>
      (aggregateInt37 input.standing tile).toNat
    fixedMelds := input.melds.length }

def parsedMelds (input : Input)
    (hparsed : ∀ index : Fin input.melds.length, (parseMeld input.melds[index]).isSome = true) :
    List Capacity.FixedMeld :=
  List.ofFn fun index => (parseMeld input.melds[index]).get (hparsed index)

def Internal.firstViolation {n : Nat} (p : Fin n → Prop) [DecidablePred p]
    (h : ¬ ∀ index, p index) : Fin n :=
  (Finset.univ.filter fun index => ¬ p index).min' (by
    obtain ⟨index, hindex⟩ := not_forall.mp h
    exact ⟨index, by simp [hindex]⟩)

lemma Internal.firstViolation_not {n : Nat} (p : Fin n → Prop) [DecidablePred p]
    (h : ¬ ∀ index, p index) : ¬ p (Internal.firstViolation p h) := by
  unfold Internal.firstViolation
  exact (Finset.mem_filter.mp
    (Finset.min'_mem (Finset.univ.filter fun index => ¬ p index) _)).2

/-- Reject raw physical-copy violations before returning any normalized data. -/
def validateAndNormalize (input : Input) : Except ValidationError NormalizedInput :=
  if hstanding : Nonnegative input.standing then
    if hmeldCounts : ∀ index : Fin input.melds.length, Nonnegative input.melds[index].tiles then
      if hcapacity : ∀ index, totalCounts input index ≤ (index.capacity : Int) then
        if hlength : input.melds.length ≤ 4 then
          if hsize : standingCount input + 3 * (input.melds.length : Int) = 13 ∨
              standingCount input + 3 * (input.melds.length : Int) = 14 then
            if hparsed : ∀ index : Fin input.melds.length,
                (parseMeld input.melds[index]).isSome = true then
              .ok ⟨parsedMelds input hparsed, normalizedHand input hstanding⟩
            else
              .error (.invalidMeld (Internal.firstViolation _ hparsed).val)
          else .error (.invalidSize (standingCount input) input.melds.length)
        else .error (.tooManyMelds input.melds.length)
      else .error (.capacityExceeded (Internal.firstViolation _ hcapacity))
    else
      let index := Internal.firstViolation _ hmeldCounts
      .error (.negativeMeld index.val
        (Internal.firstViolation _ (Internal.firstViolation_not _ hmeldCounts)))
  else .error (.negativeStanding (Internal.firstViolation _ hstanding))

theorem validateAndNormalize_ok_iff :
    validateAndNormalize input = .ok normalized ↔
      ∃ (hvalid : Valid input)
        (hparsed : ∀ index : Fin input.melds.length,
          (parseMeld input.melds[index]).isSome = true),
        normalized = ⟨parsedMelds input hparsed, normalizedHand input hvalid.1⟩ := by
  unfold validateAndNormalize
  split
  next hstanding =>
    split
    next hmeldCounts =>
      split
      next hcapacity =>
        split
        next hlength =>
          split
          next hsize =>
            split
            next hparsed =>
              constructor
              · intro heq
                cases heq
                exact ⟨⟨hstanding, hmeldCounts, hcapacity, hlength, hsize,
                  fun index => parseMeld_isSome_iff.mp (hparsed index)⟩, hparsed, rfl⟩
              · rintro ⟨_, _, rfl⟩
                rfl
            next hparsed =>
              constructor
              · intro h
                cases h
              · rintro ⟨_, h, _⟩
                exact (hparsed h).elim
          next hsize =>
            constructor
            · intro h
              cases h
            · rintro ⟨h, _, _⟩
              exact (hsize h.2.2.2.2.1).elim
        next hlength =>
          constructor
          · intro h
            cases h
          · rintro ⟨h, _, _⟩
            exact (hlength h.2.2.2.1).elim
      next hcapacity =>
        constructor
        · intro h
          cases h
        · rintro ⟨h, _, _⟩
          exact (hcapacity h.2.2.1).elim
    next hmeldCounts =>
      constructor
      · intro h
        cases h
      · rintro ⟨h, _, _⟩
        exact (hmeldCounts h.2.1).elim
  next hstanding =>
    constructor
    · intro h
      cases h
    · rintro ⟨h, _, _⟩
      exact (hstanding h.1).elim

theorem validateAndNormalize_accepts_iff :
    (∃ normalized, validateAndNormalize input = .ok normalized) ↔ Valid input := by
  constructor
  · rintro ⟨_, h⟩
    exact (validateAndNormalize_ok_iff.mp h).choose
  · intro hvalid
    have hparsed : ∀ index : Fin input.melds.length,
        (parseMeld input.melds[index]).isSome = true :=
      fun index => parseMeld_isSome_iff.mpr (hvalid.2.2.2.2.2 index)
    exact ⟨_, validateAndNormalize_ok_iff.mpr ⟨hvalid, hparsed, rfl⟩⟩

end Shanten.Input37
