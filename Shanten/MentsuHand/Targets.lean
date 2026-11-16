import Shanten.MentsuHand.State
import Shanten.Exchange

/-!
# Targets

Completed targets and their relationship to search-state histories.
-/

namespace Shanten

/-- A mentsu-hand-form target before the fixed melds are added. -/


def mentsuHandTarget (pair : Tile) (melds : List Meld) : Multiset Tile :=
  pairTiles pair + meldsTiles melds

def mentsuHandTargetWithTaatsu
    (pair : Tile) (melds : List Meld) (taatsus : List Taatsu) : Multiset Tile :=
  mentsuHandTarget pair melds + taatsuHistoryTiles taatsus

lemma completedMeldsForState_tiles
    (state : MentsuHandSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    pairTiles pair + meldsTiles (completedMeldsForState state) =
      mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
          state.taatsuHistory.reverse +
        taatsuCompletionTiles state.taatsuHistory.reverse := by
  simp only [completedMeldsForState, mentsuHandTargetWithTaatsu, mentsuHandTarget]
  rw [meldsTiles_append]
  rw [← taatsuHistoryTiles_add_completionTiles]
  ac_rfl

def mentsuHandTargetWithTaatsuOfState
    (state : MentsuHandSearchState) : Option (Multiset Tile) :=
  state.pair.map fun pair =>
    mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
      state.taatsuHistory.reverse

lemma mentsuHandTargetWithTaatsuOfState_eq_some_iff
    (state : MentsuHandSearchState) (target : Multiset Tile) :
    mentsuHandTargetWithTaatsuOfState state = some target ↔
      ∃ pair, state.pair = some pair ∧
        target = mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
          state.taatsuHistory.reverse := by
  constructor
  · intro htarget
    cases hpair : state.pair with
    | none =>
        simp [mentsuHandTargetWithTaatsuOfState, hpair] at htarget
    | some pair =>
        refine ⟨pair, rfl, ?_⟩
        simpa [mentsuHandTargetWithTaatsuOfState, hpair] using htarget.symm
  · rintro ⟨pair, hpair, rfl⟩
    rw [mentsuHandTargetWithTaatsuOfState, hpair]
    rfl

lemma mentsuHandTargetWithTaatsuOfState_eq_stateHistoryTiles
    (state : MentsuHandSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
        state.taatsuHistory.reverse =
      stateHistoryTiles state := by
  simp [mentsuHandTargetWithTaatsu, mentsuHandTarget, stateHistoryTiles,
    pairHistoryTiles, hpair, Multiset.add_assoc]

lemma mentsuHandTargetWithTaatsu_count_le_hand
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
        state.taatsuHistory.reverse).count tile ≤ hand.counts tile := by
  intro tile
  rw [mentsuHandTargetWithTaatsuOfState_eq_stateHistoryTiles state pair hpair]
  rw [← reachableWithin_used_eq_historyTiles hand fuel state hreachable]
  exact reachableWithin_used_subset hand fuel state hreachable tile

lemma mentsuHandTargetExchange_handStep
    (target : TileCounts) (before : Hand) (discarded drawn : Tile)
    (hdrawn : target drawn > before.counts drawn)
    (hdiscarded : before.counts discarded > target discarded)
    (hne : discarded ≠ drawn) :
    HandStep before (exchangeHand before discarded drawn) := by
  apply TargetExchange.handStep
  exact ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩

lemma reachesExchange_of_targetExchange
    (target : TileCounts) (before : Hand) (discarded drawn : Tile)
    (hdrawn : target drawn > before.counts drawn)
    (hdiscarded : before.counts discarded > target discarded)
    (hne : discarded ≠ drawn)
    (hrest :
      ReachesExchange (exchangeHand before discarded drawn) after distance) :
    ReachesExchange before after (distance + 1) := by
  apply ReachesExchange.step
    (mentsuHandTargetExchange_handStep target before discarded drawn
      hdrawn hdiscarded hne)
  exact hrest

lemma exchangeHand_fixedMelds
    (before : Hand) (discarded drawn : Tile) :
    (exchangeHand before discarded drawn).fixedMelds = before.fixedMelds := by
  rfl

def mentsuHandTargetOfState
    (state : MentsuHandSearchState) : Option (Multiset Tile) :=
  state.pair.map fun pair =>
    mentsuHandTarget pair state.meldHistory.reverse

lemma mentsuHandTargetOfState_eq_some_iff
    (state : MentsuHandSearchState) (target : Multiset Tile) :
    mentsuHandTargetOfState state = some target ↔
      ∃ pair, state.pair = some pair ∧
        target = mentsuHandTarget pair state.meldHistory.reverse := by
  constructor
  · intro htarget
    cases hpair : state.pair with
    | none =>
        simp [mentsuHandTargetOfState, hpair] at htarget
    | some pair =>
        refine ⟨pair, rfl, ?_⟩
        simpa [mentsuHandTargetOfState, hpair] using htarget.symm
  · rintro ⟨pair, hpair, rfl⟩
    rw [mentsuHandTargetOfState, hpair]
    rfl

end Shanten
