import Shanten.MentsuHand.Scan.Paths
import Shanten.MentsuHand.Search.Totality

/-!
# Scan / Completion

Completion targets and conditional soundness of the copy-limited scan.
-/

namespace Shanten

lemma completedTargetForState_eq_used_add_completion
    (state : MentsuHandSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    completedTargetForState state pair =
      stateHistoryTiles state +
        taatsuCompletionTiles state.taatsuHistory.reverse := by
  rw [completedTargetForState, completedMeldsForState_tiles state pair hpair]
  rw [mentsuHandTargetWithTaatsuOfState_eq_stateHistoryTiles state pair hpair]

lemma validCounts_completedTarget_of_copyLimit
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcopy : CompletionRespectsCopyLimit state)
    (pair : Tile) (hpair : state.pair = some pair) :
    ValidCounts
      (targetHand before
        (countsOfTiles (completedTargetForState state pair))) := by
  intro tile
  have htarget := hcopy tile
  change (completedTargetForState state pair).count tile ≤ 4
  rw [completedTargetForState_eq_used_add_completion state pair hpair]
  rw [← reachableWithin_used_eq_historyTiles before fuel state hreachable]
  exact htarget

lemma completedMeldsForState_card (state : MentsuHandSearchState) :
    (meldsTiles (completedMeldsForState state)).card =
      3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  rw [meldsTiles_card, completedMeldsForState_length]

lemma completedTargetForState_card
    (state : MentsuHandSearchState) (pair : Tile) :
    (completedTargetForState state pair).card =
      2 + 3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  unfold completedTargetForState
  rw [Multiset.card_add, pairTiles_card, completedMeldsForState_card]

lemma completedTargetForState_sum
    (state : MentsuHandSearchState) (pair : Tile) :
    (∑ tile : Tile, countsOfTiles (completedTargetForState state pair) tile) =
      2 + 3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  rw [countsOfTiles_sum_eq_card, completedTargetForState_card]

lemma completedTargetForState_sum_of_blockCount
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcount : state.melds + state.taatsu + before.fixedMelds = 4)
    (pair : Tile) :
    (∑ tile : Tile,
      countsOfTiles (completedTargetForState state pair) tile) =
        14 - 3 * before.fixedMelds := by
  have hmelds := reachableWithin_melds_eq_history_length
    before fuel state hreachable
  have htaatsu := reachableWithin_taatsu_eq_history_length
    before fuel state hreachable
  rw [completedTargetForState_sum, ← hmelds, ← htaatsu]
  omega

lemma completedTargetForState_sum_eq_tileCount
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcount : state.melds + state.taatsu + before.fixedMelds = 4)
    (hstanding : tileCount before = 14 - 3 * before.fixedMelds)
    (pair : Tile) :
    (∑ tile : Tile,
      countsOfTiles (completedTargetForState state pair) tile) =
        tileCount before := by
  rw [completedTargetForState_sum_of_blockCount
    before fuel state hreachable hcount pair]
  exact hstanding.symm

lemma complete_mentsuHand_completedTarget
    (before : Hand) (state : MentsuHandSearchState) (pair : Tile)
    (hvalid : ValidCounts
      (targetHand before (countsOfTiles (completedTargetForState state pair))))
    (hmelds : HasMentsuHandMeldCount before (completedMeldsForState state)) :
    Complete .mentsuHand
      (targetHand before (countsOfTiles (completedTargetForState state pair))) := by
  apply complete_mentsuHand_targetHand
  · exact hvalid
  · exact hmelds
  · exact targetHand_hasTiles_countsOfTiles before
      (completedTargetForState state pair)

lemma mentsuHandTarget_count_le_stateHistoryTiles
    (state : MentsuHandSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuHandTarget pair state.meldHistory.reverse).count tile ≤
        (stateHistoryTiles state).count tile := by
  intro tile
  simp [mentsuHandTarget, stateHistoryTiles, pairHistoryTiles, hpair,
    Multiset.count_add]

lemma mentsuHandTarget_count_le_used
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuHandTarget pair state.meldHistory.reverse).count tile ≤
        state.used.count tile := by
  intro tile
  rw [reachableWithin_used_eq_historyTiles hand fuel state hreachable]
  exact mentsuHandTarget_count_le_stateHistoryTiles state pair hpair tile

lemma mentsuHandTarget_count_le_hand
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuHandTarget pair state.meldHistory.reverse).count tile ≤
        hand.counts tile := by
  intro tile
  exact le_trans
    (mentsuHandTarget_count_le_used hand fuel state hreachable pair hpair tile)
    (reachableWithin_used_subset hand fuel state hreachable tile)

lemma mentsuHandTarget_hasMeldCount_of_complete
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcomplete : IsMentsuHandSearchComplete hand state) :
    HasMentsuHandMeldCount hand state.meldHistory.reverse := by
  have hlength := reachableWithin_melds_eq_history_length
    hand fuel state hreachable
  rcases hcomplete with ⟨hmelds, _⟩
  unfold HasMentsuHandMeldCount
  simpa [List.length_reverse, hlength] using hmelds

lemma mentsuHandTargetOfState_exists_of_complete
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcomplete : IsMentsuHandSearchComplete hand state) :
    ∃ target, mentsuHandTargetOfState state = some target ∧
      HasMentsuHandMeldCount hand state.meldHistory.reverse := by
  cases hpair : state.pair with
  | none =>
      exfalso
      simpa [hpair] using hcomplete.2
  | some pair =>
      refine ⟨mentsuHandTarget pair state.meldHistory.reverse, ?_, ?_⟩
      · rw [mentsuHandTargetOfState, hpair]
        rfl
      · exact mentsuHandTarget_hasMeldCount_of_complete
          hand fuel state hreachable hcomplete

lemma completedMeldsForState_hasMeldCount
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcount : state.melds + state.taatsu + hand.fixedMelds = 4) :
    HasMentsuHandMeldCount hand (completedMeldsForState state) := by
  have hmelds := reachableWithin_melds_eq_history_length
    hand fuel state hreachable
  have htaatsu := reachableWithin_taatsu_eq_history_length
    hand fuel state hreachable
  unfold HasMentsuHandMeldCount
  rw [completedMeldsForState_length, ← hmelds, ← htaatsu]
  omega



lemma complete_mentsuHand_of_blockSearch
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcomplete : IsMentsuHandBlockSearchComplete before state)
    (hvalid : ∀ pair, state.pair = some pair →
      ValidCounts
        (targetHand before
          (countsOfTiles (completedTargetForState state pair)))) :
    ∃ pair,
      Complete .mentsuHand
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      refine ⟨pair, ?_⟩
      apply complete_mentsuHand_completedTarget before state pair
      · exact hvalid pair hstatePair
      · exact completedMeldsForState_hasMeldCount
          before fuel state hreachable hcount

lemma complete_mentsuHand_of_blockSearch_of_copyLimit
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcomplete : IsMentsuHandBlockSearchComplete before state)
    (hcopy : CompletionRespectsCopyLimit state) :
    ∃ pair,
      Complete .mentsuHand
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      refine ⟨pair, ?_⟩
      apply complete_mentsuHand_completedTarget before state pair
      · exact validCounts_completedTarget_of_copyLimit
          before fuel state hreachable hcopy pair hstatePair
      · exact completedMeldsForState_hasMeldCount
          before fuel state hreachable hcount

lemma complete_mentsuHand_of_constrainedBlockSearch
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit before fuel state)
    (hcomplete : IsMentsuHandBlockSearchComplete before state) :
    ∃ pair,
      Complete .mentsuHand
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  exact complete_mentsuHand_of_blockSearch_of_copyLimit
    before fuel state
    (reachableWithinWithCopyLimit_to_reachableWithin
      before fuel state hreachable)
    hcomplete
    (reachableWithinWithCopyLimit_copyLimit before fuel state hreachable)

lemma validMentsuHandTargetDistance_mem_of_constrainedBlockSearch
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit before fuel state)
    (hcomplete : IsMentsuHandBlockSearchComplete before state) :
    ∃ pair melds,
      melds.length + before.fixedMelds = 4 ∧
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))) ∧
      mentsuHandTargetDistance before pair melds ∈
        validMentsuHandTargetDistances before := by
  have hreachable' :
      reachableWithin before fuel state :=
    reachableWithinWithCopyLimit_to_reachableWithin
      before fuel state hreachable
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      let melds := completedMeldsForState state
      have hmelds :
          melds.length + before.fixedMelds = 4 := by
        dsimp [melds]
        exact completedMeldsForState_hasMeldCount
          before fuel state hreachable' hcount
      have htarget :
          mentsuHandTarget pair melds =
            completedTargetForState state pair := by
        rfl
      have hvalid :
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget pair melds))) := by
        rw [htarget]
        exact validCounts_completedTarget_of_copyLimit
          before fuel state hreachable'
          (reachableWithinWithCopyLimit_copyLimit
            before fuel state hreachable)
          pair hstatePair
      refine ⟨pair, melds, hmelds, hvalid, ?_⟩
      apply (mem_validMentsuHandTargetDistances_iff
        before (by omega) (mentsuHandTargetDistance before pair melds)).2
      exact ⟨pair, melds, hmelds, hvalid, rfl⟩

lemma exists_isShapeShanten_mentsuHand_of_constrainedBlockSearch
    (before : Hand) (hbeforeValid : ValidCounts before)
    (hstanding : tileCount before + 3 * before.fixedMelds = 13)
    (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit before fuel state)
    (hcomplete : IsMentsuHandBlockSearchComplete before state) :
    ∃ value : Int, IsShapeShanten before .mentsuHand value := by
  have hreachable' :
      reachableWithin before fuel state :=
    reachableWithinWithCopyLimit_to_reachableWithin
      before fuel state hreachable
  have hcopy :
      CompletionRespectsCopyLimit state :=
    reachableWithinWithCopyLimit_copyLimit before fuel state hreachable
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      let melds := completedMeldsForState state
      have hmelds :
          melds.length + before.fixedMelds = 4 := by
        dsimp [melds]
        exact completedMeldsForState_hasMeldCount
          before fuel state hreachable' hcount
      have htarget :
          mentsuHandTarget pair melds =
            completedTargetForState state pair := by
        rfl
      have hsum' :=
        completedTargetForState_sum_of_blockCount
          before fuel state hreachable' hcount pair
      have hsum :
          (∑ tile : Tile,
            countsOfTiles (mentsuHandTarget pair melds) tile) =
            (∑ tile : Tile, before.counts tile) + 1 := by
        calc
          _ = 14 - 3 * before.fixedMelds := by
            rw [htarget]
            exact hsum'
          _ = tileCount before + 1 := by
            omega
          _ = (∑ tile : Tile, before.counts tile) + 1 := by
            rfl
      have hvalid :
          ValidCounts
            (targetHand before (countsOfTiles (mentsuHandTarget pair melds))) := by
        rw [htarget]
        exact validCounts_completedTarget_of_copyLimit
          before fuel state hreachable' hcopy pair hstatePair
      exact exists_isShapeShanten_mentsuHand_of_valid_mentsuHandTarget_one_more
        before hbeforeValid
        ⟨pair, melds, hmelds, hsum, hvalid⟩

end Shanten
