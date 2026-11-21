import Shanten.MentsuHand.Scan.Basic

/-!
# Scan / Paths

Forward choice paths, state/history invariants, and batch conversions.
-/

namespace Shanten

open MahjongDomain

def MentsuHandChoiceStateMatches
    (state : MentsuHandSearchState)
    (choices : List MentsuHandChoice) : Prop :=
  state.used = mentsuHandChoiceTiles choices ∧
    state.melds = mentsuHandChoiceMeldCount choices ∧
    state.taatsu = mentsuHandChoiceTaatsuCount choices

lemma mentsuHandChoiceStateMatches_of_perm
    {state : MentsuHandSearchState}
    {choices choices' : List MentsuHandChoice}
    (hperm : List.Perm choices choices')
    (hmatches : MentsuHandChoiceStateMatches state choices) :
    MentsuHandChoiceStateMatches state choices' := by
  have htiles := mentsuHandChoiceTiles_of_perm hperm
  have hmelds := mentsuHandChoiceMeldCount_of_perm hperm
  have htaatsus := mentsuHandChoiceTaatsuCount_of_perm hperm
  exact ⟨hmatches.1.trans htiles, hmatches.2.1.trans hmelds,
    hmatches.2.2.trans htaatsus⟩

lemma mentsuHandChoiceStateMatches_of_groupedByTiles
    {state : MentsuHandSearchState}
    {tiles : List Tile} {choices : List MentsuHandChoice}
    (hrep :
      ∀ choice, choice ∈ choices →
        ∃ tile, tile ∈ tiles ∧
          mentsuHandChoiceRepresentative choice = some tile)
    (hmatches : MentsuHandChoiceStateMatches state choices) :
    MentsuHandChoiceStateMatches state
      (mentsuHandChoicesGroupedByTiles tiles choices ++
        mentsuHandChoicesWithoutTileForTiles tiles choices) := by
  have hperm :=
    mentsuHandChoicesGroupedByTiles_perm_append hrep
  exact mentsuHandChoiceStateMatches_of_perm hperm.symm hmatches

inductive AppliesMentsuHandChoicesForwardWithCopyLimit (hand : Hand) :
    MentsuHandSearchState → List MentsuHandChoice →
      MentsuHandSearchState → Prop
  | nil (state : MentsuHandSearchState) :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand state [] state
  | snoc (state middle : MentsuHandSearchState)
      (choices : List MentsuHandChoice) (choice : MentsuHandChoice)
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit hand state choices middle)
      (hchoice : choice ∈ allMentsuHandChoices)
      (hvalid : ValidMentsuHandChoice hand middle choice)
      (hcopy :
        CompletionRespectsCopyLimit
          (applyMentsuHandChoice hand middle choice hvalid)) :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand state
        (choices ++ [choice])
        (applyMentsuHandChoice hand middle choice hvalid)

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.append
    {hand : Hand}
    {state middle final : MentsuHandSearchState}
    {choicesBefore choicesAfter : List MentsuHandChoice}
    (hbefore :
      AppliesMentsuHandChoicesForwardWithCopyLimit
        hand state choicesBefore middle)
    (hafter :
      AppliesMentsuHandChoicesForwardWithCopyLimit
        hand middle choicesAfter final) :
    AppliesMentsuHandChoicesForwardWithCopyLimit
      hand state (choicesBefore ++ choicesAfter) final := by
  induction hafter generalizing state choicesBefore with
  | nil =>
      simpa using hbefore
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
      have hmiddle :=
        ih hbefore
      rw [← List.append_assoc]
      exact .snoc _ _ (choicesBefore ++ choices) choice
        hmiddle hchoice hvalid hcopy

lemma AppliesMentsuHandChoiceBatch.of_forward
    {hand : Hand} {tile : Tile}
    {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand
        state choices final)
    (htile :
      ∀ choice, choice ∈ choices → tile ∈ choiceTiles choice) :
    AppliesMentsuHandChoiceBatch hand tile state choices final := by
  induction hpath generalizing tile with
  | nil =>
      exact .nil _
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
      have htail :=
        ih (fun candidate hcandidate =>
          htile candidate (by
            exact List.mem_append_left [choice] hcandidate))
      have hchoiceTile :
          tile ∈ choiceTiles choice :=
        htile choice (by simp)
      exact .cons _ _ (applyMentsuHandChoice hand middle choice hvalid)
        choices choice htail hchoice hchoiceTile hvalid hcopy

lemma AppliesMentsuHandChoiceBatch.of_forward_for_representative_tile
    {hand : Hand} {tile : Tile}
    {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand
        state choices final)
    (hchoices :
      ∀ choice, choice ∈ choices →
        mentsuHandChoiceRepresentative choice = some tile) :
    AppliesMentsuHandChoiceBatch hand tile state choices final :=
  AppliesMentsuHandChoiceBatch.of_forward hpath
    (fun choice hchoice =>
      mentsuHandChoiceRepresentative_mem
        (hchoices choice hchoice))

lemma AppliesMentsuHandChoiceBatch.of_forward_for_tile_filter
    {hand : Hand} {tile : Tile}
    {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand
        state (mentsuHandChoicesForTile tile choices) final) :
    AppliesMentsuHandChoiceBatch hand tile state
      (mentsuHandChoicesForTile tile choices) final :=
  AppliesMentsuHandChoiceBatch.of_forward_for_representative_tile
    hpath
    (fun choice hchoice =>
      mentsuHandChoicesForTile_representative hchoice)

lemma AppliesMentsuHandGroupedTileBatches.step_of_forward
    {hand : Hand} {tile : Tile} {tiles : List Tile}
    {source : List MentsuHandChoice}
    {state middle final : MentsuHandSearchState}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand
        state (mentsuHandChoicesForTile tile source) middle)
    (htail :
      AppliesMentsuHandGroupedTileBatches hand tiles
        (mentsuHandChoicesWithoutTile tile source) middle final) :
    AppliesMentsuHandGroupedTileBatches hand (tile :: tiles)
      source state final :=
  .step tile tiles source state middle final
    (AppliesMentsuHandChoiceBatch.of_forward_for_tile_filter hpath)
    htail

lemma reachableWithinWithCopyLimit_of_forward_choice_path
    {hand : Hand} {final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand
        initialMentsuHandState choices final) :
    reachableWithinWithCopyLimit hand choices.length final := by
  induction hpath with
  | nil =>
      rfl
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
      have hnext :=
        reachableWithinWithCopyLimit_append_choice
          hand choices.length middle choice ih hchoice hvalid hcopy
      simpa [List.length_append] using hnext

lemma applyMentsuHandChoice.state_matches_append_single
    {hand : Hand} {state : MentsuHandSearchState}
    {choices : List MentsuHandChoice} (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hmatches : MentsuHandChoiceStateMatches state choices) :
    MentsuHandChoiceStateMatches
      (applyMentsuHandChoice hand state choice hvalid)
      (choices ++ [choice]) := by
  rcases hmatches with ⟨hused, hmelds, htaatsu⟩
  cases choice <;>
    simp [MentsuHandChoiceStateMatches, applyMentsuHandChoice,
      mentsuHandChoiceTiles, mentsuHandChoiceMeldCount,
      mentsuHandChoiceTaatsuCount, hused, hmelds, htaatsu,
      mentsuHandChoiceTiles_append,
      mentsuHandChoiceMeldCount_append,
      mentsuHandChoiceTaatsuCount_append, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] <;> ac_rfl

lemma AppliesMentsuHandChoiceBatch.state_matches_append
    {hand : Hand} {tile : Tile}
    {state final : MentsuHandSearchState}
    {pre choices : List MentsuHandChoice}
    (hbatch :
      AppliesMentsuHandChoiceBatch hand tile state choices final)
    (hmatches : MentsuHandChoiceStateMatches state pre) :
    MentsuHandChoiceStateMatches final (pre ++ choices) := by
  induction hbatch generalizing pre with
  | nil =>
      simpa using hmatches
  | @cons state middle choices choice htail hchoice htile hvalid hcopy ih =>
      have hstate :
          MentsuHandChoiceStateMatches state (pre ++ choices) :=
        ih hmatches
      have hfinal :=
        applyMentsuHandChoice.state_matches_append_single
          choice hvalid hstate
      simpa [List.append_assoc] using hfinal

lemma AppliesMentsuHandChoiceBatch.state_matches_from_initial
    {hand : Hand} {tile : Tile}
    {state : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hbatch :
      AppliesMentsuHandChoiceBatch hand tile
        initialMentsuHandState choices state) :
    MentsuHandChoiceStateMatches state choices :=
  hbatch.state_matches_append (pre := [])
    (by
      simp [MentsuHandChoiceStateMatches, initialMentsuHandState,
        mentsuHandChoiceTiles, mentsuHandChoiceMeldCount,
        mentsuHandChoiceTaatsuCount])

lemma AppliesMentsuHandTileBatchScan.state_matches_append
    {hand : Hand}
    {tiles : List Tile}
    {state final : MentsuHandSearchState}
    {pre choices : List MentsuHandChoice}
    (hscan :
      AppliesMentsuHandTileBatchScan hand tiles state choices final)
    (hmatches : MentsuHandChoiceStateMatches state pre) :
    MentsuHandChoiceStateMatches final (pre ++ choices) := by
  induction hscan generalizing pre with
  | nil =>
      simpa using hmatches
  | @step tile tiles start middle final batchChoices choices hbatch htail ih =>
      have hmiddle :=
        AppliesMentsuHandChoiceBatch.state_matches_append
          hbatch hmatches
      have hfinal := ih hmiddle
      simpa [List.append_assoc] using hfinal

lemma applyMentsuHandChoice.taatsuHistory_reverse_append_single
    {hand : Hand} {state : MentsuHandSearchState}
    {choices : List MentsuHandChoice} (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hhistory :
      state.taatsuHistory.reverse =
        mentsuHandChoiceTaatsus choices) :
    (applyMentsuHandChoice hand state choice hvalid).taatsuHistory.reverse =
      mentsuHandChoiceTaatsus (choices ++ [choice]) := by
  cases choice <;>
    simp [applyMentsuHandChoice, mentsuHandChoiceTaatsus,
      mentsuHandChoiceTaatsus_append, hhistory, List.reverse_append]

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.state_matches_append
    {hand : Hand}
    {state final : MentsuHandSearchState}
    {pre choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit
        hand state choices final)
    (hmatches : MentsuHandChoiceStateMatches state pre) :
    MentsuHandChoiceStateMatches final (pre ++ choices) := by
  induction hpath generalizing pre with
  | nil =>
      simpa using hmatches
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
      have hmiddle :=
        ih hmatches
      have hfinal :=
        applyMentsuHandChoice.state_matches_append_single
          choice hvalid hmiddle
      simpa [List.append_assoc] using hfinal

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.taatsuHistory_reverse_append
    {hand : Hand}
    {state final : MentsuHandSearchState}
    {pre choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit
        hand state choices final)
    (hhistory :
      state.taatsuHistory.reverse =
        mentsuHandChoiceTaatsus pre) :
    final.taatsuHistory.reverse =
      mentsuHandChoiceTaatsus (pre ++ choices) := by
  induction hpath generalizing pre with
  | nil =>
      simpa using hhistory
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
      have hmiddle := ih hhistory
      have hfinal :=
        applyMentsuHandChoice.taatsuHistory_reverse_append_single
          choice hvalid hmiddle
      simpa [List.append_assoc] using hfinal

lemma AppliesMentsuHandChoiceBatch.taatsuHistory_reverse_append
    {hand : Hand} {tile : Tile}
    {state final : MentsuHandSearchState}
    {pre choices : List MentsuHandChoice}
    (hbatch :
      AppliesMentsuHandChoiceBatch hand tile state choices final)
    (hhistory :
      state.taatsuHistory.reverse =
        mentsuHandChoiceTaatsus pre) :
    final.taatsuHistory.reverse =
      mentsuHandChoiceTaatsus (pre ++ choices) := by
  induction hbatch generalizing pre with
  | nil =>
      simpa using hhistory
  | @cons state middle choices choice htail hchoice htile hvalid hcopy ih =>
      have hstate :
          state.taatsuHistory.reverse =
            mentsuHandChoiceTaatsus (pre ++ choices) :=
        ih hhistory
      have hfinal :=
        applyMentsuHandChoice.taatsuHistory_reverse_append_single
          choice hvalid hstate
      simpa [List.append_assoc] using hfinal

lemma AppliesMentsuHandChoiceBatch.taatsuHistory_reverse_from_initial
    {hand : Hand} {tile : Tile}
    {state : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hbatch :
      AppliesMentsuHandChoiceBatch hand tile
        initialMentsuHandState choices state) :
    state.taatsuHistory.reverse =
      mentsuHandChoiceTaatsus choices :=
  hbatch.taatsuHistory_reverse_append (pre := []) (by
    simp [initialMentsuHandState, mentsuHandChoiceTaatsus])

lemma AppliesMentsuHandTileBatchScan.taatsuHistory_reverse_append
    {hand : Hand}
    {tiles : List Tile}
    {state final : MentsuHandSearchState}
    {pre choices : List MentsuHandChoice}
    (hscan :
      AppliesMentsuHandTileBatchScan hand tiles state choices final)
    (hhistory :
      state.taatsuHistory.reverse =
        mentsuHandChoiceTaatsus pre) :
    final.taatsuHistory.reverse =
      mentsuHandChoiceTaatsus (pre ++ choices) := by
  induction hscan generalizing pre with
  | nil =>
      simpa using hhistory
  | @step tile tiles start middle final batchChoices choices hbatch htail ih =>
      have hmiddle :=
        AppliesMentsuHandChoiceBatch.taatsuHistory_reverse_append
          hbatch hhistory
      have hfinal := ih hmiddle
      simpa [List.append_assoc] using hfinal

lemma reachableWithinWithCopyLimit_of_choice_batch
    {hand : Hand} {tile : Tile}
    {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (fuel : Nat)
    (hreachable :
      reachableWithinWithCopyLimit hand fuel state)
    (hbatch :
      AppliesMentsuHandChoiceBatch hand tile state choices final) :
    reachableWithinWithCopyLimit hand
      (fuel + choices.length) final := by
  induction hbatch generalizing fuel with
  | nil =>
      simpa using hreachable
  | @cons state middle choices choice htail hchoice htile hvalid hcopy ih =>
      have hstate :
          reachableWithinWithCopyLimit hand
            (fuel + choices.length) state :=
        ih fuel hreachable
      have hnext :=
        reachableWithinWithCopyLimit_append_choice
          hand (fuel + choices.length) state choice
          hstate hchoice hvalid hcopy
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hnext

lemma reachableWithinWithCopyLimit_of_tile_batch_scan
    {hand : Hand}
    {tiles : List Tile}
    {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (fuel : Nat)
    (hreachable :
      reachableWithinWithCopyLimit hand fuel state)
    (hscan :
      AppliesMentsuHandTileBatchScan hand tiles state choices final) :
    reachableWithinWithCopyLimit hand
      (fuel + choices.length) final := by
  induction hscan generalizing fuel with
  | nil =>
      simpa using hreachable
  | @step tile tiles start middle final batchChoices choices hbatch htail ih =>
      have hmiddle :=
        reachableWithinWithCopyLimit_of_choice_batch
          fuel hreachable hbatch
      have hfinal :=
        ih (fuel + batchChoices.length) hmiddle
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hfinal

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.state_matches_from_initial
    {hand : Hand} {final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand
        initialMentsuHandState choices final) :
    MentsuHandChoiceStateMatches final choices := by
  induction hpath with
  | nil =>
      simp [MentsuHandChoiceStateMatches, initialMentsuHandState,
        mentsuHandChoiceTiles, mentsuHandChoiceMeldCount,
        mentsuHandChoiceTaatsuCount]
  | @snoc state middle choices hpath hchoice hvalid hcopy ih =>
      exact applyMentsuHandChoice.state_matches_append_single
        _ hvalid ih

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.taatsuHistory_reverse_from_initial
    {hand : Hand} {final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath :
      AppliesMentsuHandChoicesForwardWithCopyLimit hand
        initialMentsuHandState choices final) :
    final.taatsuHistory.reverse =
      mentsuHandChoiceTaatsus choices := by
  induction hpath with
  | nil =>
      rfl
  | @snoc state middle choices hpath hchoice hvalid hcopy ih =>
      exact applyMentsuHandChoice.taatsuHistory_reverse_append_single
        _ hvalid ih

lemma applyMentsuHandChoice_pair_eq_some
    (hand : Hand) (state : MentsuHandSearchState) (tile : Tile)
    (hvalid : ValidMentsuHandChoice hand state (.pair tile))
    (hpair : state.pair = none) :
    (applyMentsuHandChoice hand state (.pair tile) hvalid).pair =
      some tile := by
  simp [applyMentsuHandChoice, hpair]

lemma applyMentsuHandChoice_pair_eq_of_not_pair
    (hand : Hand) (state : MentsuHandSearchState)
    (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (pair : Tile) (hpair : state.pair = some pair)
    (hchoice : choiceUsesPair choice = false) :
    (applyMentsuHandChoice hand state choice hvalid).pair =
      some pair := by
  cases choice with
  | skip | taatsu | meld =>
      simp [applyMentsuHandChoice, hpair]
  | pair tile =>
      simp [choiceUsesPair] at hchoice

lemma nextMentsuHandStateWithCopyLimit_toNext
    (hand : Hand) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandStateWithCopyLimit hand state next) :
    NextMentsuHandState hand state next := by
  rcases hnext with ⟨choice, hchoice, hvalid, _, rfl⟩
  exact ⟨choice, hchoice, hvalid, rfl⟩

lemma reachableWithinWithCopyLimit_to_reachableWithin
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    reachableWithin hand fuel state := by
  induction fuel generalizing state with
  | zero =>
      exact hreachable
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rw [reachableWithin_succ_iff]
      exact ⟨previous, ih previous hprevious,
        nextMentsuHandStateWithCopyLimit_toNext hand previous state hnext⟩

end Shanten
