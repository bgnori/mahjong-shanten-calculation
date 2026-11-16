import Shanten.MentsuHand.Decomposition

/-!
# Scan / Basic

Copy-limited transitions, tile batches, grouped scans, and reachability.
-/

namespace Shanten

def ValidMentsuHandChoiceWithCopyLimit
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice) : Prop :=
  ∃ hvalid : ValidMentsuHandChoice hand state choice,
    CompletionRespectsCopyLimit
      (applyMentsuHandChoice hand state choice hvalid)

lemma validMentsuHandChoiceWithCopyLimit_of
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand state choice hvalid)) :
    ValidMentsuHandChoiceWithCopyLimit hand state choice :=
  ⟨hvalid, hcopy⟩

def NextMentsuHandStateWithCopyLimit
    (hand : Hand) (state next : MentsuHandSearchState) : Prop :=
  ∃ choice, choice ∈ allMentsuHandChoices ∧
    ∃ hvalid : ValidMentsuHandChoice hand state choice,
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand state choice hvalid) ∧
      next = applyMentsuHandChoice hand state choice hvalid

lemma nextMentsuHandStateWithCopyLimit_of_choice
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hchoice : choice ∈ allMentsuHandChoices)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand state choice hvalid)) :
    NextMentsuHandStateWithCopyLimit hand state
      (applyMentsuHandChoice hand state choice hvalid) :=
  ⟨choice, hchoice, hvalid, hcopy, rfl⟩

noncomputable def copyLimitChoices
    (hand : Hand) (state : MentsuHandSearchState) : Finset MentsuHandChoice :=
  by
    classical
    exact allMentsuHandChoices.filter
      (fun choice =>
        ∃ hvalid : ValidMentsuHandChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuHandChoice hand state choice hvalid))

lemma mem_copyLimitChoices_iff
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice) :
    choice ∈ copyLimitChoices hand state ↔
      choice ∈ allMentsuHandChoices ∧
        ∃ hvalid : ValidMentsuHandChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuHandChoice hand state choice hvalid) := by
  classical
  change choice ∈ allMentsuHandChoices.filter _ ↔ _
  rw [Finset.mem_filter]

lemma nextMentsuHandStateWithCopyLimit_iff
    (hand : Hand) (state next : MentsuHandSearchState) :
    NextMentsuHandStateWithCopyLimit hand state next ↔
      ∃ choice, choice ∈ copyLimitChoices hand state ∧
        ∃ hvalid : ValidMentsuHandChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuHandChoice hand state choice hvalid) ∧
          next = applyMentsuHandChoice hand state choice hvalid := by
  classical
  constructor
  · rintro ⟨choice, hchoice, hvalid, hcopy, rfl⟩
    refine ⟨choice, ?_, hvalid, hcopy, rfl⟩
    change choice ∈ allMentsuHandChoices.filter _
    exact Finset.mem_filter.mpr ⟨hchoice, ⟨hvalid, hcopy⟩⟩
  · rintro ⟨choice, hchoice, hvalid, hcopy, rfl⟩
    change choice ∈ allMentsuHandChoices.filter _ at hchoice
    exact ⟨choice, (Finset.mem_filter.mp hchoice).1,
      hvalid, hcopy, rfl⟩

/-- Several blocks may be applied at one tile position before the scan advances.

The list is built by appending the newly applied choice, matching the forward
choice paths used below.
-/
inductive AppliesMentsuHandChoiceBatch (hand : Hand) (tile : Tile) :
    MentsuHandSearchState → List MentsuHandChoice →
      MentsuHandSearchState → Prop
  | nil (state : MentsuHandSearchState) :
      AppliesMentsuHandChoiceBatch hand tile state [] state
  | cons (state middle final : MentsuHandSearchState)
      (choices : List MentsuHandChoice) (choice : MentsuHandChoice)
      (htail :
        AppliesMentsuHandChoiceBatch hand tile state choices middle)
      (hchoice : choice ∈ allMentsuHandChoices)
      (htile : tile ∈ choiceTiles choice)
      (hvalid : ValidMentsuHandChoice hand middle choice)
      (hcopy :
        CompletionRespectsCopyLimit
          (applyMentsuHandChoice hand middle choice hvalid)) :
      AppliesMentsuHandChoiceBatch hand tile state
        (choices ++ [choice])
        (applyMentsuHandChoice hand middle choice hvalid)

lemma AppliesMentsuHandChoiceBatch.append
    {hand : Hand} {tile : Tile}
    {state middle final : MentsuHandSearchState}
    {choicesBefore choicesAfter : List MentsuHandChoice}
    (hbefore :
      AppliesMentsuHandChoiceBatch hand tile
        state choicesBefore middle)
    (hafter :
      AppliesMentsuHandChoiceBatch hand tile
        middle choicesAfter final) :
    AppliesMentsuHandChoiceBatch hand tile state
      (choicesBefore ++ choicesAfter) final := by
  induction hafter generalizing state choicesBefore with
  | nil =>
      simpa using hbefore
  | @cons state middle choices choice htail hchoice htile hvalid hcopy ih =>
      have hmiddle :=
        ih hbefore
      rw [← List.append_assoc]
      exact .cons _ _ (applyMentsuHandChoice hand _ choice hvalid)
        (choicesBefore ++ choices) choice
        hmiddle hchoice htile hvalid hcopy

/-- A tile-order scan whose step may apply a batch of choices at one tile. -/
inductive AppliesMentsuHandTileBatchScan (hand : Hand) :
    List Tile → MentsuHandSearchState → List MentsuHandChoice →
      MentsuHandSearchState → Prop
  | nil (state : MentsuHandSearchState) :
      AppliesMentsuHandTileBatchScan hand [] state [] state
  | step (tile : Tile) (tiles : List Tile)
      (state middle final : MentsuHandSearchState)
      (batchChoices choices : List MentsuHandChoice)
      (hbatch :
        AppliesMentsuHandChoiceBatch hand tile state batchChoices middle)
      (htail :
        AppliesMentsuHandTileBatchScan hand tiles middle choices final) :
      AppliesMentsuHandTileBatchScan hand (tile :: tiles) state
        (batchChoices ++ choices) final

lemma AppliesMentsuHandTileBatchScan.append
    {hand : Hand} {before rest : List Tile}
    {start middle final : MentsuHandSearchState}
    {choicesBefore choicesAfter : List MentsuHandChoice}
    (hbefore :
      AppliesMentsuHandTileBatchScan hand before
        start choicesBefore middle)
    (htail :
      AppliesMentsuHandTileBatchScan hand rest
        middle choicesAfter final) :
    AppliesMentsuHandTileBatchScan hand (before ++ rest)
      start (choicesBefore ++ choicesAfter) final := by
  induction before generalizing start middle choicesBefore with
  | nil =>
      cases hbefore
      simpa using htail
  | cons tile tiles ih =>
      cases hbefore with
      | step =>
          rename_i middle' batchChoices' choices' hbatch htail'
          simpa [List.append_assoc] using
            (.step tile (tiles ++ rest) start middle' final
              batchChoices' (choices' ++ choicesAfter) hbatch
              (ih htail' htail))

lemma AppliesMentsuHandTileBatchScan.single
    {hand : Hand} {tile : Tile}
    {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hbatch :
      AppliesMentsuHandChoiceBatch hand tile state choices final) :
    AppliesMentsuHandTileBatchScan hand [tile] state choices final :=
  by
    convert
      (AppliesMentsuHandTileBatchScan.step
        tile [] state final final choices [] hbatch (.nil final))
        using 1 <;> simp

/-- Batch traversal driven by representative groups.

The source column is carried separately from the tile-order scan. Each step
consumes exactly the choices whose representative is the current tile and
recurses on the remaining source column. The base case therefore requires the
remaining column to be empty.
-/
inductive AppliesMentsuHandGroupedTileBatches (hand : Hand) :
    List Tile → List MentsuHandChoice → MentsuHandSearchState →
      MentsuHandSearchState → Prop
  | nil (state : MentsuHandSearchState) :
      AppliesMentsuHandGroupedTileBatches hand [] [] state state
  | step (tile : Tile) (tiles : List Tile)
      (source : List MentsuHandChoice)
      (state middle final : MentsuHandSearchState)
      (hbatch :
        AppliesMentsuHandChoiceBatch hand tile state
          (mentsuHandChoicesForTile tile source) middle)
      (htail :
        AppliesMentsuHandGroupedTileBatches hand tiles
          (mentsuHandChoicesWithoutTile tile source) middle final) :
      AppliesMentsuHandGroupedTileBatches hand (tile :: tiles)
        source state final

lemma AppliesMentsuHandGroupedTileBatches.to_scan
    {hand : Hand} {tiles : List Tile}
    {choices : List MentsuHandChoice}
    {state final : MentsuHandSearchState}
    (hgrouped :
      AppliesMentsuHandGroupedTileBatches hand tiles choices state final) :
    AppliesMentsuHandTileBatchScan hand tiles state
      (mentsuHandChoicesGroupedByTiles tiles choices) final := by
  induction hgrouped with
  | nil state =>
      simpa [mentsuHandChoicesGroupedByTiles] using
        (AppliesMentsuHandTileBatchScan.nil state)
  | @step tile tiles source state middle final hbatch htail ih =>
      simpa [mentsuHandChoicesGroupedByTiles] using
        (AppliesMentsuHandTileBatchScan.step
          tile tiles state middle final
          (mentsuHandChoicesForTile tile source)
          (mentsuHandChoicesGroupedByTiles tiles
            (mentsuHandChoicesWithoutTile tile source))
          hbatch ih)

lemma nextMentsuHandStateWithCopyLimit_copyLimit
    (hand : Hand) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandStateWithCopyLimit hand state next) :
    CompletionRespectsCopyLimit next := by
  rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
  exact hcopy

def reachableWithinWithCopyLimit
    (hand : Hand) : Nat → MentsuHandSearchState → Prop
  | 0, state => state = initialMentsuHandState
  | fuel + 1, state =>
      ∃ previous,
        reachableWithinWithCopyLimit hand fuel previous ∧
        NextMentsuHandStateWithCopyLimit hand previous state

lemma initialMentsuHandState_copyLimit :
    CompletionRespectsCopyLimit initialMentsuHandState := by
  intro tile
  simp [CompletionRespectsCopyLimit, initialMentsuHandState,
    taatsuCompletionTiles]

lemma reachableWithinWithCopyLimit_copyLimit
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    CompletionRespectsCopyLimit state := by
  induction fuel generalizing state with
  | zero =>
      rw [hreachable]
      exact initialMentsuHandState_copyLimit
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      exact nextMentsuHandStateWithCopyLimit_copyLimit hand previous state hnext

lemma reachableWithinWithCopyLimit_append_choice
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (choice : MentsuHandChoice)
    (hreachable : reachableWithinWithCopyLimit hand fuel state)
    (hchoice : choice ∈ allMentsuHandChoices)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand state choice hvalid)) :
    reachableWithinWithCopyLimit hand (fuel + 1)
      (applyMentsuHandChoice hand state choice hvalid) :=
  ⟨state, hreachable,
    nextMentsuHandStateWithCopyLimit_of_choice
      hand state choice hchoice hvalid hcopy⟩

lemma reachableWithinWithCopyLimit_melds_le_four
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    state.melds ≤ 4 := by
  induction fuel generalizing state with
  | zero =>
      subst state
      simp [initialMentsuHandState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
      have hbound := hvalid.2.1
      simp only [applyMentsuHandChoice] at hbound ⊢
      omega

lemma reachableWithinWithCopyLimit_used_subset
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    ∀ tile, state.used.count tile ≤ hand.counts tile := by
  induction fuel generalizing state with
  | zero =>
      intro tile
      subst state
      simp [initialMentsuHandState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      intro tile
      rcases hnext with ⟨choice, _, hvalid, _, rfl⟩
      exact hvalid.1 tile

lemma reachableWithinWithCopyLimit_taatsu_le_four
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    state.taatsu ≤ 4 := by
  induction fuel generalizing state with
  | zero =>
      subst state
      simp [initialMentsuHandState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
      have hbound := hvalid.2.2.1
      simp only [applyMentsuHandChoice] at hbound ⊢
      omega

end Shanten
