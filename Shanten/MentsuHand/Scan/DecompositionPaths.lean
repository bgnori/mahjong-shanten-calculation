import Shanten.MentsuHand.Scan.Paths

/-!
# Scan / DecompositionPaths

Constructing legal copy-limited paths from arbitrary decomposition permutations.
-/

namespace Shanten

open MahjongDomain

def mentsuHandChoicePairCount : List MentsuHandChoice → Nat
  | [] => 0
  | .pair _ :: choices => mentsuHandChoicePairCount choices + 1
  | _ :: choices => mentsuHandChoicePairCount choices

lemma mentsuHandChoicePairCount_append
      (left right : List MentsuHandChoice) :
      mentsuHandChoicePairCount (left ++ right) =
        mentsuHandChoicePairCount left +
          mentsuHandChoicePairCount right := by
  induction left with
  | nil =>
        simp [mentsuHandChoicePairCount]
  | cons choice left ih =>
        cases choice <;>
          simp [mentsuHandChoicePairCount, ih, Nat.add_assoc] <;> omega

lemma mentsuHandChoicePairCount_of_perm
      {choices choices' : List MentsuHandChoice}
      (hperm : List.Perm choices choices') :
      mentsuHandChoicePairCount choices =
        mentsuHandChoicePairCount choices' := by
  induction hperm with
  | nil =>
        rfl
  | cons choice hperm ih =>
        cases choice <;> simp [mentsuHandChoicePairCount, ih]
  | swap choice choice' choices =>
        cases choice <;> cases choice' <;>
          simp [mentsuHandChoicePairCount, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
  | trans hperm hperm' ih ih' =>
        exact ih.trans ih'

lemma MentsuHandBlockDecomposition.blockChoices_pairCount
      {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
      mentsuHandChoicePairCount decomposition.blockChoices = 1 := by
  have meldsCount (melds : List Meld) :
        mentsuHandChoicePairCount (melds.map MentsuHandChoice.meld) = 0 := by
      induction melds with
      | nil => rfl
      | cons meld melds ih => simpa [mentsuHandChoicePairCount] using ih
  have taatsusCount (taatsus : List Taatsu) :
        mentsuHandChoicePairCount (taatsus.map MentsuHandChoice.taatsu) = 0 := by
      induction taatsus with
      | nil => rfl
      | cons taatsu taatsus ih => simpa [mentsuHandChoicePairCount] using ih
  change mentsuHandChoicePairCount
        (MentsuHandChoice.pair decomposition.pair ::
          (decomposition.melds.map MentsuHandChoice.meld ++
            decomposition.taatsus.map MentsuHandChoice.taatsu)) = 1
  rw [mentsuHandChoicePairCount, mentsuHandChoicePairCount_append,
      meldsCount, taatsusCount]

lemma list_sublist_nil {α : Type} (choices : List α) :
    List.Sublist ([] : List α) choices := by
  induction choices with
  | nil => exact .slnil
  | cons choice choices ih => exact .cons choice ih

lemma list_append_single_sublist {α : Type}
    (before : List α) (choice : α) (after : List α) :
    List.Sublist (before ++ [choice]) (before ++ choice :: after) := by
  induction before with
  | nil =>
      exact .cons_cons choice (list_sublist_nil after)
  | cons head before ih =>
      simpa [List.cons_append] using (List.Sublist.cons_cons head ih)

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.pair_none_of_pairCount_eq_zero
      {hand : Hand} {choices : List MentsuHandChoice}
      {final : MentsuHandSearchState}
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState choices final)
      (hcount : mentsuHandChoicePairCount choices = 0) :
      final.pair.isNone := by
  induction hpath with
  | nil =>
        simp [initialMentsuHandState]
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
        rw [mentsuHandChoicePairCount_append] at hcount
        cases choice with
        | pair tile =>
            simp [mentsuHandChoicePairCount] at hcount
        | skip =>
            have hprefix : mentsuHandChoicePairCount choices = 0 := by
              simpa [mentsuHandChoicePairCount] using hcount
            simpa [applyMentsuHandChoice] using ih hprefix
        | taatsu taatsu =>
            have hprefix : mentsuHandChoicePairCount choices = 0 := by
              simpa [mentsuHandChoicePairCount] using hcount
            simpa [applyMentsuHandChoice] using ih hprefix
        | meld meld =>
            have hprefix : mentsuHandChoicePairCount choices = 0 := by
              simpa [mentsuHandChoicePairCount] using hcount
            simpa [applyMentsuHandChoice] using ih hprefix

lemma MentsuHandBlockDecomposition.forwardPath_of_perm_aux
      {hand : Hand}
      (decomposition : MentsuHandBlockDecomposition hand) :
      ∀ (processed choices : List MentsuHandChoice)
        (state : MentsuHandSearchState),
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState processed state →
        List.Perm (processed ++ choices) decomposition.blockChoices →
        ∃ final,
          AppliesMentsuHandChoicesForwardWithCopyLimit hand state choices final := by
  intro processed choices state hpath hperm
  induction choices generalizing processed state with
  | nil =>
        exact ⟨state, .nil state⟩
  | cons choice choices ih =>
        have hpairTotal :
            mentsuHandChoicePairCount (processed ++ choice :: choices) = 1 := by
          calc
            mentsuHandChoicePairCount (processed ++ choice :: choices) =
                mentsuHandChoicePairCount decomposition.blockChoices :=
              mentsuHandChoicePairCount_of_perm hperm
            _ = 1 := decomposition.blockChoices_pairCount
        have hpairSplit :
            mentsuHandChoicePairCount processed +
              mentsuHandChoicePairCount (choice :: choices) = 1 := by
          rw [← mentsuHandChoicePairCount_append]
          exact hpairTotal
        have hpartial :
            List.Sublist (processed ++ [choice]) (processed ++ choice :: choices) :=
          list_append_single_sublist processed choice choices
        have hmatches := hpath.state_matches_from_initial
        have hpartialTilesLe (tile : Tile) :
            (mentsuHandChoiceTiles (processed ++ [choice])).count tile ≤
              (mentsuHandChoiceTiles decomposition.blockChoices).count tile := by
          have hsubLe :=
            mentsuHandChoiceTiles_count_le_of_sublist hpartial tile
          have hfullTiles :
              mentsuHandChoiceTiles (processed ++ choice :: choices) =
                mentsuHandChoiceTiles decomposition.blockChoices :=
            mentsuHandChoiceTiles_of_perm hperm
          calc
            (mentsuHandChoiceTiles (processed ++ [choice])).count tile ≤
                (mentsuHandChoiceTiles (processed ++ choice :: choices)).count tile :=
              hsubLe
            _ = (mentsuHandChoiceTiles decomposition.blockChoices).count tile :=
              congrArg (fun tiles : Multiset Tile => tiles.count tile) hfullTiles
        have hused :
            ∀ tile, (state.used + choiceTiles choice).count tile ≤
              hand.counts tile := by
          intro tile
          calc
            (state.used + choiceTiles choice).count tile =
                (mentsuHandChoiceTiles (processed ++ [choice])).count tile := by
                  rw [mentsuHandChoiceTiles_append, hmatches.1]
                  simp [mentsuHandChoiceTiles, Multiset.count_add]
            _ ≤ (mentsuHandChoiceTiles decomposition.blockChoices).count tile :=
              hpartialTilesLe tile
            _ = (mentsuHandTargetWithTaatsu decomposition.pair
                decomposition.melds decomposition.taatsus).count tile := by
              rw [decomposition.blockChoices_tiles]
            _ ≤ hand.counts tile := decomposition.targetWithinHand tile
        have hpartialMelds :
            mentsuHandChoiceMeldCount (processed ++ [choice]) =
              mentsuHandChoiceMeldCount processed +
                (if choiceUsesMeld choice = true then 1 else 0) := by
          rw [mentsuHandChoiceMeldCount_append]
          cases choice <;> rfl
        have hpartialTaatsus :
            mentsuHandChoiceTaatsuCount (processed ++ [choice]) =
              mentsuHandChoiceTaatsuCount processed +
                (if choiceUsesTaatsu choice = true then 1 else 0) := by
          rw [mentsuHandChoiceTaatsuCount_append]
          cases choice <;> rfl
        have hfullMelds :
            mentsuHandChoiceMeldCount (processed ++ choice :: choices) =
              decomposition.melds.length := by
          calc
            mentsuHandChoiceMeldCount (processed ++ choice :: choices) =
                mentsuHandChoiceMeldCount decomposition.blockChoices :=
              mentsuHandChoiceMeldCount_of_perm hperm
            _ = decomposition.melds.length :=
              decomposition.blockChoices_meldCount
        have hfullTaatsus :
            mentsuHandChoiceTaatsuCount (processed ++ choice :: choices) =
              decomposition.taatsus.length := by
          calc
            mentsuHandChoiceTaatsuCount (processed ++ choice :: choices) =
                mentsuHandChoiceTaatsuCount decomposition.blockChoices :=
              mentsuHandChoiceTaatsuCount_of_perm hperm
            _ = decomposition.taatsus.length :=
              decomposition.blockChoices_taatsuCount
        have hmelds :
            state.melds + (if choiceUsesMeld choice = true then 1 else 0) ≤ 4 := by
          have hpartialLe :=
            mentsuHandChoiceMeldCount_le_of_sublist hpartial
          have hblocks := decomposition.blocks
          rw [hmatches.2.1, ← hpartialMelds]
          calc
            mentsuHandChoiceMeldCount (processed ++ [choice]) ≤
                mentsuHandChoiceMeldCount (processed ++ choice :: choices) :=
              hpartialLe
            _ = decomposition.melds.length := hfullMelds
            _ ≤ 4 := by omega
        have htaatsu :
            state.taatsu + (if choiceUsesTaatsu choice = true then 1 else 0) ≤ 4 := by
          have hpartialLe :=
            mentsuHandChoiceTaatsuCount_le_of_sublist hpartial
          have hblocks := decomposition.blocks
          rw [hmatches.2.2, ← hpartialTaatsus]
          calc
            mentsuHandChoiceTaatsuCount (processed ++ [choice]) ≤
                mentsuHandChoiceTaatsuCount (processed ++ choice :: choices) :=
              hpartialLe
            _ = decomposition.taatsus.length := hfullTaatsus
            _ ≤ 4 := by omega
        have hpair :
            state.pair.isNone ∨ choiceUsesPair choice = false := by
          cases choice with
          | pair tile =>
              have hprocessed : mentsuHandChoicePairCount processed = 0 := by
                simp [mentsuHandChoicePairCount] at hpairSplit
                omega
              exact Or.inl
                (hpath.pair_none_of_pairCount_eq_zero hprocessed)
          | skip =>
              exact Or.inr rfl
          | taatsu taatsu =>
              exact Or.inr rfl
          | meld meld =>
              exact Or.inr rfl
        have hvalid : ValidMentsuHandChoice hand state choice :=
          ⟨hused, hmelds, htaatsu, hpair⟩
        have hpartialTaatsusSub :
            List.Sublist
              (mentsuHandChoiceTaatsus (processed ++ [choice]))
              (mentsuHandChoiceTaatsus (processed ++ choice :: choices)) :=
          mentsuHandChoiceTaatsus_sublist_of_sublist hpartial
        have htaatsuPerm :
            List.Perm
              (mentsuHandChoiceTaatsus (processed ++ choice :: choices))
              decomposition.taatsus := by
          rw [← decomposition.blockChoices_taatsus]
          exact mentsuHandChoiceTaatsus_of_perm hperm
        have hcompletionLe (tile : Tile) :
            (taatsuCompletionTiles
                (mentsuHandChoiceTaatsus (processed ++ [choice]))).count tile ≤
              (taatsuCompletionTiles decomposition.taatsus).count tile := by
          have hsubLe :=
            taatsuCompletionTiles_count_le_of_sublist hpartialTaatsusSub tile
          calc
            (taatsuCompletionTiles
                (mentsuHandChoiceTaatsus (processed ++ [choice]))).count tile ≤
                (taatsuCompletionTiles
                  (mentsuHandChoiceTaatsus (processed ++ choice :: choices))).count tile :=
              hsubLe
            _ = (taatsuCompletionTiles decomposition.taatsus).count tile := by
              rw [taatsuCompletionTiles_of_perm htaatsuPerm]
        let next := applyMentsuHandChoice hand state choice hvalid
        have hmatchesNext :
            MentsuHandChoiceStateMatches next (processed ++ [choice]) := by
          exact applyMentsuHandChoice.state_matches_append_single
            choice hvalid hmatches
        have hhistoryNext :
            next.taatsuHistory.reverse =
              mentsuHandChoiceTaatsus (processed ++ [choice]) := by
          exact applyMentsuHandChoice.taatsuHistory_reverse_append_single
            choice hvalid (hpath.taatsuHistory_reverse_from_initial)
        have hcopy : CompletionRespectsCopyLimit next := by
          intro tile
          have hfull := decomposition.completionCopyLimit tile
          rw [← decomposition.blockChoices_tiles] at hfull
          have hfullCount :
              (mentsuHandChoiceTiles decomposition.blockChoices).count tile +
                (taatsuCompletionTiles decomposition.taatsus).count tile ≤ 4 := by
            simpa [Multiset.count_add] using hfull
          have hpartialCount :
              (mentsuHandChoiceTiles (processed ++ [choice])).count tile +
                (taatsuCompletionTiles
                  (mentsuHandChoiceTaatsus (processed ++ [choice]))).count tile ≤ 4 :=
            (Nat.add_le_add (hpartialTilesLe tile) (hcompletionLe tile)).trans
              hfullCount
          rw [hmatchesNext.1, hhistoryNext]
          simpa only [Multiset.count_add] using hpartialCount
        have hstep :
            AppliesMentsuHandChoicesForwardWithCopyLimit
              hand state [choice] next := by
          have hmem : choice ∈ processed ++ choice :: choices := by
            apply List.mem_append_right
            simp
          exact .snoc state state [] choice (.nil state)
            (decomposition.blockChoices_mem_all choice
              ((List.Perm.mem_iff hperm).1 hmem))
            hvalid hcopy
        have hpathNext := hpath.append hstep
        have hpermNext :
            ((processed ++ [choice]) ++ choices).Perm
              decomposition.blockChoices := by
          simpa [List.append_assoc] using hperm
        obtain ⟨final, htail⟩ :=
          ih (processed ++ [choice]) next hpathNext hpermNext
        exact ⟨final, hstep.append htail⟩

lemma MentsuHandBlockDecomposition.forwardPath_of_perm
      {hand : Hand}
      (decomposition : MentsuHandBlockDecomposition hand)
      {choices : List MentsuHandChoice}
      (hperm : List.Perm choices decomposition.blockChoices) :
      ∃ final,
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState choices final := by
  exact decomposition.forwardPath_of_perm_aux [] choices
      initialMentsuHandState
      (AppliesMentsuHandChoicesForwardWithCopyLimit.nil
        initialMentsuHandState)
      (by simpa using hperm)

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.uncons
      {hand : Hand} {state final : MentsuHandSearchState}
      {choices : List MentsuHandChoice}
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand state choices final)
      (hne : choices ≠ []) :
      ∃ choice rest middle,
        choices = choice :: rest ∧
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand state [choice] middle ∧
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand middle rest final := by
  induction hpath with
  | nil =>
        exact (hne rfl).elim
  | @snoc middle choices choice hprefix hchoice hvalid hcopy ih =>
        cases choices with
        | nil =>
            refine ⟨choice, [], applyMentsuHandChoice hand middle choice hvalid,
              ?_, .snoc state middle [] choice hprefix hchoice hvalid hcopy,
              .nil _⟩
            simp
        | cons first choices =>
            obtain ⟨head, tail, firstMiddle, hshape, firstPath, restPath⟩ :=
              ih (by simp)
            rcases List.cons.inj hshape with ⟨rfl, rfl⟩
            let lastPath :
                AppliesMentsuHandChoicesForwardWithCopyLimit
                  hand middle [choice]
                  (applyMentsuHandChoice hand middle choice hvalid) :=
              .snoc middle middle [] choice (.nil middle)
                hchoice hvalid hcopy
            refine ⟨first, choices ++ [choice], firstMiddle, ?_,
              firstPath, restPath.append lastPath⟩
            simp [List.cons_append, List.append_assoc]

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.final_eq_of_empty
    {hand : Hand} {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand state choices final)
    (hempty : choices = []) :
    final = state := by
  induction hpath with
  | nil =>
        rfl
  | @snoc middle choices choice hprefix hchoice hvalid hcopy ih =>
        simp at hempty

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.split_append
      {hand : Hand} {state final : MentsuHandSearchState}
      {before after : List MentsuHandChoice}
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand state (before ++ after) final) :
      ∃ split,
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand state before split ∧
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand split after final := by
  induction before generalizing state with
  | nil =>
        exact ⟨state, .nil state, by simpa using hpath⟩
  | cons choice before ih =>
        have hnonempty : (choice :: before) ++ after ≠ [] := by
          simp
        obtain ⟨head, tail, firstMiddle, hshape, hfirst, hrest⟩ :=
          AppliesMentsuHandChoicesForwardWithCopyLimit.uncons
            (by simpa [List.cons_append] using hpath) hnonempty
        rcases List.cons.inj hshape with ⟨rfl, rfl⟩
        obtain ⟨split, hbefore, hafter⟩ := ih hrest
        exact ⟨split, hfirst.append hbefore, hafter⟩

end Shanten
