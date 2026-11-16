import Shanten.MentsuHand.Scan.DecompositionPaths

/-!
# Scan / Grouping

Constructing the complete 34-tile batch scan from a given decomposition.
-/

namespace Shanten

lemma MentsuHandBlockDecomposition.blockChoices_representatives_in_tileOrder
      {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
      ∀ choice, choice ∈ decomposition.blockChoices →
        ∃ tile, tile ∈ mentsuHandTileOrder ∧
          mentsuHandChoiceRepresentative choice = some tile := by
  intro choice hchoice
  have hnotSkip := decomposition.blockChoices_ne_skip hchoice
  cases choice with
  | skip =>
        exact (hnotSkip rfl).elim
  | pair tile =>
        exact ⟨tile, tile_mem_mentsuHandTileOrder tile, rfl⟩
  | taatsu taatsu =>
        cases taatsu with
        | pair tile =>
            exact ⟨tile, tile_mem_mentsuHandTileOrder tile, rfl⟩
        | sequence suit start =>
            exact ⟨Tile.suited suit ⟨start.val, by omega⟩,
              tile_mem_mentsuHandTileOrder _, rfl⟩
  | meld meld =>
        cases meld with
        | triplet tile =>
            exact ⟨tile, tile_mem_mentsuHandTileOrder tile, rfl⟩
        | sequence suit start =>
            exact ⟨Tile.suited suit ⟨start.val, by omega⟩,
              tile_mem_mentsuHandTileOrder _, rfl⟩

lemma AppliesMentsuHandGroupedTileBatches.of_forward_grouping
      {hand : Hand} {tiles : List Tile}
      {source : List MentsuHandChoice}
      {state final : MentsuHandSearchState}
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand state (mentsuHandChoicesGroupedByTiles tiles source) final)
      (hrep :
        ∀ choice, choice ∈ source →
          ∃ tile, tile ∈ tiles ∧
            mentsuHandChoiceRepresentative choice = some tile) :
      AppliesMentsuHandGroupedTileBatches hand tiles source state final := by
  induction tiles generalizing source state with
  | nil =>
        have hsource : source = [] := by
          cases source with
          | nil => rfl
          | cons choice source =>
              obtain ⟨tile, htile, _⟩ := hrep choice (by simp)
              simp at htile
        subst source
        have hpathEmpty :
            AppliesMentsuHandChoicesForwardWithCopyLimit hand state [] final := by
          simpa [mentsuHandChoicesGroupedByTiles] using hpath
        have hfinal :=
          hpathEmpty.final_eq_of_empty rfl
        rw [hfinal]
        exact .nil state
  | cons tile tiles ih =>
        have htailRep :
            ∀ choice, choice ∈ mentsuHandChoicesWithoutTile tile source →
              ∃ nextTile, nextTile ∈ tiles ∧
                mentsuHandChoiceRepresentative choice = some nextTile := by
          intro choice hchoice
          obtain ⟨nextTile, hmem, hrepChoice⟩ :=
            hrep choice (mentsuHandChoicesWithoutTile_mem hchoice)
          have hne :=
            mentsuHandChoicesWithoutTile_representative_ne hchoice
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact (hne hrepChoice).elim
          · exact ⟨nextTile, hmem, hrepChoice⟩
        have hsplit :=
          AppliesMentsuHandChoicesForwardWithCopyLimit.split_append
            (by simpa [mentsuHandChoicesGroupedByTiles] using hpath)
        obtain ⟨middle, hbatchPath, htailPath⟩ := hsplit
        have hbatch :
            AppliesMentsuHandChoiceBatch hand tile state
              (mentsuHandChoicesForTile tile source) middle :=
          AppliesMentsuHandChoiceBatch.of_forward_for_tile_filter hbatchPath
        have htail := ih htailPath htailRep
        exact .step tile tiles source state middle final hbatch htail

lemma MentsuHandBlockDecomposition.forwardPath_groupedByTiles
      {hand : Hand}
      (decomposition : MentsuHandBlockDecomposition hand) :
      ∃ final,
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState
            (mentsuHandChoicesGroupedByTiles
              mentsuHandTileOrder decomposition.blockChoices) final := by
  apply decomposition.forwardPath_of_perm
  exact mentsuHandChoicesGroupedByTiles_perm
      decomposition.blockChoices_representatives_in_tileOrder

lemma MentsuHandBlockDecomposition.blockChoices_pair_choice
      {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand)
      {choice : MentsuHandChoice}
      (hchoice : choice ∈ decomposition.blockChoices)
      (hpair : choiceUsesPair choice = true) :
      choice = .pair decomposition.pair := by
  cases choice with
  | skip =>
        simp [choiceUsesPair] at hpair
  | pair tile =>
        change MentsuHandChoice.pair tile ∈ decomposition.blockChoices at hchoice
        unfold MentsuHandBlockDecomposition.blockChoices at hchoice
        simp only [List.mem_cons, List.mem_append, List.mem_map] at hchoice
        rcases hchoice with hpairChoice | htail
        · simpa using hpairChoice
        · simp at htail
  | taatsu taatsu =>
        simp [choiceUsesPair] at hpair
  | meld meld =>
        simp [choiceUsesPair] at hpair

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.pair_eq_none_or_target
      {hand : Hand} {choices : List MentsuHandChoice}
      {final : MentsuHandSearchState} {pair : Tile}
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState choices final)
      (hpairChoices :
        ∀ choice, choice ∈ choices →
          choiceUsesPair choice = true → choice = .pair pair) :
      final.pair = none ∨ final.pair = some pair := by
  induction hpath with
  | nil =>
        exact Or.inl rfl
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
        have hprefix :
            ∀ candidate, candidate ∈ choices →
              choiceUsesPair candidate = true →
                candidate = .pair pair := by
          intro candidate hmem huses
          apply hpairChoices candidate
          · exact List.mem_append_left [choice] hmem
          · exact huses
        have hprev := ih hprefix
        have hlast :
            choiceUsesPair choice = true → choice = .pair pair := by
          intro huses
          exact hpairChoices choice (by simp) huses
        cases choice with
        | pair tile =>
            have hchoiceEq := hlast rfl
            cases hchoiceEq
            simp [applyMentsuHandChoice]
        | skip =>
            simpa [applyMentsuHandChoice] using hprev
        | taatsu taatsu =>
            simpa [applyMentsuHandChoice] using hprev
        | meld meld =>
            simpa [applyMentsuHandChoice] using hprev

lemma AppliesMentsuHandChoicesForwardWithCopyLimit.pair_isSome_of_pairCount_pos
      {hand : Hand} {choices : List MentsuHandChoice}
      {final : MentsuHandSearchState}
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState choices final)
      (hcount : 0 < mentsuHandChoicePairCount choices) :
      final.pair.isSome := by
  induction hpath with
  | nil =>
        simp [mentsuHandChoicePairCount] at hcount
  | @snoc middle choices choice hpath hchoice hvalid hcopy ih =>
        rw [mentsuHandChoicePairCount_append] at hcount
        cases choice with
        | pair tile =>
            simp [applyMentsuHandChoice]
        | skip =>
            have hprefix : 0 < mentsuHandChoicePairCount choices := by
              simpa [mentsuHandChoicePairCount] using hcount
            simpa [applyMentsuHandChoice] using ih hprefix
        | taatsu taatsu =>
            have hprefix : 0 < mentsuHandChoicePairCount choices := by
              simpa [mentsuHandChoicePairCount] using hcount
            simpa [applyMentsuHandChoice] using ih hprefix
        | meld meld =>
            have hprefix : 0 < mentsuHandChoicePairCount choices := by
              simpa [mentsuHandChoicePairCount] using hcount
            simpa [applyMentsuHandChoice] using ih hprefix

lemma MentsuHandBlockDecomposition.finalState_of_groupedForwardPath
      {hand : Hand}
      (decomposition : MentsuHandBlockDecomposition hand)
      {final : MentsuHandSearchState}
      (hpath :
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState
            (mentsuHandChoicesGroupedByTiles
              mentsuHandTileOrder decomposition.blockChoices) final) :
      final.pair = some decomposition.pair ∧
        IsMentsuHandBlockSearchComplete hand final := by
  let choices :=
      mentsuHandChoicesGroupedByTiles
        mentsuHandTileOrder decomposition.blockChoices
  have hperm : List.Perm choices decomposition.blockChoices :=
      mentsuHandChoicesGroupedByTiles_perm
        decomposition.blockChoices_representatives_in_tileOrder
  have hpairChoices :
        ∀ choice, choice ∈ choices →
          choiceUsesPair choice = true →
            choice = .pair decomposition.pair := by
      intro choice hchoice hpair
      exact decomposition.blockChoices_pair_choice
        ((List.Perm.mem_iff hperm).1 hchoice) hpair
  have hpairState := hpath.pair_eq_none_or_target hpairChoices
  have hpairCount : 0 < mentsuHandChoicePairCount choices := by
      rw [mentsuHandChoicePairCount_of_perm hperm,
        decomposition.blockChoices_pairCount]
      omega
  have hpairSome := hpath.pair_isSome_of_pairCount_pos hpairCount
  have hpair : final.pair = some decomposition.pair := by
      rcases hpairState with hnone | hsome
      · simp [hnone] at hpairSome
      · exact hsome
  have hmatches := hpath.state_matches_from_initial
  have hmelds :
        final.melds = decomposition.melds.length := by
      calc
        final.melds = mentsuHandChoiceMeldCount choices := hmatches.2.1
        _ = mentsuHandChoiceMeldCount decomposition.blockChoices :=
          mentsuHandChoiceMeldCount_of_perm hperm
        _ = decomposition.melds.length :=
          decomposition.blockChoices_meldCount
  have htaatsu :
        final.taatsu = decomposition.taatsus.length := by
      calc
        final.taatsu = mentsuHandChoiceTaatsuCount choices := hmatches.2.2
        _ = mentsuHandChoiceTaatsuCount decomposition.blockChoices :=
          mentsuHandChoiceTaatsuCount_of_perm hperm
        _ = decomposition.taatsus.length :=
          decomposition.blockChoices_taatsuCount
  refine ⟨hpair, ?_⟩
  unfold IsMentsuHandBlockSearchComplete
  constructor
  · rw [hmelds, htaatsu]
    exact decomposition.blocks
  · simp [hpair]

lemma MentsuHandBlockDecomposition.exists_groupedForwardPath_complete
      {hand : Hand}
      (decomposition : MentsuHandBlockDecomposition hand) :
      ∃ final,
        AppliesMentsuHandChoicesForwardWithCopyLimit
          hand initialMentsuHandState
            (mentsuHandChoicesGroupedByTiles
              mentsuHandTileOrder decomposition.blockChoices) final ∧
        final.pair = some decomposition.pair ∧
        IsMentsuHandBlockSearchComplete hand final := by
  obtain ⟨final, hpath⟩ :=
      decomposition.forwardPath_groupedByTiles
  exact ⟨final, hpath,
      decomposition.finalState_of_groupedForwardPath hpath⟩

lemma MentsuHandBlockDecomposition.exists_tileBatchScan_complete
      {hand : Hand}
      (decomposition : MentsuHandBlockDecomposition hand) :
      ∃ final,
        AppliesMentsuHandTileBatchScan hand mentsuHandTileOrder
          initialMentsuHandState
          (mentsuHandChoicesGroupedByTiles
            mentsuHandTileOrder decomposition.blockChoices) final ∧
        final.pair = some decomposition.pair ∧
        IsMentsuHandBlockSearchComplete hand final := by
  obtain ⟨final, hpath, hpair, hcomplete⟩ :=
      decomposition.exists_groupedForwardPath_complete
  have hgrouped :=
      AppliesMentsuHandGroupedTileBatches.of_forward_grouping hpath
        decomposition.blockChoices_representatives_in_tileOrder
  exact ⟨final, hgrouped.to_scan, hpair, hcomplete⟩

end Shanten
