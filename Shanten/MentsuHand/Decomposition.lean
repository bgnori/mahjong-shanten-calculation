import Shanten.MentsuHand.ChoiceGrouping
import Shanten.MentsuHand.Exchange

/-!
# Decomposition

Four-block decompositions, choice multiplicities, and completion copy limits.
-/

namespace Shanten

open MahjongDomain

/-- A target has the required number of concealed melds for a hand. -/
def HasMentsuHandMeldCount (hand : Hand) (melds : List Meld) : Prop :=
  melds.length + hand.fixedMelds = 4

/-- A mentsu-hand-form decomposition before completing its taatsu blocks. -/
structure MentsuHandBlockDecomposition (hand : Hand) where
  pair : Tile
  melds : List Meld
  taatsus : List Taatsu
  blocks : melds.length + taatsus.length + hand.fixedMelds = 4
  targetWithinHand :
    ∀ tile,
      (mentsuHandTargetWithTaatsu pair melds taatsus).count tile ≤ hand.counts tile
  completionCopyLimit :
    ∀ tile,
      (mentsuHandTargetWithTaatsu pair melds taatsus +
        taatsuCompletionTiles taatsus).count tile ≤ 4

def mentsuHandChoiceTiles : List MentsuHandChoice → Multiset Tile
  | [] => 0
  | choice :: choices =>
      choiceTiles choice + mentsuHandChoiceTiles choices

def mentsuHandChoiceMeldCount : List MentsuHandChoice → Nat
  | [] => 0
  | choice :: choices =>
      (if choiceUsesMeld choice = true then 1 else 0) +
        mentsuHandChoiceMeldCount choices

def mentsuHandChoiceTaatsuCount : List MentsuHandChoice → Nat
  | [] => 0
  | choice :: choices =>
      (if choiceUsesTaatsu choice = true then 1 else 0) +
        mentsuHandChoiceTaatsuCount choices

def mentsuHandChoiceTaatsus : List MentsuHandChoice → List Taatsu
  | [] => []
  | .taatsu taatsu :: choices =>
      taatsu :: mentsuHandChoiceTaatsus choices
  | _ :: choices =>
      mentsuHandChoiceTaatsus choices

/-- Multiplicity-aware inclusion of choice columns.

Unlike `List.Sublist`, this relation does not impose an order on the selected
choices. It is the intermediate relation needed when a column is regrouped by
tile kind: repeated equal choices remain repeated, so a plain set inclusion is
not sufficient.
-/
def MentsuHandChoiceSubmultiset
    (subset superset : List MentsuHandChoice) : Prop :=
  (subset : Multiset MentsuHandChoice) ≤ superset

lemma MentsuHandChoiceSubmultiset.refl
    (choices : List MentsuHandChoice) :
    MentsuHandChoiceSubmultiset choices choices :=
  le_rfl

lemma MentsuHandChoiceSubmultiset.trans
    {left middle right : List MentsuHandChoice}
    (hleft : MentsuHandChoiceSubmultiset left middle)
    (hright : MentsuHandChoiceSubmultiset middle right) :
    MentsuHandChoiceSubmultiset left right :=
  le_trans hleft hright

lemma MentsuHandChoiceSubmultiset.of_perm
    {subset subset' superset : List MentsuHandChoice}
    (hperm : subset.Perm subset')
    (hsub : MentsuHandChoiceSubmultiset subset superset) :
    MentsuHandChoiceSubmultiset subset' superset := by
  have hsubset : (subset : Multiset MentsuHandChoice) =
      (subset' : Multiset MentsuHandChoice) :=
    Multiset.coe_eq_coe.mpr hperm
  simpa [MentsuHandChoiceSubmultiset, hsubset] using hsub

lemma MentsuHandChoiceSubmultiset.mem
    {subset superset : List MentsuHandChoice}
    (hsub : MentsuHandChoiceSubmultiset subset superset)
    {choice : MentsuHandChoice}
    (hchoice : choice ∈ subset) :
    choice ∈ superset :=
  Multiset.mem_of_le hsub hchoice

lemma MentsuHandChoiceSubmultiset.of_sublist
    {subset superset : List MentsuHandChoice}
    (hsub : List.Sublist subset superset) :
    MentsuHandChoiceSubmultiset subset superset := by
  induction hsub with
  | slnil =>
      exact bot_le
  | cons choice hsub ih =>
      simp only [MentsuHandChoiceSubmultiset] at ih ⊢
      exact ih.trans (Multiset.le_add_left
        _ ({choice} : Multiset MentsuHandChoice))
  | cons_cons choice hsub ih =>
      simp only [MentsuHandChoiceSubmultiset] at ih ⊢
      exact add_le_add
        (show ({choice} : Multiset MentsuHandChoice) ≤ {choice} from le_rfl)
        ih

lemma mentsuHandChoicesForTile_submultiset
    (tile : Tile) (choices : List MentsuHandChoice) :
    MentsuHandChoiceSubmultiset
      (mentsuHandChoicesForTile tile choices) choices :=
  MentsuHandChoiceSubmultiset.of_sublist
    (mentsuHandChoicesForTile_sublist tile choices)

lemma MentsuHandChoiceSubmultiset.append_left
    (left right : List MentsuHandChoice) :
    MentsuHandChoiceSubmultiset left (left ++ right) := by
  change (left : Multiset MentsuHandChoice) ≤
    (left : Multiset MentsuHandChoice) + right
  exact Multiset.le_add_right _ _

lemma MentsuHandChoiceSubmultiset.append_right
    (left right : List MentsuHandChoice) :
    MentsuHandChoiceSubmultiset right (left ++ right) := by
  change (right : Multiset MentsuHandChoice) ≤
    (left : Multiset MentsuHandChoice) + right
  exact Multiset.le_add_left _ _

lemma MentsuHandChoiceSubmultiset.append
    {left left' right right' : List MentsuHandChoice}
    (hleft : MentsuHandChoiceSubmultiset left left')
    (hright : MentsuHandChoiceSubmultiset right right') :
    MentsuHandChoiceSubmultiset (left ++ right) (left' ++ right') := by
  change (left ++ right : Multiset MentsuHandChoice) ≤
    (left' ++ right' : Multiset MentsuHandChoice)
  change (left : Multiset MentsuHandChoice) + right ≤
    (left' : Multiset MentsuHandChoice) + right'
  exact add_le_add hleft hright

lemma mentsuHandChoiceTaatsus_of_perm
    {choices choices' : List MentsuHandChoice}
    (hperm : List.Perm choices choices') :
    List.Perm (mentsuHandChoiceTaatsus choices)
      (mentsuHandChoiceTaatsus choices') := by
  induction hperm with
  | nil =>
      exact .nil
  | cons choice hperm ih =>
      cases choice <;>
        simp only [mentsuHandChoiceTaatsus, List.Perm.cons, ih]
  | swap choice choice' choices =>
      cases choice <;> cases choice' <;>
        simp only [mentsuHandChoiceTaatsus] <;>
        try rfl
      apply List.Perm.swap
  | trans hperm hperm' ih ih' =>
      exact ih.trans ih'

lemma mentsuHandChoiceTaatsus_append
    (choices choices' : List MentsuHandChoice) :
    mentsuHandChoiceTaatsus (choices ++ choices') =
      mentsuHandChoiceTaatsus choices ++ mentsuHandChoiceTaatsus choices' := by
  induction choices with
  | nil => rfl
  | cons choice choices ih =>
      cases choice <;>
        simp only [List.cons_append, mentsuHandChoiceTaatsus, ih]

lemma mentsuHandChoiceTaatsus_sublist_of_sublist
    {subset choices : List MentsuHandChoice}
    (hsub : List.Sublist subset choices) :
    List.Sublist (mentsuHandChoiceTaatsus subset)
      (mentsuHandChoiceTaatsus choices) := by
  induction hsub with
  | slnil =>
      exact .slnil
  | cons choice hsub ih =>
      cases choice with
      | skip | pair | meld =>
          simp only [mentsuHandChoiceTaatsus]
          exact ih
      | taatsu taatsu =>
          simp only [mentsuHandChoiceTaatsus]
          exact .cons _ ih
  | cons_cons choice hsub ih =>
      cases choice with
      | skip | pair | meld =>
          simp only [mentsuHandChoiceTaatsus]
          exact ih
      | taatsu taatsu =>
          simp only [mentsuHandChoiceTaatsus]
          exact .cons₂ taatsu ih

lemma mentsuHandChoiceTaatsus_sublist_append
    (choices choices' : List MentsuHandChoice) :
    List.Sublist (mentsuHandChoiceTaatsus choices)
      (mentsuHandChoiceTaatsus (choices ++ choices')) := by
  rw [mentsuHandChoiceTaatsus_append]
  induction mentsuHandChoiceTaatsus choices with
  | nil =>
      simp
  | cons taatsu taatsus ih =>
      exact List.Sublist.cons₂ taatsu ih

lemma mentsuHandChoiceMeldCount_append
    (left right : List MentsuHandChoice) :
    mentsuHandChoiceMeldCount (left ++ right) =
      mentsuHandChoiceMeldCount left +
        mentsuHandChoiceMeldCount right := by
  induction left with
  | nil =>
      simp [mentsuHandChoiceMeldCount]
  | cons choice left ih =>
      simp [mentsuHandChoiceMeldCount, ih, Nat.add_assoc]

lemma mentsuHandChoiceTaatsuCount_append
    (left right : List MentsuHandChoice) :
    mentsuHandChoiceTaatsuCount (left ++ right) =
      mentsuHandChoiceTaatsuCount left +
        mentsuHandChoiceTaatsuCount right := by
  induction left with
  | nil =>
      simp [mentsuHandChoiceTaatsuCount]
  | cons choice left ih =>
      simp [mentsuHandChoiceTaatsuCount, ih, Nat.add_assoc]

lemma mentsuHandChoiceTiles_append
    (left right : List MentsuHandChoice) :
    mentsuHandChoiceTiles (left ++ right) =
      mentsuHandChoiceTiles left + mentsuHandChoiceTiles right := by
  induction left with
  | nil =>
      simp [mentsuHandChoiceTiles]
  | cons choice left ih =>
      simp [mentsuHandChoiceTiles, ih, Multiset.add_assoc]

lemma mentsuHandChoiceTiles_of_perm
    {choices choices' : List MentsuHandChoice}
    (hperm : List.Perm choices choices') :
    mentsuHandChoiceTiles choices =
      mentsuHandChoiceTiles choices' := by
  induction hperm with
  | nil =>
      rfl
  | cons choice hperm ih =>
      simp [mentsuHandChoiceTiles, ih]
  | swap choice choice' choices =>
      simp [mentsuHandChoiceTiles, add_comm, add_left_comm, add_assoc]
  | trans hperm hperm' ih ih' =>
      exact ih.trans ih'

lemma mentsuHandChoiceMeldCount_of_perm
    {choices choices' : List MentsuHandChoice}
    (hperm : List.Perm choices choices') :
    mentsuHandChoiceMeldCount choices =
      mentsuHandChoiceMeldCount choices' := by
  induction hperm with
  | nil =>
      rfl
  | cons choice hperm ih =>
      simp [mentsuHandChoiceMeldCount, ih]
  | swap choice choice' choices =>
      simp [mentsuHandChoiceMeldCount, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc]
  | trans hperm hperm' ih ih' =>
      exact ih.trans ih'

lemma mentsuHandChoiceTaatsuCount_of_perm
    {choices choices' : List MentsuHandChoice}
    (hperm : List.Perm choices choices') :
    mentsuHandChoiceTaatsuCount choices =
      mentsuHandChoiceTaatsuCount choices' := by
  induction hperm with
  | nil =>
      rfl
  | cons choice hperm ih =>
      simp [mentsuHandChoiceTaatsuCount, ih]
  | swap choice choice' choices =>
      simp [mentsuHandChoiceTaatsuCount, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc]
  | trans hperm hperm' ih ih' =>
      exact ih.trans ih'

def MentsuHandBlockDecomposition.blockChoices
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    List MentsuHandChoice :=
  .pair decomposition.pair ::
    decomposition.melds.map MentsuHandChoice.meld ++
      decomposition.taatsus.map MentsuHandChoice.taatsu

lemma MentsuHandBlockDecomposition.blockChoices_length
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    decomposition.blockChoices.length =
      1 + decomposition.melds.length + decomposition.taatsus.length := by
  simp [MentsuHandBlockDecomposition.blockChoices]
  omega

lemma MentsuHandBlockDecomposition.blockChoices_meldCount
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    mentsuHandChoiceMeldCount decomposition.blockChoices =
      decomposition.melds.length := by
  have aux : ∀ melds : List Meld,
      mentsuHandChoiceMeldCount (melds.map MentsuHandChoice.meld) =
        melds.length := by
    intro melds
    induction melds with
    | nil =>
        simp [mentsuHandChoiceMeldCount]
    | cons meld melds ih =>
        simp [mentsuHandChoiceMeldCount, choiceUsesMeld, ih, Nat.add_comm]
  have auxZero : ∀ taatsus : List Taatsu,
      mentsuHandChoiceMeldCount (taatsus.map MentsuHandChoice.taatsu) = 0 := by
    intro taatsus
    induction taatsus with
    | nil =>
        rfl
    | cons taatsu taatsus ih =>
        simp [mentsuHandChoiceMeldCount, choiceUsesMeld, ih]
  simp [MentsuHandBlockDecomposition.blockChoices,
    mentsuHandChoiceMeldCount, choiceUsesMeld,
    mentsuHandChoiceMeldCount_append, aux, auxZero, Nat.add_comm] <;> omega

lemma MentsuHandBlockDecomposition.blockChoices_taatsuCount
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    mentsuHandChoiceTaatsuCount decomposition.blockChoices =
      decomposition.taatsus.length := by
  have aux : ∀ taatsus : List Taatsu,
      mentsuHandChoiceTaatsuCount (taatsus.map MentsuHandChoice.taatsu) =
        taatsus.length := by
    intro taatsus
    induction taatsus with
    | nil =>
        simp [mentsuHandChoiceTaatsuCount]
    | cons taatsu taatsus ih =>
        simp [mentsuHandChoiceTaatsuCount, choiceUsesTaatsu, ih, Nat.add_comm]
  have auxZero : ∀ melds : List Meld,
      mentsuHandChoiceTaatsuCount (melds.map MentsuHandChoice.meld) = 0 := by
    intro melds
    induction melds with
    | nil =>
        rfl
    | cons meld melds ih =>
        simp [mentsuHandChoiceTaatsuCount, choiceUsesTaatsu, ih]
  simp [MentsuHandBlockDecomposition.blockChoices,
    mentsuHandChoiceTaatsuCount, choiceUsesTaatsu,
    mentsuHandChoiceTaatsuCount_append, aux, auxZero, Nat.add_comm] <;> omega

lemma MentsuHandBlockDecomposition.blockChoices_tail_not_pair
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand)
    (choice : MentsuHandChoice)
    (hchoice :
      choice ∈
        decomposition.melds.map MentsuHandChoice.meld ++
          decomposition.taatsus.map MentsuHandChoice.taatsu) :
    choiceUsesPair choice = false := by
  simp only [List.mem_append, List.mem_map] at hchoice
  rcases hchoice with hmeld | htaatsu
  · rcases hmeld with ⟨meld, _, rfl⟩
    rfl
  · rcases htaatsu with ⟨taatsu, _, rfl⟩
    rfl

lemma MentsuHandBlockDecomposition.blockChoices_mem_all
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    ∀ choice, choice ∈ decomposition.blockChoices →
      choice ∈ allMentsuHandChoices := by
  intro choice hchoice
  unfold MentsuHandBlockDecomposition.blockChoices at hchoice
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hchoice
  rcases hchoice with (hpair | hmeld) | htaatsu
  · rw [hpair]
    exact mentsuHandChoice_mem_all _
  · rcases hmeld with ⟨meld, _, hmeld⟩
    rw [← hmeld]
    exact mentsuHandChoice_mem_all _
  · rcases htaatsu with ⟨taatsu, _, htaatsu⟩
    rw [← htaatsu]
    exact mentsuHandChoice_mem_all _

lemma MentsuHandBlockDecomposition.blockChoices_ne_skip
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand)
    {choice : MentsuHandChoice}
    (hchoice : choice ∈ decomposition.blockChoices) :
    choice ≠ .skip := by
  unfold MentsuHandBlockDecomposition.blockChoices at hchoice
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hchoice
  rcases hchoice with (rfl | ⟨meld, _, rfl⟩) | ⟨taatsu, _, rfl⟩
  · simp
  · simp
  · simp

lemma mentsuHandChoiceTiles_map_meld
    (melds : List Meld) :
    mentsuHandChoiceTiles (melds.map MentsuHandChoice.meld) =
      meldsTiles melds := by
  induction melds with
  | nil =>
      rfl
  | cons meld melds ih =>
      simp [mentsuHandChoiceTiles, choiceTiles, meldsTiles, ih]

lemma mentsuHandChoiceTiles_map_taatsu
    (taatsus : List Taatsu) :
    mentsuHandChoiceTiles (taatsus.map MentsuHandChoice.taatsu) =
      taatsuHistoryTiles taatsus := by
  induction taatsus with
  | nil =>
      rfl
  | cons taatsu taatsus ih =>
      simp [mentsuHandChoiceTiles, choiceTiles, taatsuHistoryTiles, ih]

lemma mentsuHandChoiceTaatsus_map_taatsu
   (taatsus : List Taatsu) :
   mentsuHandChoiceTaatsus (taatsus.map MentsuHandChoice.taatsu) =
     taatsus := by
  induction taatsus with
  | nil =>
     rfl
  | cons taatsu taatsus ih =>
     simp [mentsuHandChoiceTaatsus, ih]

lemma MentsuHandBlockDecomposition.blockChoices_taatsus
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    mentsuHandChoiceTaatsus decomposition.blockChoices =
     decomposition.taatsus := by
  have hmelds : ∀ melds : List Meld,
     mentsuHandChoiceTaatsus (melds.map MentsuHandChoice.meld) = [] := by
    intro melds
    induction melds with
    | nil =>
       rfl
    | cons meld melds ih =>
       simp [ih, mentsuHandChoiceTaatsus]
  unfold MentsuHandBlockDecomposition.blockChoices
  simp only [mentsuHandChoiceTaatsus, mentsuHandChoiceTaatsus_append,
    hmelds, List.nil_append, mentsuHandChoiceTaatsus_map_taatsu]

lemma MentsuHandBlockDecomposition.blockChoices_tiles
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    mentsuHandChoiceTiles decomposition.blockChoices =
      mentsuHandTargetWithTaatsu decomposition.pair decomposition.melds
        decomposition.taatsus := by
  unfold MentsuHandBlockDecomposition.blockChoices
  simp [mentsuHandChoiceTiles, choiceTiles, List.map_append,
    mentsuHandChoiceTiles_append,
    mentsuHandChoiceTiles_map_meld, mentsuHandChoiceTiles_map_taatsu,
    mentsuHandTargetWithTaatsu, mentsuHandTarget]
  ac_rfl

lemma mentsuHandChoiceTiles_count_le_of_sublist
    {subset choices : List MentsuHandChoice}
    (hsub : List.Sublist subset choices) :
    ∀ tile,
      (mentsuHandChoiceTiles subset).count tile ≤
        (mentsuHandChoiceTiles choices).count tile := by
  induction hsub with
  | slnil =>
      simp
  | cons choice hsub ih =>
      intro tile
      simp only [mentsuHandChoiceTiles, Multiset.count_add]
      exact (ih tile).trans (Nat.le_add_left _ _)
  | cons_cons choice hsub ih =>
      intro tile
      simp only [mentsuHandChoiceTiles, Multiset.count_add]
      have htail := ih tile
      omega

lemma mentsuHandChoiceMeldCount_le_of_sublist
    {subset choices : List MentsuHandChoice}
    (hsub : List.Sublist subset choices) :
    mentsuHandChoiceMeldCount subset ≤
      mentsuHandChoiceMeldCount choices := by
  induction hsub with
  | slnil =>
      simp [mentsuHandChoiceMeldCount]
  | cons choice hsub ih =>
      simp only [mentsuHandChoiceMeldCount] at ih ⊢
      omega
  | cons_cons choice hsub ih =>
      simp only [mentsuHandChoiceMeldCount] at ih ⊢
      omega

lemma mentsuHandChoiceTaatsuCount_le_of_sublist
    {subset choices : List MentsuHandChoice}
    (hsub : List.Sublist subset choices) :
    mentsuHandChoiceTaatsuCount subset ≤
      mentsuHandChoiceTaatsuCount choices := by
  induction hsub with
  | slnil =>
      simp [mentsuHandChoiceTaatsuCount]
  | cons choice hsub ih =>
      simp only [mentsuHandChoiceTaatsuCount] at ih ⊢
      omega
  | cons_cons choice hsub ih =>
      simp only [mentsuHandChoiceTaatsuCount] at ih ⊢
      omega

def MentsuHandBlockDecomposition.completedTarget
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    Multiset Tile :=
  mentsuHandTargetWithTaatsu decomposition.pair decomposition.melds
      decomposition.taatsus +
    taatsuCompletionTiles decomposition.taatsus

lemma MentsuHandBlockDecomposition.completedTarget_eq
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    decomposition.completedTarget =
      pairTiles decomposition.pair +
        meldsTiles
          (decomposition.melds ++
            taatsuCompletionMelds decomposition.taatsus) := by
  unfold MentsuHandBlockDecomposition.completedTarget
    mentsuHandTargetWithTaatsu mentsuHandTarget
  rw [meldsTiles_append]
  rw [← taatsuHistoryTiles_add_completionTiles]
  ac_rfl

lemma MentsuHandBlockDecomposition.validCounts_completedTarget
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    ValidCounts
      (targetHand hand (countsOfTiles decomposition.completedTarget)) := by
  intro tile
  exact decomposition.completionCopyLimit tile

lemma MentsuHandBlockDecomposition.completedMeldCount
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    (decomposition.melds ++
      taatsuCompletionMelds decomposition.taatsus).length +
        hand.fixedMelds = 4 := by
  rw [List.length_append, taatsuCompletionMelds_length]
  have hblocks := decomposition.blocks
  omega

def completedTargetForState (state : MentsuHandSearchState) (pair : Tile) :
    Multiset Tile :=
  pairTiles pair + meldsTiles (completedMeldsForState state)

def CompletionRespectsCopyLimit (state : MentsuHandSearchState) : Prop :=
  ∀ tile,
    (state.used + taatsuCompletionTiles state.taatsuHistory.reverse).count tile ≤ 4

lemma completionRespectsCopyLimit_of_history_perm
    (state : MentsuHandSearchState) (taatsus : List Taatsu)
    (hperm : List.Perm state.taatsuHistory.reverse taatsus)
    (hcopy : CompletionRespectsCopyLimit state) :
    ∀ tile,
      (state.used + taatsuCompletionTiles taatsus).count tile ≤ 4 := by
  intro tile
  rw [← taatsuCompletionTiles_of_perm hperm]
  exact hcopy tile

lemma MentsuHandBlockDecomposition.completion_respects_of_perm
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand)
    {state : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hperm : List.Perm choices decomposition.blockChoices)
    (hused : state.used = mentsuHandChoiceTiles choices)
    (hhistory :
      state.taatsuHistory.reverse =
        mentsuHandChoiceTaatsus choices) :
    CompletionRespectsCopyLimit state := by
  intro tile
  rw [hused]
  have husedPerm :
      mentsuHandChoiceTiles choices =
        mentsuHandChoiceTiles decomposition.blockChoices :=
    mentsuHandChoiceTiles_of_perm hperm
  rw [husedPerm]
  have hfull :
      (mentsuHandChoiceTiles decomposition.blockChoices +
        taatsuCompletionTiles decomposition.taatsus).count tile ≤ 4 := by
    rw [decomposition.blockChoices_tiles]
    exact decomposition.completionCopyLimit tile
  have htaatsuPerm :
      List.Perm
        (mentsuHandChoiceTaatsus choices)
        decomposition.taatsus := by
    rw [← decomposition.blockChoices_taatsus]
    exact mentsuHandChoiceTaatsus_of_perm hperm
  rw [hhistory, taatsuCompletionTiles_of_perm htaatsuPerm]
  rw [Multiset.count_add] at hfull ⊢
  exact hfull

end Shanten
