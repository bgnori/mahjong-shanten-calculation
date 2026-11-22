import Shanten.MentsuHand.Basic

/-!
# ChoiceGrouping

Multiplicity-preserving grouping of choice lists by representative tile.
-/

namespace Shanten

open MahjongDomain

def mentsuHandChoiceRepresentative : MentsuHandChoice → Option Tile
  | .skip => none
  | .pair tile => some tile
  | .taatsu (.pair tile) => some tile
  | .taatsu (.sequence suit start) =>
      some (Tile.suited suit ⟨start.val, by omega⟩)
  | .meld (.koutsu tile) => some tile
  | .meld (.shuntsu sequence) =>
      some (Tile.suited sequence.suit ⟨sequence.start.val, by omega⟩)

lemma mentsuHandChoiceRepresentative_mem
    {choice : MentsuHandChoice} {tile : Tile}
    (hrep : mentsuHandChoiceRepresentative choice = some tile) :
    tile ∈ choiceTiles choice := by
  cases choice with
  | skip =>
      simp [mentsuHandChoiceRepresentative] at hrep
  | pair pairTile =>
      simp [mentsuHandChoiceRepresentative] at hrep
      subst tile
      simp [choiceTiles, pairTiles, Pair.tiles, Pair.orderedTiles]
  | taatsu taatsu =>
      cases taatsu with
      | pair pairTile =>
          simp [mentsuHandChoiceRepresentative] at hrep
          subst tile
          simp [choiceTiles, taatsuTiles, pairTiles, Pair.tiles, Pair.orderedTiles]
      | sequence suit start =>
          simp [mentsuHandChoiceRepresentative] at hrep
          subst tile
          simp [choiceTiles, taatsuTiles]
  | meld meld =>
      cases meld with
      | koutsu meldTile =>
          simp [mentsuHandChoiceRepresentative] at hrep
          subst tile
          simp [choiceTiles, MentsuCandidate.tiles, MentsuCandidate.orderedTiles]
      | shuntsu sequence =>
          simp [mentsuHandChoiceRepresentative] at hrep
          subst tile
          simp [choiceTiles, MentsuCandidate.tiles, MentsuCandidate.orderedTiles,
            Shuntsu.orderedTiles, ShuntsuStart.firstRank]

def mentsuHandChoicesForTile
    (tile : Tile) : List MentsuHandChoice → List MentsuHandChoice
  | [] => []
  | choice :: choices =>
      if mentsuHandChoiceRepresentative choice = some tile then
        choice :: mentsuHandChoicesForTile tile choices
      else
        mentsuHandChoicesForTile tile choices

lemma mentsuHandChoicesForTile_sublist
    (tile : Tile) (choices : List MentsuHandChoice) :
    List.Sublist (mentsuHandChoicesForTile tile choices) choices := by
  induction choices with
  | nil =>
      exact .slnil
  | cons choice choices ih =>
      by_cases hrep :
          mentsuHandChoiceRepresentative choice = some tile
      · simpa [mentsuHandChoicesForTile, hrep] using
          (List.Sublist.cons_cons choice ih)
      · simpa [mentsuHandChoicesForTile, hrep] using
          (List.Sublist.cons choice ih)

lemma mentsuHandChoicesForTile_representative
    {tile : Tile} {choices : List MentsuHandChoice}
    {choice : MentsuHandChoice}
    (hmem : choice ∈ mentsuHandChoicesForTile tile choices) :
    mentsuHandChoiceRepresentative choice = some tile := by
  induction choices with
  | nil =>
      simp [mentsuHandChoicesForTile] at hmem
  | cons head choices ih =>
      by_cases hrep :
          mentsuHandChoiceRepresentative head = some tile
      · simp [mentsuHandChoicesForTile, hrep] at hmem
        rcases hmem with rfl | hmem
        · exact hrep
        · exact ih hmem
      · simp [mentsuHandChoicesForTile, hrep] at hmem
        exact ih hmem

def mentsuHandChoicesWithoutTile
    (tile : Tile) : List MentsuHandChoice → List MentsuHandChoice
  | [] => []
  | choice :: choices =>
      if mentsuHandChoiceRepresentative choice = some tile then
      mentsuHandChoicesWithoutTile tile choices
      else
      choice :: mentsuHandChoicesWithoutTile tile choices

lemma mentsuHandChoicesWithoutTile_mem
    {tile : Tile} {choices : List MentsuHandChoice}
    {choice : MentsuHandChoice}
    (hmem : choice ∈ mentsuHandChoicesWithoutTile tile choices) :
    choice ∈ choices := by
  induction choices with
  | nil =>
      simp [mentsuHandChoicesWithoutTile] at hmem
  | cons head choices ih =>
      by_cases hrep :
          mentsuHandChoiceRepresentative head = some tile
      · simp [mentsuHandChoicesWithoutTile, hrep] at hmem
        exact List.mem_cons_of_mem head (ih hmem)
      · simp [mentsuHandChoicesWithoutTile, hrep] at hmem
        rcases hmem with rfl | hmem
        · simp
        · exact List.mem_cons_of_mem head (ih hmem)

def mentsuHandChoicesGroupedByTiles :
    List Tile → List MentsuHandChoice → List MentsuHandChoice
  | [], _ => []
  | tile :: tiles, choices =>
      mentsuHandChoicesForTile tile choices ++
        mentsuHandChoicesGroupedByTiles tiles
          (mentsuHandChoicesWithoutTile tile choices)

def mentsuHandChoicesWithoutTileForTiles :
    List Tile → List MentsuHandChoice → List MentsuHandChoice
  | [], choices => choices
  | tile :: tiles, choices =>
      mentsuHandChoicesWithoutTileForTiles tiles
        (mentsuHandChoicesWithoutTile tile choices)

lemma list_perm_rotate
    {α : Type} (choice : α) (pre suffix : List α) :
    List.Perm (pre ++ choice :: suffix)
      (choice :: pre ++ suffix) := by
  induction pre with
  | nil =>
      exact .refl _
  | cons head pre ih =>
      exact (List.Perm.cons head ih).trans
        (List.Perm.swap choice head (pre ++ suffix))

lemma mentsuHandChoicesForTile_partition
    (tile : Tile) (choices : List MentsuHandChoice) :
    List.Perm
      (mentsuHandChoicesForTile tile choices ++
      mentsuHandChoicesWithoutTile tile choices)
      choices := by
  induction choices with
  | nil =>
      exact .refl _
  | cons choice choices ih =>
      by_cases hrep :
        mentsuHandChoiceRepresentative choice = some tile
      · simp [mentsuHandChoicesForTile, mentsuHandChoicesWithoutTile, hrep]
        exact ih
      · simp [mentsuHandChoicesForTile, mentsuHandChoicesWithoutTile, hrep]
        exact (list_perm_rotate choice
        (mentsuHandChoicesForTile tile choices)
        (mentsuHandChoicesWithoutTile tile choices)).trans
          (List.Perm.cons choice ih)

lemma mentsuHandChoicesWithoutTile_representative_ne
    {tile : Tile} {choices : List MentsuHandChoice}
    {choice : MentsuHandChoice}
    (hmem : choice ∈ mentsuHandChoicesWithoutTile tile choices) :
    mentsuHandChoiceRepresentative choice ≠ some tile := by
  induction choices with
  | nil =>
      simp [mentsuHandChoicesWithoutTile] at hmem
  | cons head choices ih =>
      by_cases hrep :
          mentsuHandChoiceRepresentative head = some tile
      · simp [mentsuHandChoicesWithoutTile, hrep] at hmem
        exact ih hmem
      · simp [mentsuHandChoicesWithoutTile, hrep] at hmem
        rcases hmem with rfl | hmem
        · exact hrep
        · exact ih hmem

lemma mentsuHandChoicesWithoutTile_mem_of_mem_of_ne
    {tile : Tile} {choices : List MentsuHandChoice}
    {choice : MentsuHandChoice}
    (hmem : choice ∈ choices)
    (hne : mentsuHandChoiceRepresentative choice ≠ some tile) :
    choice ∈ mentsuHandChoicesWithoutTile tile choices := by
  induction choices with
  | nil =>
      simp at hmem
  | cons head choices ih =>
      by_cases hrep :
          mentsuHandChoiceRepresentative head = some tile
      · simp only [mentsuHandChoicesWithoutTile, hrep]
        have hmem' : choice = head ∨ choice ∈ choices := by
          simpa using hmem
        rcases hmem' with hmem | hmem
        · subst choice
          exact (hne hrep).elim
        · exact ih hmem
      · simp only [mentsuHandChoicesWithoutTile, hrep]
        have hmem' : choice = head ∨ choice ∈ choices := by
          simpa using hmem
        rcases hmem' with hmem | hmem
        · subst choice
          simp
        · exact List.mem_cons_of_mem head (ih hmem)

lemma mentsuHandChoicesWithoutTileForTiles_mem
    {tiles : List Tile} {choices : List MentsuHandChoice}
    {choice : MentsuHandChoice}
    (hmem : choice ∈
      mentsuHandChoicesWithoutTileForTiles tiles choices) :
    choice ∈ choices := by
  induction tiles generalizing choices with
  | nil =>
      exact hmem
  | cons tile tiles ih =>
      exact mentsuHandChoicesWithoutTile_mem (ih hmem)

lemma mentsuHandChoicesWithoutTileForTiles_representative_ne
    {tiles : List Tile} {choices : List MentsuHandChoice}
    {choice : MentsuHandChoice}
    (hmem : choice ∈
      mentsuHandChoicesWithoutTileForTiles tiles choices) :
    ∀ tile, tile ∈ tiles →
      mentsuHandChoiceRepresentative choice ≠ some tile := by
  induction tiles generalizing choices with
  | nil =>
      intro tile htile
      simp at htile
  | cons tile tiles ih =>
      intro target htarget
      have hmemImmediate :
          choice ∈ mentsuHandChoicesWithoutTile tile choices :=
        mentsuHandChoicesWithoutTileForTiles_mem hmem
      simp only [List.mem_cons] at htarget
      rcases htarget with rfl | htarget
      · exact mentsuHandChoicesWithoutTile_representative_ne
          hmemImmediate
      · exact ih hmem target htarget

lemma mentsuHandChoicesWithoutTileForTiles_eq_nil
    {tiles : List Tile} {choices : List MentsuHandChoice}
    (hrep :
      ∀ choice, choice ∈ choices →
        ∃ tile, tile ∈ tiles ∧
          mentsuHandChoiceRepresentative choice = some tile) :
    mentsuHandChoicesWithoutTileForTiles tiles choices = [] := by
  by_contra hne
  obtain ⟨choice, hchoice⟩ :=
    List.exists_mem_of_ne_nil
      (mentsuHandChoicesWithoutTileForTiles tiles choices) hne
  obtain ⟨tile, htile, hchoiceTile⟩ :=
    hrep choice
      (mentsuHandChoicesWithoutTileForTiles_mem hchoice)
  exact (mentsuHandChoicesWithoutTileForTiles_representative_ne hchoice
    tile htile) hchoiceTile

lemma mentsuHandChoicesGroupedByTiles_perm_append
    {tiles : List Tile} {choices : List MentsuHandChoice}
    (hrep :
      ∀ choice, choice ∈ choices →
        ∃ tile, tile ∈ tiles ∧
          mentsuHandChoiceRepresentative choice = some tile) :
    List.Perm
      (mentsuHandChoicesGroupedByTiles tiles choices ++
        mentsuHandChoicesWithoutTileForTiles tiles choices)
      choices := by
  induction tiles generalizing choices with
  | nil =>
      simp [mentsuHandChoicesGroupedByTiles,
        mentsuHandChoicesWithoutTileForTiles]
  | cons tile tiles ih =>
      have htail :
          ∀ choice, choice ∈
              mentsuHandChoicesWithoutTile tile choices →
            ∃ nextTile, nextTile ∈ tiles ∧
              mentsuHandChoiceRepresentative choice = some nextTile := by
        intro choice hchoice
        obtain ⟨choiceTile, hchoiceTile, hchoiceRep⟩ :=
          hrep choice
            (mentsuHandChoicesWithoutTile_mem hchoice)
        simp only [List.mem_cons] at hchoiceTile
        rcases hchoiceTile with rfl | hchoiceTile
        · exact False.elim
            (mentsuHandChoicesWithoutTile_representative_ne hchoice
              hchoiceRep)
        · exact ⟨_, hchoiceTile, hchoiceRep⟩
      have hpartition :=
        mentsuHandChoicesForTile_partition tile choices
      have hgrouped :=
        ih htail
      simpa [mentsuHandChoicesGroupedByTiles,
        mentsuHandChoicesWithoutTileForTiles, List.append_assoc] using
        ((List.Perm.append_left
            (mentsuHandChoicesForTile tile choices) hgrouped).trans
          hpartition)

lemma mentsuHandChoicesGroupedByTiles_perm
    {tiles : List Tile} {choices : List MentsuHandChoice}
    (hrep :
      ∀ choice, choice ∈ choices →
        ∃ tile, tile ∈ tiles ∧
          mentsuHandChoiceRepresentative choice = some tile) :
    List.Perm
      (mentsuHandChoicesGroupedByTiles tiles choices)
      choices := by
  have hperm :=
    mentsuHandChoicesGroupedByTiles_perm_append hrep
  rw [mentsuHandChoicesWithoutTileForTiles_eq_nil hrep] at hperm
  simpa using hperm

end Shanten
