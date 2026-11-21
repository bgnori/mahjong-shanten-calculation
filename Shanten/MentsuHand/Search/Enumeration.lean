import Shanten.MentsuHand.Decomposition

/-!
# Search / Enumeration

Finite completion configurations, tile-state enumeration, and validity checks.
-/

namespace Shanten

open MahjongDomain

/-- A target is a valid mentsu-hand-form completion for the standing tiles. -/


def IsMentsuHandTarget
    (hand : Hand) (pair : Tile) (melds : List MentsuCandidate) : Prop :=
  HasMentsuHandMeldCount hand melds ∧
    ∀ tile, hand.counts tile ≤
      (mentsuHandTarget pair melds).count tile

/-- The number of additional tiles needed to realize a mentsuHand target. -/
def mentsuHandTargetDistance
    (hand : Hand) (pair : Tile) (melds : List MentsuCandidate) : Nat :=
  targetDeficit hand (mentsuHandTarget pair melds)

lemma mentsuHandTargetDistance_eq_countDeficit
    (hand : Hand) (pair : Tile) (melds : List MentsuCandidate) :
    mentsuHandTargetDistance hand pair melds =
      countDeficit hand.counts
        (countsOfTiles (mentsuHandTarget pair melds)) := by
  rfl

def mentsuHandMeldListsOfLength : Nat → Finset (List MentsuCandidate)
  | 0 => {[]}
  | length + 1 =>
      Finset.univ.biUnion fun meld =>
        (mentsuHandMeldListsOfLength length).image (meld :: ·)

lemma mem_mentsuHandMeldListsOfLength_iff
    (length : Nat) (melds : List MentsuCandidate) :
    melds ∈ mentsuHandMeldListsOfLength length ↔ melds.length = length := by
  induction length generalizing melds with
  | zero =>
      simp [mentsuHandMeldListsOfLength]
  | succ length ih =>
      simp only [mentsuHandMeldListsOfLength, Finset.mem_biUnion,
        Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨head, tail, htail, rfl⟩
        have hlength := ih tail |>.1 htail
        simp only [List.length_cons]
        omega
      · intro hlength
        cases melds with
        | nil =>
            simp at hlength
        | cons head tail =>
            simp only [List.length_cons] at hlength
            refine ⟨head, tail, ?_, rfl⟩
            exact ih tail |>.2 (by omega)

def mentsuHandTargetConfigurations (fixedMelds : Nat) :
    Finset (Tile × List MentsuCandidate) :=
  Finset.univ ×ˢ mentsuHandMeldListsOfLength (4 - fixedMelds)

def validCountsDecidable (hand : Hand) : Decidable (ValidCounts hand) := by
  unfold ValidCounts
  exact Fintype.decidableForallFintype

def validCountsBool (hand : Hand) : Bool :=
  @decide (ValidCounts hand) (validCountsDecidable hand)

lemma validCountsBool_eq_true_iff (hand : Hand) :
    validCountsBool hand = true ↔ ValidCounts hand := by
  simp [validCountsBool]

def validTileMultisetBool (tiles : Multiset Tile) : Bool :=
  validCountsBool
    { counts := countsOfTiles tiles
      fixedMelds := 0 }

lemma validTileMultisetBool_eq_true_iff (tiles : Multiset Tile) :
    validTileMultisetBool tiles = true ↔
      ∀ tile, tiles.count tile ≤ 4 := by
  change validCountsBool
    { counts := countsOfTiles tiles
      fixedMelds := 0 } = true ↔ _
  rw [validCountsBool_eq_true_iff]
  rfl

lemma validTileMultisetBool_add_left
    (tiles extra : Multiset Tile)
    (hvalid : validTileMultisetBool (tiles + extra) = true) :
    validTileMultisetBool tiles = true := by
  apply (validTileMultisetBool_eq_true_iff tiles).2
  intro tile
  have hsum :=
    (validTileMultisetBool_eq_true_iff (tiles + extra)).1 hvalid tile
  have hle : tiles.count tile ≤ (tiles + extra).count tile := by
    simp only [Multiset.count_add]
    omega
  omega

lemma validTileMultisetBool_eq_true_iff_targetHand
    (hand : Hand) (tiles : Multiset Tile) :
    validTileMultisetBool tiles = true ↔
      ValidCounts (targetHand hand (countsOfTiles tiles)) := by
  rw [validTileMultisetBool_eq_true_iff]
  change (∀ tile, tiles.count tile ≤ 4) ↔
    (∀ tile, tiles.count tile ≤ 4)
  rfl

lemma mem_mentsuHandTargetConfigurations_iff
    (fixedMelds : Nat) (hfixed : fixedMelds ≤ 4)
    (pair : Tile) (melds : List MentsuCandidate) :
    (pair, melds) ∈ mentsuHandTargetConfigurations fixedMelds ↔
      melds.length + fixedMelds = 4 := by
  rw [mentsuHandTargetConfigurations, Finset.mem_product]
  simp only [Finset.mem_univ, true_and,
    mem_mentsuHandMeldListsOfLength_iff]
  omega

def validMentsuHandTargetConfigurations (hand : Hand) :
    Finset (Tile × List MentsuCandidate) :=
  (mentsuHandTargetConfigurations hand.fixedMelds).filter
    (fun candidate =>
      validCountsBool
        (targetHand hand
          (countsOfTiles
            (mentsuHandTarget candidate.1 candidate.2))) = true)

lemma mem_validMentsuHandTargetConfigurations_iff
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4)
    (pair : Tile) (melds : List MentsuCandidate) :
    (pair, melds) ∈ validMentsuHandTargetConfigurations hand ↔
      melds.length + hand.fixedMelds = 4 ∧
      ValidCounts
        (targetHand hand
          (countsOfTiles (mentsuHandTarget pair melds))) := by
  classical
  rw [validMentsuHandTargetConfigurations, Finset.mem_filter,
    mem_mentsuHandTargetConfigurations_iff
      hand.fixedMelds hfixed pair melds]
  rw [validCountsBool_eq_true_iff]

def mentsuHandMeldTileStatesDP : Nat → Finset (Multiset Tile)
  | 0 => {0}
  | meldCount + 1 =>
      (Finset.univ.biUnion fun meld =>
        (mentsuHandMeldTileStatesDP meldCount).image
          (fun tiles => meldTiles meld + tiles)).filter
        (fun tiles => validTileMultisetBool tiles = true)

lemma mem_mentsuHandMeldTileStatesDP_iff
    (meldCount : Nat) (tiles : Multiset Tile) :
    tiles ∈ mentsuHandMeldTileStatesDP meldCount ↔
      ∃ melds, melds.length = meldCount ∧
        meldsTiles melds = tiles ∧ validTileMultisetBool tiles = true := by
  induction meldCount generalizing tiles with
  | zero =>
      change tiles ∈ ({0} : Finset (Multiset Tile)) ↔ _
      simp only [Finset.mem_singleton]
      constructor
      · rintro rfl
        refine ⟨[], rfl, rfl, ?_⟩
        apply (validTileMultisetBool_eq_true_iff 0).2
        intro tile
        simp
      · rintro ⟨melds, hlength, htiles, _⟩
        cases melds with
        | nil =>
            simpa [meldsTiles] using htiles.symm
        | cons meld melds =>
            simp at hlength
  | succ meldCount ih =>
      simp only [mentsuHandMeldTileStatesDP, Finset.mem_filter,
        Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨meld, previous, hprevious, heq⟩, hvalid⟩
        obtain ⟨melds, hlength, htiles, _⟩ :=
          (ih previous).mp hprevious
        refine ⟨meld :: melds, ?_, ?_, hvalid⟩
        · simp [hlength]
        · calc
            meldsTiles (meld :: melds) =
                meldTiles meld + meldsTiles melds := rfl
            _ = meldTiles meld + previous := by rw [htiles]
            _ = tiles := heq
      · rintro ⟨melds, hlength, htiles, hvalid⟩
        cases melds with
        | nil =>
            simp at hlength
        | cons meld melds =>
            simp only [List.length_cons] at hlength
            have hvalidFull' := hvalid
            have hvalidFull :
                validTileMultisetBool
                  (meldTiles meld + meldsTiles melds) = true := by
              rw [← htiles] at hvalidFull'
              simpa [meldsTiles] using hvalidFull'
            have htailValid :
                validTileMultisetBool (meldsTiles melds) = true := by
              apply validTileMultisetBool_add_left
                (meldsTiles melds) (meldTiles meld)
              simpa [Multiset.add_comm] using hvalidFull
            have hprevious :
                meldsTiles melds ∈ mentsuHandMeldTileStatesDP meldCount :=
              (ih (meldsTiles melds)).2
                ⟨melds, by omega, rfl, htailValid⟩
            refine ⟨⟨meld, meldsTiles melds, hprevious, ?_⟩, hvalid⟩
            calc
              meldTiles meld + meldsTiles melds =
                  meldsTiles (meld :: melds) := rfl
              _ = tiles := htiles

def mentsuHandTargetTileStatesDP (fixedMelds : Nat) :
    Finset (Multiset Tile) :=
  (Finset.univ.biUnion fun pair =>
    (mentsuHandMeldTileStatesDP (4 - fixedMelds)).image
      (fun meldTiles => pairTiles pair + meldTiles)).filter
    (fun tiles => validTileMultisetBool tiles = true)

lemma mem_mentsuHandTargetTileStatesDP_iff
    (fixedMelds : Nat) (hfixed : fixedMelds ≤ 4)
    (tiles : Multiset Tile) :
    tiles ∈ mentsuHandTargetTileStatesDP fixedMelds ↔
      ∃ pair melds,
        melds.length + fixedMelds = 4 ∧
        mentsuHandTarget pair melds = tiles ∧
        validTileMultisetBool tiles = true := by
  unfold mentsuHandTargetTileStatesDP
  simp only [Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨pair, meldTiles, hmeldTiles, rfl⟩, hvalid⟩
    obtain ⟨melds, hlength, rfl, _⟩ :=
      (mem_mentsuHandMeldTileStatesDP_iff (4 - fixedMelds) meldTiles).mp
        hmeldTiles
    refine ⟨pair, melds, ?_, rfl, hvalid⟩
    omega
  · rintro ⟨pair, melds, hlength, rfl, hvalid⟩
    have hmeldValid :
        validTileMultisetBool (meldsTiles melds) = true := by
      apply validTileMultisetBool_add_left
        (meldsTiles melds) (pairTiles pair)
      simpa [mentsuHandTarget, Multiset.add_comm] using hvalid
    refine ⟨⟨pair, meldsTiles melds, ?_, rfl⟩, hvalid⟩
    · exact (mem_mentsuHandMeldTileStatesDP_iff (4 - fixedMelds)
        (meldsTiles melds)).2
        ⟨melds, by omega, rfl, hmeldValid⟩

def mentsuHandTargetCostStatesDP (hand : Hand) :
    Finset (Multiset Tile × Nat) :=
  (mentsuHandTargetTileStatesDP hand.fixedMelds).image
    (fun tiles =>
      (tiles, countDeficit hand.counts (countsOfTiles tiles)))

lemma mem_mentsuHandTargetCostStatesDP_iff
    (hand : Hand) (state : Multiset Tile × Nat) :
    state ∈ mentsuHandTargetCostStatesDP hand ↔
      state.1 ∈ mentsuHandTargetTileStatesDP hand.fixedMelds ∧
      state.2 = countDeficit hand.counts (countsOfTiles state.1) := by
  unfold mentsuHandTargetCostStatesDP
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨tiles, htiles, heq⟩
    have hfst := congrArg Prod.fst heq
    have hsnd := congrArg Prod.snd heq
    refine ⟨?_, ?_⟩
    · rw [← hfst]
      exact htiles
    · rw [← hfst]
      exact hsnd.symm
  · rintro ⟨htiles, hcost⟩
    refine ⟨state.1, htiles, ?_⟩
    exact Prod.ext rfl hcost.symm

lemma countsOfTiles_add (tiles extra : Multiset Tile) :
    countsOfTiles (tiles + extra) =
      countsOfTiles tiles + countsOfTiles extra := by
  funext tile
  simp [countsOfTiles, Multiset.count_add]

lemma countDeficit_tiles_add_mono
    (current : TileCounts) (tiles extra : Multiset Tile) :
    countDeficit current (countsOfTiles tiles) ≤
      countDeficit current (countsOfTiles (tiles + extra)) := by
  unfold countDeficit
  apply Finset.sum_le_sum
  intro tile _
  rw [countsOfTiles_add]
  simp only [Pi.add_apply]
  omega

lemma countDeficit_add_le_card_of_le
    (current : TileCounts) (tiles extra : Multiset Tile)
    (hbelow : ∀ tile, (countsOfTiles tiles) tile ≤ current tile) :
    countDeficit current (countsOfTiles (tiles + extra)) ≤ extra.card := by
  unfold countDeficit
  calc
    ∑ tile : Tile, (countsOfTiles (tiles + extra) tile - current tile) =
        ∑ tile : Tile,
          (countsOfTiles tiles tile + countsOfTiles extra tile -
            current tile) := by
      apply Finset.sum_congr rfl
      intro tile _
      rw [countsOfTiles_add]
      rfl
    _ ≤ ∑ tile : Tile, countsOfTiles extra tile := by
      apply Finset.sum_le_sum
      intro tile _
      have htile := hbelow tile
      omega
    _ = extra.card := by
      exact countsOfTiles_sum_eq_card extra

end Shanten
