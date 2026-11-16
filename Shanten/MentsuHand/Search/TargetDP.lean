import Shanten.MentsuHand.Search.Enumeration

/-!
# Search / TargetDP

Incremental target-cost dynamic programming and its state characterization.
-/

namespace Shanten

/-- Extend a target state and add only the newly incurred deficit. -/
def mentsuHandCostStateAdd (hand : Hand)
    (state : Multiset Tile × Nat) (extra : Multiset Tile) :
    Multiset Tile × Nat :=
  let tiles := state.1 + extra
  (tiles,
    state.2 + (countDeficit hand.counts (countsOfTiles tiles) -
      countDeficit hand.counts (countsOfTiles state.1)))

lemma mentsuHandCostStateAdd_cost
    (hand : Hand) (state : Multiset Tile × Nat) (extra : Multiset Tile)
    (hcost :
      state.2 = countDeficit hand.counts (countsOfTiles state.1)) :
    (mentsuHandCostStateAdd hand state extra).2 =
      countDeficit hand.counts
        (countsOfTiles ((mentsuHandCostStateAdd hand state extra).1)) := by
  unfold mentsuHandCostStateAdd
  dsimp only
  rw [hcost]
  have hmono := countDeficit_tiles_add_mono
    hand.counts state.1 extra
  omega

def mentsuHandMeldCostStatesDP (hand : Hand) (initialTiles : Multiset Tile) :
    Nat → Finset (Multiset Tile × Nat)
  | 0 =>
      Finset.filter
        (fun state => validTileMultisetBool state.1 = true)
        ({(initialTiles,
            countDeficit hand.counts (countsOfTiles initialTiles))} :
          Finset (Multiset Tile × Nat))
  | meldCount + 1 =>
      (Finset.univ.biUnion fun meld =>
        (mentsuHandMeldCostStatesDP hand initialTiles meldCount).image
          (fun state => mentsuHandCostStateAdd hand state (meldTiles meld)))
        |>.filter (fun state => validTileMultisetBool state.1 = true)

lemma mentsuHandMeldCostStatesDP_cost
    (hand : Hand) (initialTiles : Multiset Tile) (meldCount : Nat)
    (state : Multiset Tile × Nat)
    (hstate : state ∈ mentsuHandMeldCostStatesDP hand initialTiles meldCount) :
    state.2 = countDeficit hand.counts (countsOfTiles state.1) := by
  induction meldCount generalizing state with
  | zero =>
      simp only [mentsuHandMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_singleton] at hstate
      rw [hstate.1]
  | succ meldCount ih =>
      simp only [mentsuHandMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image] at hstate
      rcases hstate with ⟨⟨meld, previous, hprevious, heq⟩, _⟩
      have hpreviousCost := ih previous hprevious
      have hnextCost :=
        mentsuHandCostStateAdd_cost hand previous (meldTiles meld)
          hpreviousCost
      calc
        state.2 =
            (mentsuHandCostStateAdd hand previous (meldTiles meld)).2 :=
          (congrArg Prod.snd heq).symm
        _ = countDeficit hand.counts
            (countsOfTiles
              (mentsuHandCostStateAdd hand previous (meldTiles meld)).1) :=
          hnextCost
        _ = countDeficit hand.counts (countsOfTiles state.1) := by
          rw [congrArg Prod.fst heq]

lemma mem_mentsuHandMeldCostStatesDP_iff
    (hand : Hand) (initialTiles : Multiset Tile)
    (meldCount : Nat) (state : Multiset Tile × Nat) :
    state ∈ mentsuHandMeldCostStatesDP hand initialTiles meldCount ↔
      ∃ melds,
        melds.length = meldCount ∧
        meldsTiles melds + initialTiles = state.1 ∧
        state.2 = countDeficit hand.counts (countsOfTiles state.1) ∧
        validTileMultisetBool state.1 = true := by
  induction meldCount generalizing state with
  | zero =>
      simp only [mentsuHandMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, hvalid⟩
        refine ⟨[], rfl, ?_, rfl, hvalid⟩
        simp [meldsTiles]
      · rintro ⟨melds, hlength, htiles, hcost, hvalid⟩
        cases melds with
        | nil =>
            simp only [List.length_nil] at hlength
            simp [meldsTiles] at htiles
            have hstate : state =
                (initialTiles,
                  countDeficit hand.counts (countsOfTiles initialTiles)) := by
              apply Prod.ext
              · exact htiles.symm
              · calc
                  state.2 =
                      countDeficit hand.counts (countsOfTiles state.1) := hcost
                  _ = countDeficit hand.counts
                      (countsOfTiles initialTiles) := by rw [htiles]
            exact ⟨hstate, hvalid⟩
        | cons meld melds =>
            simp at hlength
  | succ meldCount ih =>
      simp only [mentsuHandMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · intro hstate
        rcases hstate with ⟨⟨meld, previous, hprevious, heq⟩, hvalid⟩
        have hpreviousCost :=
          mentsuHandMeldCostStatesDP_cost hand initialTiles meldCount
            previous hprevious
        have hnextCost :=
          mentsuHandCostStateAdd_cost hand previous (meldTiles meld)
            hpreviousCost
        have hcost : state.2 =
            countDeficit hand.counts (countsOfTiles state.1) := by
          calc
            state.2 =
                (mentsuHandCostStateAdd hand previous (meldTiles meld)).2 :=
              (congrArg Prod.snd heq).symm
            _ = countDeficit hand.counts
                (countsOfTiles
                  (mentsuHandCostStateAdd hand previous (meldTiles meld)).1) :=
              hnextCost
            _ = countDeficit hand.counts (countsOfTiles state.1) := by
              rw [congrArg Prod.fst heq]
        obtain ⟨melds, hlength, htiles, _, _⟩ :=
          (ih previous).mp hprevious
        have hfst := congrArg Prod.fst heq
        refine ⟨meld :: melds, by simp [hlength], ?_, hcost, hvalid⟩
        calc
          meldsTiles (meld :: melds) + initialTiles =
              meldTiles meld + (meldsTiles melds + initialTiles) := by
                rw [show meldsTiles (meld :: melds) =
                    meldTiles meld + meldsTiles melds by rfl]
                ac_rfl
          _ = meldTiles meld + previous.1 := by rw [htiles]
          _ = (mentsuHandCostStateAdd hand previous (meldTiles meld)).1 := by
                simp [mentsuHandCostStateAdd, Multiset.add_comm]
          _ = state.1 := hfst
      · rintro ⟨melds, hlength, htiles, hcost, hvalid⟩
        cases melds with
        | nil =>
            simp at hlength
        | cons meld melds =>
            simp only [List.length_cons] at hlength
            have htilesShape :
                meldsTiles (meld :: melds) + initialTiles =
                  (meldsTiles melds + initialTiles) + meldTiles meld := by
              rw [show meldsTiles (meld :: melds) =
                  meldTiles meld + meldsTiles melds by rfl]
              ac_rfl
            have hpreviousValid :
                validTileMultisetBool
                  (meldsTiles melds + initialTiles) = true := by
              apply validTileMultisetBool_add_left
                (meldsTiles melds + initialTiles) (meldTiles meld)
              have hfinalValid := hvalid
              rw [← htiles] at hfinalValid
              rw [htilesShape] at hfinalValid
              exact hfinalValid
            let previous : Multiset Tile × Nat :=
              (meldsTiles melds + initialTiles,
                countDeficit hand.counts
                  (countsOfTiles (meldsTiles melds + initialTiles)))
            have hprevious :
                previous ∈ mentsuHandMeldCostStatesDP hand initialTiles meldCount :=
              (ih previous).2
                ⟨melds, by omega, rfl, rfl, hpreviousValid⟩
            have hnextCost :=
              mentsuHandCostStateAdd_cost hand previous (meldTiles meld) rfl
            have hfirst :
                (mentsuHandCostStateAdd hand previous (meldTiles meld)).1 =
                  state.1 := by
              calc
                (mentsuHandCostStateAdd hand previous (meldTiles meld)).1 =
                    (meldsTiles melds + initialTiles) + meldTiles meld := by
                      simp [mentsuHandCostStateAdd, previous]
                _ = meldsTiles (meld :: melds) + initialTiles :=
                  htilesShape.symm
                _ = state.1 := htiles
            refine ⟨⟨meld, previous, hprevious, ?_⟩, hvalid⟩
            apply Prod.ext
            · exact hfirst
            · calc
                (mentsuHandCostStateAdd hand previous (meldTiles meld)).2 =
                    countDeficit hand.counts
                      (countsOfTiles
                        (mentsuHandCostStateAdd hand previous (meldTiles meld)).1) :=
                  hnextCost
                _ = countDeficit hand.counts
                    (countsOfTiles state.1) := by
                      rw [hfirst]
                _ = state.2 := hcost.symm

def recursiveMentsuHandTargetCostStatesDP (hand : Hand) :
    Finset (Multiset Tile × Nat) :=
  Finset.univ.biUnion fun pair =>
    mentsuHandMeldCostStatesDP hand (pairTiles pair)
      (4 - hand.fixedMelds)

lemma recursiveMentsuHandTargetCostStatesDP_eq
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4) :
    recursiveMentsuHandTargetCostStatesDP hand =
      mentsuHandTargetCostStatesDP hand := by
  ext state
  unfold recursiveMentsuHandTargetCostStatesDP
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  rw [mem_mentsuHandTargetCostStatesDP_iff]
  constructor
  · rintro ⟨pair, hstate⟩
    obtain ⟨melds, hlength, htiles, hcost, hvalid⟩ :=
      (mem_mentsuHandMeldCostStatesDP_iff hand (pairTiles pair)
        (4 - hand.fixedMelds) state).mp hstate
    have htargetLength : melds.length + hand.fixedMelds = 4 := by
      omega
    have htarget :
        mentsuHandTarget pair melds = state.1 := by
      rw [mentsuHandTarget]
      calc
        pairTiles pair + meldsTiles melds =
            meldsTiles melds + pairTiles pair := by ac_rfl
        _ = state.1 := htiles
    have htilesTarget :
        state.1 ∈ mentsuHandTargetTileStatesDP hand.fixedMelds :=
      (mem_mentsuHandTargetTileStatesDP_iff hand.fixedMelds hfixed
        state.1).2
        ⟨pair, melds, htargetLength, htarget, hvalid⟩
    exact ⟨htilesTarget, hcost⟩
  · rintro ⟨htiles, hcost⟩
    obtain ⟨pair, melds, hlength, htarget, hvalid⟩ :=
      (mem_mentsuHandTargetTileStatesDP_iff hand.fixedMelds hfixed
        state.1).mp htiles
    refine ⟨pair, ?_⟩
    apply (mem_mentsuHandMeldCostStatesDP_iff hand (pairTiles pair)
      (4 - hand.fixedMelds) state).2
    refine ⟨melds, ?_, ?_, hcost, ?_⟩
    · omega
    · rw [← htarget, mentsuHandTarget]
      ac_rfl
    · exact hvalid

end Shanten
