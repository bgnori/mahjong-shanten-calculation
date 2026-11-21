import Shanten.SevenPairs.Exchange.Distinctness
import Shanten.SevenPairs.Exchange.PairMaking
import Shanten.SevenPairs.Exchange.ProtectedPairMaking

/-!
# Seven pairs / Reachability

Finite exchange chains, their invariants, and constructive paths to seven kinds and six pairs.
-/

namespace Shanten

open MahjongDomain

/-- Repeated pairing exchanges, with the number of exchanges explicit. -/
inductive ReachesPairing : Hand → Hand → Nat → Prop
  | done {hand} : ReachesPairing hand hand 0
  | step {hand next target distance} :
      PairingExchange hand next →
      ReachesPairing next target distance →
      ReachesPairing hand target (distance + 1)

lemma ReachesPairing.toReachesHand :
    ReachesPairing before after distance →
      ValidCounts before → ReachesHand before after distance := by
  intro h
  induction h with
  | done =>
      intro _
      exact .done
  | step hstep hrest ih =>
      intro hvalid
      have hhandStep := hstep.handStep hvalid
      exact .step hhandStep (ih hhandStep.validCounts)

/-- Repeated exchanges that introduce previously absent tile kinds. -/
inductive ReachesDistinctness : Hand → Hand → Nat → Prop
  | done {hand} : ReachesDistinctness hand hand 0
  | step {hand next target distance} :
      DistinctnessExchange hand next →
      ReachesDistinctness next target distance →
      ReachesDistinctness hand target (distance + 1)

lemma ReachesDistinctness.toReachesHand :
    ReachesDistinctness before after distance →
      ValidCounts before → ReachesHand before after distance := by
  intro h
  induction h with
  | done =>
      intro _
      exact .done
  | step hstep hrest ih =>
      intro hvalid
      have hhandStep := hstep.handStep hvalid
      exact .step hhandStep (ih hhandStep.validCounts)

lemma ReachesDistinctness.pairCount
    (h : ReachesDistinctness before after distance)
    (hpairs : pairCount before = value) :
    pairCount after = value := by
  induction h with
  | done =>
      exact hpairs
  | step hstep hrest ih =>
      apply ih
      rw [pairCount_distinctnessExchange hstep]
      exact hpairs

lemma ReachesDistinctness.isThirteenTileHand
    (h : ReachesDistinctness before after distance)
    (h13 : IsThirteenTileHand before) :
    IsThirteenTileHand after := by
  induction h with
  | done =>
      exact h13
  | step hstep hrest ih =>
      exact ih (DistinctnessExchange.isThirteenTileHand h13 hstep)

lemma reaches_seven_tile_kinds
    (hand : Hand) (h13 : IsThirteenTileHand hand)
    (hdistinct : distinctTileCount hand ≤ 7) :
    ∃ next,
      ReachesDistinctness hand next (7 - distinctTileCount hand) ∧
        distinctTileCount next = 7 := by
  have aux : ∀ n : Nat, ∀ hand : Hand,
      7 - distinctTileCount hand = n →
      IsThirteenTileHand hand →
      distinctTileCount hand ≤ 7 →
      ∃ next,
        ReachesDistinctness hand next n ∧
          distinctTileCount next = 7 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hand hn h13 hdist
        by_cases hseven : distinctTileCount hand = 7
        · have hnzero : n = 0 := by omega
          subst n
          exact ⟨hand, by simpa [hseven] using
            (ReachesDistinctness.done : ReachesDistinctness hand hand 0), hseven⟩
        · have hlt : distinctTileCount hand < 7 := by omega
          obtain ⟨next, hstep⟩ :=
            exists_distinctnessExchange hand h13 hlt
          have hnext13 :=
            DistinctnessExchange.isThirteenTileHand h13 hstep
          have hnextcount :
              distinctTileCount next = distinctTileCount hand + 1 :=
            distinctTileCount_distinctnessExchange hstep
          have hnnext :
              7 - distinctTileCount next < n := by
            omega
          obtain ⟨final, hrest, hfinal⟩ :=
            ih (7 - distinctTileCount next) hnnext next rfl hnext13 (by omega)
          refine ⟨final, ?_, hfinal⟩
          rw [show n = (7 - distinctTileCount next) + 1 by omega]
          exact .step hstep hrest
  exact aux (7 - distinctTileCount hand) hand rfl h13 hdistinct

/-- Repeated exchanges that turn singleton kinds into pairs. -/
inductive ReachesPairMaking : Hand → Hand → Nat → Prop
  | done {hand} : ReachesPairMaking hand hand 0
  | step {hand next target distance} :
      PairMakingExchange hand next →
      ReachesPairMaking next target distance →
      ReachesPairMaking hand target (distance + 1)

lemma ReachesPairMaking.toReachesHand :
    ReachesPairMaking before after distance →
      ValidCounts before → ReachesHand before after distance := by
  intro h
  induction h with
  | done =>
      intro _
      exact .done
  | step hstep hrest ih =>
      intro hvalid
      have hhandStep := hstep.handStep hvalid
      exact .step hhandStep (ih hhandStep.validCounts)

lemma ReachesPairMaking.isThirteenTileHand
    (h : ReachesPairMaking before after distance)
    (h13 : IsThirteenTileHand before) :
    IsThirteenTileHand after := by
  induction h with
  | done =>
      exact h13
  | step hstep hrest ih =>
      exact ih (PairMakingExchange.isThirteenTileHand h13 hstep)

lemma ReachesPairMaking.distinctTileCount
    (h : ReachesPairMaking before after distance)
    (hdistinct : distinctTileCount before = value) :
    distinctTileCount after = value := by
  induction h with
  | done =>
      exact hdistinct
  | step hstep hrest ih =>
      apply ih
      rw [distinctTileCount_pairMakingExchange hstep]
      exact hdistinct

lemma reaches_six_pairs
    (hand : Hand) (h13 : IsThirteenTileHand hand)
    (hdistinct : distinctTileCount hand = 7)
    (hpairs : pairCount hand ≤ 6) :
    ∃ next,
      ReachesPairMaking hand next (6 - pairCount hand) ∧
        pairCount next = 6 := by
  have aux : ∀ n : Nat, ∀ hand : Hand,
      6 - pairCount hand = n →
      IsThirteenTileHand hand →
      distinctTileCount hand = 7 →
      pairCount hand ≤ 6 →
      ∃ next,
        ReachesPairMaking hand next n ∧
          pairCount next = 6 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hand hn h13 hdist hpairs'
        by_cases hsix : pairCount hand = 6
        · have hnzero : n = 0 := by omega
          subst n
          exact ⟨hand, by simpa [hsix] using
            (ReachesPairMaking.done : ReachesPairMaking hand hand 0), hsix⟩
        · have hlt : pairCount hand < 6 := by omega
          obtain ⟨next, hstep⟩ :=
            exists_pairMakingExchange hand h13 hdist hlt
          have hnext13 :=
            PairMakingExchange.isThirteenTileHand h13 hstep
          have hnextdistinct :
              distinctTileCount next = 7 := by
            rw [distinctTileCount_pairMakingExchange hstep]
            exact hdist
          have hnextpairs :
              pairCount next = pairCount hand + 1 :=
            pairCount_pairMakingExchange hstep
          have hnnext :
              6 - pairCount next < n := by
            omega
          obtain ⟨final, hrest, hfinal⟩ :=
            ih (6 - pairCount next) hnnext next rfl hnext13
              hnextdistinct (by omega)
          refine ⟨final, ?_, hfinal⟩
          rw [show n = (6 - pairCount next) + 1 by omega]
          exact .step hstep hrest
  exact aux (6 - pairCount hand) hand rfl h13 hdistinct hpairs

/-- Repeated exchanges that make pairs in a fixed protected set. -/
inductive ReachesProtectedPairMaking
    (protectedTiles : Finset Tile) : Hand → Hand → Nat → Prop
  | done {hand} : ReachesProtectedPairMaking protectedTiles hand hand 0
  | step {hand next target distance} :
      ProtectedPairMakingExchange protectedTiles hand next →
      ReachesProtectedPairMaking protectedTiles next target distance →
      ReachesProtectedPairMaking protectedTiles hand target (distance + 1)

lemma ReachesProtectedPairMaking.toReachesHand :
    ReachesProtectedPairMaking protectedTiles before after distance →
      ValidCounts before → ReachesHand before after distance := by
  intro h
  induction h with
  | done =>
      intro _
      exact .done
  | step hstep hrest ih =>
      intro hvalid
      have hhandStep := hstep.handStep hvalid
      exact .step hhandStep (ih hhandStep.validCounts)

lemma ReachesProtectedPairMaking.isThirteenTileHand
    (h : ReachesProtectedPairMaking protectedTiles before after distance)
    (h13 : IsThirteenTileHand before) :
    IsThirteenTileHand after := by
  induction h with
  | done =>
      exact h13
  | step hstep hrest ih =>
      exact ih (ProtectedPairMakingExchange.isThirteenTileHand h13 hstep)

lemma ReachesProtectedPairMaking.protectedInvariant
    (h : ReachesProtectedPairMaking protectedTiles before after distance)
    (hinvariant : ProtectedPairingInvariant protectedTiles before) :
    ProtectedPairingInvariant protectedTiles after := by
  induction h with
  | done =>
      exact hinvariant
  | step hstep hrest ih =>
      exact ih (protectedPairingInvariant_after_protectedPairMakingExchange
        hinvariant hstep)

lemma reaches_six_pairs_protected
    (protectedTiles : Finset Tile) (hand : Hand)
    (h13 : IsThirteenTileHand hand)
    (hprotected : ProtectedPairingInvariant protectedTiles hand)
    (hpairs : pairCount hand ≤ 6)
    (hchoose :
      ∀ current,
        IsThirteenTileHand current →
        ProtectedPairingInvariant protectedTiles current →
        pairCount current < 6 →
        ∃ next,
          ProtectedPairMakingExchange protectedTiles current next ∧
            ProtectedPairingInvariant protectedTiles next) :
    ∃ next,
      ReachesProtectedPairMaking protectedTiles hand next
        (6 - pairCount hand) ∧
        pairCount next = 6 := by
  have aux : ∀ n : Nat, ∀ current : Hand,
      6 - pairCount current = n →
      IsThirteenTileHand current →
      ProtectedPairingInvariant protectedTiles current →
      pairCount current ≤ 6 →
      ∃ next,
        ReachesProtectedPairMaking protectedTiles current next n ∧
          pairCount next = 6 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro current hn hcurrent hcurrentProtected hpairs'
        by_cases hsix : pairCount current = 6
        · have hnzero : n = 0 := by omega
          subst n
          exact ⟨current, by simpa [hsix] using
            (ReachesProtectedPairMaking.done :
              ReachesProtectedPairMaking protectedTiles current current 0), hsix⟩
        · have hlt : pairCount current < 6 := by omega
          obtain ⟨next, hstep, hnextProtected⟩ :=
            hchoose current hcurrent hcurrentProtected hlt
          have hnext13 :=
            ProtectedPairMakingExchange.isThirteenTileHand hcurrent hstep
          have hnextpairs :
              pairCount next = pairCount current + 1 :=
            pairCount_protectedPairMakingExchange hstep
          have hnnext :
              6 - pairCount next < n := by
            omega
          obtain ⟨final, hrest, hfinal⟩ :=
            ih (6 - pairCount next) hnnext next rfl hnext13
              hnextProtected (by omega)
          refine ⟨final, ?_, hfinal⟩
          rw [show n = (6 - pairCount next) + 1 by omega]
          exact .step hstep hrest
  exact aux (6 - pairCount hand) hand rfl h13 hprotected hpairs

lemma reaches_six_pairs_protected_of_card
    (protectedTiles : Finset Tile) (hand : Hand)
    (h13 : IsThirteenTileHand hand)
    (hcard : protectedTiles.card = 7)
    (hprotected : ProtectedPairingInvariant protectedTiles hand)
    (hpairs : pairCount hand ≤ 6) :
    ∃ next,
      ReachesProtectedPairMaking protectedTiles hand next
        (6 - pairCount hand) ∧
        pairCount next = 6 := by
  apply reaches_six_pairs_protected protectedTiles hand h13 hprotected hpairs
  intro current hcurrent hcurrentProtected hcurrentPairs
  have hpresentSubset :
      protectedTiles ⊆
        Finset.univ.filter (fun tile => 0 < current.counts tile) := by
    intro tile htile
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcurrentProtected.1 tile htile
  have hcardle :
      protectedTiles.card ≤
        (Finset.univ.filter (fun tile => 0 < current.counts tile)).card :=
    Finset.card_le_card hpresentSubset
  have hdistinct : 7 ≤ distinctTileCount current := by
    have hcardle' :
        7 ≤ (Finset.univ.filter (fun tile => 0 < current.counts tile)).card := by
      omega
    exact hcardle'
  obtain ⟨next, hstep, hnextProtected⟩ :=
    exists_protectedPairMakingExchange protectedTiles current hcurrent
      hcard hcurrentProtected hcurrentPairs
  exact ⟨next, hstep, hnextProtected⟩

end Shanten
