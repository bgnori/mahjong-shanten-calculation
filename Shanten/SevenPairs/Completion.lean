module

public import Shanten.SevenPairs.Basic

@[expose] public section

/-!
# Seven pairs / Completion

Decomposition of tenpai hands and completion by the final draw.
-/

namespace Shanten

open MahjongDomain

lemma sevenPairsTenpai_decomposition
    (hand : Hand) (h13 : IsThirteenTileHand hand)
    (htenpai : IsSevenPairsTenpai hand) :
    ∃ pairs : Finset Tile, ∃ single : Tile,
      pairs.card = 6 ∧
      single ∉ pairs ∧
      (∀ tile, hand.counts tile =
        if tile ∈ pairs then 2
        else if tile = single then 1
        else 0) := by
  classical
  let pairs : Finset Tile :=
    Finset.univ.filter (fun tile => 2 ≤ hand.counts tile)
  have hpairsCard : pairs.card = 6 := by
    change pairCount hand = 6
    exact htenpai.2.2.2
  have hexists : ∃ single, hand.counts single = 1 := by
    by_contra hnon
    have hno : ∀ tile, hand.counts tile ≠ 1 := by
      intro tile htile
      exact hnon ⟨tile, htile⟩
    have hiff : ∀ tile,
        (0 < hand.counts tile) ↔ 2 ≤ hand.counts tile := by
      intro tile
      constructor
      · intro hpositive
        have hno' := hno tile
        omega
      · intro hpair
        have hno' := hno tile
        omega
    have hcard :
        distinctTileCount hand = pairCount hand := by
      unfold distinctTileCount pairCount
      apply congrArg Finset.card
      ext tile
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hiff tile
    have hdistinct := htenpai.2.2.1
    have hpairs := htenpai.2.2.2
    omega
  obtain ⟨single, hsingle⟩ := hexists
  have hsingleNotPair : single ∉ pairs := by
    simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  let lower : Tile → Nat :=
    fun tile =>
      (if 0 < hand.counts tile then 1 else 0) +
        (if 2 ≤ hand.counts tile then 1 else 0)
  have hlower : ∀ tile, lower tile ≤ hand.counts tile := by
    intro tile
    by_cases hpositive : 0 < hand.counts tile
    · by_cases hpair : 2 ≤ hand.counts tile <;>
        simp [lower, hpositive, hpair] <;> omega
    · have hzero : hand.counts tile = 0 :=
        Nat.eq_zero_of_not_pos hpositive
      simp [lower, hpositive, hzero]
  have hlowerSum :
      (∑ tile : Tile, lower tile) = 13 := by
    have hsum :
        (∑ tile : Tile, lower tile) =
          distinctTileCount hand + pairCount hand := by
      simp [lower, distinctTileCount, pairCount, Finset.sum_add_distrib]
    rw [hsum]
    have hdistinct := htenpai.2.2.1
    have hpairs := htenpai.2.2.2
    omega
  have hsumCounts : (∑ tile : Tile, hand.counts tile) = 13 :=
    h13.2.1
  have heq :
      ∀ tile, lower tile = hand.counts tile := by
    have hsumEq : (∑ tile : Tile, lower tile) =
        ∑ tile : Tile, hand.counts tile := by
      omega
    intro tile
    exact (Finset.sum_eq_sum_iff_of_le
      (s := Finset.univ) (fun tile _ => hlower tile)).mp hsumEq
      tile (Finset.mem_univ tile)
  refine ⟨pairs, single, hpairsCard, hsingleNotPair, ?_⟩
  intro tile
  have hbase := heq tile
  by_cases hpair : tile ∈ pairs
  · simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hpair
    have hpositive : 0 < hand.counts tile := by omega
    have hbase' := hbase
    simp [lower, hpositive, hpair] at hbase'
    have hcount : hand.counts tile = 2 := by omega
    simp [pairs, hcount]
  · by_cases htile : tile = single
    · subst tile
      simp [lower, hsingle, hpair]
    · have hnotpositive : ¬ 0 < hand.counts tile := by
        intro hpositive
        have hnotpair : ¬ 2 ≤ hand.counts tile := by
          simpa [pairs] using hpair
        let present : Finset Tile :=
          Finset.univ.filter (fun t => 0 < hand.counts t)
        have hsubset :
            insert tile (insert single pairs) ⊆ present := by
          intro t ht
          simp only [Finset.mem_insert] at ht
          rcases ht with rfl | rfl | ht
          · simp only [present, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hpositive
          · simp only [present, Finset.mem_filter, Finset.mem_univ, true_and]
            omega
          · simp only [present, Finset.mem_filter, Finset.mem_univ, true_and]
            simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at ht
            omega
        have hcardle := Finset.card_le_card hsubset
        have hpresent : present.card = distinctTileCount hand := by
          rfl
        rw [hpresent] at hcardle
        have hdistinct := htenpai.2.2.1
        have hcard :
            (insert tile (insert single pairs)).card = 8 := by
          simp [htile, hpair, hsingleNotPair, hpairsCard]
        rw [hcard] at hcardle
        omega
      have hzero : hand.counts tile = 0 :=
        Nat.eq_zero_of_not_pos hnotpositive
      simp [hzero, htile, hpair]

lemma multiset_count_fold_pairTiles_list
    (tiles : List Tile) (hnodup : tiles.Nodup) (tile : Tile) :
    (tiles.foldr (fun pair rest => pairTiles pair + rest) 0).count tile =
      if tile ∈ tiles then 2 else 0 := by
  induction tiles with
  | nil =>
      simp
  | cons pair tiles ih =>
      have hnodup' : tiles.Nodup := (List.nodup_cons.mp hnodup).2
      rw [List.foldr_cons, Multiset.count_add]
      have hcount :
          (pairTiles pair).count tile = if tile = pair then 2 else 0 := by
        by_cases htile : tile = pair
        · subst tile
          simp [pairTiles, Pair.tiles, Pair.orderedTiles, Multiset.count_cons]
        · simp [pairTiles, Pair.tiles, Pair.orderedTiles, htile, Multiset.count_cons]
      rw [hcount, ih hnodup']
      by_cases htile : tile = pair
      · subst tile
        simp [(List.nodup_cons.mp hnodup).1]
      · simp [htile, ih hnodup']

lemma multiset_count_fold_pairTiles
    (pairs : Finset Tile) (tile : Tile) :
    (pairs.toList.foldr (fun pair rest => pairTiles pair + rest) 0).count tile =
      if tile ∈ pairs then 2 else 0 := by
  simpa using multiset_count_fold_pairTiles_list pairs.toList
    pairs.nodup_toList tile

lemma complete_sevenPairs_of_counts
    (pairs : Finset Tile) (hand : Hand)
    (hfixed : hand.fixedMelds = 0)
    (hpairs : pairs.card = 7)
    (hcounts : ∀ tile, hand.counts tile =
      sevenPairsCompletionCounts pairs tile) :
    Complete .sevenPairs hand := by
  refine ⟨?_, hfixed, pairs, hpairs, ?_⟩
  · intro tile
    change hand.counts tile ≤ 4
    rw [hcounts, sevenPairsCompletionCounts]
    split <;> omega
  intro tile
  rw [hcounts, sevenPairsCompletionCounts,
    multiset_count_fold_pairTiles]

lemma reachesCompletion_sevenPairs_one_draw
    (hand : Hand) (pairs : Finset Tile) (single : Tile)
    (hfixed : hand.fixedMelds = 0)
    (hpairs : pairs.card = 6) (hsingle : single ∉ pairs)
    (hcounts : ∀ tile, hand.counts tile =
      if tile ∈ pairs then 2 else if tile = single then 1 else 0) :
    ReachesCompletion Complete .sevenPairs hand 1 := by
  let completed : Hand :=
    { counts := sevenPairsCompletionCounts (insert single pairs)
      fixedMelds := hand.fixedMelds }
  have hcompletedFixed : completed.fixedMelds = 0 := by
    dsimp [completed]
    exact hfixed
  have hcompletedCounts :
      ∀ tile, completed.counts tile =
        sevenPairsCompletionCounts (insert single pairs) tile := by
    intro tile
    rfl
  have hcomplete : Complete .sevenPairs completed := by
    apply complete_sevenPairs_of_counts (insert single pairs) completed
      hcompletedFixed
    · simp [hpairs, hsingle]
    · exact hcompletedCounts
  apply ReachesCompletion.step ?_ (.done hcomplete)
  refine ⟨rfl, ?_⟩
  refine Or.inl ⟨single, ?_, ?_⟩
  · intro tile
    change completed.counts tile ≤ 4
    dsimp [completed, sevenPairsCompletionCounts]
    split <;> omega
  intro tile
  dsimp [completed, sevenPairsCompletionCounts]
  by_cases htilePair : tile ∈ pairs
  · have hne : tile ≠ single := by
      intro heq
      subst tile
      exact hsingle htilePair
    simp [hcounts tile, htilePair, hne]
  · by_cases htileSingle : tile = single
    · subst tile
      simp [hcounts single, hsingle]
    · simp [hcounts tile, htilePair, htileSingle]

lemma reachesCompletion_of_sevenPairsTenpai
    (hand : Hand) (h13 : IsThirteenTileHand hand)
    (htenpai : IsSevenPairsTenpai hand) :
    ReachesCompletion Complete .sevenPairs hand 1 := by
  obtain ⟨pairs, single, hpairs, hsingle, hcounts⟩ :=
    sevenPairsTenpai_decomposition hand h13 htenpai
  exact reachesCompletion_sevenPairs_one_draw hand pairs single
    h13.1 hpairs hsingle hcounts

end Shanten
