import Shanten.MentsuHand.Search.Minimum

/-!
# Search / Reachability

Realizing a target distance by legal draws and exchanges.
-/

namespace Shanten

open MahjongDomain

lemma mentsuHandTargetDistance_eq_zero_iff
    (hand : Hand) (pair : Tile) (melds : List MentsuCandidate)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile) :
    mentsuHandTargetDistance hand pair melds = 0 ↔
      hand.counts = TileCounts.ofMultiset (mentsuHandTarget pair melds) := by
  constructor
  · intro hdistance
    have hdeficit :
        countDeficit hand.counts
          (TileCounts.ofMultiset (mentsuHandTarget pair melds)) = 0 := by
      rw [← mentsuHandTargetDistance_eq_countDeficit]
      exact hdistance
    have hzero :
        ∀ tile ∈ (Finset.univ : Finset Tile),
          (TileCounts.ofMultiset (mentsuHandTarget pair melds)) tile -
              hand.counts tile = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (fun tile _ => Nat.zero_le _)).mp
      exact hdeficit
    have hle :
        ∀ tile, (TileCounts.ofMultiset (mentsuHandTarget pair melds)) tile ≤
          hand.counts tile := by
      intro tile
      have hzeroTile := hzero tile (Finset.mem_univ tile)
      omega
    apply funext
    intro tile
    have heq :
        ∀ tile ∈ (Finset.univ : Finset Tile),
          (TileCounts.ofMultiset (mentsuHandTarget pair melds)) tile =
            hand.counts tile := by
      apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
        (f := TileCounts.ofMultiset (mentsuHandTarget pair melds))
        (g := hand.counts)
        (fun tile _ => hle tile)).mp
      exact hsum.symm
    exact (heq tile (Finset.mem_univ tile)).symm
  · intro hcounts
    rw [mentsuHandTargetDistance_eq_countDeficit]
    simp [countDeficit, hcounts]

lemma mentsuHandTargetDistance_pos_iff
    (hand : Hand) (pair : Tile) (melds : List MentsuCandidate)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile) :
    0 < mentsuHandTargetDistance hand pair melds ↔
      hand.counts ≠ TileCounts.ofMultiset (mentsuHandTarget pair melds) := by
  constructor
  · intro hpos hcounts
    have hzero : mentsuHandTargetDistance hand pair melds = 0 :=
      (mentsuHandTargetDistance_eq_zero_iff hand pair melds hsum).mpr hcounts
    omega
  · intro hne
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hne
        ((mentsuHandTargetDistance_eq_zero_iff hand pair melds hsum).mp hzero))

lemma mentsuHandTargetDistance_exchange
    (hand : Hand) (pair : Tile) (melds : List MentsuCandidate)
    (discarded drawn : Tile)
    (hdrawn :
      (mentsuHandTarget pair melds).count drawn > hand.counts drawn)
    (hdiscarded :
      hand.counts discarded >
        (mentsuHandTarget pair melds).count discarded)
    (hne : discarded ≠ drawn) :
    mentsuHandTargetDistance
        (exchangeHand hand discarded drawn) pair melds =
      mentsuHandTargetDistance hand pair melds - 1 := by
  rw [mentsuHandTargetDistance_eq_countDeficit,
    mentsuHandTargetDistance_eq_countDeficit]
  exact countDeficit_exchange
    (TileCounts.ofMultiset (mentsuHandTarget pair melds))
    hand discarded drawn hdrawn hdiscarded hne

lemma exists_mentsuHandTarget_exchange
    (hand : Hand) (pair : Tile) (melds : List MentsuCandidate)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hne :
      hand.counts ≠ TileCounts.ofMultiset (mentsuHandTarget pair melds)) :
    ∃ discarded drawn,
      (mentsuHandTarget pair melds).count drawn > hand.counts drawn ∧
      hand.counts discarded >
        (mentsuHandTarget pair melds).count discarded ∧
      discarded ≠ drawn ∧
      mentsuHandTargetDistance
          (exchangeHand hand discarded drawn) pair melds =
        mentsuHandTargetDistance hand pair melds - 1 := by
  obtain ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles⟩ :=
    exists_target_exchange_tiles hand
      (TileCounts.ofMultiset (mentsuHandTarget pair melds)) hsum hne
  refine ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles, ?_⟩
  exact mentsuHandTargetDistance_exchange
    hand pair melds discarded drawn hdrawn hdiscarded hneTiles

lemma exists_mentsuHandTarget_exchange_of_pos
    (hand : Hand) (pair : Tile) (melds : List MentsuCandidate)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hpos : 0 < mentsuHandTargetDistance hand pair melds) :
    ∃ discarded drawn,
      (mentsuHandTarget pair melds).count drawn > hand.counts drawn ∧
      hand.counts discarded >
        (mentsuHandTarget pair melds).count discarded ∧
      discarded ≠ drawn ∧
      mentsuHandTargetDistance
          (exchangeHand hand discarded drawn) pair melds =
        mentsuHandTargetDistance hand pair melds - 1 := by
  apply exists_mentsuHandTarget_exchange hand pair melds hsum
  exact (mentsuHandTargetDistance_pos_iff hand pair melds hsum).mp hpos

lemma reachesCompletion_mentsuHand_of_mentsuHandTarget
    (before : Hand) (pair : Tile) (melds : List MentsuCandidate)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (TileCounts.ofMultiset (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4)
    (hbeforeValid : ValidCounts before) :
    ReachesCompletion Complete .mentsuHand before
      (mentsuHandTargetDistance before pair melds) := by
  rw [mentsuHandTargetDistance_eq_countDeficit]
  apply reachesCompletion_mentsuHand_of_equal_sum
    before
    (TileCounts.ofMultiset (mentsuHandTarget pair melds))
    pair melds hsum hvalid hmelds
  · exact targetHand_hasTiles_countsOfTiles before
      (mentsuHandTarget pair melds)
  · exact hbeforeValid

set_option maxHeartbeats 1000000 in
lemma reachesCompletion_mentsuHand_of_blockDecomposition
    (hand : Hand) (h13 : IsThirteenTileHand hand)
    (decomposition : MentsuHandBlockDecomposition hand) :
    ∃ distance : Nat, distance ≤ 4 ∧
      ReachesCompletion Complete .mentsuHand hand distance := by
  let melds :=
    decomposition.melds ++
      taatsuCompletionMelds decomposition.taatsus
  have hmelds : melds.length + hand.fixedMelds = 4 := by
    dsimp [melds]
    exact decomposition.completedMeldCount
  have htarget :
      mentsuHandTarget decomposition.pair melds =
        decomposition.completedTarget := by
    rw [MentsuHandBlockDecomposition.completedTarget_eq]
    rfl
  have hsumTarget :
      (∑ tile : Tile, (mentsuHandTarget decomposition.pair melds).count tile) =
        (∑ tile : Tile, hand.counts tile) + 1 := by
    calc
      (∑ tile : Tile,
          (mentsuHandTarget decomposition.pair melds).count tile) =
          decomposition.completedTarget.card := by
        change
          (∑ tile : Tile,
            TileCounts.ofMultiset (mentsuHandTarget decomposition.pair melds) tile) =
            decomposition.completedTarget.card
        rw [htarget, TileCounts.ofMultiset_sum_eq_card]
      _ = 14 := by
        have hbase :
            (mentsuHandTargetWithTaatsu decomposition.pair
              decomposition.melds decomposition.taatsus).card =
              2 + 3 * decomposition.melds.length +
                2 * decomposition.taatsus.length := by
          have htaatsu :
              (taatsuHistoryTiles decomposition.taatsus).card =
                2 * decomposition.taatsus.length := by
            induction decomposition.taatsus with
            | nil =>
                rfl
            | cons taatsu taatsus ih =>
                cases taatsu <;>
                  simp [taatsuHistoryTiles, taatsuTiles, pairTiles, Pair.tiles, Pair.orderedTiles, ih,
                    Multiset.card_add] <;> omega
          unfold mentsuHandTargetWithTaatsu mentsuHandTarget
          simp only [Multiset.card_add, pairTiles, Pair.tiles_card,
            MentsuCandidateList.tiles_card, htaatsu]
        have hextra :
            (taatsuCompletionTiles decomposition.taatsus).card =
              decomposition.taatsus.length :=
          taatsuCompletionTiles_card decomposition.taatsus
        have hblocks := decomposition.blocks
        have hfixed := h13.1
        have htargetCard : decomposition.completedTarget.card = 14 := by
          change
            (mentsuHandTargetWithTaatsu decomposition.pair
              decomposition.melds decomposition.taatsus +
              taatsuCompletionTiles decomposition.taatsus).card = 14
          rw [Multiset.card_add, hbase,
            taatsuCompletionTiles_card decomposition.taatsus]
          omega
        exact htargetCard
      _ = (∑ tile : Tile, hand.counts tile) + 1 := by
        have hcount := h13.2.1
        rw [show (∑ tile : Tile, hand.counts tile) = tileCount hand from rfl]
        omega
  have hdistance :
      mentsuHandTargetDistance hand decomposition.pair melds ≤ 4 := by
    rw [mentsuHandTargetDistance_eq_countDeficit, htarget]
    change countDeficit hand.counts
      (TileCounts.ofMultiset
        (mentsuHandTargetWithTaatsu decomposition.pair
          decomposition.melds decomposition.taatsus +
          taatsuCompletionTiles decomposition.taatsus)) ≤ 4
    have hbound := countDeficit_add_le_card_of_le
      hand.counts
      (mentsuHandTargetWithTaatsu decomposition.pair
        decomposition.melds decomposition.taatsus)
      (taatsuCompletionTiles decomposition.taatsus)
      decomposition.targetWithinHand
    have hblocks := decomposition.blocks
    have hfixed := h13.1
    calc
      countDeficit hand.counts
          (TileCounts.ofMultiset
            (mentsuHandTargetWithTaatsu decomposition.pair
              decomposition.melds decomposition.taatsus +
              taatsuCompletionTiles decomposition.taatsus)) ≤
          (taatsuCompletionTiles decomposition.taatsus).card := hbound
      _ = decomposition.taatsus.length :=
        taatsuCompletionTiles_card decomposition.taatsus
      _ ≤ 4 := by omega
  have hreach :=
    reachesCompletion_mentsuHand_of_one_more_target_tile
      hand (TileCounts.ofMultiset (mentsuHandTarget decomposition.pair melds))
      decomposition.pair melds hsumTarget h13.2.2
      (by
        rw [htarget]
        exact decomposition.validCounts_completedTarget)
      hmelds
      (targetHand_hasTiles_countsOfTiles hand
        (mentsuHandTarget decomposition.pair melds))
  rcases hreach with ⟨distance, hdistanceEq, hreach⟩
  exact ⟨distance, by rw [hdistanceEq]; exact hdistance, hreach⟩

lemma complete_mentsuHand_of_mentsuHandTarget_distance_zero
    (before : Hand) (pair : Tile) (melds : List MentsuCandidate)
    (hdistance : mentsuHandTargetDistance before pair melds = 0)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (TileCounts.ofMultiset (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    Complete .mentsuHand before := by
  have hdeficit :
      countDeficit before.counts
        (TileCounts.ofMultiset (mentsuHandTarget pair melds)) = 0 := by
    rw [← mentsuHandTargetDistance_eq_countDeficit]
    exact hdistance
  have hzero :
      ∀ tile ∈ (Finset.univ : Finset Tile),
        (TileCounts.ofMultiset (mentsuHandTarget pair melds)) tile -
            before.counts tile = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (fun tile _ => Nat.zero_le _)).mp
    exact hdeficit
  have hle :
      ∀ tile, (TileCounts.ofMultiset (mentsuHandTarget pair melds)) tile ≤
        before.counts tile := by
    intro tile
    have hzeroTile := hzero tile (Finset.mem_univ tile)
    omega
  have heq :
      ∀ tile ∈ (Finset.univ : Finset Tile),
        (TileCounts.ofMultiset (mentsuHandTarget pair melds)) tile =
          before.counts tile := by
    apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := TileCounts.ofMultiset (mentsuHandTarget pair melds))
      (g := before.counts)
      (fun tile _ => hle tile)).mp
    exact hsum.symm
  have hcounts :
      TileCounts.ofMultiset (mentsuHandTarget pair melds) = before.counts := by
    funext tile
    exact heq tile (Finset.mem_univ tile)
  have hcomplete :
      Complete .mentsuHand
        (targetHand before
          (TileCounts.ofMultiset (mentsuHandTarget pair melds))) := by
    exact complete_mentsuHand_targetHand before
      (TileCounts.ofMultiset (mentsuHandTarget pair melds)) pair melds
      hvalid hmelds
      (targetHand_hasTiles_countsOfTiles before
        (mentsuHandTarget pair melds))
  simpa [targetHand, hcounts] using hcomplete

set_option maxHeartbeats 1000000 in
lemma reachesCompletion_mentsuHand_of_mentsuHandTarget_distance_one
    (before : Hand) (pair : Tile) (melds : List MentsuCandidate)
    (hdistance : mentsuHandTargetDistance before pair melds = 1)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (TileCounts.ofMultiset (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4)
    (hbeforeValid : ValidCounts before) :
    ReachesCompletion Complete .mentsuHand before 1 := by
  obtain ⟨discarded, drawn, hdrawn, hdiscarded, hne, hdistanceNext⟩ :=
    exists_mentsuHandTarget_exchange_of_pos
      before pair melds hsum (by omega)
  have hsumNext :
      (∑ tile : Tile, (exchangeHand before discarded drawn).counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile := by
    have hsumExchange :
        (∑ tile : Tile, (exchangeHand before discarded drawn).counts tile) =
          ∑ tile : Tile, before.counts tile := by
      change
        (∑ tile : Tile,
          exchangeCounts before discarded drawn tile) =
          ∑ tile : Tile, before.counts tile
      exact exchangeCounts_sum before discarded drawn hne (by omega)
    exact hsumExchange.trans hsum
  have hvalidNext :
      ValidCounts
        (targetHand (exchangeHand before discarded drawn)
          (TileCounts.ofMultiset (mentsuHandTarget pair melds))) := by
    change
      ValidCounts
        (targetHand before
          (TileCounts.ofMultiset (mentsuHandTarget pair melds)))
    exact hvalid
  have hmeldsNext :
      melds.length + (exchangeHand before discarded drawn).fixedMelds = 4 := by
    change melds.length + before.fixedMelds = 4
    exact hmelds
  have hcomplete :
      Complete .mentsuHand (exchangeHand before discarded drawn) := by
    have hzeroNext :
        mentsuHandTargetDistance
            (exchangeHand before discarded drawn) pair melds = 0 := by
      omega
    have hcountsNext :
        (exchangeHand before discarded drawn).counts =
          TileCounts.ofMultiset (mentsuHandTarget pair melds) :=
      (mentsuHandTargetDistance_eq_zero_iff
        (exchangeHand before discarded drawn) pair melds hsumNext).mp
        hzeroNext
    have htargetComplete :
        Complete .mentsuHand
          (targetHand (exchangeHand before discarded drawn)
            (TileCounts.ofMultiset (mentsuHandTarget pair melds))) :=
      complete_mentsuHand_targetHand
        (exchangeHand before discarded drawn)
        (TileCounts.ofMultiset (mentsuHandTarget pair melds))
        pair melds hvalidNext hmeldsNext
        (targetHand_hasTiles_countsOfTiles
          (exchangeHand before discarded drawn)
          (mentsuHandTarget pair melds))
    have hhand :
        exchangeHand before discarded drawn =
          targetHand (exchangeHand before discarded drawn)
            (TileCounts.ofMultiset (mentsuHandTarget pair melds)) := by
      cases hnext : exchangeHand before discarded drawn with
      | mk base fixed =>
          cases base with
          | mk counts =>
              simp only [targetHand]
              simpa [hnext] using
                congrArg
                  (fun counts : TileCounts =>
                    ({ counts := counts, fixedMelds := fixed } : Hand))
                  hcountsNext
    rw [hhand]
    exact htargetComplete
  apply ReachesCompletion.step
  · exact mentsuHandTargetExchange_handStep
      (TileCounts.ofMultiset (mentsuHandTarget pair melds))
      before discarded drawn hdrawn hdiscarded hne hbeforeValid hvalid
  · exact ReachesCompletion.done hcomplete

set_option maxHeartbeats 1000000 in
lemma reachesCompletion_mentsuHand_of_mentsuHandTarget_distance
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List MentsuCandidate)
    (hdistance : mentsuHandTargetDistance before pair melds = distance)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (TileCounts.ofMultiset (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4)
    (hbeforeValid : ValidCounts before) :
    ReachesCompletion Complete .mentsuHand before distance := by
  induction distance generalizing before with
  | zero =>
      have hcomplete : Complete .mentsuHand before := by
        exact complete_mentsuHand_of_mentsuHandTarget_distance_zero
          before pair melds hdistance hsum hvalid hmelds
      exact ReachesCompletion.done hcomplete
  | succ distance ih =>
      obtain ⟨discarded, drawn, hdrawn, hdiscarded, hne, hdistanceNext⟩ :=
        exists_mentsuHandTarget_exchange_of_pos
          before pair melds hsum (by omega)
      have hsumNext :
          (∑ tile : Tile,
            (exchangeHand before discarded drawn).counts tile) =
            ∑ tile : Tile, (mentsuHandTarget pair melds).count tile := by
        have hsumExchange :
            (∑ tile : Tile,
              (exchangeHand before discarded drawn).counts tile) =
              ∑ tile : Tile, before.counts tile := by
          change
            (∑ tile : Tile,
              exchangeCounts before discarded drawn tile) =
              ∑ tile : Tile, before.counts tile
          exact exchangeCounts_sum before discarded drawn hne (by omega)
        exact hsumExchange.trans hsum
      have hvalidNext :
          ValidCounts
            (targetHand (exchangeHand before discarded drawn)
              (TileCounts.ofMultiset (mentsuHandTarget pair melds))) := by
        change
          ValidCounts
            (targetHand before
              (TileCounts.ofMultiset (mentsuHandTarget pair melds)))
        exact hvalid
      have hmeldsNext :
          melds.length + (exchangeHand before discarded drawn).fixedMelds = 4 := by
        change melds.length + before.fixedMelds = 4
        exact hmelds
      have hdistanceNext' :
          mentsuHandTargetDistance
              (exchangeHand before discarded drawn) pair melds = distance := by
        omega
      have hstep := mentsuHandTargetExchange_handStep
        (TileCounts.ofMultiset (mentsuHandTarget pair melds))
        before discarded drawn hdrawn hdiscarded hne hbeforeValid hvalid
      have hrest :=
        ih (exchangeHand before discarded drawn)
          hdistanceNext' hsumNext hvalidNext hmeldsNext hstep.validCounts
      apply ReachesCompletion.step
      · exact hstep
      · exact hrest

lemma isShapeShanten_mentsuHand_of_mentsuHandTarget_distance
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List MentsuCandidate)
    (hdistance : mentsuHandTargetDistance before pair melds = distance)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (TileCounts.ofMultiset (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4)
    (hminimal :
      ∀ smaller : Nat, smaller < distance →
        ¬ ReachesCompletion Complete .mentsuHand before smaller)
    (hbeforeValid : ValidCounts before) :
    IsShapeShanten before .mentsuHand ((distance : Int) - 1) := by
  have hreaches :
      ReachesCompletion Complete .mentsuHand before distance :=
    reachesCompletion_mentsuHand_of_mentsuHandTarget_distance
      distance before pair melds hdistance hsum hvalid hmelds hbeforeValid
  refine ⟨trivial, distance, ?_, hreaches, hminimal⟩
  omega

end Shanten
