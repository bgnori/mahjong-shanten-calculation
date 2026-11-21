import Shanten.Capacity.Examples
import Mahjong.WaitCompletionFinder
import Mathlib.Util.AssertNoSorry

namespace SharedDomainW6

open Shanten Shanten.Capacity

def IsFixedContextWait (fixed : List FixedMeld) (hand : Hand) (tile : MahjongDomain.Tile) : Prop :=
  hand.counts tile < remainingCapacity fixed tile ∧
    Complete fixed .mentsuHand (drawHand hand tile)

def shantenTileOfClassification (tile : _root_.Tile) : MahjongDomain.Tile :=
  Mahjong.DomainAdapter.toDomainTile tile

def classificationTileOfShanten (tile : MahjongDomain.Tile) : _root_.Tile :=
  Mahjong.DomainAdapter.ofDomainTile tile

def CountsMatch (hand : Shanten.Hand) (tiles : List _root_.Tile) : Prop :=
  ∀ tile : MahjongDomain.Tile, tiles.count (classificationTileOfShanten tile) = hand.counts tile

theorem shantenTileOfClassification_roundTrip (tile : _root_.Tile) :
    classificationTileOfShanten (shantenTileOfClassification tile) = tile := by
  simp [shantenTileOfClassification, classificationTileOfShanten,
    Mahjong.DomainAdapter.ofDomainTile_toDomainTile]

theorem classificationTileOfShanten_roundTrip (tile : MahjongDomain.Tile) :
    shantenTileOfClassification (classificationTileOfShanten tile) = tile := by
  simp [shantenTileOfClassification, classificationTileOfShanten,
    Mahjong.DomainAdapter.toDomainTile_ofDomainTile]

def classificationTileEquiv : MahjongDomain.Tile ≃ _root_.Tile where
  toFun := classificationTileOfShanten
  invFun := shantenTileOfClassification
  left_inv := classificationTileOfShanten_roundTrip
  right_inv := shantenTileOfClassification_roundTrip

theorem classificationTile_eq_iff
    (candidate : _root_.Tile) (tile : MahjongDomain.Tile) :
    candidate = classificationTileOfShanten tile ↔
      shantenTileOfClassification candidate = tile := by
  constructor
  · intro h
    calc
      shantenTileOfClassification candidate =
          shantenTileOfClassification (classificationTileOfShanten tile) :=
        congrArg shantenTileOfClassification h
      _ = tile := classificationTileOfShanten_roundTrip tile
  · intro h
    calc
      candidate =
          classificationTileOfShanten (shantenTileOfClassification candidate) :=
        (shantenTileOfClassification_roundTrip candidate).symm
      _ = classificationTileOfShanten tile := congrArg classificationTileOfShanten h

theorem list_length_eq_sum_count {α : Type} [Fintype α] [DecidableEq α]
    [BEq α] [LawfulBEq α] (items : List α) :
    items.length = ∑ item, items.count item := by
  induction items with
  | nil => simp
  | cons first rest ih =>
      simp [List.count_cons, Finset.sum_add_distrib, ih]

theorem CountsMatch.toDomain
    (hcounts : CountsMatch hand tiles) :
    Mahjong.DomainAdapter.tileListCounts tiles = hand.counts := by
  funext tile
  rw [Mahjong.DomainAdapter.tileListCounts,
    Mahjong.DomainAdapter.toDomainTileList_count]
  simpa [classificationTileOfShanten] using hcounts tile

theorem CountsMatch.length_eq
    (hcounts : CountsMatch hand tiles) :
    tiles.length = tileCount hand := by
  calc
    tiles.length = ∑ tile : _root_.Tile, tiles.count tile :=
      list_length_eq_sum_count tiles
    _ = ∑ tile : MahjongDomain.Tile, tiles.count (classificationTileOfShanten tile) :=
      Fintype.sum_equiv classificationTileEquiv.symm
        (fun tile : _root_.Tile => tiles.count tile)
        (fun tile : MahjongDomain.Tile => tiles.count (classificationTileOfShanten tile))
        (fun tile => by
          change tiles.count tile =
            tiles.count (classificationTileOfShanten (shantenTileOfClassification tile))
          rw [shantenTileOfClassification_roundTrip])
    _ = ∑ tile : MahjongDomain.Tile, hand.counts tile := by
      apply Finset.sum_congr rfl
      intro tile _
      exact hcounts tile
    _ = tileCount hand := rfl

theorem CountsMatch.draw
    (hcounts : CountsMatch hand tiles) (candidate : _root_.Tile) :
    CountsMatch (drawHand hand (shantenTileOfClassification candidate))
      (candidate :: tiles) := by
  intro tile
  simp only [List.count_cons, beq_iff_eq, classificationTile_eq_iff]
  simp [Shanten.Capacity.drawHand, hcounts tile, eq_comm]

theorem flatMapMentsuComponentsTiles (melds : List MentsuCandidate) :
    ((melds.map fun candidate => (Sum.inr candidate : WinningComponent)).flatMap
      WinningComponent.tiles) = melds.flatMap MentsuCandidate.tiles := by
  induction melds with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, List.flatMap_cons, WinningComponent.tiles]
      rw [ih]

theorem standardCompletion_toStandardAgari {tiles : List _root_.Tile}
    {meldCount : Nat}
    (hcompletion : MahjongDomain.StandardCompletion meldCount
      (Mahjong.DomainAdapter.tileListCounts tiles)) :
    WaitCompletionFinder.IsStandardAgari tiles := by
  obtain ⟨decomposition, _, hcounts⟩ := hcompletion
  let localParts := Mahjong.DomainAdapter.ofDomainDecomposition decomposition
  let pair := localParts.1
  let melds := localParts.2
  have hdecomposition :
      Mahjong.DomainAdapter.toDomainDecomposition pair melds = decomposition := by
    change Mahjong.DomainAdapter.toDomainDecomposition
      (Mahjong.DomainAdapter.ofDomainDecomposition decomposition).1
      (Mahjong.DomainAdapter.ofDomainDecomposition decomposition).2 = decomposition
    exact Mahjong.DomainAdapter.toDomainDecomposition_ofDomainDecomposition decomposition
  have localPartsTiles :
      ((Sum.inl pair : WinningComponent) ::
          melds.map fun candidate => (Sum.inr candidate : WinningComponent)).flatMap
          WinningComponent.tiles =
        pair.tiles ++ melds.flatMap MentsuCandidate.tiles := by
    simp only [List.flatMap_cons, WinningComponent.tiles]
    rw [flatMapMentsuComponentsTiles]
  have hpartsCounts :=
    decomposition.counts_eq_parts.symm.trans hcounts
  have localCounts : ∀ tile : _root_.Tile,
      (pair.tiles ++ melds.flatMap MentsuCandidate.tiles).count tile =
        tiles.count tile := by
    intro tile
    have hcount := congrFun hpartsCounts
      (Mahjong.DomainAdapter.toDomainTile tile)
    rw [← hdecomposition, Mahjong.DomainAdapter.toDomainDecomposition,
      Mahjong.DomainAdapter.toDomainPair_count,
      Mahjong.DomainAdapter.toDomainMentsuCandidates_count,
      Mahjong.DomainAdapter.tileListCounts,
      Mahjong.DomainAdapter.toDomainTileList_count,
      Mahjong.DomainAdapter.ofDomainTile_toDomainTile] at hcount
    simpa [List.count_append] using hcount
  have partsPermutation :
      (((Sum.inl pair : WinningComponent) ::
          melds.map fun candidate => (Sum.inr candidate : WinningComponent)).flatMap
          WinningComponent.tiles).Perm tiles := by
    apply List.perm_iff_count.mpr
    intro tile
    rw [localPartsTiles, List.count_append]
    simpa [List.count_append] using localCounts tile
  have specification : WaitCompletionFinder.WinningPartitionSpec tiles
      (.inl pair :: melds.map fun candidate => (Sum.inr candidate : WinningComponent)) :=
    ⟨.inl pair, melds, rfl,
      WaitCompletionFinder.pair_mem_pairComponentCandidates pair, partsPermutation⟩
  have member := (WaitCompletionFinder.mem_winningPartitions_iff_spec _ _).mpr
    specification
  have nonempty : WaitCompletionFinder.winningPartitions tiles ≠ [] :=
    List.ne_nil_of_mem member
  unfold WaitCompletionFinder.IsStandardAgari WaitCompletionFinder.isWinning
  simpa [List.isEmpty_iff] using nonempty

theorem standardAgari_toDomainCompletion_fixed
    {fixed : List FixedMeld}
    (hAgari : WaitCompletionFinder.IsStandardAgari (candidate :: tiles))
    (hsize : tiles.length + 3 * fixed.length = 13) :
    MahjongDomain.StandardCompletion (4 - fixed.length)
      (Mahjong.DomainAdapter.tileListCounts (candidate :: tiles)) := by
  have hnonempty : WaitCompletionFinder.winningPartitions (candidate :: tiles) ≠ [] := by
    unfold WaitCompletionFinder.IsStandardAgari WaitCompletionFinder.isWinning at hAgari
    simpa [List.isEmpty_iff] using hAgari
  obtain ⟨components, member⟩ :=
    List.exists_mem_of_ne_nil _ hnonempty
  have specification :=
    (WaitCompletionFinder.mem_winningPartitions_iff_spec _ _).mp member
  obtain ⟨pairComponent, melds, componentsEq, pairMember, tilesPerm⟩ := specification
  obtain ⟨pair, pairEq⟩ :=
    WaitCompletionFinder.pair_of_mem_pairComponentCandidates pairMember
  subst pairComponent
  subst components
  have hpartsLength :
      (((Sum.inl pair : WinningComponent) ::
        melds.map fun candidate => (Sum.inr candidate : WinningComponent)).flatMap
          WinningComponent.tiles).length = 2 + 3 * melds.length := by
    calc
      _ = pair.tiles.length + (melds.flatMap MentsuCandidate.tiles).length := by
        simp only [List.flatMap_cons, List.length_append, WinningComponent.tiles]
        rw [flatMapMentsuComponentsTiles]
      _ = 2 + melds.length * mentsuTileCount := by
        simp only [Toitsu.tiles, List.length_cons, List.length_nil]
        rw [MentsuCandidate.flatMap_tiles_length]
      _ = 2 + 3 * melds.length := by
        simp [mentsuTileCount, Nat.mul_comm]
  have hpermLength := tilesPerm.length_eq
  rw [hpartsLength] at hpermLength
  have hmelds : melds.length = 4 - fixed.length := by
    simp only [List.length_cons] at hpermLength
    omega
  have hcompletion :
      MahjongDomain.StandardCompletion melds.length
        (Mahjong.DomainAdapter.tileListCounts (candidate :: tiles)) := by
    refine ⟨Mahjong.DomainAdapter.toDomainDecomposition pair melds, ?_, ?_⟩
    · simp [Mahjong.DomainAdapter.toDomainDecomposition,
        Mahjong.DomainAdapter.toDomainMentsuCandidates]
    · rw [MahjongDomain.StandardDecomposition.counts_eq_parts]
      simp only [Mahjong.DomainAdapter.toDomainDecomposition]
      funext tile
      have localParts :
          ((Sum.inl pair : WinningComponent) ::
              melds.map fun candidate => (Sum.inr candidate : WinningComponent)).flatMap
              WinningComponent.tiles =
            pair.tiles ++ melds.flatMap MentsuCandidate.tiles := by
        simp only [List.flatMap_cons, WinningComponent.tiles]
        rw [flatMapMentsuComponentsTiles]
      have domainPermutation :
          ((pair.tiles ++ melds.flatMap MentsuCandidate.tiles).map
            Mahjong.DomainAdapter.toDomainTile).Perm
            ((candidate :: tiles).map Mahjong.DomainAdapter.toDomainTile) := by
        simpa only [localParts] using tilesPerm.map Mahjong.DomainAdapter.toDomainTile
      have countsPermuted := domainPermutation.count tile
      rw [Mahjong.DomainAdapter.toDomainPair_count,
        Mahjong.DomainAdapter.toDomainMentsuCandidates_count,
        ← Mahjong.DomainAdapter.toDomainTileList_count pair.tiles tile,
        ← Mahjong.DomainAdapter.toDomainTileList_count
          (melds.flatMap MentsuCandidate.tiles) tile]
      rw [← List.count_append]
      simpa only [List.map_append, Mahjong.DomainAdapter.tileListCounts] using countsPermuted
  simpa [hmelds] using hcompletion

theorem fixedContextWait_iff_classificationWait
    (h13 : IsThirteenTileEquivalentHand fixed hand)
    (hcounts : CountsMatch hand tiles) (candidate : _root_.Tile) :
    IsFixedContextWait fixed hand (shantenTileOfClassification candidate) ↔
      WaitCompletionFinder.IsWaitFor tiles candidate ∧
        hand.counts (shantenTileOfClassification candidate) +
          (fixedTiles fixed).count (shantenTileOfClassification candidate) < 4 := by
  let tile := shantenTileOfClassification candidate
  have hsize : tiles.length + 3 * fixed.length = 13 := by
    rw [hcounts.length_eq]
    exact h13.2
  have hcapacityEquiv :
      hand.counts tile < remainingCapacity fixed tile ↔
        hand.counts tile + (fixedTiles fixed).count tile < 4 := by
    simp only [remainingCapacity]
    omega
  have hlegalSize : WaitCompletionFinder.IsTenpaiHandSize tiles.length := by
    unfold WaitCompletionFinder.IsTenpaiHandSize
    refine ⟨4 - fixed.length, ?_, ?_⟩
    · apply List.mem_range.mpr
      simp [standardHandMentsuCount]
      omega
    · simp [standardTenpaiHandSize, standardHandPairCount, mentsuTileCount]
      omega
  have hlegalCounts : WaitCompletionFinder.HasLegalTileCounts tiles := by
    intro classificationTile
    let shantenTile := shantenTileOfClassification classificationTile
    have hmatch := hcounts shantenTile
    rw [shantenTileOfClassification_roundTrip] at hmatch
    have hvalid := h13.1.2.2 shantenTile
    change tiles.count classificationTile ≤ copiesPerTile
    rw [hmatch]
    simp only [copiesPerTile]
    omega
  constructor
  · rintro ⟨hcapacity, hcomplete⟩
    have hcombined := hcapacityEquiv.mp hcapacity
    have hdrawCounts := hcounts.draw candidate
    have hshared :
        MahjongDomain.StandardCompletion (4 - fixed.length)
          (Mahjong.DomainAdapter.tileListCounts (candidate :: tiles)) := by
      have hstandard :=
        (Complete.mentsuHand_iff_standardCompletion.mp hcomplete).2
      rw [← hdrawCounts.toDomain] at hstandard
      exact hstandard
    have hagari := standardCompletion_toStandardAgari hshared
    have havailable : tiles.count candidate < copiesPerTile := by
      have hmatch := hcounts tile
      dsimp [tile] at hmatch
      rw [shantenTileOfClassification_roundTrip] at hmatch
      have hcountLt : hand.counts tile < 4 := by omega
      change tiles.count candidate < 4
      rw [hmatch]
      exact hcountLt
    exact ⟨⟨⟨hlegalSize, hlegalCounts⟩, havailable, hagari⟩, hcombined⟩
  · rintro ⟨hwait, hcombined⟩
    have hcapacity := hcapacityEquiv.mpr hcombined
    have hdrawValid : ValidHand fixed (drawHand hand tile) :=
      h13.1.draw hcapacity
    have hshared := standardAgari_toDomainCompletion_fixed hwait.2.2 hsize
    have hdrawCounts := hcounts.draw candidate
    rw [hdrawCounts.toDomain] at hshared
    have hcomplete : Complete fixed .mentsuHand (drawHand hand tile) :=
      (Complete.mentsuHand_iff_standardCompletion).mpr ⟨hdrawValid, hshared⟩
    exact ⟨hcapacity, hcomplete⟩

theorem completeTileCount
    (hcomplete : Complete fixed .mentsuHand hand) :
    tileCount hand = 2 + 3 * (4 - fixed.length) := by
  obtain ⟨hvalid, hshape⟩ := hcomplete
  obtain ⟨_, pair, melds, hlength, htiles⟩ := hshape
  have hcounts : hand.counts = countsOfTiles
      (pairTiles pair + meldsTiles melds) := by
    funext tile
    exact htiles tile
  rw [tileCount, hcounts, countsOfTiles_sum_eq_card, Multiset.card_add,
    pairTiles_card, meldsTiles_card]
  have hfixed : hand.fixedMelds = fixed.length := hvalid.1
  have hmelds : melds.length + fixed.length = 4 := by
    rw [← hfixed]
    exact hlength
  have hbound : fixed.length ≤ 4 := hvalid.2.1
  have hmelds' : melds.length = 4 - fixed.length := by omega
  rw [hmelds']

theorem notCompleteAtThirteen
    (h13 : IsThirteenTileEquivalentHand fixed hand) :
    ¬ Complete fixed .mentsuHand hand := by
  intro hcomplete
  have hcount := completeTileCount hcomplete
  have hfixed : fixed.length ≤ 4 := h13.1.2.1
  have hsize := h13.2
  omega

theorem handStepTileCount
    (hstep : Shanten.HandStep before after) :
    tileCount after = tileCount before + 1 ∨ tileCount after = tileCount before := by
  rcases hstep.2 with ⟨drawn, _, hcounts⟩ |
    ⟨discarded, drawn, hne, _, _, hcounts⟩
  · left
    unfold tileCount
    have hcountsEq : after.counts =
        fun tile => before.counts tile + (if tile = drawn then 1 else 0) :=
      funext hcounts
    rw [hcountsEq]
    simp [Finset.sum_add_distrib]
  · right
    unfold tileCount
    have hcountsEq :
        (fun tile => after.counts tile + (if tile = discarded then 1 else 0)) =
        (fun tile => before.counts tile + (if tile = drawn then 1 else 0)) :=
      funext hcounts
    have hsum := congrArg (fun counts : MahjongDomain.Tile → Nat => ∑ tile, counts tile) hcountsEq
    simp [Finset.sum_add_distrib] at hsum
    exact hsum

theorem isShapeShanten_zero_iff_exists_fixedContextWait
    (h13 : IsThirteenTileEquivalentHand fixed hand) :
    IsShapeShanten fixed hand .mentsuHand 0 ↔
      ∃ tile, IsFixedContextWait fixed hand tile := by
  constructor
  · rintro ⟨_, distance, hdistance, hreach, _⟩
    have hdistance' : distance = 1 := by omega
    subst distance
    obtain ⟨next, hstep, hcomplete⟩ :=
      (reachesCompletion_one_iff (fixed := fixed) (shape := .mentsuHand)
        (hand := hand)).mp hreach
    have hbefore : tileCount hand = 13 - 3 * fixed.length := by
      have := h13.2
      omega
    have hafter : tileCount next = tileCount hand + 1 := by
      have hcount := completeTileCount hcomplete
      have hstepCount := handStepTileCount hstep.toAbstract
      omega
    rcases hstep.toAbstract.2 with draw | exchange
    · obtain ⟨tile, _, hcounts⟩ := draw
      have hnext : next = drawHand hand tile := by
        cases next with
        | mk counts fixedMelds =>
            cases hand with
            | mk handCounts handFixed =>
                simp only [Shanten.Hand.mk.injEq, drawHand]
                constructor
                · funext kind
                  exact hcounts kind
                · exact hstep.toAbstract.1.symm
      subst next
      have hcapacity := hcomplete.1.counts_le_capacity tile
      simp [drawHand] at hcapacity
      have hdrawn : hand.counts tile < remainingCapacity fixed tile := by
        omega
      exact ⟨tile, hdrawn, hcomplete⟩
    · obtain ⟨discarded, drawn, hne, _, _, hcounts⟩ := exchange
      have hsame : tileCount next = tileCount hand := by
        unfold tileCount
        have hcountsEq :
            (fun tile => next.counts tile + (if tile = discarded then 1 else 0)) =
            (fun tile => hand.counts tile + (if tile = drawn then 1 else 0)) :=
          funext hcounts
        have hsum := congrArg
          (fun counts : MahjongDomain.Tile → Nat => ∑ tile, counts tile) hcountsEq
        simp [Finset.sum_add_distrib] at hsum
        exact hsum
      omega
  · rintro ⟨tile, hwait⟩
    have hstep : HandStep fixed hand (drawHand hand tile) :=
      drawHand_step h13.1 hwait.1
    refine ⟨trivial, 1, by omega,
      (reachesCompletion_one_iff (fixed := fixed) (shape := .mentsuHand)
        (hand := hand)).mpr ⟨drawHand hand tile, hstep, hwait.2⟩, ?_⟩
    intro smaller hsmaller hreach
    have hzero : smaller = 0 := by omega
    subst smaller
    exact notCompleteAtThirteen h13 (reachesCompletion_zero_iff.mp hreach)

theorem isShapeShanten_zero_iff_exists_classificationWait
    (h13 : IsThirteenTileEquivalentHand fixed hand)
    (hcounts : CountsMatch hand tiles) :
    IsShapeShanten fixed hand .mentsuHand 0 ↔
      ∃ candidate : _root_.Tile,
        WaitCompletionFinder.IsWaitFor tiles candidate ∧
          hand.counts (shantenTileOfClassification candidate) +
            (fixedTiles fixed).count (shantenTileOfClassification candidate) < 4 := by
  rw [isShapeShanten_zero_iff_exists_fixedContextWait h13]
  constructor
  · rintro ⟨tile, hwait⟩
    let candidate := classificationTileOfShanten tile
    have hround : shantenTileOfClassification candidate = tile := by
      simpa [candidate] using classificationTileOfShanten_roundTrip tile
    have hwait' : IsFixedContextWait fixed hand
        (shantenTileOfClassification candidate) := by
      rw [hround]
      exact hwait
    have hbridge :=
      (fixedContextWait_iff_classificationWait h13 hcounts candidate).mp hwait'
    refine ⟨candidate, ?_⟩
    simpa [candidate, classificationTileOfShanten_roundTrip] using hbridge
  · rintro ⟨candidate, hwait⟩
    refine ⟨shantenTileOfClassification candidate, ?_⟩
    exact (fixedContextWait_iff_classificationWait h13 hcounts candidate).mpr hwait

def man1 : MahjongDomain.Tile := .suited .man ⟨0, by omega⟩
def pin1 : MahjongDomain.Tile := .suited .pin ⟨0, by omega⟩
def sou1 : MahjongDomain.Tile := .suited .sou ⟨0, by omega⟩
def east : MahjongDomain.Tile := .honor ⟨0, by omega⟩
def south : MahjongDomain.Tile := .honor ⟨1, by omega⟩

def fixedSequences : List FixedMeld :=
  [ .meld (.shuntsu ⟨.pin, ⟨0, by omega⟩⟩)
  , .meld (.shuntsu ⟨.sou, ⟨0, by omega⟩⟩) ]

def fixedA : List FixedMeld :=
  .meld (.koutsu east) :: fixedSequences

def fixedB : List FixedMeld :=
  .meld (.koutsu south) :: fixedSequences

def standingAB : Hand :=
  { counts := fun tile =>
      if tile = man1 then 3 else if tile = east then 1 else 0
    fixedMelds := 3 }

def classificationStanding : List _root_.Tile :=
  [ _root_.Tile.numbered .Manzu 0, _root_.Tile.numbered .Manzu 0,
    _root_.Tile.numbered .Manzu 0, _root_.Tile.honor .East ]

def classificationEast : _root_.Tile := _root_.Tile.honor .East

theorem capacityAB :
    IsThirteenTileEquivalentHand fixedA standingAB ∧
      IsThirteenTileEquivalentHand fixedB standingAB ∧
      WaitCompletionFinder.IsWaitFor classificationStanding classificationEast ∧
      ¬ IsFixedContextWait fixedA standingAB east ∧
      IsFixedContextWait fixedB standingAB east := by
  have h13A : IsThirteenTileEquivalentHand fixedA standingAB := by
    unfold IsThirteenTileEquivalentHand ValidHand fixedA fixedSequences
    decide
  have h13B : IsThirteenTileEquivalentHand fixedB standingAB := by
    unfold IsThirteenTileEquivalentHand ValidHand fixedB fixedSequences
    decide
  have hcounts : CountsMatch standingAB classificationStanding := by
    intro tile
    fin_cases tile <;> decide
  have heast : shantenTileOfClassification classificationEast = east := by decide
  have hclassificationWait :
      WaitCompletionFinder.IsWaitFor classificationStanding classificationEast := by
    unfold WaitCompletionFinder.IsWaitFor
    refine ⟨by decide, by decide, ?_⟩
    have hmember :
        (.inl (.toitsu classificationEast) ::
          [.inr (.koutsu (_root_.Tile.numbered .Manzu 0))]) ∈
          WaitCompletionFinder.winningPartitions
            (classificationEast :: classificationStanding) := by
      apply (WaitCompletionFinder.mem_winningPartitions_iff_spec _ _).mpr
      refine ⟨.inl (.toitsu classificationEast),
        [.koutsu (_root_.Tile.numbered .Manzu 0)], rfl, ?_, ?_⟩
      · exact WaitCompletionFinder.pair_mem_pairComponentCandidates
          (.toitsu classificationEast)
      · decide
    have hnonempty :
        WaitCompletionFinder.winningPartitions
            (classificationEast :: classificationStanding) ≠ [] :=
      List.ne_nil_of_mem hmember
    simp [WaitCompletionFinder.IsStandardAgari,
      WaitCompletionFinder.isWinning, hnonempty]
  have hnotA : ¬ IsFixedContextWait fixedA standingAB east := by
    intro hwait
    have hbridge :=
      (fixedContextWait_iff_classificationWait h13A hcounts classificationEast).mp hwait
    have hcapacity :
        standingAB.counts east + (fixedTiles fixedA).count east < 4 := by
      simpa [heast] using hbridge.2
    have himpossible :
        ¬ (standingAB.counts east + (fixedTiles fixedA).count east < 4) := by
      decide
    exact himpossible hcapacity
  have hcombinedB :
      standingAB.counts east + (fixedTiles fixedB).count east < 4 := by
    decide
  have hwaitB : IsFixedContextWait fixedB standingAB east :=
    (fixedContextWait_iff_classificationWait h13B hcounts classificationEast).mpr
      ⟨hclassificationWait, hcombinedB⟩
  exact ⟨h13A, h13B, hclassificationWait, hnotA, hwaitB⟩

theorem capacityB_shanten_zero :
    IsShapeShanten fixedB standingAB .mentsuHand 0 := by
  obtain ⟨_, h13B, _, _, hwaitB⟩ := capacityAB
  exact (isShapeShanten_zero_iff_exists_fixedContextWait h13B).mpr
    ⟨east, hwaitB⟩

assert_no_sorry fixedContextWait_iff_classificationWait
assert_no_sorry isShapeShanten_zero_iff_exists_fixedContextWait
assert_no_sorry isShapeShanten_zero_iff_exists_classificationWait
assert_no_sorry capacityAB
assert_no_sorry capacityB_shanten_zero

end SharedDomainW6
