import Shanten.Exchange

/-!
# Seven pairs / Exchange / Basic

Pairing candidates and the distinctness, pair-making, and protected exchange relations.
-/

namespace Shanten

/--
A tile kind that is not yet a pair.  A zero-count tile is also a candidate:
the first exchange creates its singleton, and a later exchange can complete
the pair.  This is needed for hands concentrated in only a few tile kinds.
-/
def IsPairingCandidate (hand : Hand) (tile : Tile) : Prop :=
  hand.counts tile < 2

lemma pairingCandidate_not_pair
    (hand : Hand) (tile : Tile) (hcandidate : IsPairingCandidate hand tile) :
    ¬ 2 ≤ hand.counts tile := by
  unfold IsPairingCandidate at hcandidate
  omega

/-- One exchange that advances a tile kind toward its target pair count. -/
def PairingExchange (before after : Hand) : Prop :=
  ∃ discarded drawn,
    IsPairingCandidate before drawn ∧
      discarded ≠ drawn ∧
      before.counts discarded > 0 ∧
      after = exchangeHand before discarded drawn

/- A discard that leaves at least one pair of the same tile kind. -/
def IsPairPreservingDiscard (hand : Hand) (tile : Tile) : Prop :=
  3 ≤ hand.counts tile

/- A draw of a tile kind that is not present in the hand. -/
def IsAbsentTileKind (hand : Hand) (tile : Tile) : Prop :=
  hand.counts tile = 0

/--
An exchange that introduces a new tile kind while removing an extra copy from
an existing kind.  It preserves every existing pair.
-/
def DistinctnessExchange (before after : Hand) : Prop :=
  ∃ discarded drawn,
    IsPairPreservingDiscard before discarded ∧
      IsAbsentTileKind before drawn ∧
      discarded ≠ drawn ∧
      after = exchangeHand before discarded drawn

/--
An exchange that turns a singleton into a pair while discarding an extra copy
from another kind.
-/
def PairMakingExchange (before after : Hand) : Prop :=
  ∃ discarded drawn,
    before.counts drawn = 1 ∧
      IsPairPreservingDiscard before discarded ∧
      discarded ≠ drawn ∧
      after = exchangeHand before discarded drawn

/-- A discard that either preserves a pair or removes a protected-outside
singleton kind. -/
def IsProtectedPairMakingDiscard
    (hand : Hand) (protectedTiles : Finset Tile) (tile : Tile) : Prop :=
  3 ≤ hand.counts tile ∨
    (hand.counts tile = 1 ∧ tile ∉ protectedTiles)

/--
An exchange that makes a pair in one of the protected tile kinds.  The
discarded kind is either a surplus kind or a singleton outside the protected
set.
-/
def ProtectedPairMakingExchange
    (protectedTiles : Finset Tile) (before after : Hand) : Prop :=
  ∃ discarded drawn,
    drawn ∈ protectedTiles ∧
      before.counts drawn = 1 ∧
      IsProtectedPairMakingDiscard before protectedTiles discarded ∧
      discarded ≠ drawn ∧
      after = exchangeHand before discarded drawn

/-- Every pairing exchange is an ordinary exchange step. -/
lemma PairingExchange.handStep
    (h : PairingExchange before after) : HandStep before after := by
  rcases h with ⟨discarded, drawn, hcandidate, hne, hdiscarded, rfl⟩
  exact exchangeHand_step before discarded drawn hne hdiscarded

end Shanten
