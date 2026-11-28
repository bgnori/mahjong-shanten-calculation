module

import Shanten.Capacity.HandSnapshot
import Shanten.Capacity.Overall
meta import Shanten.Capacity.HandSnapshot
meta import Shanten.Capacity.Overall
meta import MahjongDomain.HandSnapshot

open MahjongDomain

namespace Shanten.Capacity.HandSnapshotExamples

def melds : List MahjongDomain.FixedMeld :=
  [ .chi ⟨.man, ⟨0, by decide⟩⟩ ⟨1, by decide⟩
  , .pon (.honor Honor.east) .kamicha
  , .daiminkan (.honor Honor.south) .shimocha
  , .kakan (.honor Honor.west) .toimen
  , .ankan (.honor Honor.north) ]

example :
    (melds.all fun meld =>
      Tile.all.all fun tile =>
        meld.occupiedCounts.normalized tile ==
          (fixedMeldOfSnapshot meld).tiles.count tile) = true := by
  native_decide

def sample : HandSnapshot :=
  { standing := Tile37Counts.ofNormalizedList [.honor Honor.east]
    fixedMelds :=
      [ .pon (.honor Honor.east) .kamicha
      , .chi ⟨.man, ⟨0, by decide⟩⟩ ⟨0, by decide⟩
      , .chi ⟨.pin, ⟨0, by decide⟩⟩ ⟨1, by decide⟩
      , .chi ⟨.sou, ⟨0, by decide⟩⟩ ⟨2, by decide⟩ ] }

example :
    let (fixed, hand) := ofHandSnapshot sample
    IsThirteenTileEquivalentHand fixed hand ∧ hand.fixedMelds = sample.fixedMelds.length := by
  unfold IsThirteenTileEquivalentHand ValidHand
  decide

example :
    let (_, hand) := ofHandSnapshot sample
    (Tile.all.all fun tile =>
      hand.counts tile == sample.normalizedStanding tile) = true := by
  native_decide

example :
    let (fixed, hand) := ofHandSnapshot sample
    overallMinimumSearch fixed hand = some 1 := by
  native_decide

def kanSample : HandSnapshot :=
  { standing := Tile37Counts.ofNormalizedList [.honor Honor.white]
    fixedMelds :=
      [ .ankan (.honor Honor.east)
      , .chi ⟨.man, ⟨0, by decide⟩⟩ ⟨0, by decide⟩
      , .chi ⟨.pin, ⟨0, by decide⟩⟩ ⟨1, by decide⟩
      , .chi ⟨.sou, ⟨0, by decide⟩⟩ ⟨2, by decide⟩ ] }

example :
    let (fixed, hand) := ofHandSnapshot kanSample
    overallMinimumSearch fixed hand = some 0 := by
  native_decide

example :
    let complete : HandSnapshot :=
      { kanSample with
        standing := Tile37Counts.ofNormalizedList
          [.honor Honor.white, .honor Honor.white] }
    let (fixed, hand) := ofHandSnapshot complete
    overallMinimumSearch fixed hand = some (-1) := by
  native_decide

example :
    let invalid : HandSnapshot :=
      { standing := Tile37Counts.ofNormalizedList [.honor Honor.east, .honor Honor.east]
        fixedMelds := sample.fixedMelds }
    let (fixed, hand) := ofHandSnapshot invalid
    ¬ ValidHand fixed hand := by
  unfold ValidHand
  decide

end Shanten.Capacity.HandSnapshotExamples
