module

public import Shanten.Experimental.SuitDP

@[expose] public section

/-!
# Experimental whole-hand tile-order mentsu calculation

This implementation assumes separately validated input. Its equivalence to the
capacity-aware specification is not yet proved.
-/

namespace Shanten.Experimental.TileDP

open MahjongDomain Shanten.Capacity

def canStartSequence (_position : Nat) : Tile → Bool
  | .suited _ rank => rank.val < 7
  | .honor _ => false

/-- Experimental: requires valid input and has no specification-equivalence proof yet. -/
def minimumSearch (fixed : List FixedMeld) (hand : Hand) : Option Int :=
  let maxMelds := 4 - hand.fixedMelds
  let costs := SuitDP.scanCosts hand (fixedTiles fixed) Tile.all canStartSequence maxMelds
  (costs[maxMelds * 2 + 1]!).map fun missing => (missing : Int) - 1

end Shanten.Experimental.TileDP
