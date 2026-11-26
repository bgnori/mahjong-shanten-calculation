module

public import MahjongDomain.HandSnapshot
public import Shanten.Capacity.Basic

@[expose] public section

namespace Shanten.Capacity

/-- Forget call details while retaining every tile occupied by a fixed meld. -/
def fixedMeldOfSnapshot : MahjongDomain.FixedMeld → FixedMeld
  | .chi sequence _ => .meld (.shuntsu sequence)
  | .pon tile _ => .meld (.koutsu tile)
  | .daiminkan tile _ => .kan tile
  | .kakan tile _ => .kan tile
  | .ankan tile => .kan tile

/-- Project a shared hand into the existing capacity-aware shanten model.
    The caller must still check the model's validity and hand-size conditions. -/
def ofHandSnapshot (input : MahjongDomain.HandSnapshot) : List FixedMeld × Hand :=
  (input.fixedMelds.map fixedMeldOfSnapshot,
    { counts := input.standing, fixedMelds := input.fixedMelds.length })

end Shanten.Capacity
