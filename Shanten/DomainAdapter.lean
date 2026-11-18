module

public import Shanten.Core
public import MahjongDomain.Representation

/-!
# Adapter for the shared Mahjong domain

These conversions keep the existing `Shanten` types as the public interface
while proving their tile and count representations correspond to the core.
-/

@[expose] public section

namespace Shanten.DomainAdapter

def toDomainSuit : Shanten.Suit → MahjongDomain.Suit
  | .man => .man
  | .pin => .pin
  | .sou => .sou

def ofDomainSuit : MahjongDomain.Suit → Shanten.Suit
  | .man => .man
  | .pin => .pin
  | .sou => .sou

theorem ofDomainSuit_toDomainSuit (suit : Shanten.Suit) :
    ofDomainSuit (toDomainSuit suit) = suit := by
  cases suit <;> rfl

theorem toDomainSuit_ofDomainSuit (suit : MahjongDomain.Suit) :
    toDomainSuit (ofDomainSuit suit) = suit := by
  cases suit <;> rfl

def toDomainTile : Shanten.Tile → MahjongDomain.Tile
  | .suited suit rank => .suited (toDomainSuit suit) rank
  | .honor rank => .honor rank

def ofDomainTile : MahjongDomain.Tile → Shanten.Tile
  | .suited suit rank => .suited (ofDomainSuit suit) rank
  | .honor rank => .honor rank

theorem ofDomainTile_toDomainTile (tile : Shanten.Tile) :
    ofDomainTile (toDomainTile tile) = tile := by
  cases tile with
  | suited suit rank => cases suit <;> rfl
  | honor rank => rfl

theorem toDomainTile_ofDomainTile (tile : MahjongDomain.Tile) :
    toDomainTile (ofDomainTile tile) = tile := by
  cases tile with
  | suited suit rank => cases suit <;> rfl
  | honor rank => rfl

def toDomainCounts (counts : Shanten.TileCounts) : MahjongDomain.TileCounts :=
  fun tile => counts (ofDomainTile tile)

def ofDomainCounts (counts : MahjongDomain.TileCounts) : Shanten.TileCounts :=
  fun tile => counts (toDomainTile tile)

theorem ofDomainCounts_toDomainCounts (counts : Shanten.TileCounts) :
    ofDomainCounts (toDomainCounts counts) = counts := by
  funext tile
  simp [ofDomainCounts, toDomainCounts, ofDomainTile_toDomainTile]

theorem toDomainCounts_ofDomainCounts (counts : MahjongDomain.TileCounts) :
    toDomainCounts (ofDomainCounts counts) = counts := by
  funext tile
  simp [toDomainCounts, ofDomainCounts, toDomainTile_ofDomainTile]

theorem toDomainTile_injective : Function.Injective toDomainTile := by
  intro left right h
  calc
    left = ofDomainTile (toDomainTile left) := (ofDomainTile_toDomainTile left).symm
    _ = ofDomainTile (toDomainTile right) := congrArg ofDomainTile h
    _ = right := ofDomainTile_toDomainTile right

end Shanten.DomainAdapter
