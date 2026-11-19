module

public import Shanten.Core
public import MahjongDomain.Representation
public import MahjongDomain.Parts

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

def toDomainPair (tile : Shanten.Tile) : MahjongDomain.Pair :=
  ⟨toDomainTile tile⟩

def ofDomainPair (pair : MahjongDomain.Pair) : Shanten.Tile :=
  ofDomainTile pair.tile

@[simp] theorem toDomainPair_ofDomainPair (pair : MahjongDomain.Pair) :
    toDomainPair (ofDomainPair pair) = pair := by
  cases pair with
  | mk tile => simp [toDomainPair, ofDomainPair, toDomainTile_ofDomainTile]

def toDomainMeld : Shanten.Meld → MahjongDomain.Meld
  | .triplet tile => .triplet (toDomainTile tile)
  | .sequence suit start => .sequence (toDomainSuit suit) start

def ofDomainMeld : MahjongDomain.Meld → Shanten.Meld
  | .triplet tile => .triplet (ofDomainTile tile)
  | .sequence suit start => .sequence (ofDomainSuit suit) start

def toDomainMelds (melds : List Shanten.Meld) : List MahjongDomain.Meld :=
  melds.map toDomainMeld

def ofDomainMelds (melds : List MahjongDomain.Meld) : List Shanten.Meld :=
  melds.map ofDomainMeld

def toDomainTiles (tiles : Multiset Shanten.Tile) : Multiset MahjongDomain.Tile :=
  tiles.map toDomainTile

theorem toDomainMeld_ofDomainMeld (meld : MahjongDomain.Meld) :
    toDomainMeld (ofDomainMeld meld) = meld := by
  cases meld with
  | triplet tile =>
      simp [toDomainMeld, ofDomainMeld, toDomainTile_ofDomainTile]
  | sequence suit start =>
      cases suit <;> rfl

theorem ofDomainMeld_toDomainMeld (meld : Shanten.Meld) :
    ofDomainMeld (toDomainMeld meld) = meld := by
  cases meld with
  | triplet tile =>
      simp [toDomainMeld, ofDomainMeld, ofDomainTile_toDomainTile]
  | sequence suit start =>
      cases suit <;> rfl

@[simp] theorem toDomainMelds_ofDomainMelds (melds : List MahjongDomain.Meld) :
    toDomainMelds (ofDomainMelds melds) = melds := by
  simp [toDomainMelds, ofDomainMelds, List.map_map, Function.comp_def,
    toDomainMeld_ofDomainMeld]

@[simp] theorem ofDomainMelds_toDomainMelds (melds : List Shanten.Meld) :
    ofDomainMelds (toDomainMelds melds) = melds := by
  simp [toDomainMelds, ofDomainMelds, List.map_map, Function.comp_def,
    ofDomainMeld_toDomainMeld]

@[simp] theorem ofDomainTile_eq_iff (tile : MahjongDomain.Tile) (other : Shanten.Tile) :
    ofDomainTile tile = other ↔ tile = toDomainTile other := by
  constructor
  · intro h
    calc
      tile = toDomainTile (ofDomainTile tile) :=
        (toDomainTile_ofDomainTile tile).symm
      _ = toDomainTile other := congrArg toDomainTile h
  · intro h
    calc
      ofDomainTile tile = ofDomainTile (toDomainTile other) := congrArg ofDomainTile h
      _ = other := ofDomainTile_toDomainTile other

theorem toDomainTiles_count (tiles : Multiset Shanten.Tile) (tile : MahjongDomain.Tile) :
    (toDomainTiles tiles).count tile = tiles.count (ofDomainTile tile) := by
  calc
    (toDomainTiles tiles).count tile =
        (toDomainTiles tiles).count (toDomainTile (ofDomainTile tile)) := by
      rw [toDomainTile_ofDomainTile]
    _ = tiles.count (ofDomainTile tile) := by
      exact Multiset.count_map_eq_count' toDomainTile tiles
        toDomainTile_injective (ofDomainTile tile)

theorem toDomain_pairTiles_map (pair : Shanten.Tile) :
    toDomainTiles (pairTiles pair) = (toDomainPair pair).tiles := by
  simp [toDomainTiles, pairTiles, toDomainPair, MahjongDomain.Pair.tiles]

theorem toDomain_meldTiles_map (meld : Shanten.Meld) :
    toDomainTiles (meldTiles meld) = (toDomainMeld meld).tiles := by
  cases meld <;>
    simp [toDomainTiles, meldTiles, toDomainMeld, toDomainTile, toDomainSuit,
      MahjongDomain.Meld.tiles]

theorem toDomain_meldsTiles_map (melds : List Shanten.Meld) :
    toDomainTiles (meldsTiles melds) = MahjongDomain.MeldList.tiles (toDomainMelds melds) := by
  induction melds with
  | nil =>
      simp [toDomainTiles, meldsTiles, toDomainMelds, MahjongDomain.MeldList.tiles]
  | cons meld melds ih =>
      calc
        toDomainTiles (meldTiles meld + meldsTiles melds) =
            toDomainTiles (meldTiles meld) + toDomainTiles (meldsTiles melds) := by
          change Multiset.map toDomainTile (meldTiles meld + meldsTiles melds) = _
          exact Multiset.map_add toDomainTile _ _
        _ = (toDomainMeld meld).tiles +
              MahjongDomain.MeldList.tiles (toDomainMelds melds) := by
          rw [toDomain_meldTiles_map, ih]

theorem toDomain_pairTiles_count (pair : Shanten.Tile) (tile : MahjongDomain.Tile) :
    (pairTiles pair).count (ofDomainTile tile) =
      (toDomainPair pair).tiles.count tile := by
  calc
    (pairTiles pair).count (ofDomainTile tile) =
        (toDomainTiles (pairTiles pair)).count tile :=
      (toDomainTiles_count (pairTiles pair) tile).symm
    _ = (toDomainPair pair).tiles.count tile := by rw [toDomain_pairTiles_map]

theorem toDomain_meldTiles_count (meld : Shanten.Meld) (tile : MahjongDomain.Tile) :
    (meldTiles meld).count (ofDomainTile tile) =
      (toDomainMeld meld).tiles.count tile := by
  calc
    (meldTiles meld).count (ofDomainTile tile) =
        (toDomainTiles (meldTiles meld)).count tile :=
      (toDomainTiles_count (meldTiles meld) tile).symm
    _ = (toDomainMeld meld).tiles.count tile := by rw [toDomain_meldTiles_map]

theorem toDomain_meldsTiles_count
    (melds : List Shanten.Meld) (tile : MahjongDomain.Tile) :
    (meldsTiles melds).count (ofDomainTile tile) =
      MahjongDomain.MeldList.counts (toDomainMelds melds) tile := by
  calc
    (meldsTiles melds).count (ofDomainTile tile) =
        (toDomainTiles (meldsTiles melds)).count tile :=
      (toDomainTiles_count (meldsTiles melds) tile).symm
    _ = MahjongDomain.MeldList.counts (toDomainMelds melds) tile := by
      rw [toDomain_meldsTiles_map]
      rfl

theorem toDomain_pairMeldCounts (pair : Shanten.Tile) (melds : List Shanten.Meld) :
    toDomainCounts (fun tile => (pairTiles pair + meldsTiles melds).count tile) =
      fun tile =>
        (toDomainPair pair).tiles.count tile +
          MahjongDomain.MeldList.counts (toDomainMelds melds) tile := by
  funext tile
  change (pairTiles pair + meldsTiles melds).count (ofDomainTile tile) = _
  rw [Multiset.count_add, toDomain_pairTiles_count, toDomain_meldsTiles_count]

theorem standardCompletion_iff_shantenParts
    (counts : Shanten.TileCounts) (fixedMelds : Nat) :
    fixedMelds ≤ 4 →
      (MahjongDomain.StandardCompletion (4 - fixedMelds) (toDomainCounts counts) ↔
      ∃ pair : Shanten.Tile, ∃ melds : List Shanten.Meld,
        melds.length + fixedMelds = 4 ∧
          ∀ tile, counts tile = (pairTiles pair + meldsTiles melds).count tile) := by
  intro hfixed
  constructor
  · intro hcompletion
    obtain ⟨pair, melds, hlength, hcounts⟩ :=
      (MahjongDomain.standardCompletion_iff_parts _ _).mp hcompletion
    let localPair := ofDomainPair pair
    let localMelds := ofDomainMelds melds
    refine ⟨localPair, localMelds, ?_, ?_⟩
    · simp [localMelds, ofDomainMelds]
      omega
    · intro tile
      have hshared := congrFun hcounts (toDomainTile tile)
      have hconvert := congrFun (toDomain_pairMeldCounts localPair localMelds)
        (toDomainTile tile)
      have hpair : toDomainPair localPair = pair := by
        simp [localPair]
      have hmelds : toDomainMelds localMelds = melds := by
        simp [localMelds]
      rw [hpair, hmelds] at hconvert
      have hconvert' :
          (pairTiles localPair + meldsTiles localMelds).count tile =
            counts tile := by
        simpa [toDomainCounts, ofDomainTile_toDomainTile] using hconvert.trans hshared
      exact hconvert'.symm
  · rintro ⟨pair, melds, hlength, hparts⟩
    apply (MahjongDomain.standardCompletion_iff_parts _ _).mpr
    refine ⟨toDomainPair pair, toDomainMelds melds, ?_, ?_⟩
    · have hlen : (toDomainMelds melds).length = melds.length := by
        simp [toDomainMelds]
      omega
    · funext tile
      have hlocal := hparts (ofDomainTile tile)
      have hconvert := congrFun (toDomain_pairMeldCounts pair melds) tile
      have hcounts :
          (toDomainPair pair).tiles.count tile +
              MahjongDomain.MeldList.counts (toDomainMelds melds) tile =
            toDomainCounts counts tile := by
        simpa [toDomainCounts] using hconvert.symm.trans hlocal.symm
      exact hcounts

end Shanten.DomainAdapter
