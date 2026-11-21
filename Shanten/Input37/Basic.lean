import MahjongDomain.Representation
import Shanten.Capacity.Basic

/-!
# Signed aka37 inputs and normalization

Indices 0/10/20 are red fives; 1..9/11..19/21..29 are ordinary
suited tiles; 30..36 are honors. Normalization is linear over integers.
-/

namespace Shanten.Input37

open MahjongDomain

abbrev Counts37 := MahjongDomain.Int37Counts

structure MeldInput where
  kind : String
  tiles : Counts37

structure Input where
  standing : Counts37
  melds : List MeldInput

def normalizeTile (index : Fin 37) : Tile :=
  MahjongDomain.Int37Index.tile index

def capacity (index : Fin 37) : Nat :=
  MahjongDomain.Int37Index.capacity index

def normalIndex : Tile → Fin 37
  | tile => tile.int37Index

lemma normalizeTile_normalIndex : ∀ tile, normalizeTile (normalIndex tile) = tile := by
  intro tile
  exact MahjongDomain.Int37Index.tile_int37Index tile

def normalizeCounts (counts : Counts37) (tile : Tile) : Int :=
  MahjongDomain.aggregateInt37 counts tile

def meldCounts : List MeldInput → Counts37
  | [] => fun _ => 0
  | meld :: rest => fun index => meld.tiles index + meldCounts rest index

def totalCounts (input : Input) : Counts37 :=
  fun index => input.standing index + meldCounts input.melds index

def standingCount (input : Input) : Int :=
  ∑ index, input.standing index

def Nonnegative (counts : Counts37) : Prop :=
  ∀ index, 0 ≤ counts index

instance (counts : Counts37) : Decidable (Nonnegative counts) :=
  Fintype.decidableForallFintype

lemma normalizeCounts_nonneg (h : Nonnegative counts) (tile : Tile) :
    0 ≤ normalizeCounts counts tile := by
  unfold normalizeCounts MahjongDomain.aggregateInt37
  apply Finset.sum_nonneg
  intro index _
  split
  · exact h index
  · omega

lemma normalizeCounts_add (left right : Counts37) (tile : Tile) :
    normalizeCounts (fun index => left index + right index) tile =
      normalizeCounts left tile + normalizeCounts right tile := by
  exact congrFun (MahjongDomain.aggregateInt37_add left right) tile

lemma normalizeCounts_sum (counts : Counts37) :
    (∑ tile : Tile, normalizeCounts counts tile) = ∑ index, counts index := by
  exact MahjongDomain.aggregateInt37_total counts

set_option maxRecDepth 4096 in
lemma capacity_fiber :
    ∀ tile : Tile, normalizeCounts (fun index => (capacity index : Int)) tile = 4 := by
  intro tile
  change MahjongDomain.aggregateInt37
    (fun index => (MahjongDomain.Int37Index.capacity index : Int))
    tile = 4
  exact congrFun MahjongDomain.aggregateInt37_capacity tile

lemma normalizeCounts_le_four
    (hcapacity : ∀ index, counts index ≤ (capacity index : Int)) (tile : Tile) :
    normalizeCounts counts tile ≤ 4 := by
  rw [← capacity_fiber tile]
  unfold normalizeCounts MahjongDomain.aggregateInt37
  apply Finset.sum_le_sum
  intro index _
  split
  · exact hcapacity index
  · omega

def kindMatches (kind : String) : Capacity.FixedMeld → Bool
  | .meld (.shuntsu _) => kind == "chi"
  | .meld (.koutsu _) => kind == "pon"
  | .kan _ => kind == "ankan" || kind == "daiminkan" || kind == "kakan"

def MatchesMeld (raw : MeldInput) (target : Capacity.FixedMeld) : Prop :=
  kindMatches raw.kind target = true ∧
    ∀ tile, normalizeCounts raw.tiles tile = (target.tiles.count tile : Int)

instance (raw : MeldInput) (target : Capacity.FixedMeld) :
    Decidable (MatchesMeld raw target) :=
  @instDecidableAnd _ _ inferInstance Fintype.decidableForallFintype

def Valid (input : Input) : Prop :=
  Nonnegative input.standing ∧
    (∀ index : Fin input.melds.length, Nonnegative input.melds[index].tiles) ∧
    (∀ index, totalCounts input index ≤ (capacity index : Int)) ∧
    input.melds.length ≤ 4 ∧
    (standingCount input + 3 * (input.melds.length : Int) = 13 ∨
      standingCount input + 3 * (input.melds.length : Int) = 14) ∧
    ∀ index : Fin input.melds.length, ∃ target, MatchesMeld input.melds[index] target

end Shanten.Input37
