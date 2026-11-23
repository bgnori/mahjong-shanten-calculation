module

public import MahjongDomain.Representation
public import Shanten.Capacity.Basic

@[expose] public section

/-!
# Signed aka37 inputs and normalization

Indices 0/10/20 are red fives; 1..9/11..19/21..29 are ordinary
suited tiles; 30..36 are honors. Normalization is linear over integers.
-/

namespace Shanten.Input37

open MahjongDomain

structure MeldInput where
  kind : String
  tiles : Int37Counts

structure Input where
  standing : Int37Counts
  melds : List MeldInput

def meldCounts : List MeldInput → Int37Counts
  | [] => fun _ => 0
  | meld :: rest => fun index => meld.tiles index + meldCounts rest index

def totalCounts (input : Input) : Int37Counts :=
  fun index => input.standing index + meldCounts input.melds index

def standingCount (input : Input) : Int :=
  ∑ index, input.standing index

def Nonnegative (counts : Int37Counts) : Prop :=
  ∀ index, 0 ≤ counts index

instance (counts : Int37Counts) : Decidable (Nonnegative counts) :=
  Fintype.decidableForallFintype

lemma aggregateInt37_nonneg (h : Nonnegative counts) (tile : Tile) :
    0 ≤ aggregateInt37 counts tile := by
  unfold aggregateInt37
  apply Finset.sum_nonneg
  intro index _
  split
  · exact h index
  · omega

def kindMatches (kind : String) : Capacity.FixedMeld → Bool
  | .meld (.shuntsu _) => kind == "chi"
  | .meld (.koutsu _) => kind == "pon"
  | .kan _ => kind == "ankan" || kind == "daiminkan" || kind == "kakan"

def MatchesMeld (raw : MeldInput) (target : Capacity.FixedMeld) : Prop :=
  kindMatches raw.kind target = true ∧
    ∀ tile, aggregateInt37 raw.tiles tile = (target.tiles.count tile : Int)

instance (raw : MeldInput) (target : Capacity.FixedMeld) :
    Decidable (MatchesMeld raw target) :=
  @instDecidableAnd _ _ inferInstance Fintype.decidableForallFintype

def Valid (input : Input) : Prop :=
  Nonnegative input.standing ∧
    (∀ index : Fin input.melds.length, Nonnegative input.melds[index].tiles) ∧
    (∀ index, totalCounts input index ≤ (index.capacity : Int)) ∧
    input.melds.length ≤ 4 ∧
    (standingCount input + 3 * (input.melds.length : Int) = 13 ∨
      standingCount input + 3 * (input.melds.length : Int) = 14) ∧
    ∀ index : Fin input.melds.length, ∃ target, MatchesMeld input.melds[index] target

end Shanten.Input37
