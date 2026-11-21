import Shanten.Specification

/-!
# Basic

Taatsu, search states, choices, and local block completion.
-/

namespace Shanten

open MahjongDomain

inductive Taatsu
  | pair (tile : Tile)
  | sequence (suit : Suit) (start : Fin 8)
  deriving DecidableEq, Fintype

/-- The counters carried by the mentsu-hand dynamic program. -/
structure MentsuHandSearchState where
  tileIndex : Nat
  used : Multiset Tile
  pair : Option Tile
  meldHistory : List MentsuCandidate
  taatsuHistory : List Taatsu
  melds : Nat
  taatsu : Nat
  deriving DecidableEq

/-- One branch of the mentsu-hand decomposition search. -/
inductive MentsuHandChoice
  | skip
  | pair (tile : Tile)
  | taatsu (taatsu : Taatsu)
  | meld (meld : MentsuCandidate)
  deriving DecidableEq

def taatsuTiles : Taatsu → Multiset Tile
  | .pair tile => pairTiles tile
  | .sequence suit start =>
      Multiset.ofList
        [ Tile.suited suit ⟨start.val, by omega⟩
        , Tile.suited suit ⟨start.val + 1, by omega⟩ ]

def taatsuCompletionTile : Taatsu → Tile
  | .pair tile => tile
  | .sequence suit start =>
      if hstart : start.val ≤ 6 then
        Tile.suited suit ⟨start.val + 2, by omega⟩
      else
        Tile.suited suit ⟨start.val - 1, by omega⟩

def taatsuCompletionMeld : Taatsu → MentsuCandidate
  | .pair tile => .koutsu tile
  | .sequence suit start =>
      .shuntsu ⟨suit,
        ⟨if hstart : start.val ≤ 6 then start.val else start.val - 1, by
          by_cases h : start.val ≤ 6 <;> simp [h] <;> omega⟩⟩

lemma taatsuTiles_add_completionTile
    (taatsu : Taatsu) :
    taatsuTiles taatsu + Multiset.replicate 1 (taatsuCompletionTile taatsu) =
      meldTiles (taatsuCompletionMeld taatsu) := by
  cases taatsu with
  | pair tile =>
      simp [taatsuTiles, taatsuCompletionTile, taatsuCompletionMeld,
        pairTiles, Pair.tiles, meldTiles, MentsuCandidate.tiles, Multiset.replicate_succ]
  | sequence suit start =>
      by_cases hstart : start.val ≤ 6
      · simp only [taatsuTiles, taatsuCompletionTile, taatsuCompletionMeld,
          meldTiles, MentsuCandidate.tiles, Shuntsu.tiles, dif_pos hstart]
        change Multiset.ofList
            [ Tile.suited suit ⟨start.val, by omega⟩
            , Tile.suited suit ⟨start.val + 1, by omega⟩ ] +
            Multiset.ofList [Tile.suited suit ⟨start.val + 2, by omega⟩] =
          Multiset.ofList
            [ Tile.suited suit ⟨start.val, by omega⟩
            , Tile.suited suit ⟨start.val + 1, by omega⟩
            , Tile.suited suit ⟨start.val + 2, by omega⟩ ]
        rw [Multiset.coe_add]
        rfl
      · have hstart' : start.val = 7 := by omega
        simp only [taatsuTiles, taatsuCompletionTile, taatsuCompletionMeld,
          meldTiles, MentsuCandidate.tiles, Shuntsu.tiles, dif_neg hstart, hstart', dif_neg (by omega)]
        change Multiset.ofList
            [ Tile.suited suit ⟨7, by omega⟩
            , Tile.suited suit ⟨8, by omega⟩ ] +
            Multiset.ofList [Tile.suited suit ⟨6, by omega⟩] =
          Multiset.ofList
            [ Tile.suited suit ⟨6, by omega⟩
            , Tile.suited suit ⟨7, by omega⟩
            , Tile.suited suit ⟨8, by omega⟩ ]
        rw [Multiset.coe_add]
        apply Multiset.coe_eq_coe.mpr
        exact
          (List.Perm.cons _ (List.Perm.swap _ _ [])).trans
            (List.Perm.swap _ _ _).symm

def choiceTiles : MentsuHandChoice → Multiset Tile
  | .skip => 0
  | .pair tile => pairTiles tile
  | .taatsu taatsu => taatsuTiles taatsu
  | .meld meld => meldTiles meld

end Shanten
