module

public import Shanten.Capacity.Basic

@[expose] public section

/-!
# Experimental suit-by-suit mentsu calculation

This implementation assumes a separately validated 13- or 14-tile-equivalent
input. Its equivalence to the capacity-aware specification is not yet proved.
-/

namespace Shanten.Experimental.SuitDP

open MahjongDomain Shanten.Capacity

def stateIndex (melds pair previous older : Nat) : Nat :=
  ((melds * 2 + pair) * 5 + previous) * 5 + older

structure StateKey where
  melds : Nat
  pair : Nat
  previous : Nat
  older : Nat

def minInsert (table : Array (Option Nat)) (index value : Nat) :
    Array (Option Nat) :=
  match table[index]! with
  | none => table.set! index (some value)
  | some old => table.set! index (some (min old value))

def scanCosts (hand : Hand) (occupied : Multiset Tile)
    (tiles : List Tile) (canStart : Nat → Tile → Bool) (maxMelds : Nat) :
    Array (Option Nat) := Id.run do
  let mut states : Array (Option Nat) := Array.replicate 250 none
  states := states.set! (stateIndex 0 0 0 0) (some 0)
  let mut active : List StateKey := [⟨0, 0, 0, 0⟩]
  let mut position := 0
  for tile in tiles do
    let mut next : Array (Option Nat) := Array.replicate 250 none
    let mut nextActive : List StateKey := []
    let held := hand.counts tile
    let fixed := occupied.count tile
    for key in active do
      match states[stateIndex key.melds key.pair key.previous key.older]! with
      | none => panic! "active suit DP state has no cost"
      | some cost =>
          let carried := key.previous + key.older + fixed
          if carried ≤ copiesPerTile then
            let available := copiesPerTile - carried
            let startsMax := if canStart position tile then
              min available (maxMelds - key.melds) else 0
            for starts in [:startsMax + 1] do
              let triplets := if available - starts ≥ 3 && key.melds + starts < maxMelds
                then 2 else 1
              for triplet in [:triplets] do
                let used := starts + 3 * triplet
                let heads := if key.pair == 0 && available - used ≥ 2 then 2 else 1
                for head in [:heads] do
                  let target := starts + key.previous + key.older + 3 * triplet + 2 * head
                  let newCost := cost + (target - held)
                  let newKey : StateKey :=
                    ⟨key.melds + starts + triplet, key.pair + head, starts, key.previous⟩
                  let index := stateIndex newKey.melds newKey.pair newKey.previous newKey.older
                  if next[index]!.isNone then
                    nextActive := newKey :: nextActive
                  next := minInsert next index newCost
    states := next
    active := nextActive
    position := position + 1
  let mut result : Array (Option Nat) := Array.replicate 10 none
  for melds in [:maxMelds + 1] do
    for pair in [:2] do
      result := result.set! (melds * 2 + pair) states[stateIndex melds pair 0 0]!
  return result

def localCosts (hand : Hand) (occupied : Multiset Tile)
    (tiles : List Tile) (sequences : Bool) (maxMelds : Nat) :
    Array (Option Nat) :=
  scanCosts hand occupied tiles
    (fun position _ => sequences && position + 2 < tiles.length) maxMelds

def combine (left right : Array (Option Nat)) (maxMelds : Nat) :
    Array (Option Nat) := Id.run do
  let mut result : Array (Option Nat) := Array.replicate 10 none
  for leftMelds in [:maxMelds + 1] do
    for leftPair in [:2] do
      match left[leftMelds * 2 + leftPair]! with
      | none => pure ()
      | some leftCost =>
          for rightMelds in [:maxMelds + 1 - leftMelds] do
            for rightPair in [:2 - leftPair] do
              match right[rightMelds * 2 + rightPair]! with
              | none => pure ()
              | some rightCost =>
                  result := minInsert result
                    ((leftMelds + rightMelds) * 2 + leftPair + rightPair)
                    (leftCost + rightCost)
  return result

/-- Experimental: requires valid input and has no specification-equivalence proof yet. -/
def minimumSearch (fixed : List FixedMeld) (hand : Hand) : Option Int := Id.run do
  let maxMelds := 4 - hand.fixedMelds
  let occupied := fixedTiles fixed
  let mut total : Array (Option Nat) := Array.replicate 10 none
  total := total.set! 0 (some 0)
  for suit in Suit.all do
    let tiles := List.ofFn fun rank : Rank => Tile.suited suit rank
    total := combine total (localCosts hand occupied tiles true maxMelds) maxMelds
  let honors := List.ofFn fun rank : Honor => Tile.honor rank
  total := combine total (localCosts hand occupied honors false maxMelds) maxMelds
  return (total[maxMelds * 2 + 1]!).map fun missing => (missing : Int) - 1

end Shanten.Experimental.SuitDP
