module

public import Shanten.Experimental.SuitDP

@[expose] public section

/-!
# Experimental bounded suit search

This implementation assumes validated input and has no equivalence proof.
-/

namespace Shanten.Experimental.PrunedSuitDP

open MahjongDomain Shanten.Capacity Shanten.Experimental.SuitDP

def localCosts (hand : Hand) (occupied : Multiset Tile)
    (tiles : List Tile) (sequences : Bool) (maxMelds budget : Nat) :
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
      | none => panic! "active bounded suit state has no cost"
      | some cost =>
          let carried := key.previous + key.older + fixed
          if carried ≤ copiesPerTile then
            let available := copiesPerTile - carried
            let startsMax := if sequences && position + 2 < tiles.length then
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
                  if newCost ≤ budget then
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

def boundedCombine (left right : Array (Option Nat))
    (maxMelds budget remainingHeld : Nat) : Array (Option Nat) := Id.run do
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
                  let melds := leftMelds + rightMelds
                  let pair := leftPair + rightPair
                  let cost := leftCost + rightCost
                  let required := 3 * (maxMelds - melds) + 2 * (1 - pair)
                  -- Even if all remaining held tiles are useful, the rest must be drawn.
                  if cost + (required - remainingHeld) ≤ budget then
                    result := minInsert result (melds * 2 + pair) cost
  return result

def searchWithin (hand : Hand) (occupied : Multiset Tile)
    (regions : List (List Tile × Bool)) (maxMelds budget : Nat) : Option Nat := Id.run do
  let mut remainingHeld := regions.foldl
    (fun total (tiles, _) => total + tiles.foldl (fun n tile => n + hand.counts tile) 0) 0
  let mut total : Array (Option Nat) := Array.replicate 10 none
  total := total.set! 0 (some 0)
  for (tiles, sequences) in regions do
    remainingHeld := remainingHeld - tiles.foldl (fun n tile => n + hand.counts tile) 0
    total := boundedCombine total
      (localCosts hand occupied tiles sequences maxMelds budget)
      maxMelds budget remainingHeld
    if total.all Option.isNone then
      return none
  return total[maxMelds * 2 + 1]!

/-- Experimental: requires valid input and has no specification-equivalence proof yet. -/
def minimumSearch (fixed : List FixedMeld) (hand : Hand) : Option Int := Id.run do
  let maxMelds := 4 - hand.fixedMelds
  let occupied := fixedTiles fixed
  let suits := Suit.all.map fun suit =>
    (List.ofFn (fun rank : Rank => Tile.suited suit rank), true)
  let honors := List.ofFn fun rank : Honor => Tile.honor rank
  let regions := suits ++ [(honors, false)]
  -- A completed standing hand has at most 14 tiles, hence at most 14 missing.
  for budget in [:15] do
    if let some missing := searchWithin hand occupied regions maxMelds budget then
      return some ((missing : Int) - 1)
  return none

end Shanten.Experimental.PrunedSuitDP
