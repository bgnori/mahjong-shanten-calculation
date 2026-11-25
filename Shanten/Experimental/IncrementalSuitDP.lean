module

public import Shanten.Experimental.PrunedSuitDP

@[expose] public section

/-!
# Experimental incremental bounded suit search

The input must be validated separately. Specification equivalence and the
correctness of the retained frontier have not yet been proved.
-/

namespace Shanten.Experimental.IncrementalSuitDP

open MahjongDomain Shanten.Capacity Shanten.Experimental.SuitDP

-- A standing completion contains at most 14 tiles, so its deficit is at most 14.
def maxCost : Nat := 14

structure Region where
  held : Array Nat
  occupied : Array Nat
  sequences : Bool
  distances : Array Nat
  pending : Array (List (Nat × StateKey))
  nextCost : Nat
  deriving Inhabited

def initRegion (hand : Hand) (occupied : Multiset Tile)
    (tiles : List Tile) (sequences : Bool) : Region :=
  let held := (tiles.map hand.counts).toArray
  let fixed := (tiles.map occupied.count).toArray
  let distances := (Array.replicate ((tiles.length + 1) * 250) (maxCost + 1))
    |>.set! (stateIndex 0 0 0 0) 0
  let pending := (Array.replicate (maxCost + 1) [])
    |>.set! 0 [(0, ⟨0, 0, 0, 0⟩)]
  ⟨held, fixed, sequences, distances, pending, 0⟩

/-- Resume with the same `maxMelds`; costs through `budget` are settled in order. -/
def advance (region : Region) (maxMelds budget : Nat) : Region := Id.run do
  let mut distances := region.distances
  let mut pending := region.pending
  let mut cost := region.nextCost
  while cost ≤ budget && cost ≤ maxCost do
    while !(pending[cost]!).isEmpty do
      match pending[cost]! with
      | [] => pure ()
      | (position, key) :: rest =>
          pending := pending.set! cost rest
          let index := position * 250 +
            stateIndex key.melds key.pair key.previous key.older
          -- A later improvement makes an older queued entry stale.
          if distances[index]! == cost && position < region.held.size then
            let held := region.held[position]!
            let fixed := region.occupied[position]!
            let carried := key.previous + key.older + fixed
            if carried ≤ copiesPerTile then
              let available := copiesPerTile - carried
              let startsMax := if region.sequences && position + 2 < region.held.size then
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
                    if newCost ≤ maxCost then
                      let newKey : StateKey :=
                        ⟨key.melds + starts + triplet, key.pair + head, starts, key.previous⟩
                      let nextIndex := (position + 1) * 250 +
                        stateIndex newKey.melds newKey.pair newKey.previous newKey.older
                      if newCost < distances[nextIndex]! then
                        distances := distances.set! nextIndex newCost
                        pending := pending.set! newCost
                          ((position + 1, newKey) :: pending[newCost]!)
    cost := cost + 1
  return { region with distances, pending, nextCost := cost }

/-- Read only after advancing this region through `budget`. -/
def localCosts (region : Region) (maxMelds budget : Nat) : Array (Option Nat) := Id.run do
  let mut result : Array (Option Nat) := Array.replicate 10 none
  for melds in [:maxMelds + 1] do
    for pair in [:2] do
      let index := region.held.size * 250 + stateIndex melds pair 0 0
      let cost := region.distances[index]!
      if cost ≤ budget && cost ≤ maxCost then
        result := result.set! (melds * 2 + pair) (some cost)
  return result

def initRegions (hand : Hand) (occupied : Multiset Tile)
    (regions : List (List Tile × Bool)) : Array Region :=
  (regions.map fun (tiles, sequences) => initRegion hand occupied tiles sequences).toArray

def searchWithin (initial : Array Region) (maxMelds budget : Nat) :
    Array Region × Option Nat := Id.run do
  let mut regions := initial
  let mut remainingHeld := regions.foldl
    (fun total region => total + region.held.foldl (· + ·) 0) 0
  let mut total : Array (Option Nat) := Array.replicate 10 none
  total := total.set! 0 (some 0)
  for i in [:regions.size] do
    if !(total.all Option.isNone) then
      let region := advance regions[i]! maxMelds budget
      remainingHeld := remainingHeld - region.held.foldl (· + ·) 0
      total := PrunedSuitDP.boundedCombine total (localCosts region maxMelds budget)
        maxMelds budget remainingHeld
      regions := regions.set! i region
  return (regions, total[maxMelds * 2 + 1]!)

/-- Experimental: requires valid input and has no specification-equivalence proof yet. -/
def minimumSearch (fixed : List FixedMeld) (hand : Hand) : Option Int := Id.run do
  let maxMelds := 4 - hand.fixedMelds
  let suits := Suit.all.map fun suit =>
    (List.ofFn (fun rank : Rank => Tile.suited suit rank), true)
  let honors := List.ofFn fun rank : Honor => Tile.honor rank
  let mut regions := initRegions hand (fixedTiles fixed) (suits ++ [(honors, false)])
  for budget in [:maxCost + 1] do
    let (updated, result) := searchWithin regions maxMelds budget
    regions := updated
    if let some missing := result then
      return some ((missing : Int) - 1)
  return none

end Shanten.Experimental.IncrementalSuitDP
