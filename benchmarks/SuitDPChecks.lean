import Shanten.Experimental.SuitDP

open MahjongDomain Shanten
open Shanten.Experimental.SuitDP

namespace SuitDPChecks

def numbered : List Tile := [m1, m2, m3, m4]
def honors : List Tile := [z1, z2, z3, z4]

def meldTargets (tiles : List Tile) (sequences : Bool) : List (List Tile) :=
  let triplets := tiles.map fun tile => [tile, tile, tile]
  match tiles, sequences with
  | [a, b, c, d], true => triplets ++ [[a, b, c], [b, c, d]]
  | _, _ => triplets

def targets : Nat → List (List Tile) → List (List Tile)
  | 0, _ => [[]]
  | count + 1, melds =>
      (targets count melds).flatMap fun previous =>
        melds.map fun meld => previous ++ meld

def bruteCost (tiles : List Tile) (held fixed : List Tile)
    (sequences : Bool) (meldCount pairCount : Nat) : Option Nat := Id.run do
  let heads := if pairCount == 0 then [[]] else tiles.map fun tile => [tile, tile]
  let mut minimum : Option Nat := none
  for melds in targets meldCount (meldTargets tiles sequences) do
    for head in heads do
      let completed := melds ++ head
      if tiles.all (fun tile => completed.count tile + fixed.count tile ≤ copiesPerTile) then
        let cost := tiles.foldl
          (fun sum tile => sum + (completed.count tile - held.count tile)) 0
        minimum := some (minimum.elim cost (min cost))
  return minimum

def checkLocal (tiles held fixed : List Tile) (sequences : Bool) : IO Bool := do
  let hand : Shanten.Hand :=
    { fixedMelds := 0, counts := fun tile => held.count tile }
  let actual := localCosts hand (Multiset.ofList fixed) tiles sequences 4
  for melds in [:5] do
    for pair in [:2] do
      let expected := bruteCost tiles held fixed sequences melds pair
      let got := actual[melds * 2 + pair]!
      if expected != got then
        IO.eprintln s!"local DP mismatch: melds={melds} pair={pair}, expected {repr expected}, got {repr got}"
        return false
  return true

def main : IO UInt32 := do
  let cases : List (List Tile × List Tile × List Tile × Bool) :=
    [ (numbered, [m1, m1, m1, m1, m2, m2, m2, m2, m3, m3, m3, m3, m4], [], true)
    , (numbered, [m1, m2, m4], [m1, m1, m1], true)
    , (numbered, [m2, m2, m3], [m1, m1, m1, m1, m4, m4], true)
    , (numbered, [], [], true)
    , (honors, [z1, z1, z2, z3], [], false)
    , (honors, [z2, z3], [z1, z1, z1, z1, z3, z3], false) ]
  for (tiles, held, fixed, sequences) in cases do
    if !(← checkLocal tiles held fixed sequences) then
      return 1
  IO.println "suit DP local exhaustive checks passed"
  return 0

end SuitDPChecks

def main : IO UInt32 := SuitDPChecks.main
