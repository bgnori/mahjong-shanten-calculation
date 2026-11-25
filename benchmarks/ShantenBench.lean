import Shanten.Capacity.Examples

open MahjongDomain Shanten Shanten.Capacity
open Shanten.Capacity.Examples

namespace ShantenBench

structure Case where
  name : String
  fixed : List FixedMeld
  hand : Shanten.Hand

def north : Tile := .honor 3
def green : Tile := .honor 5
def red : Tile := .honor 6

def fixedTwo : List FixedMeld := [.kan east, .meld (.koutsu south)]
def fixedThree : List FixedMeld :=
  fixedTwo ++ [.meld (.shuntsu ⟨.man, 0⟩)]

def honors (fixedCount whiteCount greenCount redCount : Nat) : Shanten.Hand :=
  { fixedMelds := fixedCount
    counts := fun tile =>
      if tile = white then whiteCount
      else if tile = green then greenCount
      else if tile = red then redCount
      else 0 }

def cases : List Case :=
  [ ⟨"closed-seven-ready-13", [], sevenPairsReady⟩
  , ⟨"closed-seven-quads-13", [], sevenPairsQuads⟩
  , ⟨"closed-seven-complete-14", [], drawHand sevenPairsReady red⟩
  , ⟨"closed-orphans-ready-13", [], kokushiReady⟩
  , ⟨"closed-orphans-far-13", [], kokushiWorstCase⟩
  , ⟨"closed-orphans-complete-14", [], drawHand kokushiReady east⟩
  , ⟨"closed-mentsu-complete-14", [], overallMentsuComplete⟩
  , ⟨"kan-one-13", [.kan east], standingHandWithOneFixedKan⟩
  , ⟨"kan-one-14", [.kan east], drawHand standingHandWithOneFixedKan north⟩
  , ⟨"kan-two-13", fixedTwo, honors 2 3 3 1⟩
  , ⟨"kan-two-14", fixedTwo, honors 2 3 3 2⟩
  , ⟨"kan-three-13", fixedThree, honors 3 3 0 1⟩
  , ⟨"kan-three-14", fixedThree, honors 3 3 0 2⟩
  , ⟨"blocked-four-13", fixedA, standing⟩
  , ⟨"ready-four-13", fixedB, standing⟩
  , ⟨"complete-four-14", fixedB, drawHand standing east⟩
  , ⟨"blocked-four-14", blockedFixed, drawHand standing south⟩
  , ⟨"kan-four-13", fixedKan, honors 4 1 0 0⟩ ]

def validCase (c : Case) : Bool := by
  letI : Decidable (IsThirteenTileEquivalentHand c.fixed c.hand ∨
      IsFourteenTileEquivalentHand c.fixed c.hand) := by
    unfold IsThirteenTileEquivalentHand IsFourteenTileEquivalentHand ValidHand TileCounts.Valid
    infer_instance
  exact decide (IsThirteenTileEquivalentHand c.fixed c.hand ∨
    IsFourteenTileEquivalentHand c.fixed c.hand)

def runSearch (operation : String) (c : Case) : Except String (Option Int) :=
  match operation with
  | "mentsu" => .ok (generalMentsuHandMinimumSearch c.fixed c.hand)
  | "overall" => .ok (overallMinimumSearch c.fixed c.hand)
  | "seven" => .ok (sevenPairsSearch c.hand)
  | "orphans" => .ok (thirteenOrphansSearch c.hand)
  | _ => .error s!"unknown operation: {operation}"

def check : IO UInt32 := do
  let checks : List (String × String × Option Int) :=
    [ ("mentsu", "blocked-four-13", some 1)
    , ("mentsu", "ready-four-13", some 0)
    , ("mentsu", "complete-four-14", some (-1))
    , ("mentsu", "blocked-four-14", some 1)
    , ("overall", "blocked-four-13", some 1)
    , ("seven", "closed-seven-ready-13", some 0)
    , ("seven", "closed-seven-quads-13", some 6)
    , ("seven", "closed-seven-complete-14", some (-1))
    , ("orphans", "closed-orphans-far-13", some 13)
    , ("orphans", "closed-orphans-complete-14", some (-1))
    , ("seven", "kan-four-13", none)
    , ("orphans", "kan-four-13", none) ]
  if !cases.all validCase then
    IO.eprintln "invalid benchmark case"
    return 1
  for (operation, name, expected) in checks do
    match cases.find? (fun c => c.name == name) with
    | none =>
        IO.eprintln s!"missing benchmark case: {name}"
        return 1
    | some c =>
        match runSearch operation c with
        | .error message =>
            IO.eprintln message
            return 1
        | .ok result =>
            if result != expected then
              IO.eprintln s!"{operation} {name}: expected {repr expected}, got {repr result}"
              return 1
  IO.println "benchmark smoke checks passed"
  return 0

def run (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
      for c in cases do
        IO.println s!"{c.name}\tfixed={c.fixed.length}\tstanding={tileCount c.hand}\tvalid={validCase c}"
      if cases.all validCase then return 0 else return 1
  | ["check"] => check
  | [operation, name] =>
      match cases.find? (fun c => c.name == name) with
      | none =>
          IO.eprintln s!"unknown case: {name}"
          return 1
      | some c =>
          if !validCase c then
            IO.eprintln s!"invalid benchmark case: {name}"
            return 1
          if !["mentsu", "overall", "seven", "orphans"].contains operation then
            IO.eprintln s!"unknown operation: {operation}"
            return 1
          let start ← IO.monoNanosNow
          match runSearch operation c with
          | .error message =>
              IO.eprintln message
              return 1
          | .ok result =>
              let finish ← IO.monoNanosNow
              let applicable := operation == "mentsu" || operation == "overall" || c.fixed.isEmpty
              if result.isSome != applicable then
                IO.eprintln s!"unexpected applicability: {operation} {name} returned {repr result}"
                return 1
              IO.println s!"operation={operation} case={name} result={repr result} calculation_ns={finish - start}"
              return 0
  | _ =>
      IO.eprintln "usage: lean --run benchmarks/ShantenBench.lean list | check | <mentsu|overall|seven|orphans> <case>"
      return 1

end ShantenBench

def main (args : List String) : IO UInt32 := ShantenBench.run args
