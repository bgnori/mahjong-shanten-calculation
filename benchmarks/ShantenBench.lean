import Shanten.Capacity.Examples
import Shanten.Experimental.TileDP

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

def repeatedSequences (lastCount : Nat) : Shanten.Hand :=
  { fixedMelds := 0
    counts := fun tile =>
      match tile with
      | .suited .man rank =>
          if rank.val < 3 then 4 else if rank.val = 3 then lastCount else 0
      | _ => 0 }

def twoFixedSequences (whiteCount : Nat) : Shanten.Hand :=
  { fixedMelds := 2
    counts := fun tile =>
      if tile = white then whiteCount
      else match tile with
      | .suited .pin rank => if rank.val < 3 then 1 else 0
      | .suited .sou rank => if 6 ≤ rank.val then 1 else 0
      | _ => 0 }

def boundaryHand (first : Tile) (second : Tile) (third : Tile) : Shanten.Hand :=
  { fixedMelds := 3
    counts := fun tile =>
      (if tile = first then 1 else 0) + (if tile = second then 1 else 0) +
        (if tile = third then 1 else 0) + (if tile = white then 1 else 0) }

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
  , ⟨"kan-four-13", fixedKan, honors 4 1 0 0⟩
  , ⟨"repeated-sequences-13", [], repeatedSequences 1⟩
  , ⟨"repeated-sequences-14", [], repeatedSequences 2⟩
  , ⟨"two-fixed-sequences-13", fixedTwo, twoFixedSequences 1⟩
  , ⟨"two-fixed-sequences-14", fixedTwo, twoFixedSequences 2⟩
  , ⟨"suit-boundary-13", fixedThree, boundaryHand m8 m9 p1⟩
  , ⟨"pin-sou-boundary-13", fixedThree, boundaryHand p8 p9 s1⟩
  , ⟨"sou-honor-boundary-13", fixedThree, boundaryHand s8 s9 z3⟩
  , ⟨"suit-end-sequence-13", fixedThree, boundaryHand m7 m8 m9⟩ ]

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
  | "suit-dp" =>
      match Shanten.Experimental.SuitDP.minimumSearch c.fixed c.hand with
      | some value => .ok (some value)
      | none => .error s!"suit DP returned no result for valid case: {c.name}"
  | "suit-overall" =>
      match Shanten.Experimental.SuitDP.minimumSearch c.fixed c.hand with
      | some value =>
          .ok (minOption (some value)
            (minOption (sevenPairsSearch c.hand) (thirteenOrphansSearch c.hand)))
      | none => .error s!"suit DP returned no result for valid case: {c.name}"
  | "tile-dp" =>
      match Shanten.Experimental.TileDP.minimumSearch c.fixed c.hand with
      | some value => .ok (some value)
      | none => .error s!"tile DP returned no result for valid case: {c.name}"
  | "tile-overall" =>
      match Shanten.Experimental.TileDP.minimumSearch c.fixed c.hand with
      | some value =>
          .ok (minOption (some value)
            (minOption (sevenPairsSearch c.hand) (thirteenOrphansSearch c.hand)))
      | none => .error s!"tile DP returned no result for valid case: {c.name}"
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
    , ("suit-dp", "blocked-four-13", some 1)
    , ("suit-dp", "ready-four-13", some 0)
    , ("suit-dp", "complete-four-14", some (-1))
    , ("suit-dp", "blocked-four-14", some 1)
    , ("suit-dp", "kan-three-13", some 0)
    , ("suit-dp", "kan-three-14", some (-1))
    , ("suit-dp", "closed-mentsu-complete-14", some (-1))
    , ("suit-dp", "repeated-sequences-13", some 0)
    , ("suit-dp", "repeated-sequences-14", some (-1))
    , ("suit-dp", "two-fixed-sequences-13", some 0)
    , ("suit-dp", "two-fixed-sequences-14", some (-1))
    , ("tile-dp", "suit-boundary-13", some 1)
    , ("tile-dp", "pin-sou-boundary-13", some 1)
    , ("tile-dp", "sou-honor-boundary-13", some 1)
    , ("tile-dp", "suit-end-sequence-13", some 0)
    , ("suit-overall", "closed-seven-ready-13", some 0)
    , ("suit-overall", "closed-orphans-complete-14", some (-1))
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
  for c in cases.filter (fun c => c.fixed.length ≥ 3) do
    let expected := generalMentsuHandMinimumSearch c.fixed c.hand
    let actual := Shanten.Experimental.SuitDP.minimumSearch c.fixed c.hand
    if actual != expected then
      IO.eprintln s!"suit DP disagrees with baseline on {c.name}: expected {repr expected}, got {repr actual}"
      return 1
    let tileResult := Shanten.Experimental.TileDP.minimumSearch c.fixed c.hand
    if tileResult != expected then
      IO.eprintln s!"tile DP disagrees with baseline on {c.name}: expected {repr expected}, got {repr tileResult}"
      return 1
  for c in cases do
    let expected := Shanten.Experimental.SuitDP.minimumSearch c.fixed c.hand
    let actual := Shanten.Experimental.TileDP.minimumSearch c.fixed c.hand
    if actual != expected then
      IO.eprintln s!"tile DP disagrees with suit DP on {c.name}: expected {repr expected}, got {repr actual}"
      return 1
  IO.println "benchmark smoke checks passed"
  return 0

def measure (controlled : Bool) (operation name : String) (iterations : Nat) : IO UInt32 := do
  match cases.find? (fun c => c.name == name) with
  | none =>
      IO.eprintln s!"unknown case: {name}"
      return 1
  | some c =>
      if !validCase c then
        IO.eprintln s!"invalid benchmark case: {name}"
        return 1
      if !["mentsu", "overall", "suit-dp", "suit-overall", "tile-dp", "tile-overall",
          "seven", "orphans"].contains operation then
        IO.eprintln s!"unknown operation: {operation}"
        return 1
      let caseRef ← IO.mkRef c
      if controlled then
        let stdout ← IO.getStdout
        stdout.putStr "SHANTEN_READY\n"
        stdout.flush
        let stdin ← IO.getStdin
        if (← stdin.getLine) != "RUN\n" then
          IO.eprintln "expected RUN after SHANTEN_READY"
          return 1
      let start ← IO.monoNanosNow
      let mut previous : Option (Option Int) := none
      for _ in [:iterations] do
        -- An IO read prevents the pure search from being lifted out of the loop.
        let current ← caseRef.get
        match runSearch operation current with
        | .error message =>
            IO.eprintln message
            return 1
        | .ok result =>
            if let some expected := previous then
              if result != expected then
                IO.eprintln s!"inconsistent result: {operation} {name} returned {repr result}, expected {repr expected}"
                return 1
            previous := some result
      let finish ← IO.monoNanosNow
      match previous with
      | none =>
          IO.eprintln "iterations must be positive"
          return 1
      | some result =>
          let applicable := operation == "mentsu" || operation == "overall" ||
            operation == "suit-dp" || operation == "suit-overall" ||
            operation == "tile-dp" || operation == "tile-overall" || c.fixed.isEmpty
          if result.isSome != applicable then
            IO.eprintln s!"unexpected applicability: {operation} {name} returned {repr result}"
            return 1
          let marker := if controlled then "SHANTEN_RESULT " else ""
          IO.println s!"{marker}operation={operation} case={name} result={repr result} calculation_ns={finish - start} iterations={iterations}"
          if controlled then
            (← IO.getStdout).flush
          return 0

def measureRepeated (controlled : Bool) (operation name count : String) : IO UInt32 := do
  match count.toNat? with
  | some iterations =>
      if iterations > 0 then
        measure controlled operation name iterations
      else
        IO.eprintln "iterations must be a positive integer"
        return 1
  | none =>
      IO.eprintln "iterations must be a positive integer"
      return 1

def run (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
      for c in cases do
        IO.println s!"{c.name}\tfixed={c.fixed.length}\tstanding={tileCount c.hand}\tvalid={validCase c}"
      if cases.all validCase then return 0 else return 1
  | ["check"] => check
  | ["controlled", operation, name, count] => measureRepeated true operation name count
  | ["controlled", operation, name] => measure true operation name 1
  | [operation, name, count] => measureRepeated false operation name count
  | [operation, name] => measure false operation name 1
  | _ =>
      IO.eprintln "usage: lean --run benchmarks/ShantenBench.lean list | check | [controlled] <mentsu|overall|suit-dp|suit-overall|tile-dp|tile-overall|seven|orphans> <case> [iterations]"
      return 1

end ShantenBench

def main (args : List String) : IO UInt32 := ShantenBench.run args
