module

public import Shanten.SevenPairs.Completion
public import Shanten.SevenPairs.Reachability

@[expose] public section

/-!
# Seven-pairs proofs

Stable public import for the seven-pairs model and proofs.
`Basic` defines tenpai and completion targets; `Counting` contains count bounds.
`Completion` proves the final draw; `Exchange` contains one-step strategies;
`Reachability` constructs finite exchange chains and proves their invariants.
Shape-independent exchanges and deficits live in `Shanten.Exchange`.
-/
