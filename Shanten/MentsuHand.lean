import Shanten.MentsuHand.Search.BlockSearch
import Shanten.MentsuHand.Scan.Grouping
import Shanten.MentsuHand.Scan.Completion
import Shanten.MentsuHand.Examples

/-!
# Mentsu-hand shanten proofs

Stable public import for the mentsu-hand model and proofs.
Shared definitions live directly under `Shanten.MentsuHand`.
`Scan` contains the copy-limited tile-order decomposition scan;
`Search` contains target enumeration, shanten correctness, and
the completed-block search with hand-tile consumption.
Regression proofs are collected in `Examples`.
-/
