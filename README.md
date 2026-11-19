# shanten

Replaceable Go shanten calculator contract, version `aka37-shanten/v2`.
This module contains types, an interface, and error categories only.
There is no calculator, adapter, registry, dynamic loader, or validation algorithm.
It depends only on the Go standard library, not on the parent aka37 module.

User-facing documentation for the contract, domain terminology, and Lean model
is indexed in [docs/](docs/README.md).
The current Lean source layout is documented in
[docs/SHANTEN_LEAN_STRUCTURE.md](docs/SHANTEN_LEAN_STRUCTURE.md).
Terminology shared by the Go contract, Mahjong model, and Lean proofs is documented
in [docs/GLOSSARY.md](docs/GLOSSARY.md).
Project plans, progress records, and reviews are grouped separately in
[docs/project/](docs/project/README.md).

## Input

`Calculator.Calculate(Input) (Result, error)` accepts standing tiles and fixed
melds. Each meld includes its kind and all its tiles, including all four tiles
of a kan. An ankan is a fixed meld even though it preserves menzen status.
Call source, called-tile position, discards, and visible tiles are not inputs.

`Counts37` is a fixed `[37]int`; invalid lengths are unrepresentable.
Its indices and capacities are:

| Indices | Tiles | Capacity per kind |
| --- | --- | --- |
| 0, 10, 20 | Red 5m, 5p, 5s | 1 |
| 1..9 | Normal 1m..9m | 3 for 5m, otherwise 4 |
| 11..19 | Normal 1p..9p | 3 for 5p, otherwise 4 |
| 21..29 | Normal 1s..9s | 3 for 5s, otherwise 4 |
| 30..36 | East, South, West, North, White, Green, Red | 4 |

Counts must be nonnegative and respect these capacities across standing tiles
and all melds combined. The adapter merges red fives into ordinary fives for
calculation; it must not change the source input or shanten meaning.

With `m = len(Melds)`, `0 <= m <= 4`, the standing tile count must be either
`13 - 3*m` or `14 - 3*m`. Each chi is three consecutive ranks in one numbered
suit; each pon is three identical kinds; each kan is four identical kinds,
after merging red fives. Each kan counts as one fixed set. Added kans replace
their original pon, rather than adding another meld. Pre-rinshan transient states
are not separately distinguished; only the supplied tile composition is evaluated.

## Result

Tenpai is `0`, completion is `-1`, and all applicable shanten values are at least
`-1`. `MentsuHand` is always applicable.

`SevenPairs.Applicable` and `ThirteenOrphans.Applicable` are true exactly when
there are no fixed melds. If false, their `Shanten` field must be zero and must
not participate in the minimum. Thus ankan also disables both special shapes.
With no fixed melds, `Shanten` is the minimum of all three shapes; otherwise it
equals `MentsuHand`. Inapplicability is not a backend capability failure.
An implementation unable to evaluate an applicable shape must return an error.

Shanten is structural: do not impose yaku, furiten, visible-tile availability,
or nagashi-mangan conditions.

## Errors and ownership

The calculator or adapter validates counts, meld structure, and hand size before
delegation, and checks backend results against this contract.
Return a zero `Result` with a non-nil error on failure; callers must ignore the
result whenever the error is non-nil. Do not normalize invalid inputs.

Wrap the exported sentinel errors with context using `%w`, preserving
`errors.Is`. Use `ErrInvalidCount` for negative counts or exceeded capacities,
`ErrInvalidHand` for inconsistent hand size or too many melds, `ErrInvalidMeld`
for unknown kinds or invalid meld composition, `ErrUnsupported` for missing
calculator capabilities, `ErrBackend` for execution failures, and
`ErrInvalidResult` for backend output that violates the result contract.
Error text must identify the offending field or backend operation when known.

Results must be deterministic. Do not mutate input or retain its slices for later
use. Callers must not mutate input during a call. Shared-instance concurrency
safety is not promised by v1; future parallel callers must use separate instances
unless the implementation explicitly guarantees concurrent use.

## Integration

The module is intended to be referenced from aka37 at `modules/shanten` as a Git
submodule. Clone/update it with `git submodule update --init --recursive`.
Git submodules pin source commits; they do not add Go `require` or `replace`
directives. Consumers can depend on `github.com/bgnori/shanten` at a chosen
module version. The parent does not import it until an adapter is implemented.
The source repository is public; no private-module Go configuration is required.

The host supplies a `Calculator` instance to its consumers. Backend-specific
types and errors remain behind the adapter. There is no Go `plugin` ABI or
general analysis registry in this contract. Future analysis modules can follow
this pattern with their own typed contracts.

Breaking changes to input meaning, result meaning, or interface signatures
require a new contract version and appropriate Go module versioning.

## Checks

```sh
go test ./...
go vet ./...
```

These compile/check the contract only; numerical conformance tests belong to a
future calculator or adapter implementation.

[GitHub Actions](.github/workflows/checks.yml) runs these Go checks and `lake build`
on every push and pull request, and supports manual runs. The Go job installs the
version from `go.mod`; the Lean job uses `lean-toolchain` and the committed
`lake-manifest.json`, without running `lake update`. A shared-domain regression job
also builds the core and both consumers at their pinned revisions, exercises their
existing public Lean entrypoints, checks both consumer links to the fixed shared
glossary, runs the classification Go contract test, and builds the fixed-context
connection package with transitive `sorryAx` checks.

The default Lean build imports [Shanten/ProofChecks.lean](Shanten/ProofChecks.lean).
Its `assert_no_sorry` checks reject transitive `sorryAx` dependencies in the main
exit theorems, including the shared validity proofs, general search correctness
and totality, batch scans, seven-pairs bounds, and the thirteen-orphans maximum.
It also checks the capacity-model correspondence, the R2 acceptance proofs, and
the general seven-pairs and thirteen-orphans formula correctness.
The overall calculation's correctness, totality, completion, and abstract-model
agreement are checked as well.
The signed 37-kind validator, normalization guarantees, and rejection regressions
are included in the same checks.
Existing `native_decide` dependencies remain permitted; ordinary warnings are
not treated as errors. Add new exit theorems to this check list when extending
the proof surface.

## Development container

Two Dev Container configurations are available; both are limited to 2 CPUs:

- `dev`: Go, Lean 4, and mathlib. Use this configuration for local development
  in this repository.
- `user`: Go only, without the Lean toolchain or mathlib, for a lighter
  environment.

The `dev` configuration is the default when opening this repository in a
Dev Container. To use the lighter `user` configuration instead, select
`.devcontainer/user/devcontainer.json` explicitly in VS Code. Lean 4 and
mathlib in `dev` are both pinned to `v4.35.0`.
The development image installs the version from [`lean-toolchain`](lean-toolchain)
at build time. Rebuild the image when the pin changes; new containers from the
same image do not download Lean again. For a plain Docker build, run
`docker build -f .devcontainer/dev/Dockerfile -t shanten-dev .` from the
repository root.
Only the imported mathlib modules and their transitive dependencies are loaded
and their prebuilt cache is fetched when the container is created. The Lean
proofs use finite sets, multisets, natural numbers, and integers rather than
the full `Mathlib` import (including real analysis). Keep mathlib imports
specific when adding proofs. The `dev` configuration mounts the host's
`~/.cache/mathlib` at
`/home/vscode/.cache/mathlib`, so the downloaded mathlib cache is reused when
the container is rebuilt or recreated. Set `MATHLIB_CACHE_DIR` in
`devcontainer.json` if you use a different host cache location.
Both Lean configurations set `LEAN_NUM_THREADS=2` to match their CPU limit.
They also set `MATHLIB_NO_CACHE_ON_UPDATE=1` to prevent `lake update` from
automatically fetching all of mathlib. After updating dependencies or adding
imports, fetch only the required cache with:

```sh
lake exe cache get $(find Shanten -name '*.lean' -exec sed -n 's/^import \(Mathlib\..*\)$/\1/p' {} + | sort -u)
```

Build the Lean project in `dev` with:

```sh
lake build
```

`Shanten` is the default build target; `lake build Shanten` is equivalent.

### Lean proof layout

[Shanten/Capacity.lean](./Shanten/Capacity.lean) is the staged, capacity-aware
model under `Shanten.Capacity`. Fixed meld contents, including all four kan
tiles, constrain standing counts, completion targets, draws, and exchanges.
Its [acceptance proofs](./Shanten/Capacity/Examples.lean) distinguish the review's
A/B inputs and establish exact shanten values 1 and 0, not just reachable bounds.
For valid hands without fixed melds, its specification agrees with the existing
abstract specification. With fixed melds, abstraction only provides a lower
bound when both values exist.

`Shanten.Capacity.generalMentsuHandMinimumSearch fixed hand` reuses the existing
block-search states, filters completed targets against fixed-tile capacity, and
computes the minimum over the remaining targets. Correctness, totality, and an
optimal-state witness are proved for both `IsThirteenTileEquivalentHand fixed hand`
and `IsFourteenTileEquivalentHand fixed hand`.
The A/B acceptance proofs also compute the search results as `some 1` and `some 0`.
For thirteen-tile-equivalent hands without fixed melds, results agree with the
original abstract search, which remains available as
`Shanten.generalMentsuHandMinimumSearch` for compatibility.

For fourteen-tile-equivalent hands, completion returns `some (-1)`. For a
noncomplete hand, the same search result equals `minimumDiscardSearch`: the
minimum thirteen-tile result over tile kinds actually present in the standing
hand. `optimalDiscards` enumerates all attaining discards; it is nonempty for
valid noncomplete fourteen-tile-equivalent hands. Check completion before using
discard recommendations: discarding from a completed hand loses the `-1` value.
Discards preserve fixed meld contents and capacity validity.

[Shanten/Special.lean](./Shanten/Special.lean) proves that the computable formulas
`sevenPairsShanten` and `kokushiShanten` equal the minimum completion distance
minus one for every valid concealed thirteen- or fourteen-tile hand.
Seven pairs counts a quad as one pair kind and accounts for missing distinct
kinds; thirteen orphans counts pairs only among terminal and honor kinds.
[Shanten/Capacity/Special.lean](./Shanten/Capacity/Special.lean) exposes
`sevenPairsSearch hand` and `thirteenOrphansSearch hand`. They return `some value`
exactly for the corresponding capacity-aware specification on valid
thirteen- or fourteen-tile-equivalent inputs, and `none` exactly when fixed
melds make the shape inapplicable (including ankan).
As with mentsu search, input validation is a separate prerequisite; these are
not validators for arbitrary hands.

[Shanten/Capacity/Overall.lean](./Shanten/Capacity/Overall.lean) exposes
`shapeSearch fixed hand shape` and `overallMinimumSearch fixed hand`.
The latter takes the minimum of the applicable shape results, omitting `none`
rather than treating it as zero. For valid thirteen- or fourteen-tile-equivalent
inputs, it always returns a unique `some value`, exactly characterized by the
calculator-independent `Capacity.IsOverallShanten` attained-minimum predicate.
The result is at least `-1`, and equals `-1` exactly when any shape is complete.
With fixed melds it reduces to mentsu search; without fixed melds it agrees with
the original abstract `OverallShanten` specification.
Input validation remains a separate prerequisite, and the underlying mentsu
enumeration is not optimized. See the [Lean source structure](./docs/SHANTEN_LEAN_STRUCTURE.md).

[Shanten/Input37.lean](./Shanten/Input37.lean) is the Lean-only input layer under
`Shanten.Input37`. `Counts37` is `Fin 37 → Int`, preserving signed values and the
contract's exact index layout. `Input` contains standing counts and a list of
`MeldInput` records with a kind string and all physical tiles.
`validateAndNormalize` returns `Except ValidationError NormalizedInput`.
It rejects negative counts in each source field, combined physical-copy
capacity violations, more than four melds, inconsistent standing size, and
malformed or unknown meld kinds. Errors identify the offending tile or meld
index where applicable. Red/ordinary-five capacities are checked before merging;
a normalized four-copy check alone cannot detect two red fives or four ordinary
fives. Invalid inputs return no normalized result.

Successful validation preserves standing tile count, fixed-set count, and every
fixed tile (all four tiles of a kan), and supplies the existing capacity-aware
thirteen- or fourteen-tile-equivalent calculator prerequisites.
Linear integer normalization preserves total counts; conversion to natural
counts requires nonnegativity. Two accepted inputs with the same normalized
standing counts, meld kinds, and normalized meld contents produce identical
normalized hands and overall values, even if red identity is redistributed.
This is not a Go implementation or a proof of Go integer arithmetic, bindings,
or error wrapping. Go implementation is deferred pending the user's separate
plan; no Go source or development-container settings were changed.

[Shanten/MentsuHand.lean](./Shanten/MentsuHand.lean) is the stable import for
mentsu-hand proofs. Its implementation is split under
[Shanten/MentsuHand/](./Shanten/MentsuHand/): shared models at the top level,
tile-order decomposition scans in `Scan/`, completion searches and their
correctness proofs in `Search/`, and regression proofs in `Examples.lean`.
The former `GeneralMentsuHand.lean` is now
[Search/BlockSearch.lean](./Shanten/MentsuHand/Search/BlockSearch.lean);
public definition and theorem names are unchanged.

[Shanten/SevenPairs.lean](./Shanten/SevenPairs.lean) is the stable import for
seven-pairs proofs. Its implementation is split under
[Shanten/SevenPairs/](./Shanten/SevenPairs/) into basic targets, counting lemmas,
completion, one-step exchange strategies, and reachability.
Shape-independent deficits, exchanges, and fixed-target reachability proofs live in
[Shanten/Exchange.lean](./Shanten/Exchange.lean).
Seven-pairs names now distinguish tenpai targets from completion counts and
pair-preserving discards from other discards; see the
[layout and rename map](./docs/SHANTEN_LEAN_STRUCTURE.md).

[Shanten/ThirteenOrphans.lean](./Shanten/ThirteenOrphans.lean) proves that the
maximum thirteen-orphans shanten number on valid concealed thirteen-tile hands is
exactly 13, using the completion-distance specification. Every such hand has a
finite value at most 13, and `kokushiWorstCase` attains 13.
See the [module map](./docs/SHANTEN_LEAN_STRUCTURE.md)
for responsibilities and a suggested reading order.
