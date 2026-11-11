# Disequality encoding and a proof benchmark

This experiment compares relation-based Egglog NEE, its proof overhead,
and the authors' four native implementations from
[Dis-Equality Graphs](https://doi.org/10.1145/3704913). The [public artifact's](https://zenodo.org/records/23166731) native
input is canonical; the checked-in Egglog program is its deterministic
translation. The figure replicates the final configuration of the artifact's parameter
sweep, rather than the complete sweep or the paper's published timings.

## Relation-based NEE

`(disequal a b)` inserts an ordered pair into a private relation for the operands'
equality sort. Congruence rebuilding canonicalizes the endpoints; a self-edge
derives a contradiction. The paper's NEE uses a private `ne` term; the relation
preserves contradiction detection without making its result a unionable equality
class.

`(separately-injective F)` adds fixed-coordinate cancellation and upward
propagation through existing applications of an already declared constructor.
There is no downward propagation. `(known-disequal a b)` reads positive evidence,
and `(contradiction)` matches an inconsistent constraint. The pass closes its
private supporting rules after user runs and before observations of pending
top-level actions. This parameter-analysis workload declares no separate
injectivity promises, so it exercises assertions and contradiction detection.

`(disequal ...)` also works in rule heads. The encoding lowers to ordinary
egglog before term/proof encoding, without changing union-find.
Existing core restrictions still apply: `begin` blocks are normal-mode only;
the benchmark uses individual top-level actions and needs no batching support.

`--proofs` records proofs; it does not verify them. `--proof-extraction` extracts
and simplifies the proof of the final check. `--proof-testing` additionally
checks that derivation against the lowered program, including the encoding
rules. This is not a separate machine-checked proof that the compiler pass
implements the paper's semantics.

## Workload and regeneration

[parameter-analysis.in](parameter-analysis.in) is the complete, unchanged
400,000-expression corpus published with the four reference drivers. Native commands
use `INPUT.in 100000 10000`: six fixed numeral disequalities, then 100,000 equality
pairs, then 10,000 disequality pairs. The remaining 180,000 expressions are read
but not asserted. The numeral initialization preserves the authors' exclusive
upper bound, which constrains distinct pairs among `1` through `4`, excluding `5`.

[parameter-analysis.egg](parameter-analysis.egg) mirrors these assertions and
their order. Numerals become `N1` through `N5`; functions `f`, `g`, and `h` retain
arities one, two, and three. Its final command is `(check (contradiction))`.
Regenerate it without running any engine or generating new random expressions:

```sh
python benchmarks/disequality/native/generate.py
```

All four unchanged native implementations returned a contradiction in diagnostic
runs on this corpus. That result does not establish Egglog proof validity;
proof testing remains a separate operation. No seed selection or per-pair
filtering is used. See [native provenance](native/README.md) for input/source
hashes, DE reconstruction, and licensing.

## Comparisons

The runner records the actual physical input and executable for each endpoint.
Old observations on the previous seed-selected fixture are not measurements of
this corpus. Builds and conversion are outside the measured whole-process time;
reading, parsing, graph execution, checking, and shutdown remain included.

The full-input strict-proof comparison is explicitly deferred in
[the shared exclusion file](../ignore.json): fresh processes exceeded the local
10 GiB allocator/address-space cap, and uncapped validation is unestablished.
The recording-only comparison remains available:

```sh
# NEE: proof recording versus ordinary execution.
./bench.py benchmarks/disequality/parameter-analysis.egg --treatment proofs
```

The native treatments `egg-de`, `egg-ee`, `egg-nee`, and
`egg-oee` use the corresponding `.in` file and run the unchanged authors'
drivers without proofs. Their CSV output and exit behavior are preserved.
They do not emit Egglog phase timings. See the
[implementation comparison](COMPARISON.md) for collection and the chart.

## Small examples and snapshots

`egglog-experimental/tests/disequality/` contains a congruence example and a
rule-head/multiple-sort example. Each has a runnable NEE desugared snapshot.
Their integration test checks all five execution modes and verifies that the
snapshots match the compiler output. Regenerate only these small snapshots with:

```sh
UPDATE_DISEQUALITY_SNAPSHOTS=1 cargo test -p egglog-experimental --test disequality
```

Negative tests separately ensure that consistent inputs do not prove a
contradiction. [What the disequality benchmark measures](PERFORMANCE.md) explains
the comparison boundaries and proof guarantees, and links to historical
measurements on the previous input.
