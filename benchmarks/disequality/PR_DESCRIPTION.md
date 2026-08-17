## Summary

- compile `(disequal lhs rhs)` and consistency checks into four selectable
  egglog encodings: EE, OEE, NEE, and relational DE
- keep every encoding outside union-find, e-class storage, and congruence
  closure so the extension remains a self-contained compiler pass
- integrate the published parameter-analysis, Propel, and EUF case studies
- import the paper artifact's source and Propel corpus in a provenance-isolated
  commit with an archive/member hash manifest
- commit inspectable EUF and Propel `.egg` captures plus each encoding's actual
  desugared output, and execute them under ordinary, term, proofs,
  proof-testing, and proof-extraction modes
- generate source-shaped EUF and Propel constructors for those captures, while
  retaining the generic Vec representation as a measured runtime control
- document parity limits, revision-pinned performance, diagnosed bottlenecks, and
  prioritized fixes in `benchmarks/disequality/PERFORMANCE_ANALYSIS.md`

## Motivation

*Dis/Equality Graphs* presents three term encodings and a native e-graph
extension. This PR tests the paper's design space as an instance of extension
by compilation: each representation is generated from the same typed egglog
commands and private schedule, without adding disequality state to the
union-find.

The relational `de` backend intentionally differs from the paper artifact's
patched adjacency structure. It stores a symmetric private relation over
canonical e-class values, and contradiction is a self-edge produced by
canonicalization. That distinction is explicit in the docs and generated
snapshots.

## Implementation

`egglog-experimental` adds typed command macros for:

```lisp
(disequal lhs rhs)
(check-disequal lhs rhs)
(check-disequalities)
```

The selected compiler pass infers the operand sort and lazily generates private
declarations, rules, and a private schedule for that sort. The commands work at
top level, in anonymous action batches, and on rule right-hand sides. EE, OEE,
NEE, and DE can be selected with `--disequality-encoding` on the experimental
CLI.

The shared in-process adapter under `benchmarks/disequality/egglog-backend/`
provides typed add, union, disequality, clone, comparison, consistency, and
stats operations. It can either use the original
`BenchmarkNode(String, Vec)` language or compile a declared `(name, arity)`
schema into real egglog constructors, with `Atom(String)` only for dynamic
names. Compiled templates avoid reparsing either schema for every graph.
Committed capture batches use immutable shared slices, so graph clones do not
copy the accumulated operation history. The EUF solver calls it through Rust.
Propel calls the same implementation through a panic-contained C ABI from
Scala Native; no external egglog process participates in solving.

Operations are submitted in `(begin ...)` batches. User-written blocks retain
their local execution scope while their resolved actions are flattened in
order for proof checking; `let`-`begin` additionally lowers its trailing value
to the corresponding global binding in the proof-check program. This lets the
committed host captures exercise the same batching shape under proof mode.

## Artifact case studies

### Parameter analysis

The existing source benchmark deterministically converts the artifact's 60,000
expressions and 30,000 pairs into ignored, regenerable TSV relations. Egglog
reconstructs 3,728,927 occurrence rows with rules, traverses the pair table,
and invokes the selected disequality compiler pass. No generated TSV is added
to Git.

### EUF

The original parser, CNF conversion, MiniSat enumeration, native egg EE, and
patched-egg DE remain available. Four `egglog-*` backends use the same live
per-model boundary: clone the base graph, apply the model's equalities and
disequalities, then check consistency. The imported native DE path and the four
egglog paths now install `true != false`; this corrects an artifact omission
that accepted contradictory Boolean congruence. Focused SAT,
congruence-UNSAT, and Boolean-congruence-UNSAT fixtures agree across all six
backends. The full 7,591-file corpus is represented in the import manifest but
is not committed or claimed as fully validated.

The parser now retains SMT declarations. Direct mode emits declared constants
and functions as `EufTerm` constructors and uses `Atom` only for generated
names; it is the EUF default. The old Vec language remains selectable.

### Propel

All original native variants remain selectable. Four `egglog-*` variants route
the original graph operations through the shared backend. A bounded 10-second
audit of the default Vec path produced 298 directly comparable egglog/native
observations across the 128 imported programs; every completed pair agreed. All
five variants completed on 72 programs, and the remaining 231 individual runs
timed out. A separate direct-constructor audit matched all 289 comparable
observations, completed all variants on 71 programs, and retained 242 timeout
rows. Neither run had an execution error. Timeout rows remain unknown rather
than being counted as matches.
The short-boundary completion counts are recorded-run coverage rather than a
stable performance comparison between term languages.

Propel can derive a direct schema from its parsed term, including source data
constructors and actual match arities. Direct mode is explicit and drives the
committed captures. Cached Vec remains the runtime default because balanced
measurements found it faster for Propel's thousands of short-lived graphs.

## Inspectable generated programs

`benchmarks/disequality/snapshots/` contains direct-constructor programs with:

- one encoding-independent source capture for an EUF SAT model;
- one encoding-independent source capture for Propel's selected final graph;
- the EE, OEE, NEE, and DE desugaring of each capture; and
- a manifest binding every output to its source input and hash.

The snapshot generator reruns both host integrations, compares generated bytes,
and replays every raw and desugared file under ordinary execution, term
encoding, proof generation, proof testing, and proof extraction. Raw source is
tested under all four encodings. Each replay attaches two simple witness
constructors to the first explicit host union and checks their equality. A Rust
regression also runs both raw captures with all four encodings in ordinary,
term, proofs, proof-testing, and proof-extraction modes, so proof testing
validates that union without constructing container values in the query. These
are executable examples for manual inspection, not pseudocode.

## Performance

Measurements were taken on an Apple M4. Parameter analysis was measured at
`88c40cf`; Propel and EUF were measured at `e7b7969` after merging base
`ffb8ae4`; the later proof-regression analysis used `fff36169` after merging
base `fdd4eac`. The heavy integrations were not remeasured after the
source-order `fail` change. Those earlier Propel and EUF values are medians of
six accepted samples from two reversed endpoint orders; parameter analysis uses
three interleaved rounds. The direct-constructor follow-up instead uses ten
samples for each small input and six for each larger input, again split across
reversed orders. That accepted follow-up used clean candidate revision
`b87057b`. These are descriptive measurements, not publication-quality
confidence intervals.

### Direct-constructor follow-up

The follow-up compares a frozen pre-change binary, current Vec with and without
template reuse, and direct constructors. On `gset_comm`, median wall time is
293.4 ms for frozen cold Vec, 214.5 ms for cached Vec, and 245.4 ms for cached
direct. On `tip_bin_plus_assoc`, the corresponding medians are 6.575 s,
6.142 s, and 7.559 s. Cached direct therefore takes 1.14-1.23x as long as
cached Vec, which remains Propel's default. Direct's extra constructor
relations are expensive when Propel creates thousands of small graphs.

EUF has the opposite result. Direct medians are 6.2% lower on `uf.815405`
(523.0 versus 557.6 ms) and 9.4% lower on `uf.614981` (4.539 versus 5.008 s),
so EUF defaults to direct. The small-input samples are visibly order-sensitive.
Every table reports combined medians and full ranges in
`benchmarks/disequality/PERFORMANCE_ANALYSIS.md`; no accepted sample is
discarded.

The eight raw Hyperfine reports, SHA-256 manifest, binary/input provenance, and
the exact forward/reverse driver are committed under
`benchmarks/disequality/reports/term-language-performance/` and
`benchmarks/disequality/scripts/benchmark_term_languages.sh`.

### Parameter analysis

| Comparison | Wall median | Ratio |
| --- | ---: | ---: |
| egglog EE / native EE | 4,936.6 / 932.8 ms | 5.29x |
| egglog DE / native DE | 4,770.7 / 639.0 ms | 7.47x |

All four egglog medians are within 166 ms. Term reconstruction costs about 2.5
seconds, pair traversal about 0.6 seconds, and non-ruleset work about 1.7
seconds. The private disequality phase is 0.2-11.8 ms, so representation
propagation is not the end-to-end bottleneck.

### Propel

| Program | Native DE | Egglog DE | Ratio |
| --- | ---: | ---: | ---: |
| `tip_list_append_assoc` | 51.6 ms | 140.4 ms | 2.72x |
| `tip_bin_plus_assoc` | 618.9 ms | 7.240 s | 11.70x |
| `tip_nat_times_alt_assoc` | 4.386 s | 12.571 s | 2.87x |

Instrumentation on the medium case found 10,357 fresh graphs, 13,591 flushes,
17,159 pair comparisons, and 620 full stats scans. Resolution/typechecking was
larger than database execution, but both were material; consistency propagation
was only 12 ms. Atomic `(begin ...)` semantics introduce another first-order
candidate: the graph snapshot retained during every host batch can disable
unique-owner mutation paths. At the measured `e7b7969` revision, each live
consistency check also cloned once to validate the complete `fail` body and
retained a second rollback snapshot while its schedule ran. Current source-order
`fail` execution instead retains one outer snapshot per source child and
disables the inner command snapshot; the heavy Propel and EUF integrations were
not remeasured after that change. The observed post-atomic slowdown is
consistent with this work, but the snapshot classes were counted rather than
timed independently. Flattening the batch was tested and was worse because it
compiled each action independently.

### EUF

| Input | Native DE, no stats | Egglog DE, no stats | Ratio |
| --- | ---: | ---: | ---: |
| `uf.815405` (245 current models) | 44.2 ms | 541.7 ms | 12.27x |
| `uf.614981` (627 models) | 410.9 ms | 5.203 s | 12.66x |

On the 627-model input, one clean `--stats` run took 15.404 seconds because each
model triggers a full host-term/class scan, about two million term lookups in
the diagnostic run. Without stats, retained rollback snapshots are a
first-order candidate alongside repeated generated-command frontend work and
database execution; the extension schedule remains small. The exact stats pair
is retained in `benchmarks/disequality/reports/euf-large-stats-summary.csv`.

The detailed report records timing boundaries, hashes, ranges, comparison with
artifact-precomputed numbers, diagnostic ablations, and fix ideas. The leading
opportunities are one-pass/cached stats, a generic typed proof-aware batch API
with an explicit failure contract, cheaper direct-schema instantiation, typed
pair queries, and reduced graph lifecycle churn. Initialized-template reuse is
now implemented.
It explicitly does not recommend restoring the removed representation-specific
database writer.

Final validation also found a separate regression in existing proof-mode
canaries: the new command-error recovery path cloned the full e-graph before
every top-level action. Same-machine measurements initially showed the
three-file suite 1.31-1.37x slower and `rw-analysis.egg` 1.50-1.60x slower than
current main. The retained fix skips that clone only for recursively verified
constructor trees. Constructor globals use a lightweight transaction over the
two eagerly updated sort entries; relation facts, partial/custom actions, and
multi-action blocks retain full rollback. It also moves committed proof-check
source commands out of a draining queue. In balanced 30-round measurements,
the stable endpoint order put suite wall time at 1.005-1.021x main and peak RSS
at 1.02-1.04x. The other order retained one 410 ms observation among otherwise
17-22 ms `integer_math.egg` runs, making its wall interval inconclusive. The
report therefore claims only that the prior repeatable 32-59% regression no
longer reproduces. The diagnostic history, non-reconstructible intermediate
ablations, exact clean revisions, commands, and intervals are recorded in
`benchmarks/disequality/PERFORMANCE_ANALYSIS.md`.

## Scope and known limits

- DE is a relational compiler encoding, not native adjacency in union-find.
- The full EUF corpus has not been run through all backends.
- Propel timeout rows remain unknown.
- `uf.815405` enumerates 245 current models versus 246 in the artifact result;
  this parity difference is retained as unresolved.
- Proof testing validates an equality derived from the first explicit host
  union in each captured program; Propel and EUF do not emit separate
  host-level proof certificates.
- The small performance sample establishes cost centers but not significance.

## Review and validation

Independent read-only full-diff reviews found rollback gaps for a failing
schedule, partial `pop`, nested `fail`, and an unrestricted user-defined command,
then found that a live `fail` expanded its complete body before earlier children
could add type information. The implementation now validates expansions in
source order, invokes each command macro once, gives every `fail` child one
atomic source-command boundary in live execution and resolved replay, and
preserves successful prefix commands. Static desugaring conservatively rejects
commands whose runtime-dependent compiler state cannot be represented. The
same review also required source-revision and dirty-state provenance before the
bounded Propel parity result could be treated as current; that metadata is now
part of the report schema. A read-only re-review of `b56a72f` verified the
one-pass `fail` repair, nested rollback and fatal-error behavior, all five
capture modes, and the regenerated parity and performance evidence. Final
performance review then found a full-e-graph clone before every proof-mode
action and a duplicate-global type-state corruption in the first optimization.
The retained `fff36169` source restricts the no-clone path to recursively
verified constructor trees and restores both global-sort entries if shadowing
rejects a constructor global. A final full-diff documentation review required
the heavy timing results to be revision-pinned rather than described as
current; the exact measurement split is now recorded above and in the detailed
report.

The final direct-constructor review found four additional issues: generated
Propel type-lambda binders needed an injective lowering, cached templates needed
a concurrency boundary, parity evidence still described dirty source, and the
term-language timing commands were not preserved. `TypeLambda(Atom(name),
body)` now preserves generated binders; clones from one template serialize
database access while remaining logically isolated; uncached and failed
templates are closed; clean Vec/direct corpus reports are committed; and the
exact timing driver, raw samples, hashes, and provenance are retained.

Successful final gates include:

```sh
make nits
make check                                             # full repository gate
make benchmark-smoke                                   # 20/20 off/proofs runs
cargo test -p egglog --test proof_mode_regression       # 32/32
make -C benchmarks/disequality check                    # includes 80 replays
uv run pytest tests/test_disequality_parameter_analysis.py
git diff --check origin/main...c52112f^                  # authored pre-import work
git diff --check c52112f..HEAD -- . \
  ':(exclude)benchmarks/disequality/disegg.patch' \
  ':(exclude)benchmarks/disequality/disegg/**'           # post-import tree changes
git diff --check 55250f3^..55250f3 -- \
  benchmarks/disequality/disegg/ARTIFACT_PROVENANCE.md   # authored reconstruction note
```

Commit `c52112f` preserves the selected Zenodo members byte-for-byte. Commit
`55250f3` reconstructs the missing `disegg` checkout from upstream `egg` 0.9.5
and the archived patch; upstream whitespace is intentionally not reformatted.

The measured code revision and timing methodology are recorded in
`benchmarks/disequality/PERFORMANCE_ANALYSIS.md`.
