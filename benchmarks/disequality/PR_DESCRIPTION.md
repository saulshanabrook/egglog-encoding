## Summary

- compile `(disequal lhs rhs)` and consistency checks into four selectable
  egglog encodings: EE, OEE, NEE, and set-backed DE
- keep every encoding outside union-find, e-class storage, and congruence
  closure so the extension remains a self-contained compiler pass
- integrate the published parameter-analysis, Propel, and EUF case studies
- import the paper artifact's source and Propel corpus in a provenance-isolated
  commit with an archive/member hash manifest
- commit inspectable EUF and Propel `.egg` captures plus each encoding's actual
  desugared output; execute every encoding in ordinary mode and execute EE,
  OEE, and NEE under term, proofs, proof-testing, and proof-extraction modes
- generate source-shaped EUF and Propel constructors for those captures, while
  retaining the generic Vec representation as a measured runtime control
- document parity limits, provenance-qualified performance, diagnosed
  bottlenecks, and prioritized fixes in
  `benchmarks/disequality/PERFORMANCE_ANALYSIS.md`

## Motivation

*Dis/Equality Graphs* presents three term encodings and a native e-graph
extension. This PR tests the paper's design space as an instance of extension
by compilation: each representation is generated from the same typed egglog
commands and private schedule, without adding disequality state to the
union-find. NEE uses a binary egglog relation for the paper's private `ne`
marker. This preserves its self-loop contradiction criterion while avoiding
the paper encoding's otherwise-unused result e-class per `ne` e-node, so its
storage accounting is an egglog-specific relational variant of NEE.

The `de` backend expresses the paper artifact's adjacency-map shape with
ordinary egglog containers rather than patched e-class storage. A private
function maps each e-class to a `Set` of disequal neighbors. Each insertion
writes both orientations; canonical key collisions merge sets with `set-union`;
container rebuild canonicalizes their members; and a self-member is a
contradiction. That distinction is explicit in the docs and generated
snapshots.

## Implementation

`egglog-experimental` adds typed command macros for:

```lisp
(disequal lhs rhs)
(check-disequal lhs rhs)
(check-known-disequal lhs rhs)
(check-disequalities)
```

The selected compiler pass infers the operand sort and lazily generates private
declarations, rules, and a private schedule for that sort. The commands work at
top level, in anonymous action batches, and on rule right-hand sides. EE, OEE,
NEE, and DE can be selected with `--disequality-encoding` on the experimental
CLI.

DE is currently normal-mode only. The CLI rejects it with `--term-encoding`,
`--proofs`, `--proof-testing`, or `--proof-extraction`, and the proof-oriented
experimental Rust constructor rejects it. EE, OEE, and NEE support all five
modes. DE's literal set-valued custom merge is not yet supported by the
term/proof encoding, so Rust callers must not bypass the guarded constructors
by enabling those modes afterward; the hidden core mode-enabling path enforces
the same incompatibility marker.

The container-backed implementation exposed a normal-mode rebuild-order bug:
container canonicalization could retire an output container id before a
custom function merge consumed it. Native rebuild now publishes container
unions before rebuilding function rows. A focused regression collapses both a
set-valued function's keys and its outputs in the same rebuild.

The shared in-process adapter under `benchmarks/disequality/egglog-backend/`
provides typed add, union, disequality, clone, comparison, consistency, and
stats operations. Mutation batches and checks are constructed as `egglog::ast`
and passed through `EGraph::run_program`; the live path no longer prints and
reparses generated source or parses textual command output. It can either use
the original `BenchmarkNode(String, Vec)` language or compile a declared `(name, arity)`
schema into real egglog constructors, with `Atom(String)` only for dynamic
names. Compiled templates avoid reparsing either schema for every graph.
Opt-in chronological recording uses persistent immutable trace chunks, so graph
clones share their history prefix; ordinary benchmark runs retain no trace.
The exporter records actual mutation, rebuild, clone, pair-query, consistency,
and stats interactions and never synthesizes a witness or final query. Its
output is an outcome-preserving chronological replay: mutations and observed
query outcomes are executable commands, while host-only rebuild, clone, and
stats observations are retained as comments. The EUF solver calls it through
Rust.
Propel calls the same implementation through a panic-contained C ABI from
Scala Native; no external egglog process participates in solving.

Operations are submitted in typed action batches. User-written `(begin ...)`
blocks retain
their local execution scope while their resolved actions are flattened in
order for proof checking; `let`-`begin` additionally lowers its trailing value
to the corresponding global binding in the proof-check program. This lets the
committed host captures exercise the same batching shape under proof mode for
EE, OEE, and NEE.

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

The parser now retains SMT declarations. Vec is the EUF default because it
matches the paper artifact's `SymbolLang` representation. Explicit
`--term-language direct` mode emits declared constants and functions as
`EufTerm` constructors and uses `Atom` only for generated names.

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

`egglog-experimental/tests/disequality/` contains encoding-independent source
programs with provenance comments for:

- Figure 2 and three compact artifact examples;
- the full parameter-analysis driver;
- one direct-constructor source capture for an EUF SAT model; and
- one direct-constructor source capture for Propel's selected final graph.

The nested `snapshots/` directory has EE, OEE, NEE, and DE expansions for every
source: 28 inspectable `.desugared.egg` files plus a hash manifest. The EUF and
Propel sources are outcome-preserving chronological replays of host
interactions, with operation counts that expose absent pair queries rather than
filling them in.
The snapshot generator reruns both host integrations and replays 224 source/snapshot
treatments. A Rust regression independently enumerates all fixtures and
compares every expansion byte-for-byte. EE, OEE, and NEE replay in ordinary,
term, proofs, proof-testing, and proof-extraction modes; DE replays in ordinary
mode only. The supported proof modes exercise the recorded term bindings,
explicit unions, disequalities, and observed query outcomes. These are
executable tests for manual inspection, not pseudocode.

## Performance

Measurements were taken on an Apple M4. The historical relation-backed
parameter analysis was measured at `88c40cf`; Propel and EUF were measured at
`e7b7969` after merging base `ffb8ae4`; the later proof-regression analysis used
`fff36169` after merging base `fdd4eac`. Those older heavy integrations were
not remeasured after the source-order `fail` change. Their Propel and EUF values
are medians of six accepted samples from two reversed endpoint orders;
parameter analysis uses three interleaved rounds. The direct-constructor
follow-up instead uses ten samples for each small input and six for each larger
input, again split across reversed orders. That accepted follow-up used clean
candidate revision `b87057b`. The hash-identified pre-final set-backed follow-up
is described below. The typed-host-AST follow-up uses clean candidate
`d5a463bf` against clean parent `6b3f7b89`, before the branch's later merge from
`origin/main`, again in reversed endpoint orders:
16 combined samples per small Propel endpoint, eight per medium endpoint, and
60 per tiny EUF endpoint. These are descriptive measurements, not
publication-quality confidence intervals.

The 2026-09-02 relational-NEE follow-up compares the current relation against
the clean constructor-backed parent `e11f3f57`. Pooled relation/constructor
medians are 1.002x on `gset_comm` and 1.012x on `tip_bin_plus_assoc`; reversed
endpoint orders likewise show parity rather than a speedup. Raw samples,
commands, and hashes are retained under
`benchmarks/disequality/reports/relational-nee-follow-up/`. Older NEE timings
below measure the constructor-backed representation.

### Typed host AST and recording follow-up

The clean 2026-09-01 follow-up isolates direct `egglog::ast` submission and
opt-in recording from the parent adapter that rendered and reparsed every
mutation batch and retained operation history in every graph.

| Workload | Encoding | source-reparse parent | typed-AST candidate | Directional result |
| --- | --- | ---: | ---: | ---: |
| Propel `gset_comm` | DE | 207.7 ms | 200.8 ms | inconclusive: +0.8% forward, -4.2% reverse |
| Propel `gset_comm` | NEE | 195.7 ms | 192.3 ms | inconclusive: +5.4% forward, -2.3% reverse |
| Propel `tip_bin_plus_assoc` | DE | 7.400 s | 7.163 s | lower in both orders: -0.3% to -3.9% |
| Propel `tip_bin_plus_assoc` | NEE | 5.657 s | 5.430 s | lower in both orders: -0.4% to -8.2% |

The small workload is order-sensitive and inconclusive. The medium workload is
directionally lower in both orders, but this remains a descriptive measurement,
not a resolution of the paper-level overhead: macro expansion, typechecking,
proof instrumentation, atomic command semantics, database execution, and graph
lifecycle remain. The EUF fixture measured in this follow-up completes below 5
ms, so its apparent 2-4% decrease is below reliable measurement resolution and
supports only a no-large-regression claim. These timings characterize the
isolated `d5a463bf` change, not the later merged final head.

On NEE `gset_comm`, recording disabled had a 177.6 ms combined median;
recording plus rendering, desugaring, and overwriting 104 files had a 202.1 ms
median, or 1.138x. Ordinary runs disable recording. Raw samples, complete
ranges, exact commands, and binary/input hashes are retained under
`benchmarks/disequality/reports/typed-host-ast/`.

### Set-backed DE follow-up

The set-backed DE candidate was measured on 2026-08-19 in two opposite endpoint
orders, retaining every sample and full ranges. Parameter analysis used three
runs per order, Propel `gset_comm` used five, and
`tip_bin_plus_assoc` used three. NEE has the lowest combined egglog median on
all three workloads:

| Workload | EE | OEE | NEE | set-backed DE | native DE |
| --- | ---: | ---: | ---: | ---: | ---: |
| Parameter analysis | 5.701 s | 5.679 s | 5.524 s | 6.062 s | not rerun |
| Propel `gset_comm` | 277.1 ms | 241.6 ms | 194.9 ms | 210.5 ms | 52.7 ms |
| Propel `tip_bin_plus_assoc` | 8.137 s | 6.603 s | 5.366 s | 7.732 s | 640.0 ms |

Set-backed DE is 1.08x NEE on small Propel, 1.44x on medium Propel, and 1.10x
on parameter analysis. A separate single parameter timing-summary run put its
private schedule at 13.096 ms, versus 20.003 ms for EE, 1.378 ms for OEE, and
0.227 ms for NEE. Container construction and rebuild outside the private
schedule are not included in those rule timings. The parameter and medium
Propel runs were endpoint-order-sensitive, so these are descriptive
comparisons rather than significance claims.

Raw Hyperfine JSON, exact commands, executable/input hashes, and the full
ranges are retained under
`benchmarks/disequality/reports/set-de-follow-up/`. The large EUF corpus was
unavailable locally for this follow-up; current DE has focused EUF semantic
coverage but no refreshed large-corpus timing claim. The older DE numbers below
measure the superseded flat-relation compiler pass and are retained only as
historical cost diagnosis.

The set-backed timing candidate was an uncommitted tree based on `46a7377`.
Its dirty source diff was not retained, so the executable hashes identify the
measured artifacts but do not make this tranche revision-reproducible; no final
measured source commit is claimed.

### Historical direct-constructor follow-up (relation-backed DE)

The `b87057b` follow-up predates set-backed DE and compares a frozen pre-change
binary, Vec with and without template reuse, and direct constructors. On
`gset_comm`, median wall time is 293.4 ms for frozen cold Vec, 214.5 ms for
cached Vec, and 245.4 ms for cached direct. On `tip_bin_plus_assoc`, the
corresponding medians are 6.575 s,
6.142 s, and 7.559 s. Cached direct therefore takes 1.14-1.23x as long as
cached Vec, which remains Propel's default. Direct's extra constructor
relations are expensive when Propel creates thousands of small graphs.

EUF has the opposite result. Direct medians are 6.2% lower on `uf.815405`
(523.0 versus 557.6 ms) and 9.4% lower on `uf.614981` (4.539 versus 5.008 s),
but Vec remains the default to match the paper baseline; direct is available
only through `--term-language direct`. The small-input samples are visibly
order-sensitive. Every table reports combined medians and full ranges in
`benchmarks/disequality/PERFORMANCE_ANALYSIS.md`; no accepted sample is
discarded.

The eight raw Hyperfine reports, SHA-256 manifest, binary/input provenance, and
the exact forward/reverse driver are committed under
`benchmarks/disequality/reports/term-language-performance/` and
`benchmarks/disequality/scripts/benchmark_term_languages.sh`.

### Historical relation-backed parameter analysis

| Comparison | Wall median | Ratio |
| --- | ---: | ---: |
| egglog EE / native EE | 4,936.6 / 932.8 ms | 5.29x |
| egglog DE / native DE | 4,770.7 / 639.0 ms | 7.47x |

All four egglog medians are within 166 ms. Term reconstruction costs about 2.5
seconds, pair traversal about 0.6 seconds, and non-ruleset work about 1.7
seconds. The private disequality phase is 0.2-11.8 ms, so representation
propagation is not the end-to-end bottleneck for that implementation.

### Historical relation-backed Propel

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

### Historical relation-backed EUF

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
artifact-precomputed numbers, diagnostic ablations, and fix ideas. Typed host
batches, typed pair checks, and initialized-template reuse are now implemented.
The leading remaining opportunities are one-pass/cached stats, an explicit
failure contract that can avoid unnecessary snapshots, cheaper direct-schema
instantiation, and reduced graph lifecycle churn.
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

- DE is a container-backed compiler encoding, not native adjacency in
  union-find.
- DE is normal-mode only; term/proof encoding rejects its set-valued custom
  merge. EE, OEE, and NEE retain full proof-mode coverage.
- The full EUF corpus has not been run through all backends.
- Propel timeout rows remain unknown.
- `uf.815405` enumerates 245 current models versus 246 in the artifact result;
  this parity difference is retained as unresolved.
- The captures replay host operations and observed outcomes; they do not emit
  separate host-level proof certificates, and rebuild, clone, and stats events
  are comments rather than executable egglog commands.
- The small performance sample establishes cost centers but not significance.

## Review and validation

Independent read-only full-diff reviews found rollback gaps for a failing
schedule, partial `pop`, nested `fail`, and an unrestricted user-defined command,
then found that a live `fail` expanded its complete body before earlier children
could add type information. The implementation now validates expansions in
source order, invokes each command macro once, gives every `fail` child one
atomic source-command boundary in live execution and supported resolved replay,
and preserves successful prefix commands. Static desugaring conservatively
rejects commands whose runtime-dependent compiler state cannot be represented.
Under term/proof encoding it also rejects a `fail` body containing `extract`,
whose multi-command lowering cannot preserve the source rollback boundary. The
same review also required source-revision and dirty-state provenance before the
bounded Propel parity result could be treated as current; that metadata is now
part of the report schema. A read-only re-review of `b56a72f` verified the
one-pass `fail` repair, nested rollback and fatal-error behavior, the
then-supported five-mode relation-backed capture matrix, and the regenerated
parity and performance evidence. Final
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

A final read-only review of the typed-host-AST change found no blockers and no
worthwhile DRY reduction. It independently passed the focused disequality gate,
the complete repository gate, and a non-selected Propel capture containing two
pair queries under all four ordinary encodings and the three proof-compatible
encodings. The committed final Propel graph has zero pair queries; its counters
and fixture documentation preserve that absence rather than synthesizing
coverage.

Successful final gates include:

```sh
make nits
make check                                             # full repository gate
make benchmark-smoke                                   # 20/20 off/proofs runs
cargo test -p egglog --test proof_mode_regression       # 34/34
make -C benchmarks/disequality check                    # includes 224 supported replays
cargo test -p egglog --test container_rebuild           # includes normal-mode set merge regression
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
