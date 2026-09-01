# Disequality case-study performance analysis

Run dates: 2026-08-12 through 2026-09-01

This report analyzes the egglog implementations of the three case studies from
*Dis/Equality Graphs*: parameter analysis, Propel, and the EUF solver. It
separates end-to-end measurements from diagnostic instrumentation and avoids
attributing generic host/API overhead to the compiled disequality rules.

## Environment and method

- Apple M4, 16 GiB RAM, arm64 macOS (Darwin 25.6.0)
- Rust 1.91.0 and Cargo 1.91.0; the older case-study tranches used uv 0.12.3,
  the 2026-08-19 set-backed follow-up used uv 0.12.5, and the typed-host-AST
  follow-up used uv 0.12.6
- case-study timing base `origin/main` at
  `ffb8ae435bd6421077b1c15826f32a6aeecf5b1b`
- final Propel and EUF measurements at code commit
  `e7b796940dbc148c3a97cc4a421a6669fa441f0e`, after merging `origin/main` at
  `ffb8ae435bd6421077b1c15826f32a6aeecf5b1b`
- final proof-mode regression analysis after merging `origin/main` at
  `fdd4eac12c1318c578badbf5d1299e0e3eb4e6c0`; the measured candidate source
  tree was committed unchanged as
  `fff36169eb9527ee817477bceecf371ddbe67b8c`
- parameter-analysis measurements at
  `88c40cf6a298a8c503a741b8e736d5cc7498f348`; the later commit changes live
  `fail` handling, which the consistent parameter workload does not execute
- set-backed DE follow-up from an uncommitted tree based on `46a7377`, with
  exact measured executable hashes under `reports/set-de-follow-up/`; its dirty
  source diff was not retained, so this tranche is pre-final and not tied to a
  reproducible source revision
- typed-host-AST follow-up from clean candidate `d5a463bf` against frozen clean
  parent `6b3f7b89`, with binary/input hashes and every accepted sample under
  `reports/typed-host-ast/`
- release builds for timed Rust and Scala Native executables
- six accepted samples per historical Propel and EUF endpoint: two three-run
  Hyperfine invocations with endpoint order reversed, after one Propel warmup
  and two EUF warmups
- three interleaved endpoint rounds for parameter analysis
- hash-identified pre-final set-backed follow-up in two opposite endpoint
  orders: three samples per order for parameter analysis and medium Propel,
  five for small Propel
- typed-host-AST follow-up in two opposite endpoint orders: eight samples per
  order for small Propel, four for medium Propel, and 30 for the sub-5 ms EUF
  fixture; the recording/export ablation uses eight samples per order

The commands below regenerate the revision-pinned results. For the set-backed
tranche, the retained commands reproduce the invocation shape, but its missing
dirty source diff prevents reconstruction of the exact measured executables.
Generated parameter TSV files and the large EUF corpus are intentionally not
committed. These sample sizes are enough to identify the large cost centers
here, but not for a publication-quality statistical claim. Ranges are
descriptive.
Complete timing attempts that overlapped Rust builds, the independent
reviewer's validation, or another worktree's concurrent benchmark and compiler
processes were rejected before analysis. No sample inside an accepted
invocation was discarded.

## Summary

| Case study | Comparison | Measured result | Observed costs and candidates |
| --- | --- | ---: | --- |
| Typed host AST, Propel small | candidate / source-reparse parent | 0.967x DE; 0.983x NEE wall | direct AST submission and no retained trace in ordinary runs produce a modest change |
| Typed host AST, Propel medium | candidate / source-reparse parent | 0.968x DE; 0.960x NEE wall | frontend work is reduced, but graph lifecycle and database work remain |
| Opt-in capture, Propel small | recording+export / recording off | 1.138x wall | includes persistent tracing, rendering, desugaring, and 104 file writes |
| Set-backed candidate parameter analysis | set DE / NEE | 1.10x wall | 3.7M occurrence rows dominate; set DE private schedule was 13.1 ms in one diagnostic |
| Set-backed candidate Propel, small | set DE / NEE; set DE / native DE | 1.08x; 3.99x wall | fixed graph lifecycle, host calls, and container work |
| Set-backed candidate Propel, medium | set DE / NEE; set DE / native DE | 1.44x; 12.08x wall | repeated graph creation and set-valued adjacency merges |
| Historical parameter analysis | relational DE / native DE | 7.47x wall | relation-backed DE propagation itself was 2.5 ms |
| Historical Propel, medium | relational DE / native DE | 11.70x wall | repeated creation, frontend/database/query/stats work, and rollback snapshots |
| Historical EUF, 627 models | relational DE / native DE | 12.66x wall | 403K operations across 628 atomic flushes, frontend work, and database execution |
| Historical EUF, 627 models with stats | relational DE / native DE | 39.71x reported full time | 627 full graph scans and about 2M term lookups |

## Typed host AST and opt-in recording follow-up

The 2026-09-01 follow-up isolates the host adapter refactor before the branch's
later merge from `origin/main`. Frozen clean parent
`6b3f7b8981be086fab768e79cc0cd23cca943748` prints and reparses each generated
operation batch and retains operation history in ordinary graphs. Clean
candidate `d5a463bf17f099f26965a72503f756185855711e` constructs `egglog::ast`
actions and checks directly, submits them through `EGraph::run_program`, and
retains a persistent trace only when source export is requested. Both use the
paper-faithful Vec term language and the same inputs, encodings, and process
boundaries.

Every workload was measured in opposite endpoint orders and every sample was
retained. Combined medians and full ranges are:

| Workload | Encoding | source-reparse parent | typed-AST candidate | Directional result |
| --- | --- | ---: | ---: | ---: |
| Propel `gset_comm` | DE | 207.7 ms (195.6-237.6) | 200.8 ms (185.5-236.0) | inconclusive: +0.8% forward, -4.2% reverse |
| Propel `gset_comm` | NEE | 195.7 ms (189.2-207.3) | 192.3 ms (183.8-322.5) | inconclusive: +5.4% forward, -2.3% reverse |
| Propel `tip_bin_plus_assoc` | DE | 7.400 s (7.062-8.236) | 7.163 s (6.988-7.793) | lower in both orders: -0.3% to -3.9% |
| Propel `tip_bin_plus_assoc` | NEE | 5.657 s (5.415-5.986) | 5.430 s (5.178-6.288) | lower in both orders: -0.4% to -8.2% |

The small workload changes sign with endpoint order and is inconclusive. The
medium workload is directionally lower in both orders, but the magnitude is
order-sensitive. This is not a change in the paper-level overhead. The
candidate removes source rendering/parsing from the live path and avoids
retaining capture history in ordinary runs, but it deliberately preserves
command-macro expansion, typechecking, proof instrumentation, atomic command
semantics, database execution, and the existing graph lifecycle. These
measurements characterize the isolated `d5a463bf` change, not the branch's
later merged final head.

The only EUF input measured in this follow-up is the tiny `tests/sat.smt2`
fixture. Its
combined medians were 3.022 ms versus 2.961 ms for DE and 2.986 ms versus 2.867
ms for NEE. Hyperfine warns that all four commands are below 5 ms, where shell
startup resolution is material. These samples confirm there is no
order-of-magnitude regression on the fixture; they are not evidence for a EUF
speedup. The published large EUF corpus remains unavailable locally.

Recording is opt-in. On NEE `gset_comm`, recording disabled had a 177.6 ms
combined median (174.1-207.3 ms), while recording plus source and desugared
export had a 202.1 ms median (195.5-223.1 ms), or 1.138x. This ablation includes
persistent trace construction, rendering, desugaring, and overwriting 104
files; it is not the cost of trace retention alone. Ordinary benchmark runs
take the recording-disabled path.

Raw Hyperfine JSON, exact commands, source revisions, executable/input hashes,
and environment details are retained in
[`reports/typed-host-ast/`](reports/typed-host-ast/).

## Set-backed DE follow-up

The 2026-08-19 follow-up measured a hash-identified pre-final candidate using
the set-backed DE compiler pass, which maps each e-class to a literal egglog
`Set` of disequal neighbors. Each workload was run in two opposite endpoint
orders after one warmup. Parameter analysis and the medium Propel input use
three samples per order; small Propel uses five. Every sample is retained.
Combined medians and full ranges follow:

| Workload | EE | OEE | NEE | set-backed DE | native DE |
| --- | ---: | ---: | ---: | ---: | ---: |
| Parameter analysis | 5.701 s (5.394-5.893) | 5.679 s (5.473-6.266) | 5.524 s (5.263-6.421) | 6.062 s (5.483-6.890) | not rerun |
| Propel `gset_comm` | 277.1 ms (260.9-323.1) | 241.6 ms (229.1-259.5) | 194.9 ms (188.1-242.9) | 210.5 ms (197.5-225.0) | 52.7 ms (50.2-57.7) |
| Propel `tip_bin_plus_assoc` | 8.137 s (6.885-10.518) | 6.603 s (6.360-6.777) | 5.366 s (5.318-6.226) | 7.732 s (7.414-8.490) | 640.0 ms (600.9-806.3) |

The parameter and medium Propel samples are visibly endpoint-order-sensitive,
so these are descriptive results rather than significance claims. NEE has the
lowest combined egglog median in each row. Set-backed DE is 1.08x NEE on small
Propel, 1.44x on medium Propel, and 1.10x on parameter analysis. This cost is
the tradeoff for representing the paper's per-class forbid list with generic
egglog containers instead of a flat relation or patched union-find state.

A separate single parameter-analysis timing-summary run attributed 20.003 ms
to EE's private ruleset, 1.378 ms to OEE, 0.227 ms to NEE, and 13.096 ms to
set-backed DE. The DE value excludes set construction, key collision merges,
and container rebuild work outside the private schedule, so it is not the
total representation cost. It does establish that schedule saturation alone
does not explain the roughly 0.5-second DE/NEE median difference.

The raw Hyperfine JSON, executable and input hashes, exact commands, and
environment are retained in
[`reports/set-de-follow-up/`](reports/set-de-follow-up/). The omitted published
EUF corpus was unavailable locally for this follow-up. Current DE therefore has
EUF semantic fixture coverage but no refreshed large-corpus timing result; the
EUF numbers later in this report are explicitly historical relation-backed DE
measurements.

## Historical direct-constructor follow-up (relation-backed DE)

The 2026-08-17 follow-up adds source-shaped constructors as an explicit
`--term-language direct` alternative while retaining generic Vec as the
paper-faithful default. This tranche predates the set-backed DE compiler pass
and must not be read as current DE performance. It also isolates schema reuse
with `--no-template-cache`. The frozen baseline is parent commit `5069c43`; its
Propel and EUF binaries have SHA-256
`2140063b5030876f35c8f71b04d061e46f74cc73890584a8e5c59bdc366bdf81`
and
`35f541999e170b15ec1ecae3413499853fd82377f496691ef12b8353e8b9a22a`.
The accepted candidate run used clean source revision
`b87057b36f4c8cc2eed68e2a4dd950a530525216`; its Propel and EUF executables
have SHA-256
`0ce1df22cebf55dbfb33367dffdb98154b8ed8520df3166b5bf507768fb4ca0f`
and
`f56767aaee988076e118a2394b864a00f1f50d59c6621340d2b61745e1e71f96`.
Candidate commands name the term language explicitly, so CLI default choices
do not affect these measurements.

Propel uses two reversed Hyperfine invocations: five runs per order for
`gset_comm` and three per order for `tip_bin_plus_assoc`, each after one warmup.
EUF uses five runs per order for `uf.815405` and three per order for
`uf.614981`, each after two warmups. No sample within an invocation was
discarded. The full ranges therefore retain visible machine-noise outliers.
All EUF measurements omit `--stats`.

The eight raw Hyperfine JSON files, run provenance, and their hashes are
committed under
[`reports/term-language-performance/`](reports/term-language-performance/).
[`benchmark_term_languages.sh`](scripts/benchmark_term_languages.sh) reproduces
all forward and reversed invocations, including the frozen, cold, cached, Vec,
and direct arms. It requires the two revision-pinned baseline executables and
the two published EUF inputs because neither is rebuilt implicitly.

### Propel representation and template ablation

| Program | Frozen Vec, cold | `b87057b` Vec, cold | `b87057b` Vec, cached | Direct, cold | Direct, cached | Direct / cached Vec |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `gset_comm` | 293.4 ms (279.8-462.9) | 306.0 ms (271.5-415.1) | 214.5 ms (195.7-294.0) | 480.7 ms (469.0-928.9) | 245.4 ms (238.6-285.3) | 1.14x |
| `tip_bin_plus_assoc` | 6.575 s (6.309-7.820) | 7.150 s (6.395-8.090) | 6.142 s (5.663-6.965) | not run | 7.559 s (7.156-7.824) | 1.23x |

Template reuse is real: the `b87057b` cold Vec takes 1.43x and 1.16x as long as
cached Vec on the small and medium inputs; frozen cold Vec takes 1.37x and
1.07x as long. Direct mode also requires a cached schema; compiling it per
graph takes 1.96x as long on the small input. Cached direct still takes
1.14-1.23x as long as cached Vec. Propel creates
many short-lived graphs, and every direct constructor is a separate egglog
function/relation that participates in graph cloning and rebuild bookkeeping.
This interpretation is supported by a diagnostic correction during the
implementation: removing three declarations that could never occur cut a
single medium direct run from about 15.2 seconds to 7.8 seconds. That diagnostic
was not a balanced benchmark, so it establishes sensitivity to schema width,
not a precise component cost.

The result changes the rollout decision. Propel defaults to cached Vec to avoid
a regression. Direct remains an explicit mode, is covered by source replay and
corpus parity checks, and is used to generate the readable committed `.egg`
captures.

### EUF representation ablation

| Input | Frozen Vec | `b87057b` Vec | Direct | Direct / `b87057b` Vec |
| --- | ---: | ---: | ---: | ---: |
| `uf.815405` (245 models) | 530.9 ms (508.6-562.0) | 557.6 ms (526.3-595.5) | 523.0 ms (496.4-634.0) | 0.94x |
| `uf.614981` (627 models) | 4.895 s (4.834-5.190) | 5.008 s (4.835-5.443) | 4.539 s (4.438-4.620) | 0.91x |

Direct-constructor medians are 6.2% and 9.4% lower than `b87057b` Vec on the
two published inputs (`b87057b` Vec takes 1.07x and 1.10x as long). The small
input is endpoint-order-sensitive and its direct range overlaps both Vec
ranges; the larger input is consistent across orders. Unlike Propel,
EUF builds one declared term graph and clones its populated state per SAT model
instead of creating thousands of independent empty schemas. EUF therefore
defaults to Vec to match the paper artifact's `SymbolLang` representation.
Direct remains an explicit alternative and the source form used for readable
snapshots despite its lower median on these two inputs.

The answer to "typechecking or engine?" is workload-dependent:

- parameter analysis is dominated by relational term reconstruction plus
  process/input/frontend work;
- current Propel and EUF retain a complete command snapshot across every
  `(begin ...)` batch so a failed action block can roll back atomically;
- at the measured `e7b7969` revision, each live `fail` also cloned once for
  whole-body validation and retained a second snapshot while executing a
  potentially failing child;
- current code executes a `fail` body in source order with one snapshot per
  source child and no inner command snapshot, but the heavy integrations were
  not remeasured after that change;
- at the profiled pre-atomic revision, repeated parsing/typechecking and
  database execution were both material;
- EUF with `--stats` is dominated by repeated graph scans; and
- the encoding-specific `@disequality` schedule is small in all measured
  parameter-analysis encodings and in the instrumented host integrations.

## Proof-mode regression found during final validation

The first published branch head introduced a separate regression in existing
proof workloads. GitHub's CodSpeed comparison reported a 31.76% aggregate
regression, but also warned that the endpoints used different runtime
environments. Same-machine runs confirmed the problem without accepting that
cross-environment magnitude: relative to current `origin/main`, the three-file
proof suite was 1.31-1.37x slower, `rw-analysis.egg` was 1.50-1.60x slower, and
peak RSS was 1.14-1.24x higher on the affected files.

The canaries contain no `fail` commands. A commit bisect placed the regression
in the proof-history/rollback commit rather than the imported artifact or
disequality rules. Timing-summary decomposition assigned 94-100% of the added
wall time to the unmeasured residual, not parsing, typechecking, rules,
equality maintenance, or ordinary command execution.

The intermediate ablations below were run from disposable dirty worktrees at
merge commit `52c81540753ede042136fd7da32b64a23d481ea6`. Their patches and raw
reports were not retained, so the values are diagnostic rather than
independently reproducible. The final comparison below uses committed source
and retained reproduction commands.

Two hypotheses were tested separately:

1. Removing one of the two proof-history markers did not help. The suite
   remained 1.32-1.38x slower and all affected files retained higher RSS, so
   that experiment was reverted.
2. Avoiding the full `EGraph` rollback clone for constructor-only unions cut
   the suite result to 1.06-1.10x. The slowdown tracked the number and size of
   top-level actions because proof mode had begun cloning the complete graph
   before every action, including actions with no runtime failure path.

The retained fix recognizes only constructor trees: literals and variables,
plus calls whose heads are declared constructors and whose children are also
constructor trees. Constructor-only unions and expression actions do not
invoke partial primitives or custom function lookups, so they skip the full
rollback clone after successful typechecking. Global bindings retain the clone
only when their value is not a constructor tree. A constructor-valued global
instead retains the old entries from the source and encoded global-sort maps,
then restores them if later shadowing rejects the command. Relation facts
retain the full clone because relations are not classified as constructors.
`set`, `delete`/`subsume`, `panic`, action blocks, `let`-`begin`, and any
expression containing a primitive or custom function remain on the atomic
rollback path. A regression test confirms that rejecting a different-sort
duplicate global does not corrupt type state in ordinary, term, proofs,
proof-testing, or proof-extraction mode; the existing partial primitive,
action-block, schedule, nested-`fail`, and `pop` recovery tests keep covering
the conservative path.

Committed proof-check source commands now live in a `VecDeque` and are moved
into proof history as each marker commits, rather than cloned twice and
retained beside the committed program. This preserves the remaining-stream
semantics across `push`/`pop` while reducing retained AST storage.

The first review repair conservatively restored full snapshots for every
global. That clean revision (`5e04f88c2f1f99f940c99b68b55e49d04ab4c7a2`)
fixed the type-state bug but measured 1.1266x slower as a suite (inverted 95%
CI 1.0223-1.2310x) with 1.096-1.139x per-file peak RSS in the reverse 12-round
report, `/tmp/disequality-proof-final-reverse-v2.jsonl`. The retained map-only
transaction removes that cost.

The final candidate was measured in both endpoint orders with 30 samples per
file and endpoint. No observation was removed:

| Collection order | Suite wall ratio, candidate / main | Candidate peak RSS / main |
| --- | ---: | ---: |
| main, then candidate | 0.785-1.70x; inconclusive | 1.02-1.04x across files |
| candidate, then main | 1.005-1.021x (inverse reported interval) | 1.02-1.04x across files |

The forward collection contains one 410 ms `integer_math.egg` observation;
every other candidate observation for that file was 17-22 ms. That anomaly is
retained and makes the forward confidence interval inconclusive. The reverse
collection was stable, but endpoint order still matters, so the conservative
conclusion is only that the prior repeatable 32-59% same-machine regression no
longer reproduces. The remaining wall difference is below what these short,
process-per-sample canaries resolve reliably; peak RSS is consistently 2-4%
above main. All 32 focused proof-mode regressions passed for that retained
proof implementation. Its 80 raw/desugared capture replays were the historical
all-mode relation-backed matrix; the current set-backed gate instead replays
224 supported treatments, with DE ordinary-only and EE/OEE/NEE retaining their
term/proof modes. The host
integrations still submit multi-action `(begin ...)` blocks, which deliberately
keep their full atomic snapshot; this fix therefore does not change the Propel
or EUF timing tables below.

## Historical relation-backed parameter analysis

This section records the earlier flat-relation DE implementation. It is useful
for diagnosing generic ingestion and host overhead, but it does not measure the
current set-backed DE compiler pass.

### Workload

The artifact input has 60,000 expressions paired into 30,000 constraints. The
deterministic converter expands it into 3,728,927 occurrence-preserving AST
rows and about 59 MB of TSV data. Its source SHA-256 is
`829b712812d7e1c8563e2f9c9dbd5a8b520c967086d05bc407d8f7b733f70638`.
Preprocessing is outside the timed region.

Egglog loads the relations, reconstructs `Expr` values bottom-up, traverses the
root pairs, performs `union` or `disequal`, and runs the private extension
schedule. Native wall time includes process startup and file reading; native
`full_time` begins later, so only wall-to-wall ratios are used below.

### Results

| Engine | Encoding | Wall median | Term rules | Pair rules | Disequality rules | Non-ruleset wall | Wall range |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| egglog | EE | 4,936.6 ms | 2,525.4 ms | 608.2 ms | 11.815 ms | 1,739.8 ms | 4,851.7-5,331.3 ms |
| egglog | OEE | 4,822.2 ms | 2,510.9 ms | 607.5 ms | 1.238 ms | 1,712.8 ms | 4,793.5-4,905.3 ms |
| egglog | NEE | 4,789.4 ms | 2,499.9 ms | 556.4 ms | 0.192 ms | 1,734.6 ms | 4,754.1-4,828.5 ms |
| egglog | relational DE | 4,770.7 ms | 2,485.7 ms | 566.6 ms | 2.492 ms | 1,722.7 ms | 4,767.2-4,850.2 ms |
| native egg 0.9.5 | EE | 932.8 ms | n/a | n/a | n/a | n/a | 924.1-940.6 ms |
| native patched egg | DE | 639.0 ms | n/a | n/a | n/a | n/a | 630.4-722.8 ms |

Timing-summary v4 assigns assembly, search, apply, execution, and merge to each
ruleset. Global native rebuild, command execution, frontend work, relation
loading, and process overhead remain in `non_ruleset_wall_ms`. The raw
observations for this historical tranche are in
[`relational-ratio-0.5.csv`](../../egglog-experimental/benchmarks/disequality/relational-ratio-0.5.csv).

All four egglog medians are within 166 ms. The selected disequality
representation therefore does not explain the roughly five-second runtime.
Term reconstruction costs about 2.5 seconds, pair traversal about 0.6 seconds,
and non-ruleset work about 1.7 seconds. The private disequality phase ranges
from 0.2 to 11.8 ms.

These accepted rows predate the final source-order `fail` fix. The parameter
driver is consistent, so `(check-disequalities)` executes the private schedule
directly and never enters that changed path. Two attempted reruns at the final
revision were rejected in full: another worktree overlapped the first with
compiler/benchmark processes, and the immediate follow-up remained thermally
unstable, with egglog endpoints varying from about 5 to 10 seconds while the
native endpoints stayed near their prior values. Their temporary observations
are not committed or used in the table.

The earlier removed `CompiledDisequalityWriter` established an optimistic
lower bound: direct compiled database insertion could beat both artifact
programs. It was not retained because it bypassed source typechecking and
proof instrumentation and duplicated representation-specific loading logic in
Rust. The useful conclusion is not to restore that writer, but to add a generic
typed, proof-aware bulk input path.

## Historical relation-backed Propel

This section likewise predates the set-backed DE change. The hash-identified
set-backed small and medium Propel measurements are in the follow-up section
above.

### Integration boundary

Propel uses egglog live through the Scala Native C ABI. Every graph add, union,
disequality, rebuild, clone, comparison, consistency check, and stats request
crosses that interface. This is not an offline trace replay.

### End-to-end results

| Program | Artifact precomputed native DE | Measured native DE | Measured egglog DE | Egglog / native |
| --- | ---: | ---: | ---: | ---: |
| `tip_list_append_assoc` | 85 ms | 51.6 ms (46.1-57.8) | 140.4 ms (133.3-154.1) | 2.72x |
| `tip_bin_plus_assoc` | 1.308 s | 618.9 ms (610.0-639.0) | 7.240 s (6.742-7.640) | 11.70x |
| `tip_nat_times_alt_assoc` | 8.361 s | 4.386 s (4.327-4.444) | 12.571 s (12.304-12.771) | 2.87x |

The measured native implementation is substantially faster than the artifact's
precomputed numbers on these cases. The host machine or Scala Native build
therefore does not explain the egglog gaps. Values are medians of six accepted
samples; parentheses contain the full accepted range.

The host adapter submits each flush as one `(begin ...)` command. Egglog
preserves source-command atomicity by retaining a complete `EGraph`
snapshot while that block executes. This keeps rollback correct, but persistent
tables lose their unique-owner fast path while thousands of mutations occur.
At measured revision `e7b7969`, each consistency query added two distinct
snapshots: one for complete-`fail` validation and another while its schedule
executed. The medium profile counted 1,393 such queries. Relative to the
pre-atomic `55250f3` measurements, the `e7b7969` medians increased from 101.2
ms, 3.497 s, and 6.356 s to 140.4 ms, 7.240 s, and 12.571 s. An intermediate
implementation that omitted rollback for failing schedules measured 139.5 ms,
5.797 s, and 10.842 s; those numbers are not valid final results. The observed
slowdown is consistent with retained snapshot overhead, but validation,
action-batch, and failing-child snapshots were not timed independently, so this
comparison does not isolate their costs. Since `b56a72f`, current `fail`
execution retains one outer snapshot per source child and disables inner
rollback; Propel was not remeasured after that change. A temporary diagnostic
that flattened batches into independent top-level actions was not a fix:
repeated compilation made the medium and large paths about 5.2 and 10.5 seconds
even before preserving equivalent rollback semantics.

### Diagnostic profile

An instrumented `tip_bin_plus_assoc` run at pre-merge integration revision
`55250f3` observed:

| Event | Count |
| --- | ---: |
| fresh egglog graphs | 10,357 |
| graph clones | 3,667 |
| flushes | 13,591 |
| generated operations | 60,367 |
| generated source bytes | 4,005,064 |
| pair comparisons | 17,159 |
| consistency checks | 1,393 |
| full stats scans | 620 |

Propel asks for two statistics per reduction. Each C ABI getter currently
calls `graph.stats()` independently, so 310 reductions become 620 scans.

The same instrumented egglog-DE run attributed about 59.5 ms to batch parsing,
27.6 ms to parsed term expressions, 120.2 ms to macro expansion, 534.2 ms to
resolution/typechecking, and 404.0 ms to database execution. Consistency
propagation was only 12.0 ms. These are instrumented phase totals, not additive
end-to-end components: caller/lifecycle timers overlap them and the
instrumentation itself perturbs runtime.

Across encodings on that medium case, resolve/typecheck cost 511.7-834.6 ms and
database execution cost 392.9-679.2 ms, while consistency propagation cost
6.1-42.3 ms. The frontend is often larger than execution, but execution is not
negligible. Neither is evidence that the disequality rules dominate.

### Diagnostic ablations

Temporary ablations were removed after measurement. They isolate opportunities
but are not production results and are not additive:

| Change | Before | After | Observed saving |
| --- | ---: | ---: | ---: |
| skip stats, medium case | 3.419 s | 3.115 s | 304 ms; about 235 ms differential versus native |
| cache an initialized template, no stats | 3.029 s | 2.426 s | 603 ms |
| query DE tables directly for pair comparison, cached/no stats | 2.448 s | 2.023 s | 425 ms |
| batch weak-reference cleanup | 3.419 s | 3.365 s | 54 ms |
| combined safe diagnostics, large case | 6.130 s | 5.381 s | 749 ms; native no-stats was 4.263 s |

The largest tested opportunities are initialized-graph reuse, avoiding parsed
top-level check programs for pair comparisons, and eliminating repeated stats
scans. Cleanup batching is real but secondary.

The follow-up now retains initialized-template reuse as production code. The
table above supersedes the temporary template row with balanced measurements
and separates that benefit from the direct-constructor representation.

## Historical relation-backed EUF solver

The large published inputs were not locally available for the set-backed
follow-up, so every DE timing in this section describes the earlier relation
representation.

### Workload and boundary

The solver parses SMT-LIB, translates it to CNF, enumerates MiniSat models,
clones the base term graph for each model, adds equalities/disequalities, and
checks consistency. Two files from the omitted published corpus were measured:

| Input | SHA-256 | Enumerated models |
| --- | --- | ---: |
| `uf.815405.smt2` | `957697674165b33dc541f2a905e60e7524c314e58b3d74991127d6f598a0a800` | 245 current / 246 artifact |
| `uf.614981.smt2` | `3f6de121f080be7d0b8220993fe72610a2bb50dbb80e9e8a21ef9e056335a5da` | 627 |

The one-model difference on `uf.815405` is retained as an unresolved parity
caveat, likely involving SAT-model enumeration order. The larger case matches
the artifact's 627 models exactly.

### Results without stats

| Input | Artifact precomputed native DE | Measured native DE | Measured egglog DE | Egglog / native |
| --- | ---: | ---: | ---: | ---: |
| `uf.815405` | 100.366 ms | 44.2 ms (42.6-49.5) | 541.7 ms (534.0-591.2) | 12.27x |
| `uf.614981` | 973.656 ms | 410.9 ms (391.8-435.4) | 5.203 s (5.080-5.853) | 12.66x |

As in Propel, measured native DE is substantially faster than the artifact's
precomputed result, so the environment does not explain the egglog ratio.
Values are six-sample medians with full accepted ranges. Reversing endpoint
order matters on the larger case, which is why the range is retained rather
than presenting a narrow standard deviation.

### Stats cost

On `uf.614981`, enabling stats produced these single-run results:

| Backend | Solver full time | Setup |
| --- | ---: | ---: |
| native DE | 387.892 ms | 1.425 ms |
| egglog DE | 15.404 s | 1.558 s |

Against the accepted 5.203-second no-stats median, this single egglog stats run
adds about 10.20 seconds. It is 39.71x the same single native stats run.
The solver requests stats once for each of 627 models. `graph.stats()` walks
every host term, parses/evaluates its lookup expression, computes an e-class
id, and scans extension tables. Instrumentation at revision `55250f3` counted
627 stats calls and 2,005,773 term-expression evaluations; stats consumed about
9.31 seconds of a 12.63-second diagnostic run. This is reporting overhead, not
the core theory check. The exact final pair, input hash, measured code revision,
row count, and raw-output hashes are retained in
[`reports/euf-large-stats-summary.csv`](reports/euf-large-stats-summary.csv).

### No-stats diagnostic profile

The same pre-merge instrumented large case observed:

| Event or phase | Value |
| --- | ---: |
| flushes / graph clones | 628 / 627 |
| generated operations | 403,221 |
| generated source | 22,965,948 bytes |
| batch construction / parsing | 31.9 / 206.8 ms |
| macro expansion | 62.9 ms |
| resolution and typechecking | 1,260.4 ms |
| database execution | 1,181.2 ms |
| clone time | 72.3 ms |
| consistency propagation | 33.2 ms |

Resolution/typechecking and database execution are both first-order costs at
the profiled revision. The actual extension schedule is a small fraction of
the no-stats run. The measured code also retained a rollback snapshot during
each of the 628 generated `(begin ...)` flushes. At `e7b7969`, every consistency
check cloned once for whole-body validation and once for rollback while the
private schedule ran. These snapshot classes were counted but not timed
independently, so the report treats them as additional first-order candidates
rather than assigning the complete post-`55250f3` delta to any one class. Since
`b56a72f`, current `fail` execution uses one outer source-child snapshot; EUF
was not remeasured after that change. Simply removing the block and compiling
403,221 operations as separate commands made a temporary large-case diagnostic
roughly 19 seconds, so the needed primitive is one compiled batch without a
full retained graph snapshot, not source flattening.

## Prioritized fixes

These ideas preserve the central design requirement: EE, OEE, NEE, and DE stay
self-contained compiler passes rather than becoming four Rust-side special
cases.

1. **Make stats one-pass and reusable.** Return nodes, classes, extension rows,
   and tuples from one FFI call. Cache term handles/class ids within a stable
   graph generation. This removes the clearest avoidable cost: about 10 seconds
   on the measured EUF stats run and hundreds of milliseconds in Propel.
2. **Keep typed batches; add an explicit failure contract if snapshots remain
   costly.** The host adapter now submits structured actions through
   `EGraph::run_program` without rendering and reparsing source. The clean
   follow-up improved the measured Propel medians by 1.7-4.0%, so frontend
   parsing was real but not dominant. For callers that discard a graph after
   failure, a trusted/poison-on-error batch could avoid retaining a full graph
   snapshot. A generally atomic API instead needs backend transaction support.
   Parameter analysis still needs the analogous bulk relation/input path. The
   removed representation-specific writer is not the right API.
3. **Keep initialized-schema reuse; reduce direct-schema lifecycle cost.**
   Template cloning is now implemented and improves cached Vec. Direct
   constructors expose a different cost: each operator adds a relation that
   every short-lived Propel graph must clone and rebuild. A future direct-mode
   optimization should measure a cache keyed by the operators actually used by
   a graph, or make empty relation schemas cheaper to instantiate.
4. **Keep typed pair comparison behind the selected compiler pass.** The host
   adapter now constructs equality and pair-only disequality checks as typed
   commands and shares their lowering with source programs. It still uses the
   ordinary command-processing path. A lower-level backend query saved about
   425 ms in the historical medium diagnostic, but any further shortcut must
   preserve the representation selected by the compiler pass and proof-mode
   behavior.
5. **Reduce graph lifecycle churn.** Batch host operations more aggressively
   and investigate snapshot/push-pop semantics for branch exploration where
   they preserve host behavior. Propel created over 10,000 graphs and EUF cloned
   once per SAT model.
6. **Deduplicate parameter facts where semantics permit.** The current converter
   intentionally preserves every AST occurrence. A second benchmark mode could
   hash-cons identical subtrees before relational reconstruction while keeping
   the same 30,000 root pairs. Report it separately because it changes the
   ingestion workload, not the final constraints.
7. **Do not optimize the private schedule first.** Its measured cost is too
   small to close the observed gaps. Work on ingestion, frontend reuse, stats,
   and host-query boundaries before tuning EE/OEE/NEE/DE rules.

## Reproduction

Generate parameter facts and run the interleaved benchmark using the commands
in
[`../../egglog-experimental/benchmarks/disequality/README.md`](../../egglog-experimental/benchmarks/disequality/README.md).

Build and measure the live integrations:

```sh
make -C benchmarks/disequality propel-native
cargo build --release --manifest-path benchmarks/disequality/euf-solver/Cargo.toml

PROPEL=benchmarks/disequality/inductive-prover/propel/.native/target/scala-3.4.2/propel
PROPEL_INPUT=benchmarks/disequality/inductive-prover/benchmarks/propel/tip_bin_plus_assoc.propel

hyperfine --warmup 1 --runs 3 --export-json /tmp/propel-forward.json \
  "$PROPEL -f $PROPEL_INPUT --variant de" \
  "$PROPEL -f $PROPEL_INPUT --variant egglog-de"

hyperfine --warmup 1 --runs 3 --export-json /tmp/propel-reverse.json \
  "$PROPEL -f $PROPEL_INPUT --variant egglog-de" \
  "$PROPEL -f $PROPEL_INPUT --variant de"

EUF=benchmarks/disequality/euf-solver/target/release/euf-solver
EUF_INPUT=/path/to/uf.614981.smt2

hyperfine --warmup 2 --runs 3 --export-json /tmp/euf-forward.json \
  "$EUF $EUF_INPUT --backend disegg-de" \
  "$EUF $EUF_INPUT --backend egglog-de"

hyperfine --warmup 2 --runs 3 --export-json /tmp/euf-reverse.json \
  "$EUF $EUF_INPUT --backend egglog-de" \
  "$EUF $EUF_INPUT --backend disegg-de"

"$EUF" "$EUF_INPUT" --backend disegg-de --stats
"$EUF" "$EUF_INPUT" --backend egglog-de --stats
```

Reproduce the complete direct-constructor follow-up, including reversed order,
with the committed driver. The first two executables are frozen builds from
`5069c43`; the remaining two are clean builds from measured candidate
`b87057b` (or a source-identical descendant).

```sh
benchmarks/disequality/scripts/benchmark_term_languages.sh \
  /path/to/5069c43/propel \
  "$PROPEL" \
  /path/to/5069c43/euf-solver \
  "$EUF" \
  /path/to/uf.815405.smt2 \
  /path/to/uf.614981.smt2 \
  /tmp/disequality-term-language-performance
```

Reproduce the balanced proof-mode regression check:

```sh
CANARIES="egglog/tests/web-demo/rw-analysis.egg \
egglog/tests/web-demo/resolution.egg egglog/tests/integer_math.egg"

uv run --locked ./bench.py \
  --target final=@fff36169eb9527ee817477bceecf371ddbe67b8c \
  --treatment proofs --compare-target main=@fdd4eac12c13 \
  --compare-treatment proofs --rounds 30 --timeout-sec 120 --force-run \
  --report /tmp/disequality-proof-final-forward-v4.jsonl --format markdown \
  $CANARIES

uv run --locked ./bench.py \
  --target main=@fdd4eac12c13 --treatment proofs \
  --compare-target final=@fff36169eb9527ee817477bceecf371ddbe67b8c \
  --compare-treatment proofs --rounds 30 --timeout-sec 120 --force-run \
  --report /tmp/disequality-proof-final-reverse-v4.jsonl --format markdown \
  $CANARIES
```

Repeat the Propel pair with `tip_list_append_assoc.propel` and
`tip_nat_times_alt_assoc.propel`, and the EUF pair with `uf.815405.smt2`.
Accept every sample from an otherwise uncontended invocation; reject the whole
invocation if another build or test process overlaps it. The JSON paths above
are disposable measurement output and are not committed.

The large EUF files must be extracted from the verified Zenodo archive. The
repository's focused gate does not require or download them.
