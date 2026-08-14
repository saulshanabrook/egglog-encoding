# Disequality case-study performance analysis

Run date: 2026-08-14 (America/New_York)

This report analyzes the egglog implementations of the three case studies from
*Dis/Equality Graphs*: parameter analysis, Propel, and the EUF solver. It
separates end-to-end measurements from diagnostic instrumentation and avoids
attributing generic host/API overhead to the compiled disequality rules.

## Environment and method

- Apple M4, 16 GiB RAM, arm64 macOS (Darwin 25.6.0)
- Rust 1.91.0, Cargo 1.91.0, uv 0.12.3
- merged base `origin/main` at `ffb8ae435bd6421077b1c15826f32a6aeecf5b1b`
- final Propel and EUF measurements at code commit
  `e7b796940dbc148c3a97cc4a421a6669fa441f0e`, after merging `origin/main` at
  `ffb8ae435bd6421077b1c15826f32a6aeecf5b1b`
- parameter-analysis measurements at
  `88c40cf6a298a8c503a741b8e736d5cc7498f348`; the later commit changes live
  `fail` handling, which the consistent parameter workload does not execute
- release builds for timed Rust and Scala Native executables
- six accepted samples per Propel and EUF endpoint: two three-run Hyperfine
  invocations with endpoint order reversed, after one Propel warmup and two EUF
  warmups
- three interleaved endpoint rounds for parameter analysis

The commands below regenerate the results; generated parameter TSV files and
the large EUF corpus are intentionally not committed. Six samples are enough to
identify the large cost centers here, but not for a publication-quality
statistical claim. Ranges are descriptive. Complete timing attempts that
overlapped Rust builds, the independent reviewer's validation, or another
worktree's concurrent benchmark and compiler processes were rejected before
analysis. No sample inside an accepted invocation was discarded.

## Summary

| Case study | Comparison | Current result | Observed costs and candidates |
| --- | --- | ---: | --- |
| Parameter analysis | egglog EE / native EE | 5.29x wall | 3.7M occurrence rows, term reconstruction, and non-ruleset work |
| Parameter analysis | egglog DE / native DE | 7.47x wall | same; DE propagation itself is 2.5 ms |
| Propel, small | egglog DE / native DE | 2.72x wall | fixed graph lifecycle, host calls, and atomic action batches |
| Propel, medium | egglog DE / native DE | 11.70x wall | repeated creation, measured frontend/database/query/stats work; rollback snapshots are an unisolated candidate |
| Propel, large | egglog DE / native DE | 2.87x wall | native Propel work; rollback snapshots are an unisolated candidate |
| EUF, 245 models | egglog DE / native DE | 12.27x wall | one cloned graph and atomic generated-command batch per SAT model |
| EUF, 627 models | egglog DE / native DE | 12.66x wall | 403K operations across 628 atomic flushes, frontend work, and database execution |
| EUF, 627 models with stats | egglog DE / native DE | 39.71x reported full time | atomic batches plus 627 full graph scans and about 2M term lookups |

The answer to "typechecking or engine?" is workload-dependent:

- parameter analysis is dominated by relational term reconstruction plus
  process/input/frontend work;
- current Propel and EUF retain a complete command snapshot across every
  `(begin ...)` batch so a failed action block can roll back atomically;
- each live `fail` also clones the graph once to validate its complete body and
  retains a second snapshot while executing a potentially failing child, so a
  partially mutating schedule can be rolled back correctly;
- at the profiled pre-atomic revision, repeated parsing/typechecking and
  database execution were both material;
- EUF with `--stats` is dominated by repeated graph scans; and
- the encoding-specific `@disequality` schedule is small in all measured
  parameter-analysis encodings and in the instrumented host integrations.

## Parameter analysis

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
loading, and process overhead remain in `non_ruleset_wall_ms`. The current raw
observations are in
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

## Propel

### Integration boundary

Propel uses egglog live through the Scala Native C ABI. Every graph add, union,
disequality, rebuild, clone, comparison, consistency check, and stats request
crosses that interface. This is not an offline trace replay.

### End-to-end results

| Program | Artifact precomputed native DE | Current native DE | Current egglog DE | Egglog / current native |
| --- | ---: | ---: | ---: | ---: |
| `tip_list_append_assoc` | 85 ms | 51.6 ms (46.1-57.8) | 140.4 ms (133.3-154.1) | 2.72x |
| `tip_bin_plus_assoc` | 1.308 s | 618.9 ms (610.0-639.0) | 7.240 s (6.742-7.640) | 11.70x |
| `tip_nat_times_alt_assoc` | 8.361 s | 4.386 s (4.327-4.444) | 12.571 s (12.304-12.771) | 2.87x |

The current native implementation is substantially faster than the artifact's
precomputed numbers on these cases. The host machine or Scala Native build
therefore does not explain the egglog gaps. Values are medians of six accepted
samples; parentheses contain the full accepted range.

The host adapter submits each flush as one `(begin ...)` command. Current
egglog preserves source-command atomicity by retaining a complete `EGraph`
snapshot while that block executes. This keeps rollback correct, but persistent
tables lose their unique-owner fast path while thousands of mutations occur.
Each consistency query adds two distinct snapshots: one validates the complete
`fail` body, and another remains live while its schedule executes so a schedule
that mutates and then errors can be rolled back. The medium profile counted
1,393 such queries. Relative to the pre-atomic `55250f3` measurements, the
final egglog medians increased from 101.2 ms, 3.497 s, and 6.356 s to 140.4 ms,
7.240 s, and 12.571 s. An intermediate implementation that omitted rollback
for failing schedules measured 139.5 ms, 5.797 s, and 10.842 s; those numbers
are not valid final results. The observed slowdown is consistent with retained
snapshot overhead, but validation, action-batch, and failing-child snapshots
were not timed independently, so this comparison does not isolate their costs.
A temporary diagnostic that flattened batches into independent top-level
actions was not a fix: repeated compilation made the medium and large paths
about 5.2 and 10.5 seconds even before preserving equivalent rollback
semantics.

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

## EUF solver

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

| Input | Artifact precomputed native DE | Current native DE | Current egglog DE | Egglog / current native |
| --- | ---: | ---: | ---: | ---: |
| `uf.815405` | 100.366 ms | 44.2 ms (42.6-49.5) | 541.7 ms (534.0-591.2) | 12.27x |
| `uf.614981` | 973.656 ms | 410.9 ms (391.8-435.4) | 5.203 s (5.080-5.853) | 12.66x |

As in Propel, current native DE is substantially faster than the artifact's
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
the no-stats run. Current code also retains a rollback snapshot during each of
the 628 generated `(begin ...)` flushes. Every consistency check clones once
for whole-body validation and once for rollback while the private schedule
runs. These snapshot classes were counted but not timed independently, so the
report treats them as additional first-order candidates rather than assigning
the complete post-`55250f3` delta to any one class. Simply removing the block
and compiling 403,221 operations as separate commands made a temporary
large-case diagnostic roughly 19 seconds, so the needed primitive is one
compiled batch without a full retained graph snapshot, not source flattening.

## Prioritized fixes

These ideas preserve the central design requirement: EE, OEE, NEE, and DE stay
self-contained compiler passes rather than becoming four Rust-side special
cases.

1. **Make stats one-pass and reusable.** Return nodes, classes, extension rows,
   and tuples from one FFI call. Cache term handles/class ids within a stable
   graph generation. This removes the clearest avoidable cost: about 10 seconds
   on the measured EUF stats run and hundreds of milliseconds in Propel.
2. **Add a typed, proof-aware batch API with an explicit failure contract.**
   Submit already structured host operations without reparsing generated source
   on every flush, while still routing actions through command-macro expansion,
   typechecking, and proof instrumentation. For callers that discard a graph
   after failure, a trusted/poison-on-error batch can retain one compiled action
   batch without cloning the full graph. A generally atomic API instead needs
   backend transaction support. Parameter analysis needs the analogous bulk
   relation/input path. The removed representation-specific writer is not the
   right API.
3. **Cache the initialized generic-language graph.** Clone a compiled prelude
   or instantiate a reusable database template rather than resolving the same
   declarations for every short-lived Propel graph. The diagnostic lower bound
   saved about 603 ms on the medium case.
4. **Expose typed pair comparison.** Avoid constructing and parsing tiny check
   programs for every `equal`/`unequal` query. A backend query over the generated
   representation saved about 425 ms in the medium diagnostic, but the API must
   remain generated from the selected compiler pass.
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

Repeat the Propel pair with `tip_list_append_assoc.propel` and
`tip_nat_times_alt_assoc.propel`, and the EUF pair with `uf.815405.smt2`.
Accept every sample from an otherwise uncontended invocation; reject the whole
invocation if another build or test process overlaps it. The JSON paths above
are disposable measurement output and are not committed.

The large EUF files must be extracted from the verified Zenodo archive. The
repository's focused gate does not require or download them.
