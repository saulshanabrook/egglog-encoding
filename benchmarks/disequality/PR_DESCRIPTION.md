## Review stack

This is Stage 2 of a two-PR review. Stage 1, [PR
#82](https://github.com/saulshanabrook/egglog-encoding/pull/82), contains the
verbatim paper artifact and the separately documented `disegg` reconstruction.
This PR is based on that branch, so its **Files changed** view contains only the
egglog implementation, adaptations, tests, captures, and reports.

Of the 213 verbatim imported files, this stage modifies only 11:

- the artifact-level README;
- the EUF manifest, lockfile, README, and solver; and
- the Propel README, build, language adapter, equality engine, CLI, and
  experiment runner.

The other 202 imported files and all 40 files in the reconstructed `disegg/`
tree are absent from this stage's diff. The exact boundary and verification
command are in `benchmarks/disequality/ARTIFACT_IMPORT.md`.

## Feature

This PR adds an encoding-neutral disequality surface to
`egglog-experimental`:

```lisp
(disequal lhs rhs)              ; action, including rule heads and batches
(check-disequal lhs rhs)        ; propagate, then require this pair to be unequal
(check-known-disequal lhs rhs)  ; query this pair without global propagation
(check-disequalities)           ; propagate and reject any collapsed disequality
```

`--disequality-encoding` selects a self-contained compiler pass for each
operand sort. None of the encodings adds disequality state or operations to
union-find, e-class storage, or congruence closure.

| Flag | Compiled representation | Contradiction criterion | Modes |
| --- | --- | --- | --- |
| `ee` | Paper-style equality term equated with false, plus the five EE rules | true and false become equal | ordinary, term, proofs, proof testing, proof extraction |
| `oee` | Equality term equated with false, plus reduced OEE propagation | a reflexive equality term becomes false | ordinary, term, proofs, proof testing, proof extraction |
| `nee` | Private binary `ne(lhs, rhs)` relation | canonicalization produces `ne(x, x)` | ordinary, term, proofs, proof testing, proof extraction |
| `de` | Symmetric per-e-class `Set` of disequal neighbors merged with `set-union` | a canonical class occurs in its own neighbor set | ordinary only |

NEE intentionally stores one oriented relation fact and needs no symmetry
rule. This is an egglog-specific relational realization of the paper's private
`ne` e-node: it preserves the self-loop criterion but does not create the
otherwise-unused result e-class counted by the paper's NEE theorem.

DE is closer to the paper's adjacency-map interface than the earlier flat
relation: each insertion writes both orientations, key collisions merge sets,
and container rebuild canonicalizes members. It remains a compiled egglog
encoding, not the paper artifact's patched native edge storage. DE is ordinary
mode only because term/proof encoding does not yet support its set-valued
custom merge; unsupported combinations fail explicitly.

## Why this is in egglog

The paper presents EE, OEE, and NEE as term encodings and DE as an e-graph
extension. This PR tests the broader compiler-pass story: a common surface can
lower to all four representations using ordinary egglog declarations, actions,
rules, schedules, functions, and containers. The same `.egg` program therefore
runs under every encoding, and EE/OEE/NEE also compose with term and proof
encoding without changing their implementation.

## What changed

### Compiler support

- infer the operand sort and lazily generate private support declarations and
  schedules for `disequal` and the three checks;
- support `disequal` at top level, in action batches, and in rule heads;
- preserve source order and rollback for `fail`, including typed action blocks
  used by generated host replays;
- allow transactional `Command::Actions` under proof-mode `fail` while keeping
  unsupported top-level `begin`/`LetBegin` cases explicit; and
- publish container unions before custom function merges consume set values,
  fixing the normal-mode rebuild case exposed by set-backed DE.

### AST-first host integration

The shared Rust adapter under `benchmarks/disequality/egglog-backend/` no longer
keeps a parallel operation language or sends generated source through
`parse_and_run_program` during solving.

- Term insertion, union, and disequality calls append real
  `egglog::ast::Action` values immediately.
- A flush submits one `Command::Actions` batch through `EGraph::run_program`.
- Equality, known-disequality, and consistency checks submit typed `Command`
  values and return ordered `CommandOutput` values.
- Only the exact expected `CheckError` and `ExpectFail` variants become query
  outcomes. Every other egglog error remains fatal and is not recorded.
- Pair-only `check-known-disequal` remains separate from global propagation so
  Propel can query one pair after an unrelated branch contradiction.

Recording is opt-in for captures. It stores successful commands, expected
query failures, outputs, and host lifecycle observations in persistent trace
chunks. Clones share their history prefix, pending actions are recorded before
a clone without executing the parent, and descendants remain isolated. Source
is rendered from AST `Display`; expected failed queries receive a `fail`
wrapper, so each capture is a complete runnable replay. Rebuild, clone, and
stats observations remain comments because they are host operations rather
than egglog commands.

The EUF solver uses the Rust API directly. Propel uses a focused,
panic-contained C ABI whose opaque result has stable `success`, `check_failed`,
`expect_fail_failed`, and `error` tags plus ordered output kind/text accessors.
Scala maps those tags to an ADT rather than parsing diagnostics. Source and
desugared source cross the ABI as owned UTF-8 values; Scala owns file output,
and the Rust ABI accepts no output paths.

Both integrations retain the paper-faithful generic
`BenchmarkNode(String, Vec)` runtime default. `--term-language direct` remains
an explicit, tested alternative that generates real constructors from EUF
declarations or Propel's parsed language. Captures use direct mode because it
is easier to review against the source language.

## Paper case studies

### Parameter analysis

The existing `.egg` benchmark converts the artifact's 60,000 expressions and
30,000 pairs into ignored, regenerable TSV relations. Rules reconstruct
3,728,927 occurrence rows, traverse the pair table, invoke `union` or
`disequal`, and run the selected private schedule. Generated TSV files are not
tracked.

### EUF solver

The integration retains the artifact's SMT parser, normalization and CNF
pipeline, MiniSat model enumeration, native egg EE, and patched-egg DE. Four
`egglog-*` backends clone the base graph for each model, apply true equalities
as unions and false equalities as disequalities, and issue a structured global
consistency command. Focused SAT, congruence-UNSAT, and Boolean-congruence-UNSAT
fixtures agree across all six backends.

Vec remains the default because it matches the paper's untyped `SymbolLang`
baseline. Direct mode turns declared constants and functions into real
constructors and reserves `Atom(String)` for generated names. Both modes erase
SMT sorts into one e-graph term sort. The complete 7,591-file corpus is not
committed; two published stress inputs are used in the performance gate.

### Propel

All three native Scala variants remain available, and the four `egglog-*`
variants replace Propel's live add/union/disequal/saturate/query boundary with
the shared backend. Scala interprets structured command status to implement
`Equal`, `Unequal`, `Indeterminate`, and contradiction behavior.

A bounded 10-second audit of all 128 imported programs keeps timeout rows
unknown. On the final Vec implementation, all 332 directly comparable
egglog/native outcomes match; 81 programs complete all five selected variants
and 196 individual runs time out. Direct mode matches all 251 comparable
outcomes; 59 programs complete all five variants and 280 individual runs time
out. Neither audit has an execution error.

## Inspectable generated programs

`egglog-experimental/tests/disequality/` contains seven encoding-independent
programs with source provenance:

- Figure 2 and three compact examples from the artifact;
- the complete parameter-analysis driver;
- one direct-constructor EUF SAT-model capture; and
- graph 42 of 52 from Propel's `gset_comm` run, selected because it exercises
  an individual `check-known-disequal` query.

The adjacent `snapshots/` directory commits the actual EE, OEE, NEE, and DE
desugaring of every program: 28 desugared files plus a hash manifest. The
generator reruns both host integrations and checks 224 treatments. All four
encodings run normally; EE/OEE/NEE additionally run under term, proofs, proof
testing, and proof extraction. A Rust regression independently desugars,
byte-compares, and replays the same supported matrix.

These captures are executable tests, not reconstructed pseudocode. Mutation
ASTs render directly; expected query failures render inside `fail`; host clone,
rebuild, and stats boundaries remain explicit comments.

## Performance

The final gate compares clean AST-first commit `069d9ac4` with clean merged
baseline `4737838d` in forward and exact reverse endpoint order, using the Vec
term language. EUF omits `--stats`, while Propel retains its normal
per-reduction statistics collection. The predeclared blocker was a candidate
slowdown above 10% in both orders.

| Workload | Encoding | Forward delta | Reverse delta |
| --- | --- | ---: | ---: |
| Propel `gset_comm` | DE | +4.05% | +4.79% |
| Propel `gset_comm` | NEE | +2.61% | +1.27% |
| Propel `tip_bin_plus_assoc` | DE | +3.68% | +5.42% |
| Propel `tip_bin_plus_assoc` | NEE | +5.18% | +5.16% |
| EUF `uf.815405` | DE | +1.97% | +1.50% |
| EUF `uf.815405` | NEE | +3.04% | -0.66% |
| EUF `uf.614981` | DE | -1.03% | -5.80% |
| EUF `uf.614981` | NEE | +2.82% | +2.94% |

The gate passes; the largest directional slowdown is 5.42%. Negative deltas
are not presented as speedups because several reverse-order baseline arms are
visibly noisy.

On candidate NEE `gset_comm`, enabling `--emit-source-dir` adds 16.06% in
forward order and 18.25% in reverse. That separate ablation includes trace
construction, AST rendering, desugaring, and 104 file writes. Ordinary runs do
not retain the trace.

Exact revisions, executable/input hashes, means, commands, raw-output hashes,
and limitations are in
`benchmarks/disequality/reports/ast-first-host/README.md`. Raw Hyperfine JSON
stays under `/tmp`. The broader historical comparison against native paper
engines and the remaining optimization ideas are in
`benchmarks/disequality/PERFORMANCE_ANALYSIS.md`; this PR does not claim native
performance parity.

## Provenance and limits

- Stage 1 commit `1cc22b6c` imports 213 selected files byte-for-byte from Zenodo record
  [13938878](https://doi.org/10.5281/zenodo.13938878); the import manifest
  accounts for every included and excluded member.
- Stage 1 commit `c88505be` reconstructs the artifact's missing `disegg` checkout from
  egg 0.9.5 plus the archived patch.
- DE is a container-backed compiler encoding and remains normal-mode only.
- The full EUF corpus is neither committed nor claimed as fully validated.
- Propel timeout rows are unknown, not matches.
- `uf.815405` enumerates 245 current models versus 246 in the artifact result;
  that parity difference remains unresolved.
- Captures replay egglog commands and observed outcomes; they are not separate
  host-level proof certificates.

## Validation

The final validation gate is:

```sh
make -C benchmarks/disequality check  # Rust/C ABI/EUF/Scala/parity/snapshots
make check                            # full repository tests and nits
make benchmark-smoke                  # 20 off/proofs benchmark canaries
git diff --check
```

Focused coverage includes pending AST batches, submitted-command identity,
expected and unexpected error recording, clone/pending ordering, shared-history
isolation, all C ABI status/output/ownership/null/panic cases, Scala three-way
comparison and contradiction behavior, Vec/direct terms, source ownership,
EUF backend agreement, and the complete 224-treatment snapshot matrix.
