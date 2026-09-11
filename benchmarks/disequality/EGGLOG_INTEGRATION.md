# Dis/Equality Graphs egglog integration

Run date: 2026-09-11

This stage implements and evaluates the four encodings from *Dis/Equality
Graphs* in ordinary egglog execution:

| Flag | Encoding | Generated representation |
| --- | --- | --- |
| `ee` | Equality embedding | `eq(x, y) = false` plus the paper's five propagation rules |
| `oee` | Optimized equality embedding | Equality terms, reduced propagation, and a reflexive contradiction rule |
| `nee` | Negated equality embedding | A private `ne(x, y)` relation and a reflexive contradiction rule |
| `de` | Disequality edges | A function from each e-class to a merged `Set` of disequal neighbors |

All four are compiler passes. They add ordinary egglog declarations, actions,
rules, and a private saturating schedule; they do not modify union-find,
e-class storage, or congruence closure.

## Review boundary and provenance

[PR #82](https://github.com/saulshanabrook/egglog-encoding/pull/82) is the
unchanged first stage. Its import commit
`1cc22b6c09dde6642435b14330751f0a2c91453c` copies 213 selected files from
[Zenodo record 13938878](https://doi.org/10.5281/zenodo.13938878) byte for byte.
[`IMPORT_MANIFEST.json`](IMPORT_MANIFEST.json) records each imported member and
accounts for all 7,608 exclusions. The archive SHA-256 is
`3e9080ca461457af0a10cfc433a5150952f82f752b4c316df1e03236d93599c4`.

This second stage modifies only seven imported artifact files:

- EUF: `Cargo.toml`, `Cargo.lock`, and `euf-solver.rs`;
- Propel: `build.sbt`, `Language.scala`, `equality.scala`, and `propel.scala`.

The shared backend, Scala bridge, fixtures, tests, and reports are new files.
The imported READMEs and `scripts/modules/experiment.py` remain unchanged, so a
reviewer can first inspect the paper artifact in PR #82 and then review only the
integration in this stage. Verify the import with:

```sh
make -C benchmarks/disequality import-check
```

The command verifies a cached or downloaded 795 MB archive. It never executes
artifact code.

## Egglog surface and lowering

The source interface is independent of the selected representation:

```lisp
(datatype Term (A) (B) (F Term))
(disequal (F (A)) (F (B)))
(union (A) (B))
(fail (check-disequalities))
```

`disequal` is an action and is valid at top level, in a `begin`, or in a rule
head. Both operands must have the same unionable e-sort. Generated support is
sort-specific and uses readable private names such as
`@disequality-ne-Term`. The propagation rules live in the private
`@disequality` ruleset, so an ordinary `(run)` does not invoke them.

The queries have deliberately different behavior:

- `(check-disequalities)` saturates the private ruleset and reports a global
  contradiction.
- `(check-disequal a b)` propagates, then checks one pair.
- `(check-known-disequal a b)` checks one already-propagated pair without first
  running the global schedule. Propel needs this after an unrelated branch has
  contradicted.

The NEE implementation uses an egglog relation rather than adding a marker
e-node to the operand sort. Relation arguments canonicalize with their
e-classes, so `ne(a, b)` still becomes the contradictory `ne(x, x)` after a
union. This preserves the consistency behavior but does not preserve the
paper's NEE e-class-count theorem. DE is likewise an egglog realization of the
paper interface, not its patched storage layout: each insertion updates both
orientations of an e-class-to-neighbor-set function, and rebuild canonicalizes
keys and set members.

Disequality is currently a normal-mode experiment. An explicit
`--disequality-encoding` is rejected with `--term-encoding`, `--proofs`,
`--proof-testing`, or `--proof-extraction`. Existing term/proof behavior for
programs that do not select disequality is unchanged. Proof composition is a
separate follow-up rather than part of this first reproduction.

## Host adapter

[`egglog-backend`](egglog-backend/) is shared by the Rust EUF solver and Scala
Native Propel integration. Hosts construct actual `egglog::ast::Action` and
`Command` values. A flush sends one `Command::Actions` batch through
`EGraph::run_program`; no live path prints and reparses egglog source. Equality,
known-disequality, and consistency queries also use typed commands. Rust
classifies `Result<Vec<CommandOutput>, Error>` by concrete error variant, so an
expected failed check is data while every other error is fatal.

The focused C ABI exposes opaque graph/template handles, term construction,
mutation, clone/rebuild, query commands, counts, and source export. Command
results contain only a stable status tag and error text because Propel's current
commands have no payload. Scala maps those tags to an ADT; it never parses
diagnostic text to decide equality or consistency.

Templates compile the schema once and are always reused by Propel's many
short-lived graphs. Two term representations remain available:

- `vec` is the default and matches the paper's untyped `SymbolLang` shape with
  one operator-name-plus-children constructor;
- `direct` is an explicit ablation that creates one egglog constructor per
  declared source operator. Only dynamic variables and generated identifiers
  use `Atom(String)`.

Source recording is opt-in. Successful AST commands and expected query failures
are retained in a persistent shared history; graph clones share their prefix.
Rendering uses AST `Display`, and expected failures receive an enclosing
`fail`, producing an executable replay. Clone, rebuild, and statistics events
remain comments because they are host lifecycle operations rather than egglog
commands. Normal benchmark runs do not retain this history.

## Paper case studies

### Parameter analysis

The public `.egg` driver reconstructs the artifact's 60,000 expressions from
TSV relations, traverses 30,000 pairs, issues `union` or `disequal`, and invokes
the private schedule. Inputs and the native EE/DE programs are extracted only
from named, hash-verified archive members. The generated Cargo manifest changes
the artifact's absolute `/disegg/` dependency to the reconstructed checkout in
this repository; the generated manifest records both hashes.

```sh
make -C benchmarks/disequality prepare-parameter-facts
make -C benchmarks/disequality parameter-analysis
```

Facts and native builds live under `target/disequality/`. Interleaved timing
rows go to `/tmp/egglog-disequality-parameter-analysis.csv` by default.

### EUF solver

The integration preserves the artifact's SMT-LIB parser, normalization and CNF
pipeline, MiniSat candidate-assignment enumeration, native egg EE backend, and patched-egg DE
backend. It adds `egglog-ee`, `egglog-oee`, `egglog-nee`, and `egglog-de`.
For each SAT assignment, the solver clones the base term graph, maps true
equality literals to `union`, maps false literals to `disequal`, and checks
consistency live.

Vec is the paper-faithful default. `--term-language direct` uses constructors
derived from preserved SMT declarations. Both modes intentionally erase SMT
sorts into one e-graph sort. The native DE and egglog backends add `true !=
false`; the published native DE code omitted this edge and otherwise accepts a
Boolean-congruence counterexample, so the correction is explicit and tested.

The 7,591-file EUF corpus is not committed. The target below extracts the
recorded `uf.614981.smt2` member, runs the live solver, and writes only its
first MiniSat candidate assignment as a 5,150-line raw trace plus its
desugared form under `target/disequality/`:

```sh
make -C benchmarks/disequality generate-euf-capture
make -C benchmarks/disequality replay-generated-euf
```

The replay target runs the encoding-neutral source under EE, OEE, NEE, and DE,
then runs the generated DE desugaring through core egglog.

### Propel

Propel's original equality-graph calls route through
[`EqualityGraph.scala`](inductive-prover/propel/src/main/scala/propel/evaluator/EqualityGraph.scala).
The native `de`, `ee`, and `nee` implementations remain available beside the
four `egglog-*` variants. Scala Native calls the Rust adapter in process; JVM
and JavaScript builds retain native Propel and reject egglog variants at
runtime.

```sh
make -C benchmarks/disequality propel-smoke
make -C benchmarks/disequality propel-parity
```

The smoke test runs all seven backends on `gset_comm` and both term languages
on selected programs. The bounded parity audit compares completed rows against
native DE across all 128 imported programs. Timeouts remain unknown; semantic
mismatches and execution errors always fail. Its JSON output defaults to
`/tmp/egglog-disequality-propel-parity.json`.

## Reviewable fixtures

[`egglog-experimental/tests/disequality`](../../egglog-experimental/tests/disequality/)
contains seven human-readable, encoding-neutral `.egg` programs. They cover
Figure 2, compact artifact examples, the parameter driver, one EUF model, and a
Propel graph with an individual disequality query. Opening comments identify
their source. The nested directory contains 28 committed desugarings: one EE,
OEE, NEE, and DE result per source. All 35 files replay in ordinary mode.

```sh
make -C benchmarks/disequality snapshots        # check and replay
make -C benchmarks/disequality update-snapshots # regenerate
```

## Validation boundary

`make -C benchmarks/disequality check` covers the compiler pass, C ABI, EUF
fixtures, Scala JVM/native compilation, Propel smoke cases, snapshot identity,
and normal-mode replay. The root `make check` and `make benchmark-smoke` cover
repository integration.

The evidence does not establish a formal correctness proof. The full EUF
corpus is not part of the focused gate, bounded Propel timeouts remain unknown,
NEE and DE deliberately use egglog-native representations rather than the
paper's storage layout, and proof/term-encoding composition is deferred. See
[`PERFORMANCE_ANALYSIS.md`](PERFORMANCE_ANALYSIS.md) for measured overhead and
optimization candidates.
