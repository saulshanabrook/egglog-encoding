# Disequality fixtures

Every top-level `.egg` file in this directory is readable source using the
encoding-neutral `disequal` and `check-disequalities` surface syntax. Source
comments identify the paper, artifact file, SMT fixture, or Propel graph from
which each program was derived.

The three benchmark-facing programs are:

- `euf-sat.egg`: the single MiniSat candidate assignment from
  `euf-solver/tests/sat.smt2`;
- `propel-gset-comm.egg`: zero-based graph index 42 (43rd of 52) from
  `gset_comm.propel`, selected
  because it exercises Propel's individual disequality query; and
- `parameter-analysis.egg`: the relational driver for the artifact's
  `parameter-analysis/exprs.in` workload.

The EUF and Propel files are generated outcome-preserving chronological host
replays, not final-state reconstructions. Live mutations and queries are real
`egglog::ast` commands submitted through `EGraph::run_program`; the exporter
renders those recorded ASTs rather than reconstructing source from an operation
log. Expected failed queries are wrapped in `fail`, keeping the captured file
runnable with the observed outcome. Rebuild, clone, and stats events are host
lifecycle observations and remain comments. Source export is opt-in and does
not append synthetic witnesses or checks. `(check-known-disequal lhs rhs)` is
the pair-only host probe used by the Propel replay. Unlike
`(check-disequal lhs rhs)`, it does not run the global contradiction schedule
first.

The other four files are Figure 2 plus compact, illustrative artifact
adaptations; their opening comments identify any vocabulary or control-flow
change. `parameter-analysis.egg` needs TSV inputs. Its Rust regression creates a
small deterministic fact directory; `make -C benchmarks/disequality
prepare-parameter-facts` generates the full input under `target/disequality/`.

[`snapshots/`](snapshots/) contains the fully desugared EE, OEE, NEE, and DE
program for every top-level source file. The Rust regression independently
desugars each source, checks the committed bytes, and replays every source and
snapshot in ordinary mode. Proof and term-encoding composition is intentionally
deferred.

Run the focused regression with:

```sh
cargo test -p egglog-experimental disequality_fixture --lib
```

Regenerate the source captures and all desugared snapshots with:

```sh
make -C benchmarks/disequality update-snapshots
```

Use `make -C benchmarks/disequality snapshots` to check committed bytes without
updating them.
