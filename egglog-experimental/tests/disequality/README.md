# Disequality fixtures

Every top-level `.egg` file in this directory is readable source using the
encoding-neutral `disequal` and `check-disequalities` surface syntax. Source
comments identify the paper, artifact file, SMT fixture, or Propel graph from
which each program was derived.

The three full benchmark-facing programs are:

- `euf-sat.egg`: the single MiniSat model from `euf-solver/tests/sat.smt2`;
- `propel-gset-comm.egg`: graph 42 of 52 from `gset_comm.propel`, selected
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

The other four files are compact examples from Figure 2 and the published
artifact. `parameter-analysis.egg` needs TSV inputs; its Rust regression creates
a small deterministic fact directory, while benchmark runs use the generated
full-size facts under `egglog-experimental/benchmarks/disequality/`.

[`snapshots/`](snapshots/) contains the fully desugared EE, OEE, NEE, and DE
program for every top-level source file. The Rust regression enumerates these
files, independently desugars each source, checks the committed bytes, and
replays every EE, OEE, and NEE expansion in ordinary, term, proofs,
proof-testing, and proof-extraction modes. DE expansions replay in ordinary
mode only because their set-valued custom merge is not yet supported by
term/proof encoding.

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
