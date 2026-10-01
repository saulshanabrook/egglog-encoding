# Math end-state size verification

Verified on 2026-09-21 after the fixed workload's 11 iterations and terminal
check or proof extraction. The four conditions in the Math figure have the
same logical size:

| Engine | Proof setting | Math nodes | Math e-classes |
| --- | --- | ---: | ---: |
| Egg | Off | 1,047,896 | 443,832 |
| Egg | Recording + extraction | 1,047,896 | 443,832 |
| Egglog | Off | 1,047,896 | 443,832 |
| Egglog | Recording + extraction | 1,047,896 | 443,832 |

Every shared constructor matches individually across all four conditions:

| Constructor | Nodes in each condition |
| --- | ---: |
| Add | 641,743 |
| Const | 5 |
| Cos | 1 |
| Diff | 13,504 |
| Div | 3 |
| Integral | 32,434 |
| Ln | 1 |
| Mul | 345,075 |
| Pow | 2 |
| Sin | 1 |
| Sqrt | 1 |
| Sub | 15,123 |
| Var | 3 |
| **Total** | **1,047,896** |

## What is counted

Egg nodes are the nodes in its rebuilt e-classes, counted through
`EGraph::classes()`. This is the meaning of `report.egraph_nodes`, rather than
Egg's hashcons-index size returned by `total_size()`. Egg's `Constant` and
`Symbol` variants correspond to Egglog's `Const` and `Var` constructors.

Egglog counts come from `print_size`: in proof mode it resolves each original
constructor to its canonical view table. Hidden proof tables, permanent term
records, internal bindings, and primitive values are excluded. Counting the
physical tables under the original constructor names would be misleading
under term encoding because they retain historical term representatives.

Egg e-classes are counted with `number_of_classes()`. Egglog classes were
counted in a separate diagnostic invocation: after the original workload,
a dedicated ruleset inserts the canonical result of each of the 13
constructors into a unary `SeenMathEClass(Math)` relation. The relation's size
counts distinct Math classes. All 13 constructor counts were checked before
and after this diagnostic and remained unchanged. Diagnostic work is outside
the recorded performance measurements.

## Evidence and regression

Fresh Egglog CLI runs used the actual plotted release executable, with the
original workload followed by `(print-size)`, both without proof flags and
with `--proof-extraction`. The workload and both executable SHA-256 values
match the four groups in `egg-vs-egglog.data.json`:

| Input | SHA-256 |
| --- | --- |
| Math workload | `29e120079c588d0bf079891b393ae041ec4e1a45d369114cde3754e5c6b7878f` |
| Egg executable | `41d3799cd77d4c9370b1a1067ff29f10b8fa1525f64141d838c41f2ba083bb81` |
| Egglog executable | `fcfc0957eccbb1b6aa05896c5c38f360ea13edf69f9adf9aa154f192c0c7994b` |

The existing test in `egg-math-benchmark/src/main.rs` now checks each named
constructor after the real Egg execution and proof-postprocessing path, for
`Off`, `Extract`, and `Check`. Its inspection hook is compiled only for tests,
so it adds no work to the benchmark executable. Run it with:

```sh
cargo test -p egg-math-benchmark -- --nocapture
```

For Egglog, the Rust test uses its native mode for `Off` and strict proof
testing for `Extract` and `Check`. The extraction-only configuration is
crate-private, so the exact timed Egglog mode is verified separately through
its public CLI. Strict proof tests additionally validate the terminal proof.
All three Rust cases produced the counts above, and both exact Egglog CLI
modes produced the same constructor and class counts.

Validation passed: the focused parity test, formatting, scoped Clippy, and
the complete root `make check` suite.

Local diagnostic inputs, original outputs, identity hashes, and test logs are
archived in `review/math-size-parity/`. No benchmark observations or figure
data were changed for these checks.

This establishes matching logical graph sizes and the same checked terminal
equality for this workload. It does not establish graph isomorphism or
identical internal work: scheduling, matching, and proof bookkeeping can still
differ even when all final counts agree.
