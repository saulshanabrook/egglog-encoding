# LMFAO covariance case study

This case study optimizes LMFAO's 140 Favorita covariance queries together in an
egraph and executes the selected plan through LMFAO's C++ backend. The queries
compute counts, sums, squares and pairwise products, grouped by categorical
features. A **view** is an intermediate aggregate result that several queries
can reuse. A query's **root** is the table where its final grouping happens.
The extractor chooses roots and shared views together.

We use the public sample: six tables and 2,000,000 Sales rows. This corresponds
to **Favorita / Covar Matrix / LMFAO** in the [paper's Table 3](https://dept.stat.lsa.umich.edu/~xuanlong/Papers/soann-sigmod19.pdf#page=12).
It reproduces the released workload and compiler pipeline on that sample, not
the full dataset (127M joined tuples), model training or other workloads. We
chose it because the artifact provides runnable data and many related queries
that can share work; we have not compared all of the paper's workloads.

```text
LMFAO query generation
  → original optimizer OR egraph rewriting + plan extraction
  → LMFAO C++ generation → compilation → answer checking → timed execution
```

## Rules and extraction

[`logical.egg`](logical.egg) is the single handwritten rule source.
[`program.py`](../../benchmarking/lmfao/program.py) translates each query into
nested sums over joined rows, preserving duplicates. It supplies unoptimized
alternatives for all six roots of LMFAO's join tree. The search changes the root
and evaluation order within that tree; it does not consider arbitrary join trees.

Rules perform three kinds of work:

- **Hoisting and loop interchange:** move independent factors out of sums and
  exchange independent loops. These transformations allow a child table to be
  aggregated before it is joined.
- **Fusion:** combine aggregates over the same rows. Multipatterns find the
  compatible reductions across queries and intermediate results.
- **Lowering:** turn the resulting expressions into views LMFAO can execute.
  Rules derive the grouping keys, scalar functions and dependencies too.

For example, this rule combines two reductions into one computing both results:

```lisp
(rewrite pair (Reduce rows $row (Tuple a b)) :name "scoped-fuse"
  :when ((= pair (Tuple left right))
         (= left (Reduce rows $row a)) (= right (Reduce rows $row b))))
```

Slotted egglog handles binding and identifies expressions that differ only in
bound-variable names. The ordinary egglog comparison uses de Bruijn indices
with explicit rules for shifting indices and exchanging bound variables.
Both receive the same query alternatives, transformations and rewrite budget.

The Rust [`lmfao-extract`](src/lib.rs) crate selects a plan directly from the
live egraph. Its [DAG extractor](src/dag.rs) uses HiGHS to solve a 0–1 integer
program across all 140 outputs, charging shared work once. Computing a view
costs `1 + input branches + grouping columns`; each aggregate column adds
`2 + local scalar functions`. The functions are the unchanged per-row
computations supplied by LMFAO. The solver reports the chosen cost, a lower
bound and whether it proved optimality. That optimum concerns the cost model
and available alternatives, not measured execution time.

LMFAO handles physical grouping, loops, data structures and C++ generation after
extraction. The selected equations are written to `plan.txt`, with the machine
representation in `plan.json`.

## Reproduce

CMake, a C++ compiler, libclang and Boost are required. Cargo.lock pins the Rust
solver and bundled HiGHS source. Prepare the external backend explicitly:

```sh
git clone https://github.com/fdbresearch/LMFAO /tmp/LMFAO
git -C /tmp/LMFAO checkout df6a5f59d597e9d7dd5984f268700223553789d0
uv run --locked python -m benchmarks.reproduction.lmfao.prepare \
  --source /tmp/LMFAO --output benchmarks/local/lmfao
./bench.py figures lmfao --rounds 3 --timeout-sec 300
```

`./bench.py figures` includes LMFAO in the full paper evaluation; adding `lmfao`
selects only this table. `--lmfao-data` and `--lmfao-backend` override the prepared
paths. Neither command downloads sources or prepares the backend implicitly.
Preparation uses a separate checkout, verifies the patches and records the
source revision, patch/header hashes and binary hash. Evaluation rejects
mismatches; after changing the adapter, prepare a new output directory.

`--boost PREFIX` supports unpacked Boost. Generated programs also need its include
path. `--lmfao-cxxflags` replaces all default flags, so retain the optimization flags:

```sh
--lmfao-cxxflags '-std=c++11 -O3 -pthread -mtune=native -ftree-vectorize -fopenmp -I/PREFIX/include'
```

The harness reads checked-in [`inputs/slotted.egg`](inputs/slotted.egg) and
[`inputs/debruijn.egg`](inputs/debruijn.egg). Regenerate them after changing
`workload.json` or `logical.egg`; tests check that they match:

```sh
uv run --locked python -m benchmarking.lmfao.program
uv run --locked python -m benchmarking.lmfao.program --check
```

Each live LMFAO invocation must export the same workload as `workload.json`
before optimization uses the static input. Benchmark collection does not
regenerate the inputs.

`--rounds` controls measured repetitions. The search uses 192 rewrite rounds;
this does not imply saturation. Optimizers and generated programs use one
thread. The focused `./bench.py lmfao --data PATH --backend PATH --output-dir PATH`
command provides additional controls: `--rewrite-rounds` generates an input
with a different search budget, `--cpu N` sets CPU affinity, `--jobs` controls
compilation, and `--cxxflags` supplies generated-program flags.
`--dag-timeout` limits extraction; `--build-timeout` limits backend builds and
checks. Egraph runs, including extraction, use the shared timeout and 16 GiB
allocator/address-space cap. `--memory-limit-gib` and `--no-memory-limit`
override the cap; peak RSS is measured separately. Generated C++ execution
has a timeout but no allocator cap.

## Results and timing

The experiment compares LMFAO's shipped roots, our implementation of the paper's
section 3.3 root heuristic, slotted egglog, and ordinary egglog. Every program
uses the same corrected backend and compiler flags. Before timing, all 140
outputs are checked against independent DECIMAL queries: keys and counts must
match exactly; floating-point results use `rtol=1e-9`, `atol=1e-7`.

Egraph measurements use the shared collector and JSONL cache. `--report PATH`
selects the cache (default `.reports.jsonl`; the focused `./bench.py lmfao`
command defaults to `OUTPUT/optimizer.jsonl`). Successful observations are
reused. A resource failure stops repetition at unchanged limits and remains
visible in the table. C++ preparation and execution run afresh and have separate
records. Correctness checking warms each program; timed executions rotate and
reverse method order.

| Column | What is measured |
|---|---|
| Egraph process time / peak RSS | Parsing and rewriting in separate processes; replay rows also check the selected plan, with or without proofs. Excludes DAG extraction. RSS is resident memory. |
| Full planning | LMFAO query export, input validation, rewriting, extraction, and a second LMFAO invocation to import the plan and generate C++. Controls use one LMFAO invocation. |
| C++ compilation | One build per distinct generated program. |
| Query time / LMFAO | Mean warm computation time divided by the shipped-roots LMFAO mean; lower is better. Excludes loading, sorting and checking, as in the paper. |

**Full planning already includes a rewrite run; do not add the Egraph process column.**
Repeated time/RSS measurements have 95% Student-t intervals. Query-time ratios
use independent Fieller intervals, as in the other paper reports. A single
sample has no interval. Planning/generation and compilation each have one
observation. Identical plans share compilation/execution observations, with that
reuse recorded in the report. Absolute query times and whole-process execution
times remain in the results JSON.

Our ratio baseline is the artifact's configured-roots LMFAO program. The original
paper's [Table 3](https://dept.stat.lsa.umich.edu/~xuanlong/Papers/soann-sigmod19.pdf#page=12)
compares LMFAO with MonetDB and the commercial system DBX. Those competitors are
not timed here; the independent SQL queries above check correctness only.

The [paper output guide](../../figures/README.md) lists the generated table and
caption files. Detailed `pipeline.json`, `comparison.md`, `execution.jsonl`,
validation records and per-method plans/C++ live under the output's `lmfao/`
directory. Status and artifact paths go to stderr; the focused command prints
Markdown to stdout (`--format json` selects JSON). Results are generated, not
checked in.

## Comparison with the paper

The paper describes a rule for choosing roots across the query batch. The
released covariance code instead uses configured roots. Our `paper` control
implements the described rule and then runs LMFAO's original optimizer; it is
not a released upstream mode. Comparing with both separates an improvement over
the shipped configuration from an improvement over the paper's algorithm.

The public configuration gives 140 final aggregates, 46 intermediate aggregates
and 125 views, matching Table 2. The paper's experiment scripts refer to an
unavailable feature configuration, so these counts do not establish identical
roots or reproduce published timings. The ordinary egglog comparison is also
specific to the chosen encoding, rules and budget; another encoding or schedule
can behave differently.

## Ownership and tests

LMFAO is pinned to `df6a5f59d597e9d7dd5984f268700223553789d0`. We reuse its query
generation, schema parsing, physical grouping and C++ backend.
`features.conf`, `treedecomposition.conf` and `LICENSE` are unchanged upstream
files. The two configuration files verify the dataset's selected features,
table schemas and join tree. `workload.json` is the unoptimized frontend export;
it also supplies tests that need neither an external LMFAO build nor its data.

The [adapter](../reproduction/lmfao/) contains one header and two patches:

- `OptimizerBridge.hpp` exports queries/plans, imports selected views and
  implements the paper's root heuristic.
- `optimizer-bridge.patch` adds export-only and plan-import paths. Python runs
  the Rust optimizer between those two LMFAO invocations.
- `dependent-output.patch` fixes accumulation of output values. Every compared
  method receives the same fix.

The rules, translator, Rust extractor and evaluation/checking code are new.
Their tests are included in `make check`. Small examples cover duplicate rows,
fractional/negative values and empty tables in both encodings. Tests also check
that extraction needs hoisting, sharing needs fusion, small DAG choices match
exhaustive search, and the adapter rejects mismatched files and cleans up after
timeouts.

## Proof replay

The generated table includes two replay rows for the selected slotted plan:
proofs off and proofs generated and checked. Both use the same binary, input,
repetition count and memory cap. Their timeout is three times the optimization
timeout. They use the same benchmark collector and cache as the optimization
rows; missing measurements are collected automatically by `./bench.py figures`.

The `slotted-proof-testing` treatment passes `--slotted --proofs` to generate
and check source proofs. Ordinary egglog's `proofs` treatment only records proof
information. A slotted input without equality checks does not certify a plan.

The LMFAO run writes `slotted/proof.egg` beside the selected plan. This
self-contained input asks whether the original query batch equals the selected
computations. To repeat just this comparison through the harness:

```sh
./bench.py figures/output/eval/lmfao/slotted/proof.egg --compare-treatment slotted \
  --treatment slotted-proof-testing --rounds 1 --timeout-sec 900 \
  --memory-limit-gib 16 --report /tmp/lmfao-proof.jsonl
```

For an existing plan made with the default rewrite budget, regenerate its replay
with `python -m benchmarking.lmfao.program --proof-plan PLAN.json --output FILE.egg`.

The check is appended after rewriting and asserts no new equalities. One batch
claim avoids copying the proof context for each query. The run repeats rewriting
with proofs enabled, reconstructs a source proof, checks it, simplifies it, and
checks it again before formatting the result. A completed replay includes both
checks and formatting. DAG extraction and C++ compilation are measured separately.
Replay does not select or execute another plan, so its preparation and execution
cells are blank. Proof failures prevent publication; resource failures remain
visible with their completed/failed sample counts.

These proofs cover logical query transformations. Backend code generation and
physical sharing are checked separately by executing every output against
independent answers.
