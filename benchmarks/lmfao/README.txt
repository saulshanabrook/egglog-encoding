LMFAO logical optimization case study
====================================

This runs LMFAO's 140-query covariance workload on the public Favorita fragment:
six relations, 16 features and 2,000,000 Sales rows. The queries compute counts,
sums, squares and pairwise products over the join, with categorical features as
grouping keys. They form a non-centered covariance (Gram) matrix used in linear
regression; this experiment computes the aggregates without training a model.

  LMFAO frontend -> original optimizer OR egraph + DAG extraction
                 -> LMFAO views -> grouping/code generation -> C++ execution

Rules expose root choices, aggregate pushdown and shared views in one egraph.
A cost-based DAG extractor selects roots and implementations jointly across all
outputs. The comparison retains the same corrected LMFAO backend. It reproduces
the artifact's query workload, not the paper's full 127M-row Favorita experiment,
other datasets/models, or parallel execution.

Provenance and ownership
-----------------------
  Paper: https://arxiv.org/abs/1906.08687
  Artifact: https://github.com/fdbresearch/LMFAO
  Commit: df6a5f59d597e9d7dd5984f268700223553789d0

Reused upstream code supplies query generation, schema/configuration parsing,
view grouping, multi-output loops, execution data structures and C++ generation.
features.conf, treedecomposition.conf and LICENSE are copied from that commit.
workload.json is a frozen frontend export, including functions and the join tree.

The additions under benchmarks/reproduction/lmfao are:
  optimizer-bridge.patch  Hook in QueryCompiler::compile().
  OptimizerBridge.hpp    Export queries/plans and invoke the optimizer subprocess.
  ImportPlan.hpp         Validate and import the selected DAG.
  dependent-output.patch Correct accumulation across terminal output keys.

The Rust crate here supplies DAG extraction and plan serialization. All Python
under benchmarking/lmfao and the egraph translation/rules are new; Python reads
the frontend export, runs experiments and checks results. It does not reconstruct
the query workload. The two headers are additions to the pinned checkout,
separate from its patches.

Run
---
Prepare the backend explicitly; collection never acquires sources or regenerates
frozen inputs. CMake, a C++ compiler, libclang and Boost are required. Cargo.lock
pins the Rust solver binding and its bundled HiGHS source.

  git clone https://github.com/fdbresearch/LMFAO /tmp/LMFAO
  git -C /tmp/LMFAO checkout df6a5f59d597e9d7dd5984f268700223553789d0
  uv run --locked python -m benchmarks.reproduction.lmfao.prepare \
    --source /tmp/LMFAO --output /tmp/lmfao-backend
  ./bench.py lmfao --data /tmp/LMFAO/data/favorita-small \
    --backend /tmp/lmfao-backend/build/multifaq \
    --output-dir /tmp/lmfao-results --treatment slotted --variant shared \
    --rounds 5 --timeout-sec 900

Preparation creates a separate checkout. --boost PREFIX supports an unpacked
Boost installation. For generated programs, --cxxflags replaces all default
flags; retain the optimization flags when adding its include path:

  --cxxflags '-std=c++11 -O3 -pthread -mtune=native -ftree-vectorize -fopenmp -I/PREFIX/include'

Compiler flags are identical across variants.

Preparation checks out the exact commit above, checks each patch before applying
it, and writes provenance.json beside build/. The evaluator verifies that commit,
the patch/header hashes and the executable hash before running. A changed adapter
requires a new prepared directory. The source checkout's branch and uncommitted
changes are preserved.

--treatment and --variant may be repeated. Omitting both requests all three
variants on egglog's slotted encoding and the native slotted-egraphs MultiPattern
matcher with snapshot substitution. Original LMFAO is always the control.
A single-engine invocation does not establish graph equivalence.

Add --binding-control named --binding-control canonical to compare selected
plans against ordinary egglog. Named retains each kernel's source binder as
constructor data; canonical gives these closed kernels one binder name. Both
use the same shared-view rules, cost, Rust DAG extractor and C++ backend. The
report includes plan sizes/costs, preparation and execution, and validates every
output. Canonicalization is included in preparation.

--rounds/--samples sets measured repetitions, not the frozen 64-round rewrite
budget; a budget does not establish saturation. --cpu N pins the experiment;
extraction and generated executables use one thread. --jobs controls compilation.
--dag-timeout bounds the joint solver; --build-timeout bounds each backend build
or diagnostic subprocess. --timeout-sec bounds optimizer processes and timed
executables. --memory-limit-gib/--no-memory-limit applies to optimizer processes,
including Rust extraction, but not generated C++ execution.

--report PATH selects the shared append-only optimizer cache (default
OUTPUT/optimizer.jsonl). Execution samples are fresh. Status goes to stderr;
the final pipeline JSON goes to stdout. Optimizer-only comparisons need no data
or backend:

  ./bench.py benchmarks/lmfao/inputs/shared.egg \
    --treatment slotted --compare-treatment slotted-ref-multi \
    --rounds 5 --timeout-sec 900 --report /tmp/lmfao-engines.jsonl --format markdown

Rules, extraction and controls
-----------------------------
logical.egg is the hand-written rule source. The generator adds queries/schema
and freezes self-contained copies: inputs/ has all 140 queries; correctness/ has
six queries for routine tests. Freshness tests cover both directories. There is
no separate source of generated rules to keep synchronized with logical.egg.

logical.egg connects AggregateQuery, directional ComputeView, and ViewColumn
with an explicit SharedView producer. Inputs contain original queries and
orientations of the supplied tree, never optimized targets. All six roots are
candidates; arbitrary join orders are outside the search space.

The main multipattern rules, abbreviated, are:

  query = AggregateQuery(domain, keys, weights), TreeRoot(domain, region)
    => query = ViewRequest(region, keys, weights)

  request = ViewRequest(region, keys, weights), region = Region(...)
    => request = ComputeView(region, keys, weights,
                             SelectWeights(local, weights), ChildRequests(...))

  a = ComputeView(region, keys, wa, la, ca)
  b = ComputeView(region, keys, wb, lb, cb), wa != wb
    => a = ViewColumn(SharedView(region, keys), wa, la, ca)

Child requests retain separator keys and required query keys, and receive the
scalar functions belonging to that subtree. Rewrites normalize masks, function
vectors and the distinct-weight test. Views preserve bag multiplicities without
assuming unique dimension keys. Closed scalar lambdas have fresh binder names;
slotted identifies alpha-equivalent kernels. Planning treats these kernels as
opaque, so canonicalized binders also suffice in ordinary egglog.

Each column owns its incoming aggregate dependencies. Compatible selected columns
reference one SharedView. Rust reads closed planning terms directly from the live
egglog tables; native-reference runs use its graph export. It checks query
keys/functions, directional pushdown and acyclic dependencies, then HiGHS selects
one DAG, charging each producer/column once. The serializer retains selected
identities without discovering compatibility groups or merging views. Scalar
kernel bodies remain opaque; function-vector positions identify frontend kernels.

A producer costs 1 + incoming regions + grouping columns. An aggregate column
costs 2 + local scalar functions. ComputeView pays both; ViewColumn pays the
column cost and references a shared producer. These fixed unit weights use only
the graph, without reading data or configured root preferences. Reports include
the solver's bound, gap and time limit. Optimality concerns this structural
objective within the exported graph, not executable runtime.

  single-root  Sales only, pushdown and shared producers enabled
  roots        All six roots, pushdown enabled, shared producers disabled
  shared       All six roots, pushdown and shared producers enabled
  original     LMFAO's original root/decomposition/view-merging policy

A root is where an aggregate's traversal ends. Compare shared with single-root
for root choice, and shared with roots for shared producers. Every variant still
has identical-subexpression reuse and backend multi-output optimization.
The original covariance frontend uses Sales for ungrouped queries, a configured
relation for one categorical feature, and the second feature's relation in
schema order for a categorical pair. This differs from the paper's batch
coverage-weight heuristic; original measures that shipped policy.

Backend and correctness
-----------------------
The bridge exports queries before optimization. For egraph runs it calls
optimize.py to translate the export and invoke lmfao-extract. Egglog rewriting
and extraction run in that Rust process without exporting a graph to Python.
Each invocation checks the export against the frozen workload; drift requires
explicit regeneration. An unpatched executable is rejected.

dependent-output.patch applies to every variant, including original. It fixes a
terminal output loop that accumulated a register across keys before writing each
result. It evaluates a product per output tuple when all enclosing loops are
output loops and no nested aggregate remains, preserving accumulation for reduced
loops. On the public data, this corrects a count by store/holiday_type from 3158
to 1989 for (1, 2). Report results as a corrected-backend comparison.

Every plan is selected before the independent Python checker reads data. All 140
answers are checked with DECIMAL arithmetic: exact keys/counts, rtol=1e-9 and
atol=1e-7 for floating moments. Checking uses a separate executable with 17-digit
output; timed executables omit dumping and checking. Validation is the warmup;
subsequent executions rotate/reverse plan order.

Reports and timing
------------------
  comparison.md          Computation table, ablations and preparation costs.
  pipeline.json          Phase summaries, failures and artifact references.
  optimizer.jsonl        Shared cache with input/binary hashes and peak RSS.
  *-graph.json           Frozen engine-comparison graphs.
  *-isomorphism.json     Full graph verdict; limits/timeouts are inconclusive.
  VARIANT/workload.json  Actual frontend export.
  VARIANT/graph.json     Native-reference input to Rust extraction, when selected.
  VARIANT/extraction.json Selected alternatives, cost, bound/gap, phases and input hash.
  VARIANT/plan.json      Views, columns and query references.
  VARIANT/plan.txt       Readable equations for the selected plan.
  metadata.json         Dataset hashes, versions, affinity and timing scopes.
  builds.json           Generation/compilation times, flags and binary hashes.
  execution.jsonl       Fresh C++ process-wall and computation samples.
  validation.json       Independent output checks.

The primary table reports computation medians, excluding loading/sorting,
optimization and compilation. The paper's Table 3 uses this scope with means of
four runs after warmup (Section 4.1 and Appendix B). Whole-process execution
remains in pipeline.json. Missing results are unavailable, not timings.

Preparation reports one observation each for optimization/generation and C++
compilation. Generation includes the entire LMFAO compiler process and optimizer
subprocess. Its phase breakdown is in extraction.json; do not add it again.
Identical serialized plans reuse compilation/execution observations, charged in
full and identified by execution_aliases. Tool builds, graph diagnostics and
independent checking are excluded; oracle loading/computation is recorded as
validation_preparation_seconds. Separate optimizer-only samples include startup,
parsing, graph construction and rewriting. Egglog's ruleset_work_seconds is
exclusive ruleset work, not rewrite wall time. Those samples and graph-export
reruns are excluded from generation.

For N executions of a reused plan, preparation + N times execution is an
amortization estimate, not a measured end-to-end runtime; specify whether
execution includes loading/sorting.

Validation and regeneration
---------------------------
Read logical.egg, src/lib.rs (planning terms/cost/serialization), src/dag.rs
(joint extraction) and src/terms.rs (live table reads). optimize.py translates
the frontend export; backend.py invokes LMFAO and its generated programs;
optimizer.py adapts the shared collector; cli.py connects the stages.

make check includes live two-engine count/extraction-cost checks, Rust solver
tests against exhaustive search, and Python tests of extracted plans for every
root orientation, bag duplicates, negative weights, squares and cross-relation
products. Matching counts do not establish graph equivalence;
the CLI checks full isomorphism separately. Real-data C++ validation belongs to
the explicit experiment. Checked proofs are not supported with --slotted.

After building the bridge, explicitly export the upstream input:

  mkdir -p /tmp/lmfao-export
  (cd /tmp/lmfao-export && \
    LMFAO_WORKLOAD_FILE=/tmp/lmfao-export/workload.json \
    /tmp/lmfao-backend/build/multifaq --path /tmp/LMFAO/data/favorita-small \
      --model covar --parallel none --mo 1 --compress 1 --out /tmp/lmfao-export)
  cp /tmp/lmfao-export/workload.json benchmarks/lmfao/workload.json

Then regenerate the self-contained benchmark and test programs:

  uv run --locked python -m benchmarks.reproduction.slotted.lmfao --check
  uv run --locked python -m benchmarks.reproduction.slotted.lmfao
  uv run --locked python -m benchmarks.reproduction.slotted.lmfao --fixtures
  uv run --locked python -m benchmarks.reproduction.slotted.lmfao --fixtures --check
