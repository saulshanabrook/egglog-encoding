# Causal Slice Receipts v1

## Steering frame

- Mission: make causal proof testing faster than full proof testing on Math,
  Eggcc, Pointer, Hardboiled, and Luminal using exact native receipts followed
  by a small, fully grounded replay through the unchanged proof system.
- Base: `4940be37429e7adf16cc43283b38508e692cf045` (PR #23).
- Oracle only: `d98c112955e2e817c9005e42287011224798679c`.
- Non-goals: Prefix or conservative recovery, selector rules, partial
  bindings, query planning, source projection, proof-database translation, a
  second evaluator, proof extraction, Herbie, or workload-specific behavior.
- Current frontier: benchmark surface and receipt-only capture. Replay work is
  blocked until the receipt gate passes.

## Roster

| Agent | Circle/domain | Aim | Status | Output | Stop |
|---|---|---|---|---|---|
| root | coordinator | Preserve scope, integrate, and own final gates | active | accepted checkpoints and final handoff | gates pass or user decision is needed |
| implementation worker | Rust/Python implementation | Build the accepted design serially | checkpoint 1-2 accepted; receipt kernel pending | reviewable diff and targeted tests | checkpoint passes, path is disproved, or two cycles show no movement |
| proof reviewer | read-only proof boundary | Verify exact-one replay and unchanged proof checking | pending | evidence-backed findings | criteria pass or one blocking objection remains |
| benchmark verifier | read-only benchmark gate | Own broad benchmark commands and endpoint identity | checkpoint 1-2 passed | per-file measurements with SHAs | comparison completes or validity fails |

All sub-agents use `gpt-5.6-sol` at `ultra` reasoning effort. Only the
implementation worker writes feature code. Reviewers are read-only.

## Accepted contract

1. Native execution records exact receipts. No Prefix or fallback exists.
2. Effective facts receive immutable `FactId`s. Matches record rule, cumulative
   wave, ordered premise FactIds, and one compact `ReplayTermId` for every
   ordinary variable. Match capture copies handles only: no tree walks, ASTs,
   strings, or source rendering.
3. `ReplayTermId` refers into a shared hash-consed structural DAG installed at
   semantic producer sites. Missing O(1) producer mappings fail closed.
4. Applied equality edges have exact immutable reasons. Rebuild and
   congruence store endpoint pairs and explain them lazily during slicing.
5. Merge receipts cite the match and prior fact. Decomposed joins carry exact
   premise FactIds through materialized intermediates.
6. Same-ID Vec canonicalization creates an immutable container-version receipt
   at the registry rebuild site, linked to the prior version and changed child
   equality or nested-version causes.
7. Successful checks record exact fact premises plus equality endpoints as
   roots. Leaf FactIds map to source assertions, TSV rows, or globals.
8. Replay uses top-level `(let-check name expr)` aliases and list-form
   `(run-rule ("name" ((var expr) ...)) ...)`. Every ordinary variable is bound.
   `run-rule` means exact one: point-probe all premises and guards against one
   shared pre-wave snapshot, then run existing compiled heads in list order and
   publish/merge/rebuild once. It never builds plans or performs joins/scans.
9. `let-check` resolves prior aliases and lookup-only EqSort constructors.
   Explicitly replay-safe pure primitives may deterministically intern base or
   Vec container values. It never creates relational rows, e-classes, unions,
   timestamps, globals-as-functions, or proof facts.
10. The sliced artifact contains only source leaves, checked aliases, grounded
    rule firings by cumulative wave, and the original unchanged check. It is
    executed as `Vec<Command>` through existing proof mode; rendering is for
    inspection only.

Unsupported retained delete/subsume/absence, effectful or nondeterministic
primitives, unsupported containers, custom stateful merges, missing causes, or
order-dependent replay divergence fail closed.

## Hypotheses

### H1: compact receipt capture is cheap

- Prediction: producer-side term promotion plus per-effect handle copies costs
  about 1.3x native and remains below 1.5x on each cohort workload, including
  Math's high match-to-retained ratio.
- Disconfirmation: match-time reconstruction/rendering occurs, any exact cause
  is missing, or a workload remains above 1.5x after a three-round screen.

### H2: exact recording removes Hardboiled breadth

- Prediction: stable FactIds, equality reasons, decomposed witnesses, and Vec
  versions yield zero Prefix and a substantially smaller causal frontier.
- Disconfirmation: the retained check reaches an unattributed fact/equality/
  container change or a forbidden semantic feature.

### H3: complete grounding removes replay search

- Prediction: replay cost is point probes plus existing head tapes and one
  barrier per wave, with zero plan builds, joins, scans, or partial matches.
- Disconfirmation: any variable cannot be named structurally or exact-one
  validation requires search.

### H4: causal proofs win per file

- Prediction: recording + slicing + grounded proof replay is faster than full
  proofs on every cohort file while strict proof checking remains unchanged.
- Disconfirmation: any per-file median loses after the candidate is frozen.

## Checkpoints

1. Snapshot and cohort: Herbie excluded; Math includes the positive check from
   `d98c112`; baseline and candidate resolve the same input bytes.
2. Benchmark surface: `causal-receipts` and `causal-proofs` treatments; normal
   `.reports.jsonl`; `make benchmark-smoke` passes.
3. Receipt kernel and focused semantic canaries.
4. Receipt-only all-five gate before replay code: target 1.30x, hard 1.50x per
   workload, zero Prefix/unsupported/missing causes, and every check rooted.
5. Language and grounded executor canaries.
6. Backward slice, rendered artifact, and unchanged proof-mode integration.
7. `make proof-tests`, `make check`, then one-round and six-round frozen
   `./bench.py` comparisons with per-file results.

## Experiment log

Append each accepted or rejected probe with status, smallest repro, exact
command/cwd, endpoint SHAs, observation, hypothesis result, and next gate.

### 2026-07-22 — checkpoints 1-2 benchmark surface

- Status: accepted and reviewable; no broad benchmark was run.
- Snapshot: `/Users/saul/p/wt/egglog-encoding/causal-slice-receipts-v1`,
  branch `agent/causal-slice-receipts-v1`, tracked `HEAD`
  `4940be37429e7adf16cc43283b38508e692cf045`; oracle read only at
  `d98c112955e2e817c9005e42287011224798679c`.
- Smallest repro: two workload-command assertions, one five-file default
  assertion, and two parameterized treatment-CLI assertions. Before the
  production edit,
  `uv run --locked pytest -q tests/test_workloads.py tests/test_benchmark.py`
  produced the expected four failures and 34 passes. After the edit it
  produced 38 passes.
- Change: the default cohort is Math, Eggcc, Pointer, Hardboiled, and Luminal;
  Herbie alone is removed. `causal-receipts` maps to
  `--causal-receipts`; `causal-proofs` maps to
  `--causal-slice --proofs`; both are main-backend-only treatments. The same
  registry supplies benchmark and profile CLI choices. No binary causal flag
  exists yet, so this checkpoint tests command construction and leaves the
  public smoke on the implemented proofs treatment.
- Math input: the three-line positive check after `(run 11)` is byte-identical
  to the oracle file; SHA-256 is
  `6017cf55fcc0bbc0dfb6c512b1a805709a33ac501b7f72796a74a788c804f77c`.
  `rg -n '^\\s*\\(prove\\b' egglog/tests/math-microbenchmark.egg` found no
  executable prove command.
- Direct semantic probe after `cargo build -p egglog-experimental`:
  `target/debug/egglog-experimental --mode no-messages -j 1
  egglog/tests/math-microbenchmark.egg`, the same command with `--proofs`, and
  the same command with `--proof-testing` all exited successfully. Both proof
  modes emitted only the existing generated-global naming warning.
- Static checks:
  `uv run --locked ruff check benchmarking/models.py
  benchmarking/benchmark.py benchmarking/profile.py benchmarking/targets.py
  benchmarking/workloads.py tests/test_workloads.py tests/test_benchmark.py`;
  the corresponding `ruff format --check`; and
  `uv run --locked mypy benchmarking tests/test_workloads.py
  tests/test_benchmark.py` all passed.
- Expanded narrow regression:
  `uv run --locked pytest -q tests/test_workloads.py tests/test_benchmark.py
  tests/test_profile.py` passed all 68 tests.
- Public smoke: `make benchmark-smoke` passed, built tracked HEAD, collected
  `main/off` and `main/proofs` for `integer_math.egg`, and wrote two rows only
  to `/tmp/egglog-encoding-bench-smoke.jsonl`. Repository `.reports.jsonl`
  remained absent.
- Hypothesis result: this checkpoint establishes the measurement surface but
  does not test H1-H4. The next stop is coordinator review and preservation of
  checkpoints 1-2 before any receipt-kernel work.
