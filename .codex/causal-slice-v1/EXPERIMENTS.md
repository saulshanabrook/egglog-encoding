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

### 2026-07-22 — checkpoint 3 receipt-kernel vertical canaries

- Status: semantic canaries passed, but the checkpoint was rejected by an
  independent cost-shape review. The first implementation put permanent
  boxed/hash-map drafts, eager FactId/cause sidecars, witness reads, and large
  cause reservations on hot paths. The bounded in-place repair is recorded
  separately below; frontend/bridge installation, decomposed witness
  transport, rebuild/container receipts, check roots, and replay are
  intentionally not claimed here.
- Snapshot: `/Users/saul/p/wt/egglog-encoding/causal-slice-receipts-v1`,
  branch `agent/causal-slice-receipts-v1`, starting `HEAD`
  `544d63d888e524a83f5048374a1453b603aa6478`; changes remain uncommitted for
  coordinator review.
- Smallest semantic canary:
  `cargo test -p egglog-core-relations
  causal_receipts_record_only_effective_constructor_and_union_commits --
  --nocapture` from the worktree root passed. One source fact feeds one native
  rule match; an effective constructor insertion, relational insertion, and
  applied UF edge share that exact match, while the second no-op wave creates
  no durable fact/edge receipt.
- Parallel boundary canary:
  `cargo test -p egglog-core-relations
  causal_receipts_parallel_merge_preserves_proposal_and_fact_causes --
  --nocapture` passed with 20,002 staged rows on a four-thread pool, exceeding
  the real strict `> 20_000` table threshold. A same-wave merge retains both
  proposal matches before either has a FactId; a later effective merge retains
  the immutable prior FactId. The 20,000 no-op proposals in the later wave
  promote no matches or facts.
- Core regression: `cargo test -p egglog-core-relations --lib` passed all 60
  tests. `cargo fmt --all` and `git diff --check` passed.
- Data-path result: aligned cause sidecars cross serial and parallel table
  buffers; staged proposal folds retain draft-to-draft predecessor edges;
  effective commits alone allocate FactIds; applied UF updates retain their
  rule/merge reason while redundant proposals are counted but not persisted.
  Compaction preservation is implemented but did not yet have a focused
  post-repair canary.
- Scope warning: current replay-term handles are test-producer placeholders,
  equality endpoints are not yet the final immutable equality-node design,
  and the one-atom witness canary is not evidence for decomposed joins. H1's
  all-five recording-overhead gate and H2's zero-Prefix gate remain untested.
- Hypothesis result: the canaries support the bounded mechanism behind H1/H2
  (native exact attribution survives both commit paths) without testing their
  workload-wide performance or completeness. The next gate is coordinator
  review before expanding the recording contract.

### 2026-07-22 — checkpoint 3 receipt-kernel cost-shape repair

- Status: repaired and green at the bounded core-relations gate; no broad
  benchmark was run and no frontend/replay scope was added.
- Storage repair: `ReplayTermId` is `u32`; wave-local matches, causes,
  premises, and term handles use flat arenas; atomic ID ranges publish through
  worker-local `ReceiptBatch` fragments with one lock at the native barrier;
  only roots from effective facts and applied unions promote into the durable
  cause DAG, and finalization reclaims the whole provisional wave. Fact lookup
  is dense by `FactId`; cause unfolding is iterative and lazy.
- Ordinary-path repair: bindings and table/UF/staged causes are lazy
  `Option` sidecars. Serial and parallel table insertion each use one
  const-generic source loop, yielding a receipt-free monomorphization without
  FactId lookups, active sentinel causes, provisional allocations, or the
  prior 2 MiB-per-shard cause reservation. Ordinary `used_vars` remains
  RHS-only.
- Disabled-path canary:
  `cargo test -p egglog-core-relations
  receipt_disabled_rule_path_uses_no_fact_sidecars_or_witness_reads --
  --nocapture` passed. Test-only probes observed zero FactId lookups, zero
  witness-row reads, and zero causal sidecar bytes while an ordinary rule
  committed its result.
- Publication canary:
  `cargo test -p egglog-core-relations
  receipt_batches_publish_out_of_order_without_holes -- --nocapture` passed.
  It publishes a higher atomic cause range before a lower one, then finalizes
  with no holes or live provisional storage.
- Witness canary:
  `cargo test -p egglog-core-relations
  receipt_witness_rejects_first_row_decoy_and_accepts_bound_row --
  --nocapture` passed. A binding established by one atom rejects the second
  atom's first-row decoy and accepts the binding-consistent row with its
  immutable FactId. This is a direct helper canary rather than a
  planner-shape-dependent test.
- Existing serial and parallel exact-attribution canaries both passed after
  the repair. The parallel case still stages 20,002 proposals; wave 2 promotes
  only its one effective match and finishes with zero provisional matches and
  zero live provisional bytes.
- Fail-closed boundary: effective facts and applied unions now reject missing
  attribution at the recording site. Guarded receipt execution returns a
  structured error before search because that capture path does not preserve
  native match witnesses. Snapshot/finalization reject open, abandoned, or
  unfinalized fragments.
- Activation/mutation boundary: initial receipt activation rejects a database
  containing any committed row; `MutationBuffer::stage_insert_with_cause` is
  mandatory for every implementation; and low-level
  `ExecutionState::stage_remove` fails before staging whenever receipts are
  enabled. The focused activation and embedding-delete canaries passed.
- Regression gate: `cargo test -p egglog-core-relations --lib` passed all 65
  tests. `cargo fmt --all` and `git diff --check` passed.
- Remaining checkpoint gaps: a focused post-compaction FactId-sidecar canary
  was deliberately deferred to avoid expanding this bounded repair.
  Decomposed/materialized witness transport remains the next recording
  checkpoint; the direct decoy canary is not evidence that it works.
- Hypothesis result: the repair removes the concrete always-on and
  no-op-retention failure modes found by review, but H1 remains untested until
  the receipt-only five-workload benchmark gate. No performance claim is made
  from unit tests.

### 2026-07-22 — checkpoint 4a stable FactIds and decomposed witnesses

- Status: bounded core-relations checkpoint is green and uncommitted for
  coordinator review. Equality/rebuild/container receipts, bridge/check roots,
  slicing, replay, and workload benchmarks were not started.
- Snapshot: `/Users/saul/p/wt/egglog-encoding/causal-slice-receipts-v1`,
  branch `agent/causal-slice-receipts-v1`, starting `HEAD`
  `e8233328d17512393aaa801931c2635bbc7c9079`.
- Compaction result: focused serial and parallel canaries force physical
  compaction, observe both a changed table generation and a moved surviving
  `RowId`, and prove that the survivor retains its immutable `FactId`.
  Replaced historical facts remain addressable in the receipt arena. Both
  paths passed without a production repair.
- Discriminating decomposed repro: a four-edge rectangle query with an
  unrelated first-row decoy asserts `Plan::DecomposedPlan` and at least two
  materialized stages. Before witness transport it reached native execution
  and failed at `free_join/execute.rs` with
  `missing exact premise FactId for atom AtomId(0)`. The same canary now passes
  with source-ordered premise FactIds and no decoy retention.
- Transport: receipt metadata maps each source `AtomId` once to a compact
  `PremiseSlot`. Materialized rows optionally carry flat, row-aligned witness
  records containing direct `(PremiseSlot, FactId)` evidence and prior-only
  compact `(MatId, group, row)` ancestor references. The final action resolves
  them through the already-retained immutable materialization map, unfolds
  this acyclic structure iteratively, and requires duplicate evidence for a
  premise slot to agree. References are three `u32` words with no owned state.
  Ordinary materializations leave a pointer-sized optional sidecar absent;
  the three-vector witness payload is boxed only when capture is enabled.
- Scoped and projection canaries: the same exact rectangle passes through the
  forced scoped/parallel materializer above the real 10,000-row database
  threshold. A second decomposed query with two existential supports for one
  projected key deterministically retains row zero and records its exact
  aligned `R`/`S` facts. An ordinary decomposed control records zero witness
  sidecar allocations/writes and zero FactId/witness lookups.
- Focused commands:
  `cargo test -p egglog-core-relations
  compaction_preserves_live_and_historical_fact_ids -- --nocapture` passed both
  compaction canaries; and
  `cargo test -p egglog-core-relations decomposed -- --nocapture` passed all
  four decomposed receipt/ordinary controls.
- Regression gate: `cargo test -p egglog-core-relations --lib` passed all 71
  tests. `cargo fmt --all` and `git diff --check` passed.
- Deferred measured cost: receipt-enabled materialized groups still allocate
  their boxed witness payload lazily. Flattening it across scoped workers would
  require synchronization or barrier remapping, so H1 must report total
  materialization groups/rows, sidecar groups/witness rows, fact/ancestor
  entries, vector capacities/estimated bytes, and sidecar-groups per
  materialized-row before deciding whether this needs optimization.
- Hypothesis result: this closes the native FactId stability and decomposed
  premise-transport gaps for the exercised table/materializer paths, including
  deterministic existential projection. It does not establish H1 recording
  overhead or workload-wide zero-Prefix completeness; those remain later
  explicit gates.
