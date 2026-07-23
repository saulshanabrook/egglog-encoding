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
6. Pair, Vec, Maybe, and Either canonicalization creates an immutable
   container-version receipt at the registry rebuild site, linked to the prior
   fact version and changed child equality or nested-version causes. Raw
   container IDs are candidate indexes only; exact ancestry is checked against
   current registry contents and logical child-sort slots.
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

### 2026-07-23 — checkpoint 4b1 typed producers and fact-owned terms

- Status: bounded core-relations producer/fact-term checkpoint is green and
  uncommitted for coordinator review. Bridge/CLI activation, equality and
  rebuild causes, container versions, check roots, slicing, and replay were not
  started.
- Snapshot: `/Users/saul/p/wt/egglog-encoding/causal-slice-receipts-v1`,
  branch `agent/causal-slice-receipts-v1`, starting `HEAD`
  `0fe412547330314fabdad189031771b787bc7ed9`.
- Storage result: every pending and durable FactId now owns one immutable,
  physical-row-aligned term range. Worker fragments append term IDs to a local
  flat vector and rebase once at publication; finalization moves the completed
  provisional flat vector out once, reserves durable storage once, and copies
  ranges directly without a temporary allocation per fact. Source causes
  contain only SourceRef. Derived and merge facts therefore resolve terms
  without inspecting their cause, and out-of-order worker publication
  preserves dense FactId lookup with no term holes.
- Typed producer store: stable ReplaySortId/ReplayOpId identify a sharded,
  hash-consed DAG of backend-neutral Literal and Call nodes. A separate sharded
  `(sort, Value)` map provides average-constant-time current-value lookup.
  Structural nodes share `Arc<[ReplayTermId]>` children; effective commits
  append handles directly into their worker-local vector with no per-fact
  allocation and no receipt-arena lock. Diagnostics are derived from map sizes
  only, with no hot-path counter atomics.
- Physical layouts: receipt mode registers immutable
  `TableId -> Arc<[Option<ReplaySortId>]>` layouts. Engine-only timestamp or
  subsume columns stay row-aligned as `ReplayTermId::MISSING`; receipt metadata
  rejects an ordinary binding that selects such a column. Source installation
  validates the complete row before installing any typed value mapping.
- Match timing: native witness capture retains only ordered premise FactIds.
  `Bindings::ensure_receipt_causes` resolves ordered ordinary-variable handles
  immediately before the first effect, after preceding action-tape
  instructions. Premise variables resolve immutable fact-column handles inside
  the match-registration arena lock. The all-premise common path allocates no
  term scratch and enters that arena only once; a mixed match pre-resolves only
  its typed Current handles into a compact SmallVec before the same single
  registration lock. The stored term order remains the declared ordinary
  variable order.
- Constructor seam: ordinary `LookupOrInsertDefault` is unchanged.
  Receipt-aware constructors compile to a distinct instruction. It reads hits,
  deduplicates predicted misses without staging, fills all outputs, installs
  the typed Call on the first unseen output, then resolves owner-lane causes
  and stages only unique misses. Phase 2 probes each output binding before
  visiting or copying its key arguments, so an existing output mapping is
  exactly one typed point lookup and avoids child lookup/hash-cons work. The
  replay-only metadata is boxed at compilation so its allocation stays off
  ordinary action tapes and `Instr` remains within its pre-receipt 80-byte
  footprint.
- Exact-row canaries: Source A produces derived B, then a next-wave rule
  consumes B to produce C while the same constructor transitions from miss to
  hit; both paths share one typed Call and B/C carry complete terms. Separate
  canaries cover primitive-only current values, ignored physical columns,
  serial merge output distinct from its proposal, parallel native publication
  distinct from merge scratch, and out-of-order fact-term range publication.
  The ordinary control asserts its compiled tape contains only the non-replay
  constructor variant, plus zero FactId/witness reads and zero table sidecar
  bytes.
- Focused commands:
  `cargo test -p egglog-core-relations causal_receipt -- --nocapture`,
  `cargo test -p egglog-core-relations receipts::tests -- --nocapture`, and
  `cargo test -p egglog-core-relations
  receipt_disabled_rule_path_uses_no_fact_sidecars_or_witness_reads --
  --nocapture` all passed.
- Regression gate: `cargo test -p egglog-core-relations --lib` passed all 78
  tests. `cargo fmt --all` and `git diff --check` passed.
- Hypothesis result: the native producer/fact-term layer now carries exact
  derived terms without eager rendering, a second evaluator, per-match trees,
  or producer work on the ordinary path. H1 recording overhead and all
  workload-wide completeness/performance claims remain untested until the
  later bridge and receipt-only gates.

### 2026-07-23 — checkpoint 4b2a typed applied-union join forest

- Status: bounded core-relations equality checkpoint is green and uncommitted
  for independent review. Table rebuild/congruence, container versions,
  bridge activation, check roots, slicing, and replay were not started.
- Snapshot: `/Users/saul/p/wt/egglog-encoding/causal-slice-receipts-v1`,
  branch `agent/causal-slice-receipts-v1`, starting `HEAD`
  `7483baa6a6ccd97a68fb307f23116548a8944800`.
- Typed staging: receipt-mode unions use a dedicated action/buffer operation
  carrying an explicit logical `ReplaySortId`. Both raw endpoints resolve to
  canonical `ReplayTermId`s before the UF buffer is initialized or native
  state can mutate. Database receipt activation marks existing and future UF
  buffers so raw `stage_insert` and raw caused inserts fail closed. Missing
  terms and values installed only under another sort also fail before staging.
- Native boundary: `DisplacedTable` remains the sole connectivity oracle and
  the ordinary merge loop plus `insert_impl` remain on their baseline path.
  The receipt branch captures the two roots returned by the existing native
  finds, calls the same `uf.union(raw_left, raw_right)`, and asserts its
  parent/child are exactly those roots. Path compression changes no receipt
  topology.
- Join forest: every successful native union allocates one dense `EqNodeId`
  shared 1:1 with its equality edge. The immutable node joins the two
  pre-union components, each either a typed leaf term or an earlier join node.
  A receipt-only boxed map mirrors current native roots to typed components;
  applied union replaces the native parent entry and removes the child.
  Redundant proposals allocate neither edge nor node and promote no match.
  Endpoints retain sort, canonical term, and exact proposal-time raw value;
  edges retain cumulative wave, native parent/child, and the cause DAG until
  finalization.
- Exact reasons: finalization accepts a direct `RuleUnion(match)` or the
  bounded merge shape `MergeFn { rule_match, prior_fact }`. Source causes,
  nested same-wave merge chains, and other unreached shapes fail closed
  instead of flattening or widening. Those shapes require later recording-site
  work, not a conservative fallback.
- Canaries: the migrated constructor/direct-union test records a typed
  same-head `RuleUnion` and one Term/Term join. A `30=20`, then `20=10`, then
  redundant `30=10` sequence records exactly two immutable binary joins,
  promotes only the first two matches, increments `redundant_unions` once, and
  stays unchanged after native path compression. Raw, raw-caused, missing-term,
  and wrong-sort proposals all leave the UF and durable receipts empty. A
  merge callback that returns false records exactly one incoming match and its
  immutable prior `FactId`. The ordinary UF canary keeps its component sidecar
  absent, and the existing `Instr <= 80` footprint guard still passes.
- Focused commands:
  `cargo test -p egglog-core-relations typed_union -- --nocapture`,
  `cargo test -p egglog-core-relations
  merge_function_union_cites_one_match_and_immutable_prior_fact --
  --nocapture`,
  `cargo test -p egglog-core-relations
  causal_receipts_record_only_effective_constructor_and_union_commits --
  --nocapture`, and
  `cargo test -p egglog-core-relations uf::tests::displaced -- --nocapture`
  all passed.
- Regression gate: `cargo test -p egglog-core-relations --lib` passed all 81
  tests. The focused instruction-footprint guard passed.
  `cargo fmt --all -- --check` and `git diff --check` passed.
- Hypothesis result: the applied-union recording site can maintain an exact
  typed immutable explanation forest beside the native path-compressed UF
  without another find/connectivity implementation. Workload-wide
  completeness and H1 overhead remain untested until the excluded bridge,
  rebuild, container, and receipt-only activation stages exist.

### 2026-07-23 — checkpoint 4b2a independent-review repair

- Status: the first frozen diff was rejected by independent correctness and
  cost review. The repaired diff remains uncommitted for re-review; no
  rebuild, container, bridge, check-root, slicing, or replay work was added.
- Atomicity repair: the receipt UF path now validates an effective proposal's
  timestamp and component-sort invariants before the native union. Its
  post-union suffix only appends the already-validated native row, records the
  edge, and updates the receipt mirror. A lower-timestamp canary catches the
  error and proves the two proposed endpoints remain separate while the
  earlier durable equality is unchanged.
- Sort repair: the bridge owns one global UF, so the repair deliberately does
  not bind the whole table to one logical sort. It instead checks the sort of
  each existing native component before the redundancy early return. A value
  may have structural terms under two sorts, but connectivity established for
  one sort cannot silently justify a redundant proposal for the other.
- Finalization repair: every applied equality cause is preflighted before any
  wave-local match, cause, fact, or equality is durabilized. Only a direct rule
  or one merge of a rule with an immutable prior FactId is accepted; a source
  union canary now errors during finalization rather than surviving until
  snapshot.
- Cost repair: UF proposal sidecars no longer copy both raw endpoints and one
  wave per lane. Each lane carries only cause, sort, and two term handles; raw
  endpoints come from the aligned native row and wave is stored once per
  buffer/batch. The action path reads each registered lane cause directly
  instead of allocating a second all-lanes cause vector. Redundant proposals
  validate one component once and allocate no applied proposal; applied
  proposals perform one component lookup per distinct root.
- Typed-boundary repair: the public buffer API accepts an opaque resolved
  proposal token whose fields can only be constructed after canonical
  `(sort, raw) -> ReplayTermId` lookup. The buffer validates the token's raw
  endpoints against its aligned native row before queueing, so compact storage
  cannot substitute or swap term handles.
- Lifecycle/API repair: ordinary caused UF staging remains supported when
  receipts are disabled. Receipt-enabled database clone and table clear fail
  before mutation because forking one shared receipt arena or erasing a forest
  epoch is not yet supported.
- Discriminating canaries cover lower timestamps, cross-sort redundancy,
  invalid source causes at finalization, ordinary caused staging, and
  clone/clear guards. `cargo test -p egglog-core-relations --lib` passed all 86
  tests; the instruction footprint guard, `cargo fmt --all`, and
  `git diff --check` passed.
- Hypothesis result: the review removed one missing-edge correctness hole and
  the largest avoidable per-proposal copy before H1 measurement. Required
  typed lookups, component-map operations, and one applied-edge allocation
  remain for the all-five receipt gate to measure.

### 2026-07-23 — checkpoint 4b2b table rebuild and congruence receipts

- Status: bounded core-relations rebuild/rekey checkpoint is green and
  uncommitted for independent review. Same-ID container versions, bridge
  activation, source/check roots, slicing, grounded replay, and workload
  measurements remain excluded.
- Snapshot: `/Users/saul/p/wt/egglog-encoding/causal-slice-receipts-v1`,
  branch `agent/causal-slice-receipts-v1`, starting `HEAD`
  `29265e4c33b962aff177d4bbf22324ed17b0b5aa`.
- Immutable rekeys: each changed semantic row keeps its old `FactId` as
  history and commits a new fact version with `RebuildDependency { wave,
  prior_fact, EqualityLandmark }`. The landmark stores only typed old/new
  endpoint pairs in physical-column order plus a dense applied-edge cutoff;
  it performs no equality-path walk while rebuilding. Timestamp and ignored
  columns contribute no pair.
- Native integration: all four existing incremental/nonincremental,
  serial/parallel staging loops call one receipt-aware row helper. With
  capture disabled they retain raw remove/insert staging. With capture
  enabled, prior FactId, table layout, old fact-owned term, new typed value
  term, and the historical cutoff are validated before that row's first
  staged removal; the same native merge/rebuild machinery then commits the
  caused row. The initial implementation intentionally takes one receipt-arena
  lock per changed row; H1's 1.5x screen must reject that simple choice if
  rebuild-heavy workloads make it too costly.
- Congruence: when a rebuilt key collides, the existing table merge creates
  `Merge(rebuild_draft, target_prior_fact)`. A union proposed by that native
  merge becomes `Congruence { fact_a, fact_b, equalities }`, citing the
  rewritten-away row, the colliding row, and the earlier key equalities. It
  invents no rule match. Rule and merge-function union reasons remain
  unchanged.
- Lazy explanations: `ReceiptSnapshot::explain_equality` unfolds one exact
  deterministic path through the immutable applied-edge forest, bounded by
  `EqualityEdgeCount`. It is iterative and runs only for retained landmarks.
  Later edges cannot justify an earlier rebuild. Redundant proposal adjacency
  remains deliberately unrecorded: shorter alternative explanations are an
  optional slice-size optimization, not correctness data or hot-path work.
- Failure boundary: a missing typed rebuilt endpoint errors before staging;
  receipt-mode table runners restore temporarily removed tables before
  propagating the diagnostic. The same-ID container refresh path now fails
  before its first row mutation pending the explicit Vec version checkpoint.
  The ordinary database/table rebuild path does not enter the unwind-safe
  receipt wrapper and allocates no fact sidecar.
- Discriminating canaries cover a direct rekey plus no-op identity retention,
  a later edge beyond the historical cutoff, exact collision/congruence, two
  changed columns supplied in reverse rebuild order, a missing typed endpoint
  with no latent staged mutation, the same-ID refresh guard, the ordinary
  zero-sidecar control, and chained lazy explanation with an earlier cutoff.
- Focused commands:
  `cargo test -p egglog-core-relations causal_receipt_rebuild -- --nocapture`,
  `cargo test -p egglog-core-relations causal_receipt_same_id_refresh --
  --nocapture`,
  `cargo test -p egglog-core-relations
  ordinary_table_rebuild_uses_no_receipt_sidecars -- --nocapture`, and
  `cargo test -p egglog-core-relations
  typed_union_forest_is_immutable -- --nocapture` all passed.
- Regression gate: `cargo test -p egglog-core-relations --lib` passed all 92
  tests before the final lazy-explanation type tightening; a fresh full run,
  formatting, diff check, and independent correctness/cost review are the
  freeze gate below.
- Hypothesis result: the engine can retain exact rebuild and congruence
  dependencies using the single native execution path and lazy endpoint
  landmarks. This is recording plumbing, not a second evaluator. Route-wide
  parallel coverage, container versions, and H1 recording cost remain open;
  no workload performance claim is made at this checkpoint.

### 2026-07-23 — checkpoint 4b2c rebuild review repair

- Status: the earlier 4b2b/4b2c freezes were rejected. Correctness review found that a
  later row/table validation failure could leave an earlier buffer queued, and
  that parallel same-key rebuilt proposals produced an unsupported
  `Merge(Rebuild, Draft(Rebuild))`. Cost review found three per-row temporary
  vectors, repeated forest construction/path walks, a nontransactional
  incremental cursor, and growing cause-prefix work. This repair is frozen
  for another independent review; container and bridge work remains excluded.
- Operation abort: every receipt-mode rebuild buffer now shares one explicit
  tri-state `MutationTransaction` (`Pending`, `Committed`, or `Aborted`). A
  table merge treats pending as an invariant violation, consumes committed
  batches, and discards only explicitly aborted batches. The coordinator
  records the terminal decision after all target tables finish validation;
  unwind restoration records `Aborted` before propagating the diagnostic.
  Multi-row and cross-table canaries then force a later real table merge and
  prove the old FactIds/keys survive while no rejected rekey appears.
- Same-wave congruence: equality validation now runs before native UF mutation.
  A congruence reason unfolds an arbitrary rebuild-only native merge DAG into
  its ordered immutable leaf FactIds and typed rebuild landmarks. This covers
  serial `Merge(Rebuild, Fact)`, parallel
  `Merge(Rebuild, Draft(Rebuild))`, and nested three-proposal folds without a
  Prefix or same-wave draft identity escaping the wave. Real 20,001-row,
  four-thread canaries cross both parallel thresholds and verify two- and
  three-leaf reasons, typed terms, common endpoints, cutoffs, and explainable
  historical paths.
- Same-wave merge functions use the same bounded DAG rule: a `MergeFn` reason
  points to every ordered `RuleMatchId` and immutable prior `FactId` read by
  the fold, including nested parallel `Merge(Rule, Draft(Merge(...)))` shapes. A
  three-proposal canary proves no same-wave proposal identity is lost; mixed
  rule/rebuild merge DAGs remain an explicit unsupported error rather than a
  widened slice.
- Recording cost repair: rebuild preparation uses one inline `SmallVec` and
  promotes its flat pairs directly into durable storage only when the cause is
  reachable. Rebuild counters likewise advance only on promotion, so aborted
  or no-op drafts do not inflate H1. The per-row hot path increments logical
  live-byte accounting by exactly one cause plus its changed-cell pairs; it no
  longer rescans every provisional fact and arena segment after each rebuilt
  row. One equality cutoff is captured once at the database rebuild barrier
  after checking zero open/abandoned fragments and a complete dense edge
  prefix; every target table and row in the operation reuses it.
- Abort-cost repair: a transaction retains the exact pending-row and removal
  counter increments made by its published buffers. Commit drops that tiny
  adjustment list; abort subtracts it. Rejected batches can therefore remain
  queued for fail-closed disposal without affecting the next merge's reserve
  size or serial/parallel choice, and no shard-queue scan is added.
- Incremental retry safety: receipt-mode table rebuild previews the
  canonicalizer subset and publishes every target table's `SubsetTracker`
  cursor only at the shared database transaction barrier. A 10,001-row
  single-target canary rejects the sole changed row, installs its missing
  typed term, and proves a retry against the unchanged UF version still
  performs the rekey. A second canary gives two 10,001-row targets the same UF
  delta: the first validates, the second rejects, and a corrected retry proves
  both cursors were rolled back rather than only the failing table's cursor.
- UF publication is preflighted atomically: receipt mode drains the complete
  pending queue and simulates it in FIFO order with a sparse union-by-min
  parent overlay, component-sort overrides, and a shadow highest timestamp.
  Only after every effective proposal's timestamp, exact cause, and typed
  components validate does the code open a receipt fragment or touch the
  native UF. The commit pass begins with read-only native roots, while the
  first mutation remains the existing `union`; ordinary mode is unchanged.
  Canaries cover a late invalid row in one batch, a conflicting-sort row in a
  later batch, a depth-two native path that must remain structurally identical
  after rejection, and an unsupported cause that becomes harmless only
  because an earlier pending proposal makes it redundant. Rejected proposals
  are discarded under the experiment's fail-closed exit contract; they do not
  reserve equality IDs, as a same-wave corrected publication proves.
- Cutoff failure is pre-transactional: the shared equality boundary is
  validated while the canonicalizer and every target table are still
  installed. A canary holds an open receipt fragment, observes the expected
  cutoff rejection, then proves both tables remain accessible and the empty
  fragment can still publish/finalize cleanly.
- Slice-time cost repair: `EqualityExplanationIndex` builds one forest view per
  historical cutoff, assigns immutable leaf intervals, and answers subtree
  membership in constant time. The future slicer can reuse that index across
  every retained changed-cell pair rather than rebuilding the forest or
  walking parents for each membership query. Convenience single-pair
  explanation delegates to the same index.
- Deep-cause cost repair: every published cause draft caches one constant-size
  equality classification from its already-cached children. Pre-UF and
  finalization validation are O(1) per equality. Public fact merges and
  equality reasons retain a snapshot-owned shared cause-root ID; ordered
  source/rule/fact/rebuild dependencies unfold lazily, preserving mixed-kind
  fold order without copying growing prefixes. A 512-proposal canary records
  511 effective prefix unions, retains exactly 1,023 cause nodes, and unfolds
  the final ordered 512 rule leaves only on request.
- Global provisional accounting now advances incrementally at source, match,
  worker publication, and rebuild sites. It no longer rescans the growing
  cause/fact arenas per source row or shard publication; H1 still decides the
  measured constant factor.
- Regression gate: `cargo test -p egglog-core-relations` passed 105 unit tests
  and 2 doc tests. The real parallel canaries finish in about 0.3 seconds
  together on this machine. `cargo fmt --all` and `git diff --check` passed.
  No workload timing has been run; H1 remains the required five-workload gate.

### 2026-07-23 — checkpoint 4b2d recording-site validation and hot-path repair

- Status: the 4b2c freeze was rejected by independent treatment-isolation and
  cost review. The reviewers found that table merge callbacks could stage an
  invalid union and then publish their parent row before UF preflight, that a
  panic could strand a `TableInfo` temporarily removed by the database merge
  coordinator, and that transaction/cause bookkeeping had leaked into the
  ordinary buffer and rebuild hot paths. This repair remains scoped to the
  existing native execution path; container, bridge, root, slicer, and replay
  work is still excluded.
- Valid-by-construction engine proposals: `ExecutionState` now carries a
  compact `CauseCapability` beside the draft ID. Direct rule actions construct
  the known Rule capability without an arena lookup; serial and parallel table
  merge folds compute capabilities while the exact proposal and prior FactId
  are in hand. `stage_union_with_replay` validates that capability before it
  allocates a UF buffer or notification, so an unsupported merge-induced union
  cannot be followed by a replacement parent-row commit.
- Typed proposal boundary: endpoint terms are resolved first and both raw
  equality values are checked under one receipt-only sort-registry lock before
  either binding is installed. This reflects the bridge's one global UF with
  globally fresh equality values: disjoint logical sorts can share the table,
  but one native equality value cannot change logical sort. The cumulative
  wave/timestamp consistency check also runs before buffer staging. The UF's
  whole-queue preflight remains as a low-level invariant guard; supported
  engine proposals no longer depend on it for semantic rejection.
- Cause storage repair: provisional cause storage is again one `CauseDraft`
  per cause. Only merge drafts have a sparse cached equality summary, and
  durable causes do not retain a second summary. Equality reasons are decided
  while the provisional classification exists, then stored directly on the
  durable edge. The active capability is ephemeral and is not copied into
  pending rows or facts.
- Mutation publication repair: receipt rebuild transactions own deferred
  buffer publications, target cursors, and changed-table notifications.
  Ordinary `Buffer` and `PendingRowBatch` shapes retain inline counters, raw
  removal queues, and no transaction-state check. Commit publishes once at the
  existing database barrier; abort drops every unpublished row/removal and
  cursor without queue scans or pending-count repair.
- Rebuild dispatch repair: receipt selection is hoisted once above the four
  incremental/full and serial/parallel loops. A single const-generic row helper
  preserves staging order, while the ordinary specialization has no per-row
  receipt, transaction, or `Option` branch. Transaction attachment remains one
  buffer-construction operation in receipt mode.
- Structural unwind safety: `merge_simple`, dependency-stratified `merge_all`,
  and direct `merge_table` restore every extracted table before propagating a
  panic; `merge_table` also restores its size estimate. This is not rollback:
  unsupported causal semantics still fail closed and terminate the treatment,
  but a caught diagnostic can inspect a structurally intact database.
- New canaries: a source-attributed merge function that attempts a union fails
  at `stage_union_with_replay`, preserves the immutable prior parent fact and
  both separate UF roots, and leaves its table addressable. Separate canaries
  cover simple, direct, and four-table stratified unwind restoration. The
  conflicting-sort canaries now assert rejection at proposal construction,
  before UF notification or mutation.
- Regression gate: `cargo test -p egglog-core-relations` passed 109 unit tests
  and 2 doc tests. `cargo check --workspace`, `cargo fmt --all -- --check`, and
  `git diff --check` passed. No workload timing has been run; the receipt-only
  all-five H1 gate remains mandatory before replay implementation.

### 2026-07-23 — checkpoint 4b2e activation and batched-classification repair

- Status: independent correctness review passed 4b2d, while treatment review
  found a delayed activation failure and cost review found two global-arena
  locks inside per-union/per-collision loops. This bounded repair addresses
  only those findings plus the reviewer's disjoint-sort canary; H1 remains
  unmeasured.
- Activation is now one side-effect-free all-table preflight followed by the
  infallible mode switch. The default contract rejects committed rows;
  `SortedWritesTable` and `DisplacedTable` additionally reject queued ordinary
  mutations and any live receipt-disabled buffer. The latter uses the already
  present `Weak` buffer handle count, so ordinary staging gains no new counter
  or branch. Adding a table to an active receipt database runs the same
  preflight before registering or enabling the table.
- Activation canaries cover dropped-but-unmerged and still-live buffers for
  both relations and the global UF, a preloaded table added after activation,
  and all-or-nothing mode selection across multiple tables. The last canary
  proves an earlier UF still accepts raw ordinary staging after a later table
  rejects preflight.
- UF publication preflight now collects the effective proposal causes while
  simulating the drained queue, then validates the complete list under one
  arena lock after the simulation. It still skips unsupported causes that an
  earlier pending proposal makes redundant, and still panics only after
  releasing the lock so caught fail-closed diagnostics cannot poison the
  arena.
- Each pending table row batch preloads its published constant-size cause
  summaries under one arena lock into the existing worker-local summary map.
  Every serial/parallel collision and same-wave fold then performs only local
  lookups. Publication removes local draft summaries and discards the external
  cache; external summaries are never duplicated in durable storage.
- The dependency-stratified ordinary merge path now stores its usually-small
  outer stratum list inline with `SmallVec` instead of introducing an
  unconditional heap `Vec`. Receipt-disabled row and buffer paths otherwise
  remain unchanged.
- A positive canary proves the single native UF accepts two disjoint logical
  sorts in one wave while existing overlap canaries still reject one raw value
  or component used through conflicting sorts.
- Regression gate: `cargo test -p egglog-core-relations` passed 114 unit tests
  and 2 doc tests. Focused activation, invalid-union, merge-function, and
  disjoint-sort canaries passed. Workspace checking, formatting, diff checking,
  and independent re-review remain the freeze gate below.

### 2026-07-23 — checkpoint 4b2f exact source causes and check roots

- Status: accepted after one bounded review/repair cycle. This checkpoint adds
  only the core source-action and positive-check receipt contracts; bridge,
  frontend, container versions, slicing, and replay remain outside it.
- Source actions carry `SourceRef` directly and allocate causes only for lanes
  that commit an effective fact. They create no synthetic `RuleMatch`. The
  builder rejects any source action with a query body, preventing a
  query-derived fact from being mislabeled as an input axiom.
- Positive checks retain the deterministic minimum successful native witness:
  cumulative wave, ordered premise `FactId`s, exact equality endpoints, and a
  validated equality-edge cutoff. Every active lane participates, including
  when sorted scan order opposes `FactId` order.
- Equality endpoint syntax is independent of the canonical runtime value.
  Premise endpoints resolve their `ReplayTermId` from the immutable fact-owned
  column, so two equal e-class values can retain distinct source terms. Typed
  current endpoints remain an explicit producer-map lookup and fail closed on
  a miss.
- Cost shape: the cutoff is captured once when the temporary check rule is
  built; each surviving lane bulk-resolves premise terms under one arena lock;
  inline `SmallVec`s choose one local candidate; publication occurs once per
  action batch and allocates boxed root storage only when the candidate wins.
  The earlier `batches x equality-prefix` scan is absent.
- Canaries cover an effective empty-query source action, rejection of a
  query-derived source action, distinct premise terms for one equal runtime
  value with reversed scan/FactId order, deterministic root ordering, and a
  missing current endpoint that publishes no root.
- Regression gate: `cargo test -p egglog-core-relations --lib` passed all 118
  tests; `cargo check --workspace`, formatting, and `git diff --check` passed.
  Independent correctness and cost reviews both passed frozen diff
  `ecb0c61ccd7c8e75d4b40c01b3afb97be85035c7f9f4ccc1577e8e4d486df35c`.

### Historical v0 profiling figures carried into the active ledger

- The packed report contained 5,119 report occurrences but only about 244
  distinct report keys. These are not comparable plan counts and must not be
  presented as such.
- The sampled profiles attributed about 14.1 seconds to preparation/planning
  and 11.2 seconds to search. Sampled CPU buckets are not additive wall time.
- Disabling decomposition made the observed case 16.5x slower, so it is not a
  general escape hatch for receipt or replay design.
- The inspected proof certificate contained 35 `Rule` nodes, 34 of them user
  rule nodes. This calibrates Hardboiled only as evidence that Prefix breadth
  can collapse; it is not an expected exact firing count for the new slice.

### 2026-07-23 — checkpoint 4b2j scoped decomposed witnesses

- Hypothesis: Eggcc's `Bop` witness mismatch came from treating every atom in
  the source query as an owner in every intermediate materialization. The
  first atom-only bag filter did not flip the failure; the same `Bop` was a
  projected semijoin atom in the active bag. This falsification narrowed the
  bug to the planner's projected-variable boundary.
- A decomposed bag now owns a premise only when the bag contains every source
  variable of that real atom. Projected `R(x, -)`-style atoms still constrain
  native execution, but cannot contribute an arbitrary existential row as the
  eventual source premise. A planner invariant checks that every non-ground
  real atom has at least one fully covering bag.
- Each join block also retains its compact set of variables actually
  established or consumed. Exact row validation compares only those variables
  against the shared binding map, whose other slots intentionally contain
  stale values across materialized bags. Local existentials omitted by the
  native planner come from the selected fact's immutable row instead.
- The first-row decoy guard remains: a singleton support must still be the
  native current subset, satisfy its atom constraints, and agree on every live
  variable. A focused canary now distinguishes a stale projected-out binding
  from a contradictory live binding.
- Eggcc advanced from the `Bop` binding assertion to the next independent
  producer gap: an effective fact contains a value with no installed replay
  term. There was no Prefix or witness search.
- Validation: all 119 core-relations tests and all 12 frontend causal canaries
  passed; `cargo check --workspace`, formatting, and `git diff --check` passed.

### 2026-07-23 — checkpoint 4b2i exact equality check roots

- Status: focused semantic checkpoint. All five checks now have an exact root
  shape, but equality dependencies inside ordinary rule bodies, TSV sources,
  primitive/merge result terms, Vec versions, slicing, and replay remain
  pending.
- Check lowering retains each explicit equality side's pre-canonical producer
  cell, chases the existing canonicalization substitutions, and then records
  its final `(body atom, logical column)`. The backend maps body indices past
  primitive guards to table-premise ordinals; the bridge converts those cells
  to the core's existing premise-owned equality endpoints.
- The supported equality surface is deliberately the cohort's outer,
  single-output function/constructor calls whose final producer premises stay
  distinct. Literal, bare-variable, primitive, tuple, and congruence-collapsed
  endpoints fail closed instead of searching for an approximate witness.
  `run :until` now propagates those metadata errors and swallows only an
  ordinary failed check.
- The canary exposed and fixed a temporal identity bug: a semantic rekey had
  been assigning the rebuilt fact the canonical target term. Direct rebuilds
  now inherit the prior immutable fact's term handles; their rebuild cause
  separately records the old/new raw equality endpoints. The terms are copied
  from the prior fact during the native batch's existing cause preload, so the
  effective-commit loop adds no per-fact arena lock.
- The frontend canary records a rule-caused `A(1) = B(2)`, then checks a global
  `A(1)` against `B(2)`. Its root has two exact premises, equal canonical raw
  values, distinct source-ordered term handles, and exactly the one applied
  rule-union edge as its lazy explanation.
- Independent review found that congruence could collapse two distinct source
  endpoint producers onto one surviving structural term. Runtime root
  publication now rejects that case explicitly; a focused canary preserves
  the fail-closed boundary rather than emitting a reflexive empty explanation.
- Validation: all 12 frontend causal canaries passed, all 119 core-relations
  tests passed, `cargo check --workspace` passed, formatting and
  `git diff --check` passed.

### 2026-07-23 — checkpoint 4b2h ordinary rules and relational roots

- Status: accepted focused vertical checkpoint; equality-body/check endpoint
  layouts, TSV rows, primitive result producers, Vec versions, slicing, replay,
  and the five-workload receipt gate remain pending.
- Ordinary native rules now promote one shared match record only when an
  effect commits. The record owns the stable source rule ordinal, cumulative
  logical wave, source-ordered exact premise `FactId`s, and compact term handles
  for source variables. Canonicalized literal bindings copy a validated typed
  `ReplayTermId`; no term is rendered or reconstructed at match time.
- The frontend catalog retains ruleset/name and source variable name/sort pairs
  for later replay emission. Table premises retain bridge source order and use
  the existing decomposed-plan witness sidecar; primitives are guards, not
  `FactId` premises.
- Positive relational checks now publish their first exact successful native
  premise witness. Explicit equality endpoints are intentionally not yet
  claimed by this checkpoint.
- A logical wave is one frontend execution leaf (`step_rules` or a future
  grounded batch), not a bridge timestamp. Separate run commands advance a
  global counter, while monotone native timestamps across multi-pass rebuild
  remain inside one wave.
- Source `run-rule` schedules fail closed before opening a wave while recording
  receipts. The final proof replay will use its own grounded list-form command
  with receipt recording disabled; guarded native witness capture is therefore
  not added to this checkpoint.
- Direct rule unions and constructor merge/congruence unions retain their
  logical EqSort. Constructor merges derive that sort from the executing
  database's registered table layout, preserving receipt-mode isolation across
  cloned databases while supporting both CLI early activation and the
  empty-function late-activation API. Union effects inside merge action blocks
  remain an explicit unsupported receipt boundary.
- Discriminating canaries cover mixed `[Premise(y), Constant(7)]` bindings,
  one exact relational root, waves 1 then 2 across separate runs, direct plus
  multi-pass congruence in one wave, early source-`run-rule` rejection, and
  activation after empty function declarations.
- Validation before freeze: `cargo test -p egglog causal_receipt -- --nocapture`
  passed the focused frontend canaries; the multi-pass rebuild canary passed
  separately; `cargo test -p egglog-core-relations --lib` passed 119 tests;
  `cargo check --workspace`, formatting, and `git diff --check` passed. No
  workload timing or receipt-overhead claim is made.

### 2026-07-23 — checkpoint 4b2g frontend source-constructor vertical slice

- Status: bounded source-only bridge checkpoint. This is not yet a receipt
  treatment for ordinary rules, checks, TSV input, primitive outputs, unions,
  or replay; those remain explicit next stages rather than fallback paths.
- The frontend now owns stable replay sort and operation catalogs before
  physical `ColumnTy` erasure. Function layouts are registered side-band on
  the private bridge `FunctionInfo`; public `FunctionConfig` remains
  unchanged. Constructor plans select the existing typed receipt instruction
  only when the catalog is present, so receipt-disabled action tapes remain
  unchanged.
- Typed source literals are interned as compact DAG nodes at backend lowering.
  Empty-query top-level actions carry a stable `SourceRef` through `RuleSpec`
  and the bridge into the core source-action builder. Successful action
  barriers finalize their provisional receipt segment before snapshots.
- Activation is all-or-nothing and fallible through the embedding API. It
  rejects existing frontend rules before touching the backend and reports
  pre-existing native rows/queued buffers as an error; the legacy core
  activation API retains its panic-on-invalid contract for existing callers.
- The end-to-end canary enables receipts, declares `(Leaf i64)`, evaluates a
  top-level source construction, and observes source-caused immutable facts,
  zero synthetic matches, zero unattributed commits, and resolvable typed call
  terms. Separate canaries prove late-rule and late-row activation leave
  ordinary mode usable.
- Regression gate: the three frontend causal canaries passed; all 26 bridge
  tests passed; `cargo check --workspace`, formatting, and `git diff --check`
  passed. No workload timing has been run because ordinary rule/check/TSV
  receipt production is intentionally not part of this checkpoint.

### 2026-07-23 — checkpoint 4b2k pure primitive replay producers

- Hypothesis: Hardboiled's first missing term (`128` from a rule RHS `/`) and
  Eggcc's next producer gap came from proof-checkable pure primitives returning
  native values without installing compact structural replay terms. The
  bounded treatment reuses the native result and never re-executes the
  primitive.
- The frontend registers stable operation IDs by exact source name and logical
  input/output sort signature. Only specializations with a pure runtime
  context and a proof validator receive replay metadata; effectful,
  nondeterministic, and unsupported primitives remain fail-closed.
- Receipt-enabled rule tapes append one `PromoteReplayCall` after an eligible
  native external call. It first probes `(logical sort, output value)`, then
  hash-conses one call node from existing child term IDs only on a miss.
  Receipt-disabled tapes contain no promotion instruction or receipt branch.
- Body primitives are promoted only when they bind a previously ungrounded
  value. Guard-only calls with an already-known output remain ordinary. Bound
  body promotions are deferred to the existing body/head boundary, after all
  relational joins and primitive guards, so rejected candidates allocate no
  permanent DAG nodes and heads can still consume the promoted values.
- Independent review found and bounded two representation hazards. Replay
  metadata is shared behind `Arc`, keeping the receipt-disabled logical rule
  variants pointer-sized instead of growing each call payload from 32 to 56
  bytes. A distinct fallback-replay instruction also retains the primary-call
  success mask, so a value returned by a general fallback is never mislabeled
  as the primary operation.
- Two frontend canaries cover a direct action primitive and a bound body
  primitive consumed by a later action primitive. Both retain strict positive
  checks, resolvable nested call DAGs, and zero unattributed commits.
- The treatment flipped both observed primitive failures. Eggcc advanced to
  its next independent planned boundary: container canonicalization performs
  an effective Set/Pair registry insertion without a container-version cause
  (`stage_insert` from the bridge Set merge callback during
  `apply_rebuild_nonincremental`). Hardboiled currently exposes a separate
  decomposed-witness disagreement before reaching its earlier `/` producer;
  that regression is being diagnosed independently rather than widened.
- Validation: `cargo test -p egglog-core-relations --lib` passed all 120 tests;
  `cargo test -p egglog causal_receipt -- --nocapture` passed all 13 focused
  frontend canaries; `cargo check --workspace`, formatting, and diff checking
  passed. The all-five H1 receipt-overhead gate remains unmeasured until every
  workload reaches an exact root with zero unsupported semantics.

### 2026-07-23 — checkpoint 4b2l exact conditional action causes

- Hypothesis: Luminal's first reached unsupported instruction was the native
  `InsertIfEq` emitted for an effective `(subsume (MMul ...))`; the ordinary
  conditional action already had the exact rule lane in hand and needed only
  the same cause-capability plumbing as `Insert`.
- Receipt mode now enumerates condition-true lane indexes, resolves causes for
  those lanes only, and stages the existing native insertion under each exact
  capability. False lanes allocate and stage nothing. Effective-commit and
  merge filtering remain in the existing table path, so redundant proposals
  do not promote matches and an update still cites the immutable prior fact.
  The receipt-disabled three-shape conditional loop is unchanged.
- A mixed true/false core canary records one source-backed rule match and one
  output fact, identifies the retained premise as the condition-true source
  lane, then repeats the rule and proves the no-op firing stays provisional.
  All-false batches skip match registration and cause-vector allocation. This
  covers exact lane attribution without introducing a new receipt or
  conditional-action semantics.
- The direct Luminal probe advanced from the effective subsumption boundary to
  an independent decomposed-witness ownership disagreement (slot 6,
  `FactId(2343)` versus `FactId(1519)`). This is the same planner-DAG ownership
  class now diagnosed precisely on Hardboiled, not an `InsertIfEq` failure.
- H1 timing remains deferred until the exact receipt path reaches all five
  workload roots.

### 2026-07-23 — checkpoint 4b2m decomposed witness ownership

- Hypothesis: Hardboiled's `FactId(2737)` versus `FactId(2736)` disagreement
  and Luminal's later slot disagreement were not missing provenance. A
  projected `KeyOnly`/`Lookup` probe was contributing arbitrary row zero for a
  materialization that the completed match also scanned through an exact
  `Full`/`Value` result row.
- `MaterializedWitnessRef` now packs `ExactRow` versus `ProjectedGroup` into
  the high bit of its row word, preserving the three-`u32` sidecar. Projected
  references can denote only row zero. At final receipt resolution, an exact
  direct owner suppresses a nested projected subtree only for the same
  `(MatId, group)`; different keys, direct projected roots, and genuine owner
  disagreements remain fail-closed.
- The existing existential canary still retains deterministic row-zero support
  when no exact result owner exists. A new precision canary forces one
  materialization through both a projected intermediate probe and an exact
  result scan, then verifies its two output matches retain the aligned 100 and
  101 premise rows rather than both inheriting row zero.
- Direct single-thread treatment probes now move both workloads past the
  ownership bug: Hardboiled reaches the planned same-ID container row-refresh
  boundary, while Luminal reaches the separate unsupported removal boundary.
  Neither boundary is widened here.
- Focused validation: all five decomposed tests pass, including the scoped
  transport and ordinary-mode no-sidecar controls. Full core/workspace gates
  are required before freezing the checkpoint.

### 2026-07-23 — checkpoint 4b2n batched TSV source receipts

- Hypothesis: Pointer's first failure occurred before rule execution because
  `(input ...)` used raw `TableAction` writes with no active source cause. Its
  23 files and 2,255 rows require a per-file batch, not one receipt arena lock
  and execution-state construction per row.
- `SourceRef::InputRow { command, line }` now names the frontend-global input
  command and one-based physical TSV line. Parsing and type validation still
  complete for the entire file before a command ordinal, replay term, cause,
  or native mutation is produced.
- The bridge validates the complete typed row batch, bulk-registers its
  heterogeneous source causes under one receipt-arena lock for a nonempty
  file, and stages every row through one native `ExecutionState`. Constructor
  rows retain the native shared prediction map, install one structural call
  term for the minted ID, and make duplicate keys no-ops; custom/relation rows
  retain exact typed terms for all visible columns. One flush and one receipt
  finalization follow the file. The atomicity contract is unchanged native
  import semantics: parse/schema failures occur before all effects, while a
  custom merge failure during flush is not a transactional file rollback.
- The frontend canary combines constructor and relation inputs. It proves
  distinct command ordinals, exact physical lines, first-effective duplicate
  ownership, resolvable constructor calls, and zero unattributed commits.
- The direct single-thread Pointer treatment command now exits successfully
  with its original check, moving from the first predicted-insertion panic
  through the complete workload. No Pointer-specific rule or fallback was
  added. Full focused and workspace regressions remain required before
  freezing the checkpoint.

### 2026-07-23 — checkpoint 5a dead fixture pruning

- Hypothesis: the bounded Eggcc `ExprSet` helpers and Hardboiled aligned-
  broadcast `UnstableFn` subsystem are parsed but unreachable under the
  benchmark schedules, so deleting them reduces the causal language surface
  without changing any observation.
- The bounded Eggcc fixture no longer declares `ExprSet`; its proof-testing
  snapshot remained byte-identical, and a fixture-shape test rejects the dead
  vocabulary. Live Pair, Either, and Maybe helpers remain.
- Hardboiled 32 no longer declares the unused `UnstableFn` subsystem. Its
  shared snapshot changed only by removing the nine zero-count rows owned by
  that subsystem; the ordinary, term, 32-thread, and proof-testing variants
  still pass.
- Focused validation:
  `cargo test -p egglog-experimental --test eggcc_2mm_proof`,
  `cargo test -p egglog-experimental --test files
  'proofs/eggcc_2mm_pass1_proof_testing'`, and
  `cargo test -p egglog --test files hardboiled_conv1d_32`.

### 2026-07-23 — checkpoint 5b serial-only activation boundary

- The benchmark harness invokes every treatment with `-j 1`, and causal
  capture now makes that evaluation assumption explicit. CLI activation
  rejects any requested thread count other than one, configures Rayon before
  enabling receipts, and the public bridge activation independently verifies
  that the active pool actually has one worker.
- The lower-level `core-relations::Database` activation seam remains
  intentionally ungated. Its already-landed parallel fragment, merge-cause,
  and witness-transport canaries stay intact as dormant future-work coverage;
  the current experiment adds no parallel recording or parity machinery.
- The serial restriction is checked at activation. The supported CLI path
  then owns the same one-thread global pool for the program's lifetime.
  Embedders must likewise keep execution in the pool used for activation.
- Canaries cover both the CLI's `--threads 2` rejection and direct bridge
  activation in a two-thread Rayon pool.

### 2026-07-23 — checkpoint 5c exact ordered-container and check provenance

- Hypothesis: the remaining Hardboiled/Eggcc boundary was container
  canonicalization history discarded between the registry and table/UF
  commit paths. The treatment records only positional endpoint pairs and
  immutable prior FactIds at the native sites that already know them; equality
  paths remain lazy and are unfolded only by a later slicer.
- Pair, Vec, Maybe, and Either construction use the existing compact
  hash-consed `Call` replay terms. Pair/registry ID changes publish an exact
  `ContainerCanonicalize` cause. Stable-ID Vec refreshes publish a new
  immutable fact version with `ContainerRefresh { prior_fact, changed
  children, cutoff }`; nested Vec refreshes compose through the same fact and
  term machinery. Raw IDs are only reverse-index candidates: the causal path
  checks actual registry contents against the logical child-sort schema, so an
  unrelated Set element with the same bits is not treated as an ancestor. A
  genuinely reached changed Set, Map, MultiSet, or UnstableFn dependency still
  fails closed with its kind named.
- Causal container rebuild is one transaction: it rebuilds a cloned registry,
  defers UF batches, notifications, and incremental cursors, and publishes all
  of them only after every supported environment succeeds. A late unsupported
  container therefore restores the original registry and leaks no native
  union or receipt state. This deliberately simple clone has O(total
  containers) causal-only cost; H1's 1.5x gate, rather than speculation, decides
  whether it later needs a mutation journal.
- Constructor commits now carry an optional row-term sidecar through native
  staging. A constructor fact snapshots one coherent witness: its output Call
  and that exact Call's ordered child terms, rather than independently
  consulting the first-wins `(sort, native value)` map for each cell.
  Same-table merges inherit the prior fact's coherent term vector. Registered
  constructor tables use the serial commit path while receipts are active,
  preserving exact sidecars even above the native 20,000-row parallel
  threshold; receipt-disabled and non-constructor parallel paths are unchanged.
  This fixed Math's collapsed runtime-value check without eagerly rendering
  source text.
- Successful top-level checks record the exact ordered premise FactIds plus
  typed equality endpoints and the applied-edge cutoff visible at match time.
  Constructor endpoints are reconstructed read-only from immutable fact-owned
  child terms and a registered operation ID. Schedule `:until` probes do not
  allocate check IDs or roots: replay does not re-decide schedule control
  flow, so they are not soundness roots.
- Eggcc and Math exposed one additional exact case: two distinct native IDs can
  already denote terms in one historical logical component. Such an effective
  UF operation now records `NativeAliasRecord` with its exact cause, native
  parent, and native child, while allocating no duplicate logical equality
  node or edge. This includes both identical structural terms and a native
  catch-up whose distinct endpoint terms are already connected by the forest.
  A structural term owned by a genuinely third component still fails before
  native publication. This check is deliberately order-sensitive: the
  recorder does not reorder or search a batch to make a later alias legal.
- Focused container/check canaries pass, including Pair canonicalization,
  one/two-level stable Vec refresh chains, nested Vec refresh, Either variant
  child slots, unrelated raw-ID collisions, registry/UF transaction rollback,
  the above-threshold constructor sidecar, direct and transitive
  unsupported-container failures, distinct equality-root terms, the
  non-recording `:until` path, and both durable and same-publication
  native-alias/catch-up paths.
  Multiple nominal logical container sorts sharing one physical registry entry
  remain explicitly unsupported and fail closed rather than choosing an
  arbitrary term.
  The existing deliberately unsupported corner remains fail-closed: if
  congruence has collapsed both same-operation check producers to one
  surviving FactId and one structural term, the current FactId-root contract
  cannot invent two source witnesses.
- Direct serial causal validation exits successfully for
  `math-microbenchmark.egg`, `eggcc-2mm-pass1.egg`,
  `pointer-analysis-small.egg` with its fact directory, and
  `hardboiled_conv1d_32.egg`. Luminal advances to and fails at the unchanged
  explicit removal boundary. These are semantic probes, not benchmark
  measurements. The already-landed low-level parallel receipt implementation
  remains intact; public causal activation is serial-only, so the benchmark
  path selects serial table operations through the existing one-thread
  heuristic. `make check` passes; after the final same-publication UF canary,
  all 130 core-relations unit tests and `make nits` also pass.
- No H1 recording-overhead or causal-replay performance claim is made here.
  The five-workload receipt gate remains intentionally blocked on Luminal's
  separate removal boundary, and no delete/subsume implementation or slicer
  retention policy is part of this checkpoint.

### 2026-07-23 — finish-plan checkpoint 1: lazy effective-event promotion

- Falsifying hypothesis: Math's 48.5x receipt cost and Eggcc's 1.52x cost were
  driven by candidate-scale construction of durable matches, unfolded premise
  witnesses, and copied merge predecessors rather than by the compact term DAG
  itself. This checkpoint changes only those costs; the recording benchmark
  gate remains deliberately unmeasured until independent review.
- Rule candidates now live in a wave-local `PendingMatchBatch`. A pending lane
  owns compact current-value `ReplayTermId`s, an `Arc<Materialization>` witness
  resolver, merge predecessor links, and a native execution ordinal. Ordered
  premise `FactId`s and durable match terms are resolved only when an effective
  table write, changed merge result, applied/native-alias union, or selected
  check promotes the lane. Multiple effective effects memoize and share the
  same promoted match.
- Producer-created values carry exact term sidecars through constructor hits,
  misses, pure replay-call primitives, and counters. A deliberately competing
  global structural alias canary confirms that an effective RHS commit records
  the actual producer term rather than a first-wins reverse-map alias.
- Deferred UF publication is prepare-then-publish. All effective causes are
  validated and lazily resolved before either the native UF or durable receipt
  arenas mutate. A later-invalid cause therefore leaves both snapshots
  unchanged. Nested merge/rebuild causes validate their enclosing root and
  prepare dependencies without incorrectly requiring a direct rebuild child to
  be independently publishable.
- Pending native work owns an explicit lease from transaction creation through
  row/UF queue drain or drop. Wave finalization and receipt snapshots reject an
  open lease. Pending witnesses contain no borrowed table `RowId`; immutable
  `FactId`s and owned materialization resolvers make physical compaction safe.
  Queue drain and the existing rebuild/wave-finalization boundaries discharge
  or reject unresolved work; there is no new global compaction barrier.
- Dense `RuleMatchId` order derives from the native ordinal reserved when a
  batch actually begins executing. The full-batch-then-tail canary proves that
  discovery order does not invert replay order, including a 128-lane batch
  whose 127 redundant effects remain unpromoted.
- Candidate-scale durable match/premise/term allocations and eager merge-term
  copies were removed from the serial hot path. Compact pending cause refs,
  current-term arrays, and check-candidate premise IDs remain deliberately
  candidate-shaped. Canaries prove that 100,000 redundant union proposals
  promote zero durable matches, 100,000 no-op constructor collisions copy zero
  prior term vectors, one effective merge-union promotes exactly one shared
  match and predecessor, an unchanged-merge-only firing remains absent, and a
  decomposed rule unfolds only its promoted witness. Positive checks preserve
  their established lexicographic winner semantics: candidate premise IDs and
  witnesses are resolved transiently for comparison, while only the winning
  root and durable terms are published.
- Every serial table merge callback attaches its immutable predecessor
  `FactId` to a compact batch-local lane sidecar before invoking the merge,
  including unchanged `:merge old/new` results. A merge read alone never
  promotes. Reachable matches copy ordered `merge_reads` at wave finalization,
  after every sibling table has drained, so a later no-op merge is retained
  even when an earlier effective sibling provisionally promoted the match.
- Receipt-enabled rule execution, dependency-stratified table merging, table
  insertion/deletion, rebuild scanning, and physical rehash selection are
  serial even under a larger direct-core Rayon pool. Existing parallel
  implementations remain compiled and ordinary-mode coverage remains
  unchanged; causal activation no longer enters a candidate-promoting parallel
  table or rebuild path. The four-thread 20,001-row threshold canary covers
  both rebuild and publication while retaining the exact applied two-leaf
  equality cone.
- Rejected alternatives and corrected assumptions:
  - eagerly rendering structural terms was not needed; compact producer-term
    handles plus promotion-time witness resolution preserve match-time identity;
  - forcing ordinary and causal table insertion through one global serial path
    broke ordinary parallel expectations and was rejected; dispatch now selects
    serial only when receipts are enabled, leaving ordinary and dormant parallel
    implementations intact;
  - recursively validating every nested equality reason as a standalone root
    rejected valid rebuild/congruence histories; only the published root owns
    that precondition, while nested reasons prepare their dependencies.
- Validation from clean checkpoint
  `1872563051efe819959f90d94f9b6e2448ddbe7c`:
  - `cargo test -p egglog-core-relations merge_ --lib -q`: 11 passed, 0 failed.
  - `cargo test -p egglog-core-relations
    causal_receipt_serial_rebuild_congruence_keeps_only_applied_leaves --lib
    -q`: 1 passed, 0 failed.
  - `cargo test -p egglog-core-relations transactional_ --lib -q`: 2 passed,
    0 failed.
  - `cargo test -p egglog-core-relations rebuild_ --lib -q`: 13 passed, 0
    failed.
  - `cargo test -p egglog-core-relations --lib -q`: 142 passed, 0 failed.
  - `cargo check -p egglog-core-relations`: passed with no warnings.
  - `cargo fmt --all -- --check`: passed.
  - `git diff --check`: passed.
- Scope freeze: no deletion/timeline recording, slicer, replay, benchmark, or
  performance claim is included. The worktree remains intentionally
  uncommitted for independent checkpoint review. Checkpoint 2 must extend the
  native lease canary to a removal-only transaction once causal delete
  recording exists; the current language boundary still rejects that path, so
  it is a deletion handoff rather than a checkpoint-1 table-lease omission.

### 2026-07-23 — checkpoint-1 release integration: rebuild term inheritance

- Falsifying release probe from committed checkpoint
  `10342bb9dc7393fc5563e64cdc034a8594704e3f`: Math panicked during rebuild at
  `record_fact_with_terms` with `constructor row result has incompatible
  structural Call metadata`. The lazy-promotion refactor had removed the old
  batch-wide cause preload, but an effective direct rebuild with no explicit
  producer terms then fell through to the global reverse term map. A competing
  current alias for the same e-class value could therefore replace the prior
  fact's immutable match-time syntax.
- The repair remains proportional to effective events. A direct
  `Rebuild`/`ContainerRefresh` cause copies only its referenced prior FactId's
  immutable term slice when `record_fact_with_terms` is committing the new
  fact. Constructor merge inheritance uses the same helper, while the
  candidate/batch-wide rebuild-term preload stays deleted. Cause-arena and
  fact-arena locks are released before replay-term lookup, and rebuild
  inheritance does not increment the candidate merge-copy counter.
- The competing-alias canary installs two structural `Call` terms for one raw
  constructor output, makes the wrong alias win the global reverse map, then
  rekeys the exact source row through a deferred rebuild cause. The new FactId
  retains the prior fact's exact term slice and `FactCause::Rebuild`, while
  `merge_prior_term_copies` remains zero.
- Validation on the repaired source:
  - `cargo build --release -p egglog-experimental`: passed.
  - `RUST_BACKTRACE=1 target/release/egglog-experimental -j 1
    --causal-receipts egglog/tests/math-microbenchmark.egg`: exited 0; the
    former release panic is absent.
  - `RUST_BACKTRACE=1 target/release/egglog-experimental -j 1
    --causal-receipts
    egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg`: exited 0.
  - `cargo test -p egglog-core-relations
    effective_constructor_rebuild_inherits_prior_terms_over_competing_alias
    --lib -q`: 1 passed, 0 failed.
  - `cargo test -p egglog-core-relations rebuild_ --lib -q`: 14 passed, 0
    failed.
  - `cargo test -p egglog-core-relations --lib -q`: 143 passed, 0 failed.
  - `cargo check -p egglog-core-relations`: passed with no warnings.
- These are integration and regression checks, not receipt-overhead benchmark
  measurements. Deletion/timeline recording and all later checkpoints remain
  untouched.

### 2026-07-23 — checkpoint-1 optimization 1: ordered local prior lookup

- Falsifying profile: the coordinator's release Math sample at clean
  `d2a18a827864d12b6ac679eeb3b8d3582c63951c` placed 3,372 of 6,697 samples in
  `ReceiptBatch::cache_prior_fact_terms`. The effective-event repair was
  linearly scanning every fact already appended to the batch for every rebuilt
  fact, making a rebuild-heavy batch quadratic even though only effective
  events copied terms.
- One variable changed: batch-local prior lookup is now allocation-free binary
  search over the existing `(FactId, PendingFact)` vector. A cheap first/last
  range guard sends prior-wave FactIds directly to the shared arena without any
  local comparisons. No per-batch map, counter, eager preload, or additional
  retained memory was introduced.
- The ordering invariant is explicit at append: each batch debug-asserts that
  its new FactId is strictly greater than the preceding local FactId. Global
  atomic allocation may leave gaps when batches interleave, but cannot reverse
  one batch's append order.
- The focused canary gives one batch FactIds 1 and 3 while another batch owns
  FactId 2, then resolves both local endpoints and verifies their exact term
  slices. This exercises ordered lookup across a real global-ID gap rather than
  assuming local density.
- Validation:
  - `cargo test -p egglog-core-relations
    batch_local_prior_lookup_handles_interleaved_fact_ids --lib -q`: 1 passed,
    0 failed.
  - `cargo test -p egglog-core-relations --lib -q`: 144 passed, 0 failed.
  - `cargo check -p egglog-core-relations`: passed with no warnings.
  - `cargo build --release -p egglog-experimental`: passed.
  - direct release Math and Eggcc `-j 1 --causal-receipts` probes both exited
    0. The Math command's diagnostic wall time fell from 11.86s before this
    change to 2.76s in this run, and its printed merge/rebuild split fell from
    1.970s/8.399s to 0.671s/0.414s. These are directional integration probes,
    not the contracted `./bench.py` receipt gate; the coordinator owns that
    measurement.
- Scope remains frozen: no deletion/timeline, slicing, replay, workload cases,
  or benchmark-runner changes.

### 2026-07-23 — checkpoint-1 optimization 2: serial structural maps

- Falsifying profile at clean
  `f18797058aac4c8fc4ac7744c834768c229e20dc`: controlled Math causal receipts
  measured 2.231s versus 0.426s native, with causal phase split
  search/apply/merge/rebuild = 0.170s/0.890s/0.587s/0.389s. No second
  algorithmic hotspot remained; the bounded cluster was structural term
  identity lookup/interning in sharded `DashMap` operations plus hashing and
  library overhead.
- One variable changed: only `ReplayTermStore`'s five hot identity maps
  (`by_node`, `nodes`, `by_value`, `sorts_by_value`, and
  `original_value_by_term`) became separately locked plain Fx hash maps.
  Table layouts, constructor metadata, and container metadata remain DashMaps;
  the atomic ReplayTermId allocator is unchanged.
- Locking stays narrow. Interning is the sole dual-lock operation and always
  acquires `by_node` before `nodes`, publishing the forward node before making
  its reverse identity visible. All other paths copy or clone their result and
  release one guard before touching another map or calling a store method.
  Current-value installation preserves first-wins lookup while still recording
  every structural term's original value and sort membership.
- Existing canaries continue to cover typed sort scoping and competing
  structural aliases. A new four-thread duplicate-intern canary verifies that
  one structural node, one value mapping, and one stable ReplayTermId are
  published under contention; it also exercises the only nested lock order.
- Validation:
  - `cargo test -p egglog-core-relations
    concurrent_replay_term_interning_deduplicates_identical_nodes --lib -q`:
    1 passed, 0 failed.
  - `cargo test -p egglog-core-relations --lib -q`: 145 passed, 0 failed.
  - `cargo test -p egglog causal_receipt --lib -q`: 22 passed, 0 failed.
  - `cargo test -p egglog-experimental causal_receipt --lib -q`: 1 passed, 0
    failed.
  - `cargo check -p egglog-experimental`: passed with no warnings.
  - `cargo build --release -p egglog-experimental`: passed.
  - direct release Math and Eggcc `-j 1 --causal-receipts` probes both exited
    0. The concurrent directional Math probe completed in 2.65s; this is not
    evidence against the controlled 2.231s baseline and is not a benchmark
    claim. The coordinator owns the exact `./bench.py` gate.
  - `cargo fmt --all -- --check`: passed.
- Scope remains frozen: no non-identity map conversion, non-atomic ID
  allocation, deletion/timeline, slicing, replay, or benchmark-runner change.

### 2026-07-23 — checkpoint-1 recording gate: failed after bounded optimization

- The contracted comparison used the same clean final binary for both
  endpoints, the normal append-only `.reports.jsonl`, `main/off` versus
  `main/causal-receipts`, `-j 1` through the benchmark target, a 120-second
  timeout, and the unchanged Math and Eggcc files. The final command was:

  ```sh
  ./bench.py --target . --backend main --treatment causal-receipts \
    --compare-backend main --compare-treatment off --rounds 3 \
    --timeout-sec 120 --report .reports.jsonl --detail files \
    --format markdown egglog/tests/math-microbenchmark.egg \
    egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg
  ```

- At clean commit `41bbe244d63a8f30cb03d820fb55c8d768db1498`, the three exact
  cached rounds were JSONL lines 24-35. Arithmetic means were:

  | Workload | Native wall | Receipts wall | Wall ratio | Native RSS | Receipts RSS | RSS ratio |
  | --- | ---: | ---: | ---: | ---: | ---: | ---: |
  | Math | 0.450s | 2.452s | 5.44x | 256.4 MiB | 1.505 GiB | 6.01x |
  | Eggcc | 1.237s | 1.811s | 1.46x | 121.4 MiB | 213.6 MiB | 1.76x |

  The report's bootstrap intervals were 4.36-6.95x for Math and 1.36-1.59x
  for Eggcc. Eggcc's mean clears the strict wall screen, but its interval
  crosses 1.5x; Math decisively fails both the approximately 1.3x target and
  the 1.5x hard screen.
- Optimization 1 was strongly validated: its clean one-round Math result at
  `f18797058aac4c8fc4ac7744c834768c229e20dc` improved from the pre-fix
  27.0x result to 5.24x by deleting the quadratic prior-fact scan.
  Optimization 2 was not a material second win: the final one-round Math point
  estimate was 5.04x, and the three-round mean remained 5.44x. The serial-map
  change did modestly reduce Eggcc's mean and RSS, but did not alter the Math
  boundary.
- The post-fix Samply artifact is
  `/tmp/egglog-causal-profile-f187970/v3/be3bb6224b720bff873884a513f4d394c1a04c4bbbedc9f0449f2a26fcf1e808/6017cf55fcc0bbc0dfb6c512b1a805709a33ac501b7f72796a74a788c804f77c/no-facts/main-causal-receipts-i1.json.gz`.
  It has no replacement runaway function: the largest application self symbol
  is serial table insertion at 8.5%, followed by structural-map operations,
  fact recording, finalization, witness resolution, and native execution.
  Controlled phase data at `f187970` was native
  search/apply/merge/rebuild = 0.094s/0.096s/0.050s/0.148s versus receipts
  0.170s/0.890s/0.587s/0.389s. Exact-event cost is distributed rather than one
  remaining representation bug.
- Cardinality explains the remaining floor. Math executes 943,125 native rule
  candidates; 810,853 (85.98%) are promoted because they have effective
  effects. Exact capture retains 1,731,581 immutable fact versions, 1,607,701
  durable causes, 439,079 rebuild causes, 182,412 logical equality edges,
  167,956 native aliases, and a 1,398,704-node structural term DAG. This is not
  Prefix or eager losing-candidate elaboration; it is the supported exact-event
  contract applied to a workload with unusually dense effective history.
- Gate decision: stop after the two measured bounded optimizations. Do not
  begin deletion/timeline recording, slicing, grounded replay, or causal-proof
  benchmarking under a failed receipt-cost premise. No Prefix, projection,
  selector search, workload special case, or third architecture is introduced.
  The committed checkpoint remains a coherent, exact, serial recording
  experiment and the replay-independent debugging artifact; reaching the full
  plan now requires an explicit decision to relax the 1.5x screen or change
  the recording contract, not another unmeasured tuning pass.
