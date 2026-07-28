# DuckDB Native SQL Goal State

Updated: 2026-07-28 America/New_York

## Mission

Implement a benchmark-first, proof-agnostic, fully typed DuckDB backend on
current `origin/main`. DuckDB is authoritative for function rows and executes
matching, merges, effects, containers, and rebuild through generated SQL or
safe public vector UDFs. The five frozen non-Herbie proof-mode workloads must
statically lower with no host matching/merge fallback; bounded semantic gates
are blocking, while full-workload timeouts are censored performance results.

## Non-goals and accepted no-go facts

- Do not base the implementation on PR 22, the causal-slicing branches, or a
  dirty donor worktree. They are behavioral or historical oracles only.
- Do not patch or fork `duckdb-rs`; do not use `duckdb::ffi`, private handles,
  transmutation, or backend-owned unsafe code.
- Do not add Appender, Arrow-Appender, `read_csv`, or `COPY` in this goal.
- Rust-parsed input values are rendered with one central, type-aware,
  injection-safe SQL literal encoder and inlined into generated `VALUES` or
  effect SQL. Bound parameters are not the accepted input-ingestion path.
- Do not create ART indexes for ordinary function storage by default, including
  indirectly through `PRIMARY KEY` or `UNIQUE` constraints. Any later index
  must re-enter through measured evidence; correctness uses full typed SQL
  equality and relational consolidation.
- Do not retain a production host matcher, host merge evaluator, function-row
  mirror, or proof-aware storage path.
- Proof-encoding relations and proof IDs are ordinary program data. Durable
  per-row backend metadata is only generation and subsumption state.
- Full `UnstableFn`, causal receipts/replay, Windows support, every example,
  and a standalone full-Math SQL program are outside the blocking scope.
- No subprocess may run longer than 115 seconds.
- Do not push or open a pull request without explicit user approval.

## Provenance

| Item | Identity | Role |
|---|---|---|
| implementation base | `853fbfd533a3f73b390de364d980f3f939427eae` | fresh `origin/main` fetched 2026-07-28 |
| worktree | `/Users/saul/p/wt/egglog-encoding/duckdb-native-sql` | isolated clean checkout |
| branch | `agent/duckdb-native-sql` | tracks `origin/main` |
| PR 22 head | `6b8214090da6ddb2a40088c6fc30f046a57e9e96` | historical proof/backend oracle |
| requested prior art | local `../egglog-duckdb` is absent; exact `oflatt/egglog-duckdb` commit `03ee12c9c433b0a82112a00216d5c03bcabbdd0d` was audited read-only through commit-qualified GitHub content | SQL-expression and probe ideas only; no fetch, checkout, or mutation |
| positive donor | `ae4bb61d822d696ed10206a33c48641736dddb8c` | runtime/build/SQL oracle only |
| intended Rust client | unmodified crates.io `duckdb 1.10504.0` | must be reverified before acceptance |
| intended engine | DuckDB 1.5.4 | must be reverified from the loaded runtime |

The thread-level goal service still contains an older paused attachment-based
objective and rejected creation of the replacement goal. This ledger and the
user's latest explicit implementation request are the active scope authority.

## Frozen primary corpus

| Workload | Source SHA-256 | Fact-directory SHA-256 |
|---|---|---|
| `egglog/tests/math-microbenchmark.egg` | `aaa8942131b4db57e76710486718790e1d7f2cb9288aeb702c0c17019439cf16` | none |
| `egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg` | `23efdf1b2c31b7566c3da3268180ea27076b2563c3c80b545cb59a6270753f4f` | none |
| `benchmarks/pointer-analysis-small.egg` | `dbb091872559ee71f685986f2f49c80ee6c929d72de2843c19688c4677b3f76f` | `c15261f17ff692435f41beafa4de893bb1cca0a36874aafa472bce78781f6e78` |
| `egglog/tests/hardboiled_conv1d_32.egg` | `bd82a9cd8036d123826926ec0189e59a652aa2a9a155dd280d5ea3935b10c005` | none |
| `benchmarks/luminal-llama.egg` | `4bd1d2f346de94b81b359c50d5fb4129f04011128f7442b53adde3731b740dad` | none |

## Semantic canary contract

The backend remains proof-agnostic, but its ordinary relational behavior must
preserve these current SPI semantics:

- one bounded rules run reads a stable pre-wave snapshot; writes become match
  inputs only in a later iteration;
- effects preserve source action order within a firing and flush in
  delete, then set/merge, then subsume order;
- lookup is read-only; repeated lookup-or-insert misses in one action stream
  share one predicted row; a subsumed row still satisfies lookup;
- merge arguments are atomic old/new row snapshots, and merge dependencies and
  rebuilds run to fixed point;
- remove-then-reinsert of an equal logical row is a fresh seminaive event;
- Live, All, and Subsumed reads remain distinct, and subsumption does not erase
  the current function mapping;
- `clone_boxed` produces an independent backend-visible snapshot for push/pop;
- no total global match order is invented beyond guaranteed local action and
  phase ordering;
- causal receipts/history remain optional and out of scope unless explicitly
  advertised by the backend.

## Steering frame

- **Current frontier:** checkpoint 0 is accepted and locally ready to commit.
  The workspace has a current-main DuckDB-authoritative typed storage/input
  scaffold, safe nonbundled runtime path, primary-surface census, and a truthful
  fallible native-input SPI. Checkpoint 0.5 remains open: the next slice is a
  table-only, Set-only production `RuleSpec` SQL compiler with source-driven
  main differentials for the selective Pointer and broad Math kernels.
- **Scoreboard:** current-main pinned; proof baseline and pre-acceptance proof
  gate green (212/212); safe prebuilt runtime is DuckDB v1.5.4; DuckDB backend
  tests 12/12, bridge 26/26, proof-mode regression 12/12, DD 38/38, and
  feature-enabled CLI 4/4 passed. Independent final review is `PASS`.
  Checkpoint 0.5 remains open because its two current SQL kernels are
  feasibility probes rather than production main differentials.
- **Progress signal:** a reviewable production slice plus exact capped command
  evidence that advances one checkpoint gate.
- **No movement:** no reviewable patch, no new reproducible evidence, and no
  decision-narrowing result. A falsified hypothesis counts as movement.
- **Two-cycle trigger:** after two consecutive same-domain no-movement cycles,
  freeze implementation, preserve evidence, and run one bounded
  Understand/Explore/Decide reassessment before resuming.
- **Active risks:** current-main API drift from donor; typed nested value
  boundary limitations in safe `duckdb-rs`; reference native input now clones
  a quiescent bridge state per batch for rollback correctness; DuckDB
  `clone_boxed` still requires a deep database snapshot; scheduler rollback
  currently downcasts to the reference backend; proof-instrumented primitive
  breadth; order-sensitive merge semantics; slow bounded proof workloads.
- **Next decision:** implement the checkpoint 0.5 production RuleSpec slice:
  Live table atoms, typed variables/literals, exactly one table Set head, and
  one-column `MergeFn::Old`, with stable pre-wave staging and per-rule
  generation watermarks. Pass source-driven main differentials for the frozen
  Pointer five-way join and Math Add swap before expanding the supported IR.

## Roster

| Agent | Circle/domain | Aim | Authority and write set | Expected output | Stop |
|---|---|---|---|---|---|
| `/root` | coordinator | preserve mission, integrate checkpoints, own broad/final commands and user communication | shared ledger, diff review, final gates, narrow recorded integration repairs only after worker is seated | accepted checkpoint and next bounded slice | goal completes, evidence rejects architecture, or user decision is required |
| `/root/fallible_input_worker` | checkpoint 0 implementation | deliver the reassessment-authorized fallible native-input boundary | explicitly authorized bridge/backend-trait/frontend/DD/DuckDB files; targeted commands only | accepted fallible-input patch and exact command evidence | completed with independent PASS |
| `/root/checkpoint_reviewer` | independent read-only review | evaluate checkpoint artifacts against scope, safety, semantics, and evidence rubric | no writes; raw diff and raw artifacts only | `PASS`, `REVISE`, or `REASSESS` with live issues separated from stale feedback | one evidence-backed verdict and one bounded re-review if needed |

No overlapping writing worker may be added. Read-only specialist circles may
be seated only for disjoint evidence questions with explicit stop terms.

## Worker contract: checkpoint 0/0.5

- **Hypothesis:** current-main's `Backend`/`RuleSpec` and encoded bulk-input
  surfaces can host a fresh, proof-agnostic DuckDB crate using only safe public
  APIs, with typed SQL storage and no host row mirror.
- **Target artifact:** a minimal workspace-integrated DuckDB backend skeleton
  plus safe API/type/input/kernel probes sufficient to decide the next vertical
  slice; no speculative full compiler rewrite before the probes pass.
- **Expected delta:** `--backend duckdb` is registered behind a feature, the
  crate installs typed scalar tables and transactions, and focused probes prove
  generated SQL `VALUES`, rollback, nested output projection, and representative
  selective/broad match SQL behavior.
- **Owned write set:** root `Cargo.toml`/`Cargo.lock` and, for the first repair,
  root `Makefile` gate wiring;
  `egglog-experimental/Cargo.toml`; `egglog-experimental/src/main.rs`; and new
  `egglog-experimental/duckdb/{Cargo.toml,src/lib.rs,src/storage.rs,
  PRIMARY_SURFACE_CENSUS.md}` with focused probes. No backend-trait or frontend
  changes were authorized in the initial slice; the later recorded reassessment
  explicitly authorized the bridge/backend-trait/frontend/DD input boundary.
- **Forbidden shortcuts:** old downstream-only helpers, bridge authority,
  function-row mirrors, host matching/merge, Appender/file-reader ingestion,
  proof-specific branches, unsafe/private DuckDB APIs, fixture weakening, or
  snapshot masking.
- **Owned commands:** targeted `cargo check`/unit tests and reduced probes, each
  with an external 115-second watchdog.
- **Request-only commands:** full `make check`, `make proof-tests`, and the
  five-workload benchmark matrix; coordinator owns final-gate reruns.
- **Evidence contract:** command, cwd, SHA, features, inputs, exit status,
  duration, artifact/report path, and whether the result is fresh or inherited.
- **Stop:** pass the slice gates; falsify the architectural hypothesis; hit a
  required user decision; or reach two no-movement cycles.

## Checkpoint scoreboard

| Checkpoint | Blocking gate | Status | Evidence |
|---|---|---|---|
| 0 provenance/integration/census | exact refs and primary surface census; plausible safe-native lowering for every reached primary surface | **passed** | worktree/base and frozen corpus pinned; census complete; safe crates.io client and loaded v1.5.4 runtime verified; typed literal/no-ART/transaction/input/CLI surfaces passed focused gates; final independent review PASS |
| 0.5 API/literal/kernel spike | typed input/API probes and two real kernels agree with main on reduced data | not passed | 12/12 DuckDB focused tests pass against loaded DuckDB v1.5.4 through the crate-supported prebuilt path, but the kernels are handwritten feasibility probes rather than production main differentials; bundled source builds are timeout-censored |
| 1 typed IR/storage/input | primary schemas and input commands install; deterministic SQL manifest | pending | |
| 2 SQL matching/transcripts | bounded primary proxies match main without Rust match enumeration | pending | |
| 3 primitives/containers | all five statically compile with deny fallback and run bounded first iteration | pending | |
| 4 native merges/effects/fixed point | canaries and bounded proxies agree; complete rollback; host oracle removed | pending | |
| 4.5 SQL artifact | standalone `hot-scc.sql` reproduces expected digest | pending | |
| 5 acceptance/benchmarks | scoped repository gates plus one capped full attempt per primary workload | pending | |

## Evidence log

| Time | Owner | Command or artifact | Result | Frontier effect |
|---|---|---|---|---|
| 2026-07-28 | coordinator | `git fetch origin main` | `origin/main` advanced to `853fbfd`; completed in 0.3s | established current base |
| 2026-07-28 | coordinator | `git worktree add -b agent/duckdb-native-sql ... origin/main` | clean worktree at `853fbfd` | implementation isolation established |
| 2026-07-28 | coordinator | goal-service replacement attempt | rejected because older goal is paused | recorded infrastructure state; implementation continues from latest user scope |
| 2026-07-28 | coordinator | `/opt/homebrew/bin/timeout --signal=TERM --kill-after=5s 110s make proof-tests` | PASS: core 204/204 plus experimental 8/8; 212 total, zero failures, completed under cap | current-main proof baseline established |
| 2026-07-28 | coordinator | `shasum -a 256 ...`; benchmark harness `sha256_directory` | five source identities and pointer fact-directory identity recorded above | primary corpus frozen reproducibly |
| 2026-07-28 | read-only semantic audit | current Backend SPI, DD differential tests, and committed causal-slice contract at `298053748818f4d826bd0eb27c48a0e06db5071b` | semantic canary contract recorded above; causal history confirmed optional | checkpoint reviews now distinguish required relational semantics from non-goal proof storage |
| 2026-07-28 | implementation worker | current-main SPI, donor, safe `duckdb-rs`, and frozen-corpus census before edits | fresh crate selected; donor wholesale port rejected; exact owned paths recorded; no SPI expansion justified | checkpoint 0/0.5 implementation authorized within narrowed write set |
| 2026-07-28 | read-only donor audit | `ae4bb61d`, PR 22, public `duckdb-rs` 1.10504.0, and remote prior-art commit `03ee12c9` | safe connection/transaction/probe idioms retained; all-BIGINT storage, Appender, host matcher/merge, private/unsafe API rejected | checkpoint implementation has a verified reuse/reimplement boundary |
| 2026-07-28 | implementation worker | two capped `cargo test -p egglog-experimental-duckdb --features bundled --lib` attempts | both exit 124 while compiling the unmodified dependency stack; neither linked nor ran tests | censored build-path evidence, not a semantic failure; repeated bundled-build domain stopped |
| 2026-07-28 | implementation worker | `DUCKDB_DOWNLOAD_LIB=1 ... cargo test -p egglog-experimental-duckdb --no-default-features --lib` | PASS: 7/7 in 37.83s; loaded runtime reports `v1.5.4`; typed schemas, rollback/generation, nested projection, Pointer selective kernel, and Math broad kernel green | checkpoint 0.5 has executable runtime evidence within the cap |
| 2026-07-28 | implementation worker | crate/runtime provenance | `duckdb` and `libduckdb-sys` both `1.10504.0`; official prebuilt archive SHA-256 `3f3c52970ad1407ec5037062e1a5e575b24bd5b993c889f89fe5876eff47782c`, dylib SHA-256 `4890e5b4a340aae7d5fc207d267b9ac78a1578abbc6eec9061a56d086fee93de` | exact tested runtime recorded without patch/fork/system install |
| 2026-07-28 | independent checkpoint review | raw checkpoint 0/0.5 diff and focused prebuilt gates | `REVISE`: bound input parameters violate the SQL-literal lock; ordinary-table PK/`ON CONFLICT` violates no-ART; prebuilt path is unreachable through the CLI feature/standard gates; `add_values` re-reports an already-flushed change and can defer storage errors; kernel probes do not satisfy the main-differential gate. Positive architecture and 8/8 prebuilt tests retained. | authorized one bounded repair; checkpoint remains unaccepted |
| 2026-07-28 | independent checkpoint review | accidental nested-reviewer bundled CLI command under 110-second watchdog | exit 124 while compiling; no semantic evidence, no lingering process, no retry, no source/commit/remote mutation | incident recorded; bundled-build domain remains stopped |
| 2026-07-28 | implementation worker | first bounded repair through the nonbundled prebuilt route | PASS: backend 11/11; feature-enabled CLI 4/4; public CLI invocation, targeted clippy, formatting, and diff checks green; no bundled command | literal/no-ART/transaction/runtime/CLI repair evidence established |
| 2026-07-28 | independent checkpoint re-review | frozen repaired patch plus fresh focused gates and `make proof-tests` | `REASSESS`: all requested repair areas passed except `dump_debug_info` consumed the sticky input-error latch; proof gate 212/212; no edits or bundled command | triggered the recorded Understand/Explore/Decide step instead of another silent micro-fix |
| 2026-07-28 | two independent read-only reassessment circles plus coordinator source audit | void `Backend::add_values`, term-encoding maintenance sequencing, `(fail ...)`, and diagnostic boundary alternatives | confirmed the reviewed bug and a broader temporal-coupling hole: an input failure can be logged as success and misclassified by `(fail ...)` before an out-of-block maintenance run. Chose a fallible shared input boundary; rejected eager panic and a permanent sticky input poison channel. | authorized one bounded SPI correction; DuckDB storage architecture retained |
| 2026-07-28 | reassessment implementation worker | fallible `Backend::add_values`; atomic bridge `try_add_values`; DD/DuckDB direct errors; exact term-only `Fail([Input])`; separate DuckDB deferred-rule-panic channel | PASS: bridge 26/26, proof-mode regression 12/12, DD 38/38, DuckDB 12/12, feature CLI 4/4, trait tests/docs, scoped clippy, fmt, and diff checks; no bundled command | input failures now propagate before success logging and all three backends remain usable after rejected input |
| 2026-07-28 | independent final review | frozen fallible-input artifact, including quiescent bridge checkpoint and staged-notification canary | `PASS`: preexisting staged work commits before checkpoint, failed input rows/counters/timestamps roll back, shared panic channel is cleared safely, later flush is sound, exact fail admission cannot mask siblings, and full proofs still reject | checkpoint 0 accepted; checkpoint 0.5 remains explicitly open |
| 2026-07-28 | coordinator | `/opt/homebrew/bin/timeout --signal=TERM --kill-after=5s 110s make proof-tests` on the final accepted patch | PASS: core 204/204 plus experimental 8/8; 212 total, zero failures, completed under cap | final checkpoint-0 proof gate confirmed after bridge rollback correction |

## Review rubric

An advancing checkpoint receives independent read-only review of:

1. owned-path scope and preservation of unrelated changes;
2. safe documented DuckDB APIs and absence of unsafe/private escape hatches;
3. DuckDB authority and absence of proof-specific or host-match/merge fallback;
4. semantic/error/rollback coverage, including input and generation behavior;
5. raw diff, commands, reports, provenance, timeouts, and cache isolation;
6. repository-prescribed checks appropriate to the checkpoint.

One worker repair and re-review is allowed. A second rejection changes the
frontier to reassessment rather than another micro-variant.

## First bounded repair contract

- Add one central type-aware, injection-safe SQL literal encoder and use it for
  all Rust-parsed input rows. Inline typed `VALUES`; production ingestion must
  contain neither placeholders nor `params_from_iter`. Cover adversarial UTF-8
  strings (quotes, comment/statement text, NUL, Unicode), integer extrema, and
  floating-point finite/signed-zero/NaN/infinity cases.
- Remove every `PRIMARY KEY`/`UNIQUE` constraint and ART index from ordinary
  function tables. Preserve first-incoming-row-wins and existing-row-wins with
  ordinal `row_number` plus full typed-equality `NOT EXISTS` consolidation in
  the same serial transaction. Assert zero ordinary function indexes. Replace
  the rollback test's unique-index fault with an index-free constraint fault.
- Make bundled DuckDB explicitly opt-in. `duckdb-backend` activates the
  dependency without forcing bundled, and repository gates exercise the
  feature-enabled CLI/backend through `DUCKDB_DOWNLOAD_LIB=1`. Do not attempt
  another bundled build in this repair.
- Do not latch `changed` after `add_values`, which already flushes. Add a
  regression asserting the following `flush_updates` is false.
- Surface stored input errors at the next observable backend operation rather
  than only at a later nonempty `run_rules`; add an input-only failure test.
- Re-run the focused prebuilt tests/checks under the 110-second command cap and
  reconcile this ledger. Do not claim the checkpoint 0.5 kernel gate: the
  existing Pointer/Math SQL tests remain useful feasibility evidence only.

## Reassessment decision: fallible native input

- Change `Backend::add_values` to return `anyhow::Result<()>` and update the
  reference adapter, DD backend, and DuckDB backend. This is the narrow shared
  API change justified by the second-cycle evidence.
- Have `native_input` propagate the backend error as `Error::BackendError`
  before emitting its success log. This makes direct frontend input and input
  inside `(fail ...)` truthful without depending on a later maintenance run.
- The reference adapter calls bridge `try_add_values`: it flushes and validates
  preexisting staged work, clones only a quiescent bridge state, and restores
  that checkpoint on a batch merge failure. DD returns its existing fallible
  merge-aware `apply_sets`; DuckDB returns its transactional `insert_batch`
  result directly.
- Remove input failures from DuckDB's deferred-panic latch. Retain a separate
  deferred rule-panic channel for `Backend::new_panic`, whose documented
  delivery boundary remains `run_rules`.
- Diagnostics must never consume a deferred rule error. `runtime_version` is a
  provenance helper, not an error-delivery boundary; `dump_debug_info` may
  report pending diagnostics but must leave the channel intact.
- Focused gates must cover immediate input error propagation, rollback and
  continued usability, DD/reference compilation, and `(fail ...)` propagation
  at the frontend boundary. No bundled build is authorized.

## Next action

Commit the accepted checkpoint 0 locally without pushing. Then seat one bounded
implementation worker for the checkpoint 0.5 table-only/Set-only production
RuleSpec compiler and source-driven main differentials. Do not claim checkpoint
0.5 until both production differentials pass.
