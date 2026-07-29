# DuckDB Native SQL Goal State

Updated: 2026-07-29 America/New_York

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
- No subprocess may run longer than 110 seconds.
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

- **Current frontier:** checkpoints 0 and 0.5 plus typed storage, native input,
  path compression, and direct cleanup are committed through `21b482b`. The
  accepted standard scalar rebuild artifact now compiles exact eq-key and
  eclass-output `ReadMode::All` rules and executes their typed View/UF
  ordered-union merges through DuckDB-authoritative staged queues. It passed
  three independent reviews, one bounded repair, and fresh coordinator
  acceptance at owned hash `4c3acea8...`. Math, Eggcc, Hardboiled, and Luminal
  now reach marker rekey; Pointer admits its first rebuild and reaches the
  independently identified raw-input/Block-write boundary. The next diagnostic
  frontier is therefore two disjoint capabilities—marker rekey and typed raw
  input—not performance tuning or container/custom merge work.
- **Scoreboard:** current-main pinned; loaded DuckDB v1.5.4; DuckDB backend
  tests 61/61 and feature-enabled CLI 4/4 pass; both scoped Clippy lanes with
  warnings denied, feature build, formatting, and diff checks pass. Fresh
  public boundary timings are Math 0.256s, Eggcc 0.336s, Pointer 0.368s,
  Hardboiled 0.312s, and Luminal 0.241s, with no timeout. The repository proof
  gate remains green at core 204/204 plus experimental 8/8 (212/212) in 28.09s.
  All frozen reviews pass at owned hash
  `4c3acea85587ff222842bcadde867c89557e7cb63959733078e7f0c6e14f175c`.
- **Progress signal:** a reviewable production slice plus exact capped command
  evidence that advances one checkpoint gate.
- **No movement:** no reviewable patch, no new reproducible evidence, and no
  decision-narrowing result. A falsified hypothesis counts as movement.
- **Two-cycle trigger:** after two consecutive same-domain no-movement cycles,
  freeze implementation, preserve evidence, and run one bounded
  Understand/Explore/Decide reassessment before resuming.
- **Active risks:** reference native input clones a quiescent bridge state per batch
  for rollback correctness; DuckDB `clone_boxed` still requires a deep database
  snapshot; scheduler rollback currently downcasts to the reference backend;
  proof-instrumented primitive breadth; order-sensitive merge semantics; public
  result transport for future nested container columns without a client patch;
  DuckDB BIGNUM has a finite domain and exact-number readback relies on the
  pinned v1.5.4 canonical decimal projection;
  the benchmark harness does not yet advertise the DuckDB endpoint; direct
  execution of the downloaded dylib needs its dependency directory added to
  `DYLD_LIBRARY_PATH` on macOS; and slow bounded proof workloads.
- **Next decision:** seat one DuckDB-only writer for the reconciled standard
  scalar rebuild contract below. Freeze its first reviewable artifact before
  independent semantic, admission, and safe-SQL/test reviews; no marker,
  container, custom-merge, or performance expansion may enter this slice. Preserve
  UnstableFn as schema-only deferred: hardboiled stores only its `ColumnTy::Id`,
  while no frozen workload constructs or applies one.

## Roster

| Agent | Circle/domain | Aim | Authority and write set | Expected output | Stop |
|---|---|---|---|---|---|
| `/root` | coordinator | preserve mission, integrate checkpoints, own broad/final commands and user communication | shared ledger, diff review, final gates, narrow recorded integration repairs only after worker is seated | accepted checkpoint and next bounded slice | goal completes, evidence rejects architecture, or user decision is required |
| `/root/fallible_input_worker` | checkpoint 0 implementation | deliver the reassessment-authorized fallible native-input boundary | explicitly authorized bridge/backend-trait/frontend/DD/DuckDB files; targeted commands only | accepted fallible-input patch and exact command evidence | completed with independent PASS |
| `/root/rule_sql_worker` | checkpoint 0.5 implementation | deliver the smallest production SQL-native rule compiler plus real main differentials | DuckDB crate and focused tests only; no shared SPI/frontend edits without a stop-and-review | table-only/Set-only compiler, Pointer/Math transcripts, exact gate evidence | completed; both differentials and canaries pass |
| `/root/primary_lowering_frontier` | checkpoint 1 read-only diagnosis and downstream SQL blueprint | locate the first unsupported production surface, then prepare the exact staged-wave implementation without observing the moving writer diff | committed blobs only for the follow-up; no writes/builds/tests or writer contact | exact failure matrix, scratch schemas, wave algorithm, primitive dispatch, canaries, and any unavoidable remaining SPI blocker | follow-up active; one bounded advisory report is the stop |
| `/root/primary_schema_merge_census` | checkpoint 1 read-only schema/merge diagnosis | enumerate public proof-lowered schemas and merge trees without admitting unsupported execution | no writes; symbolic frontend/config inspection and source evidence only | exact shared prefix, full merge/type distribution, and narrow SPI recommendation | completed with a 9,344-config census and common 23-table prefix |
| `/root/merge_assert_codec_worker` | checkpoint 1 implementation | advance all five public workloads through the common proof table prefix using real SQL-native semantics | DuckDB crate, its focused tests/census, and mechanical DuckDB dependency lock changes only; no shared SPI, frontend, DD, fixtures, or benchmark harness | native one-output `AssertEq`, lossless config admission, typed exact-number codecs, and a public boundary that reaches the first generated rule | completed; artifact frozen without commit or push and all focused gates passed |
| `/root/codec_public_api_audit` | checkpoint 1 read-only codec review | verify exact safe public APIs and SQL forms for lossless BIGNUM/BigRat/Rational construction and projection | no writes/builds; pinned dependency source, engine docs/tests already present locally, and current crate only | implementation-ready codec constraints and failure canaries | completed; typed storage plus canonical SQL text projection is the sole safe public design |
| `/root/assert_eq_semantics_audit` | checkpoint 1 read-only semantic review | pin AssertEq behavior, config admission invariants, and rollback hazards against current main/DD | no writes/builds; current source/tests and frozen diff only | exact conformance matrix and likely defect probes for independent review | completed; existing SPI suffices for the bounded slice, with one fresh-ID caveat |
| `/root/checkpoint_reviewer` | independent read-only review | evaluate checkpoint artifacts against scope, safety, semantics, and evidence rubric | no writes; raw diff and raw artifacts only | `PASS`, `REVISE`, or `REASSESS` with live issues separated from stale feedback | one evidence-backed verdict and one bounded re-review if needed |
| `/root/checkpoint_1_reviewer` | checkpoint 1 independent read-only review | evaluate the frozen shared-prefix slice against reference semantics, transactionality, codec boundaries, and evidence | no writes/builds/tests; complete raw diff plus pinned source only | formal verdict with code defects separated from ledger drift | completed final `PASS` after one ledger/evidence-only repair; no implementation defect found |
| `/root/primary_lowering_frontier` and subcircles | path-compression IR/SPI diagnosis | pin the exact first rule/config across all five workloads and identify the smallest non-special-cased continuation | committed-source/desugar inspection only; no writes or DuckDB execution | exact RuleSpec, merge tree, shared blockers, canaries, and writer contract | completed; all five are isomorphic and a DuckDB-only admission patch is rejected |
| `/root/causal_semantics_audit/committed_semantics_review/duckdb_contract` | independent semantic contract | separate mandatory observable semantics from SQL-physical choices using current reference/DD and committed causal lessons | committed blobs only; no writes/builds/tests | old/new tuple, action/fresh/fixed-point/generation/rollback matrix | completed; native staged-wave design is coherent after typed merge metadata |
| `/root/sql_artifact` | independent SQL architecture | compare multi-statement work queues with a tagged recursive CTE for the exact frontier | safe public DuckDB 1.5.4 SQL/source only; no writes/builds/tests | two materially different designs and bounded recommendation | completed; staged work queues recommended first, recursive CTE retained as the second design |
| `/root/typed_merge_input_spi_worker` | checkpoint 1 shared prerequisite | preserve reference/DD behavior while making merge calls typed and native input fresh allocation atomic | recorded bounded write set plus the allocator-boundary and direct-DD amendments below | independently reviewable typed merge IR plus fresh-slot batch boundary | completed at code hash `514583114d774461886f81f899bf1ad775a2f1973a957bbedfb0ee5dbcf457cd`; focused and broad gates pass |
| `/root/spi_prereq_final_reviewer` and allocator/direct-path subreviews | independent prerequisite final review | audit the frozen code diff against the typed-merge, transaction, counter, proof-registration, and public-API contracts | read-only frozen diffs; no builds/tests/writes or writer contact | `PASS`, `REVISE`, or `REASSESS` with live defects separated from later SQL/container work | final `PASS` after allocator-boundary reassessment and one narrow DD direct-primitive parity repair |
| `/root/duckdb_path_compress_worker` | DuckDB-local path-compression implementation | compile the exact reached structural rule and typed UF Block into native staged SQL | `egglog-experimental/duckdb/**` only; no shared SPI, frontend, DD, harness, manifest, fixture, or snapshot edits | source-independent canaries plus all five public probes beyond `@uf_path_compress` | bounded repair completed and frozen at owned artifact hash `774c919ad247ffd59cacf39c216c8296af022662be16900ea8148f56b6f10275`; no commit or push |
| `/root/path_compress_ir_audit` | read-only exact IR audit | freeze the backend-facing rule/config/merge shape and next likely frontier | committed HEAD `14a2d5d`; no writes/builds or writer contact | structural admission predicate, typed action/merge order, canaries | completed; all five graphs agree and the next frontier is the generated two-Delete cleanup rule |
| `/root/staged_wave_sql_audit` | read-only SQL architecture audit | adversarially specify transaction/work-queue semantics using safe public DuckDB 1.5.4 | committed HEAD `14a2d5d`; no writes/builds or writer contact | scratch schemas, SQL phases, wave/fold/allocation/rollback risks | completed; staged typed queues are feasible without another SPI change |
| `/root/path_primitive_lowering_audit` | read-only primitive audit | pin every primitive reached by the path rule/UF Block and its exact typed SQL semantics | committed HEAD `14a2d5d`; no writes/builds or writer contact | stable names, types, tie/failure behavior, lowering requirements | completed; six stable typed signatures suffice and unknown calls remain fail closed |
| `/root/path_semantics_review` | independent frozen semantic review | audit stable pre-wave, global folds, identity, fresh ordering, rollback, generation, and absence of host enumeration | exact frozen owned artifact only; no writes/builds/tests or writer contact | `PASS`, `REVISE`, or `REASSESS` with exact source evidence | completed `PASS`; executor unchanged by the bounded repair |
| `/root/path_admission_review` | independent frozen admission review | audit name-independent typed topology validation and pre-mutation failure boundaries | exact frozen owned artifact only; no writes/builds/tests or writer contact | `PASS`, `REVISE`, or `REASSESS` with exact source evidence | repaired-surface re-review completed `PASS`; exact eight-role/config/canary/RuleId findings closed |
| `/root/path_api_tests_review` | independent frozen API/test review | audit public API, forbidden shortcuts, scratch lifecycle, literal SQL, and canary sufficiency | exact frozen owned artifact only; no writes/builds/tests or writer contact | `PASS`, `REVISE`, or `REASSESS` with exact source evidence | repaired-surface re-review completed `PASS`; telemetry wording and 38-test accounting reconciled |
| `/root/delete_ir_census` | read-only cleanup-rule IR census | pin the first two-Delete rule across all five programs and its next public boundary | clean committed `578f53b`; no writes/builds/tests or writer contact; capped desugar/public probes only | exact typed graph, structural admission, distribution, canaries, and writer recommendation | completed `PASS`; 2,169 schema-parametric Delete rules, key arity 0..27, then the paired Subsume rule |
| `/root/delete_semantics_audit` | independent cleanup semantic audit | separate mandatory Delete/phase/generation/subsumption/rollback semantics from SQL choices | clean committed `578f53b`; current Reference/DD source only; no writes/builds/tests or writer contact | implementation/review matrix and existing-SPI verdict | completed `PASS`; main/DD Delete-report divergence and exact generated Subsume contract pinned |
| `/root/delete_sql_architecture` | read-only safe-SQL cleanup design | design the smallest general SQL-native cleanup lowering over the accepted executor | clean committed `578f53b`; safe public DuckDB 1.5.4 and current source only; no writes/builds/tests or writer contact | scratch/effect phases, alternatives, risks, canaries, and recommendation | completed; generic direct effect list selected over a proof-cleanup executor or table rewrite |
| `/root/duckdb_cleanup_effect_worker` | DuckDB-local direct cleanup implementation | compile native Delete effects and the body-bound one-Subsume subset with global effect phases | `egglog-experimental/duckdb/**` only; no shared SPI/frontend/DD/harness/manifest/fixture/snapshot/ledger edits | source-independent canaries and all five public probes beyond Delete/Subsume cleanup registration | bounded repair completed and frozen at owned hash `fc55d94180d70f0e98045d9a947c19165f9ae9399297bbaa5c159e03589c6a6c`; no executor redesign, commit, or push |
| `/root/cleanup_semantics_review` | independent frozen cleanup semantic review | audit stable pre-wave, effect phases, change split, generation, same-key Subsume, rollback, and watermarks | exact frozen owned artifact only; no writes/builds/tests or writer contact | `PASS`, `REVISE`, or `REASSESS` with exact source evidence | completed `PASS`; main/DD divergence correctly isolated |
| `/root/cleanup_admission_review` | independent frozen cleanup admission review | audit typed/name-independent effect languages, pre-RuleId failures, safe scope, and forbidden shortcuts | exact frozen owned artifact only; no writes/builds/tests or writer contact | `PASS`, `REVISE`, or `REASSESS` with exact source evidence | repaired-surface re-review completed `PASS`; Delete priority, mixed rejection, RuleId, and exact path validation closed |
| `/root/cleanup_sql_tests_review` | independent frozen SQL/test review | audit keyed/nullary SQL, deterministic staging, scratch, telemetry, and meaningful canaries | exact frozen owned artifact only; no writes/builds/tests or writer contact | `PASS`, `REVISE`, or `REASSESS` with exact source evidence | completed `PASS`; repaired 48-test inventory and telemetry/docs coherent |
| `/root/rebuild_ir_census` | read-only rebuild-frontier census | pin every first reached `@rebuild_rule` shape across the five frozen workloads and its next boundary | clean committed `21b482b`; capped read-only probes/desugaring and committed source only; no writes/build products/commits/pushes or writer contact | exact typed RuleSpec/config distribution, structural admission predicate, canaries, and existing-SPI verdict | completed; 3,892 rules collapse to six classes, and the two standard scalar forms move every workload to marker rekey |
| `/root/readmode_all_semantics` | independent `ReadMode::All` semantic audit | separate mandatory rebuild visibility/fixed-point/merge/rollback behavior from DuckDB-physical choices | clean committed `21b482b`; current Reference/DD and accepted DuckDB source only; no writes/builds/tests or writer contact | implementation/review matrix, divergences, canaries, and SPI verdict | completed; Reference-authoritative All/refiring/merge/phase/rollback contract pinned; existing SPI suffices |
| `/root/rebuild_sql_architecture` | read-only safe-SQL rebuild design | compare two materially different SQL-native lowerings for the exact frontier | clean committed `21b482b`; safe public DuckDB 1.5.4 and accepted DuckDB source only; no writes/builds/tests or writer contact | scratch/phase design, deterministic scheduling, risks, recommendation, and stop rule | completed; typed multi-statement queues selected, recursive `USING KEY` retained only as the second design |
| `/root/duckdb_rebuild_worker` | DuckDB-local standard scalar rebuild implementation | compile eq-key and eclass-output rebuilds into a target-typed View-to-UF staged merge queue | `egglog-experimental/duckdb/**` only, excluding this ledger; no shared SPI/frontend/DD/harness/manifest/fixture/snapshot edits | source-independent canaries plus the corrected public registration/input boundaries | completed and frozen at owned hash `fd1a712a55cb492d670b070a0cbcd9c7acd608387cb7cce0979d5311b512a28b`; no commit or push |
| `/root/rebuild_semantics_review` | independent frozen rebuild semantic review | audit All visibility/refiring, stable pre-wave phases, split body/output UFs, merge orientations, status/generation/change, allocation, rollback, and watermarks | exact frozen owned hash only; no writes/builds/tests or writer contact | `PASS`, `REVISE`, or `REASSESS` with exact source evidence | completed `PASS`; no production semantic defect |
| `/root/rebuild_admission_review` | independent frozen rebuild admission review | audit exact tri-state/name-independent topology, RuleId preservation, split-UF routing, and fail-closed marker/custom/container variants | exact frozen owned hash only; no writes/builds/tests or writer contact | `PASS`, `REVISE`, or `REASSESS` with exact source evidence | repaired-surface re-review completed `PASS`; tri-state ownership and negative matrix closed |
| `/root/rebuild_sql_tests_review` | independent frozen rebuild SQL/test/API review | audit typed/nullary/wide SQL, wave/scratch lifecycle, safe public APIs, forbidden surfaces, telemetry, and canary/evidence sufficiency | exact frozen owned hash only; no writes/builds/tests or writer contact | `PASS`, `REVISE`, or `REASSESS` with exact source evidence | repaired-surface re-review completed `PASS`; all three canary-evidence gaps closed |

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
| 0.5 API/literal/kernel spike | typed input/API probes and two real kernels agree with main on reduced data | **passed** | 19/19 DuckDB tests pass against loaded DuckDB v1.5.4; reduced source-pinned Pointer and Math fixtures use production `add_rule`/`run_rules` on independently constructed main and DuckDB state and agree across initial/fresh/no-delta transcripts; independent implementation review found no live defect |
| 1 typed IR/storage/input | primary schemas and input commands install; deterministic SQL manifest | **in progress; path-compression and cleanup verticals passed** | full config retention, typed BigInt/BigRat/Rational storage, native AssertEq, typed merge primitive/constants, atomic dense fresh slots, one SQL-authoritative DuckDB counter, bounded host-counter allocation, structural path compression, and direct Delete/body-bound Subsume effects through native staged SQL are accepted. All five now advance to the common rebuild rule requesting `ReadMode::All`; the general deterministic manifest remains open. |
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
| 2026-07-28 | checkpoint-0.5 implementation worker | production Live-table/one-Set/one-output-Old `RuleSpec` compiler; stable pre-wave stages; one transaction; per-rule watermarks; typed relational consolidation | PASS: DuckDB 19/19, Pointer and Math main differentials 2/2, scoped clippy with warnings denied, formatting and diff checks; no bundled command | handwritten probes are no longer the production-kernel gate; complete workload lowering remains unsupported and unclaimed |
| 2026-07-28 | checkpoint-0.5 bounded measurements | one warm-up plus three execution-only samples per reduced fixture | Pointer 1.695-2.243 ms; Math 0.829-1.021 ms; explicit statement count is `1 + 4N + (changed ? 1 : 0)` excluding transaction begin/commit | descriptive evidence recorded with no threshold or tuning loop |
| 2026-07-28 | coordinator | fresh nonbundled DuckDB gate plus `/opt/homebrew/bin/timeout --signal=TERM --kill-after=5s 110s make proof-tests` | PASS: DuckDB 19/19 in 0.08s test time; core 204/204 plus experimental 8/8 in 22.5s wall; clippy, fmt, and diff checks pass | checkpoint-wide regression evidence refreshed under the command cap |
| 2026-07-28 | independent checkpoint-0.5 review | frozen implementation, compiler admission, transaction/watermark semantics, differential scope, and exact documentation follow-up | initial `REVISE` only for stale ledger text; no implementation defect found; fresh reviewer timings Pointer 1.59-1.91 ms and Math 0.68-1.08 ms; documentation-only re-review `PASS` | checkpoint 0.5 accepted; complete-program lowering remains the next frontier |
| 2026-07-28 | coordinator | feature-enabled public DuckDB CLI on current HEAD, nonbundled downloaded v1.5.4 runtime, `--backend duckdb --proofs --mode no-messages` | Math built and then failed closed at table registration: `DuckDB add_table(@PCons) failed: only one-column MergeFn::Old ...`; direct invocations of all other frozen workloads reached the same boundary when the dylib dependency directory was supplied | established one common production boundary rather than five speculative surface lists |
| 2026-07-28 | read-only lowering frontier | proof desugaring, exact public-path failures, and reached action/primitive inspection for the five frozen workloads | `@PCons` is a materially scheduled proof table, not an unused declaration; its generated sets appear throughout desugared Math. After admitting the common prefix, the next command is generated `uf_path_compress`, with multiple actions and primitive `!=` | selected native `AssertEq` as real progress and reserved path compression for the following checkpoint |
| 2026-07-28 | read-only schema/merge census | symbolic public proof-lowered `FunctionConfig` census without source changes | 9,344 configurations total: Math 75, Eggcc 1,334, Pointer 207, Hardboiled 587, Luminal 7,141. Reached top-level merges are AssertEq 6,819, Old 182, Block 2,342, and one Columns; proof instrumentation adds BigInt, BigRat, and Rational columns to every public path. All five share 23 configurations before the first generated rule: 21 one-output AssertEq, one Old, and one two-output identity Block. | corrected the six-scalar census and bounded checkpoint 1 to exact-number storage plus native AssertEq/config retention |
| 2026-07-28 | independent AssertEq/config audit | current backend contract, reference bridge, DD merge evaluator/tests, and DuckDB checkpoint-0.5 implementation at `1d009896` | existing SPI can retain/admit complete configs and provide atomic DuckDB row/generation/watermark rollback. Conflict detection must precede ranking, include subsumed existing rows, and observe earlier scheduled-rule inserts; frontend-minted fresh IDs remain outside `add_values` rollback. | supplied the checkpoint review matrix and recorded the only shared-boundary caveat without widening this slice |
| 2026-07-28 | independent safe-public codec audit | crates.io `duckdb`/`libduckdb-sys` 1.10504.0 source plus pinned `num` 0.4.3 family | no direct high-level BIGNUM or STRUCT bind/read exists; the viable path is physical BIGNUM and typed numerator/denominator STRUCT columns, generated canonical decimal casts on ingress, and SQL-side canonical text projection on egress. BigRat/Rational must normalize before storage; hostile Rational64 pairs must return errors rather than invoke fixed-width sign overflow. | resolved the client-boundary risk without patch/fork/unsafe and supplied corruption/domain canaries; BIGNUM's finite 8,388,607-byte engine limit remains fail-closed |
| 2026-07-28 | coordinator | direct launch and benchmark-harness inspection | the downloaded `libduckdb.dylib` binary needs `target/debug/deps` in `DYLD_LIBRARY_PATH` when launched directly on macOS; `bench.py` currently advertises only main/DD backends, and Pointer must be a separate fact-directory invocation | recorded a later harness integration requirement without mixing it into the semantic slice |
| 2026-07-28 | checkpoint-1 implementation worker | frozen dirty artifact at HEAD `1d0098966d67f0e2390561e6a1f844519b594bfc`; `git diff \| shasum -a 256` and production-path diff excluding coordinator-owned `STATE.md`, repository root | fresh pre-reconciliation full-diff identity `bbfbe75f1105bde4f71f88d6a809e2b04f60e0e05ea3584ebe17f85d6033294a`; production-path identity remains `e1c6089d736801b1c25c79b806df2a944d1196d6b9ad1147fd1d0103ebdd3b61` after the ledger-only repair; eight expected modified paths; no external artifact, commit, or push | established the exact candidate reviewed and tested below while allowing the durable ledger to record its own reconciliation |
| 2026-07-28 | coordinator | `/opt/homebrew/bin/timeout --signal=TERM --kill-after=5s 110s env -u DUCKDB_LIB_DIR -u DUCKDB_INCLUDE_DIR -u DUCKDB_STATIC DUCKDB_DOWNLOAD_LIB=1 cargo test -p egglog-experimental-duckdb --no-default-features --lib`, repository root, frozen dirty diff | fresh PASS: 27/27 in Cargo-reported 0.08s, exit 0; no retained artifact | native AssertEq, config, codecs, rollback, differentials, and no-ART canaries pass |
| 2026-07-28 | coordinator | same capped nonbundled environment with `cargo clippy -p egglog-experimental-duckdb --no-default-features --lib --tests -- -D warnings`; `cargo test -p egglog-experimental --features duckdb-backend --bin egglog-experimental`; `cargo build -p egglog-experimental --features duckdb-backend --bin egglog-experimental`; `cargo fmt --all --check`; `git diff --check` | fresh exits 0; clippy green, CLI 4/4, build green, format/diff green; build artifact `target/debug/egglog-experimental` | candidate compiles through the supported public feature path without bundled DuckDB |
| 2026-07-28 | coordinator | five direct `target/debug/egglog-experimental --backend duckdb --proofs --mode no-messages` invocations under 110s with `DYLD_LIBRARY_PATH=target/debug/deps`; frozen sources above and Pointer's frozen `-F` directory | fresh exits 1 at the same intentional boundary: `@uf_path_compress` has four actions. Tool wall times: Math 0.437s, Eggcc 0.529s, Pointer 0.494s, Hardboiled 0.466s, Luminal 0.426s; no report artifact | all public paths advance beyond `@PCons`; timeout/performance is not involved |
| 2026-07-28 | coordinator | `/opt/homebrew/bin/timeout --signal=TERM --kill-after=5s 110s env -u DUCKDB_LIB_DIR -u DUCKDB_INCLUDE_DIR -u DUCKDB_STATIC make proof-tests`, repository root, frozen dirty diff | fresh PASS: core 204/204 plus experimental 8/8, exit 0, 29.37s wall; no retained artifact | current reference proof suite remains green |
| 2026-07-28 | independent checkpoint-1 review | frozen eight-path diff and current reference semantics; no writes/builds/tests | `REVISE` for stale ledger/evidence only; implementation, transaction, codec, reference, and test subreviews found no code defect; residual coverage gaps and fresh-ID/clone boundaries recorded above | authorized one documentation-only reconciliation and bounded re-review; code remains frozen |
| 2026-07-28 | independent checkpoint-1 documentation re-review | reconciled `STATE.md`, frozen non-ledger diff `e1c6089d736801b1c25c79b806df2a944d1196d6b9ad1147fd1d0103ebdd3b61`; no writes/builds/tests | final `PASS`; frontier, in-progress checkpoint status, provenance-complete evidence, residual risks, and next action agree | shared-prefix slice accepted for a local checkpoint commit; complete checkpoint 1 remains open |
| 2026-07-28 | coordinator | local checkpoint commit | `f9d07ebd57712a102b08969cd3b130411346aa04 feat: add typed AssertEq DuckDB storage`; clean worktree; no push | accepted shared-prefix slice is now a durable rollback point |
| 2026-07-28 | read-only exact RuleSpec census | five proof-mode desugar invocations, each under a 20-second cap, plus committed lowering source | all five first rules are isomorphic: two Live UF atoms, `!=`, one `get-fresh!`, its SSA alias, `Trans` Set, and tuple UF Set; the complete desugared corpus contains 174 instances of this one shape | removed action-count ambiguity and proved one structural lowering can advance every primary workload |
| 2026-07-28 | three independent read-only path/merge audits | current bridge/DD merge evaluators, exact `FunctionConfig`, backend SPI, and safe DuckDB SQL design at clean `f9d07eb` | effective path compression necessarily executes the identity-changing UF `Block`; merge primitives retain only opaque IDs and constants are untyped, so a DuckDB-only native compiler would require a host callback, registration-order guess, or proof-specific branch | authorized one shared typed-merge prerequisite; admission-only work is a recorded no-go |
| 2026-07-28 | independent SQL architecture audit | staged per-key work queues versus tagged `USING KEY` recursion | both are feasible after typed merge metadata; staged queues preserve one old/new fold per key per wave and isolate failures, while the recursive CTE remains a higher-risk artifact/performance alternative | selected staged multi-statement waves without a statement-count performance gate |
| 2026-07-28 | independent prerequisite pre-review | committed source at `1b2a2252c2f8e77610db6b8d674c97910ce15acb`; no writer diff, builds, tests, or writes | `REVISE`: `id_counter()` currently controls both generic fresh registration and proof-container callbacks, so a DuckDB dummy counter or SQL-calling host callback would violate single-counter authority. Dense-slot, sentinel, and rollback traps were also pinned. | amended the sole writer's scope to split native-fresh capability from host `CounterId`; DuckDB registration is a fail-closed semantic token pending native SQL lowering |
| 2026-07-28 | read-only staged-wave blueprint | exact committed path rule, UF Block, reference/DD merge semantics, and current DuckDB transaction boundary at `1b2a225`; no moving-diff reads, builds, tests, or writes | no further shared SPI is needed after this prerequisite. One logical wave must contain repeated one-candidate-per-key fold passes; all original candidates drain before Block-generated `w+1` candidates become eligible. Head IDs precede Block IDs and all effects/counters/scratch share one transaction. | implementation-ready scratch schemas, typed primitive table, allocation order, 13 source-independent canaries, and a DuckDB-local writer contract are available after prerequisite acceptance |
| 2026-07-28 | independent prerequisite final review | frozen 11-file code diff `1298c02903095b204f8e396dec55108a8e1f2794b5036de53f8ab316225dea37`; static bridge/frontend, metadata/typechecker, DD rollback, and DuckDB transaction subreviews | `REVISE`: reference/DD checked capacity only for explicit slots; the same batch could mint `u32::MAX` through collision-time `Lookup`/`DefaultVal::FreshId` and commit a stale/wrapped ID. Every other reviewed surface passed. | authorized exactly one bridge/DD repair with adversarial counter-at-maximum canaries and a focused re-review |
| 2026-07-29 | allocator-boundary reassessment and implementation | frozen code-only diff `514583114d774461886f81f899bf1ad775a2f1973a957bbedfb0ee5dbcf457cd` at HEAD `1b2a2252c2f8e77610db6b8d674c97910ce15acb`; atomic bounded counter, shared reference allocator lock, real two-mint merge Block, side-effect rollback, DD direct-RHS parity | independent final `PASS`; bounded contention reserves exactly the final eight valid IDs; reference/DD exhaustion returns `Err` without panic or stale publication, restores complete native-input state, and reuses the rolled-back ID; a failed DD direct primitive cannot commit a following Set | closes both live fresh-allocation findings without a host DuckDB allocator, proof-specific branch, or broad interpreter/prediction rewrite |
| 2026-07-29 | coordinator focused acceptance gates, repository root, same frozen code diff | capped `cargo test`: core-relations 58/58, bridge 30/30, DD 42/42, egglog lib 69/69, proof-mode regression 12/12, nonbundled DuckDB 28/28, feature CLI 4/4; scoped non-DuckDB, DuckDB, and feature-CLI Clippy with warnings denied; format and diff checks | every fresh command exited 0 under the 110-second watchdog; production feature build completed in 39.27s; no report artifact, bundled build, push, or external write | prerequisite compiles and preserves all focused reference/DD/DuckDB contracts |
| 2026-07-29 | coordinator broad proof gate | `/opt/homebrew/bin/timeout --signal=TERM --kill-after=5s 110s make proof-tests`, repository root, same frozen code diff | fresh PASS: core 204/204 plus experimental 8/8, 212 total, zero failures; Cargo test execution completed under the cap | current proof conformance remains green after shared SPI and allocator changes |
| 2026-07-29 | coordinator five public DuckDB probes | feature-built `target/debug/egglog-experimental --backend duckdb --proofs --mode no-messages`, `DYLD_LIBRARY_PATH=target/debug/deps`, frozen sources and Pointer fact directory | all five exit 1 at the intentional next boundary `@uf_path_compress ... found 4 actions`; tool wall times Math 0.325s, Eggcc 0.246s, Pointer 0.238s, Hardboiled 0.272s, Luminal 0.318s; no timeout or report artifact | confirms the prerequisite changes no public boundary and authorizes the DuckDB-local staged path-compression writer |
| 2026-07-29 | coordinator local checkpoint commit | `14a2d5d05675b9217171f15b5ae136faaf5ba754 feat: add typed merge and fresh input SPI`; clean worktree immediately after commit; no push | accepted shared prerequisite has a durable rollback point | path-compression work begins from a source-controlled state |
| 2026-07-29 | three committed-source path audits | exact first-rule/config graph, typed primitive semantics, and staged typed-queue design at `14a2d5d`; no moving-diff reads or writes | all five workloads share the same name-independent graph; six stable primitive signatures suffice; staged queues can preserve global wave drain, identity guards, fresh order, rollback, and scratch cleanup with safe public DuckDB 1.5.4 | froze the implementation contract and predicted the next two-Delete cleanup frontier |
| 2026-07-29 | DuckDB-local path-compression worker | frozen owned artifact `38cab3be89ed16c6178e3df12f52bac83c3255b3e5fe10e1bfd4c78fe9a04334` at HEAD `14a2d5d`; only `egglog-experimental/duckdb/**` changed outside this ledger | native structural admission and set-wise staged execution implemented; DuckDB lib 36/36, feature CLI 4/4, DuckDB and feature-CLI Clippy with warnings denied, production feature build, format, and diff checks all pass under the 110-second cap | candidate is frozen for independent review; no commit or push |
| 2026-07-29 | worker five public proof-mode probes | freshly built feature binary, downloaded DuckDB 1.5.4 dylib, frozen inputs, Pointer fact directory, and one external watchdog per invocation | Math 0.286s, Eggcc 0.292s, Pointer 0.251s, Hardboiled 0.317s, Luminal 0.245s; all exit 1 at `@delete_rule ... found 2 actions`, with no timeout | every primary workload now executes through native path compression; the common generated two-Delete cleanup rule is the next bounded compiler frontier |
| 2026-07-29 | three independent frozen path reviews | owned artifact `38cab3be89ed16c6178e3df12f52bac83c3255b3e5fe10e1bfd4c78fe9a04334`; committed Reference/DD source plus complete DuckDB diff; no reviewer writes/builds/tests | semantic executor review `PASS`; admission review `REVISE` because fresh/alias/inequality roles were not proven distinct and proof targets omitted `DefaultVal::Fail`/`n_identity_vals=None`; API/test review `REVISE` only for two telemetry wording inaccuracies | authorize one bounded admission/test/documentation repair, then frozen-surface re-review; no executor redesign or next-slice work |
| 2026-07-29 | bounded path-compression repair and two independent re-reviews | repaired owned artifact `774c919ad247ffd59cacf39c216c8296af022662be16900ea8148f56b6f10275`; executor unchanged; no reviewer writes/builds/tests | worker gates pass: focused path 10/10, DuckDB lib 38/38, feature CLI 4/4, scoped Clippy/build/fmt/diff; admission reviewer `PASS` for exact eight-role distinctness, proof config, rejection canaries, and RuleId nonconsumption; API/test reviewer `PASS` for precise telemetry and coherent 38-test accounting | repair loop closes successfully; coordinator-owned final acceptance gates are authorized |
| 2026-07-29 | coordinator final path-compression acceptance | reproduced owned hash `774c919ad247ffd59cacf39c216c8296af022662be16900ea8148f56b6f10275`; nonbundled DuckDB lib test and Clippy; feature CLI test/build/Clippy; format/diff; five rebuilt proof-mode probes; `make proof-tests`, every process externally capped at 110 seconds | fresh PASS: DuckDB 38/38; feature CLI 4/4; all Clippy/build/format/diff gates exit 0; all five probes exit at the same later `@delete_rule ... found 2 actions` boundary with no timeout; proof gate core 204/204 plus experimental 8/8 | path-compression vertical accepted for one local checkpoint commit; generated two-Delete cleanup is the next bounded compiler frontier |
| 2026-07-29 | coordinator local checkpoint commit | `578f53b feat: execute native DuckDB path compression`; seven expected paths; clean worktree immediately after commit; no push | accepted structural lowering, native staged-wave executor, 10 path canaries, census, and ledger are a durable rollback point | seated three disjoint read-only cleanup-rule circles before any new writer |
| 2026-07-29 | three cleanup-frontier audits at clean `578f53b` | five fresh proof desugarings, generated-rule source, current Reference/DD semantics, accepted DuckDB executor, and safe public DuckDB 1.5.4 | all five first rules are one typed Delete template; 2,169 generated instances span key arity 0..27; existing SPI suffices; generic staged effects are preferred; the adjacent one-Subsume companion is safe to include only when its full target row is body-bound | authorize one DuckDB-only direct-effect writer; no proof names/config registry or shared API change |
| 2026-07-29 | coordinator reduced Reference Delete-report probe | temporary `egglog-bridge` example, removed immediately; one keyed row and one table-only Delete rule; capped `cargo run -p egglog-bridge --example delete_changed_probe` | first run `changed=false`, table size `1 -> 0`; rerun `changed=false`, size `0`; after cleanup only this ledger is dirty | main is authoritative for `RuleSetReport.changed`; DD's `changed=true` on physical Delete is a recorded backend divergence, while DuckDB still advances its physical freshness epoch |
| 2026-07-29 | DuckDB cleanup-effect worker | frozen owned artifact `955a42e787ee5bfeff6559356d0ea08350ec9c60a51c998a163655a4d6f96b10` at HEAD `578f53b`; only `egglog-experimental/duckdb/**` changed outside this ledger | typed Delete/body-bound Subsume effects and global phases implemented; focused cleanup 9/9, DuckDB lib 47/47, feature CLI 4/4, scoped Clippy/build/fmt/diff green under 110 seconds | five public probes register through Delete/Subsume and reach common `@rebuild_rule requests All` boundary in 0.21--0.37 seconds; candidate frozen for review |
| 2026-07-29 | three independent frozen cleanup reviews | owned hash `955a42e787ee5bfeff6559356d0ea08350ec9c60a51c998a163655a4d6f96b10`; full DuckDB diff plus current Reference/DD source; no reviewer writes/builds/tests | semantics `PASS`; safe-SQL/tests `PASS`; admission `REVISE` because the coarse path-compression pre-dispatch captures valid three-body/four-Delete rules before generic effect admission | authorize exactly one path-dispatch/adversarial-canary repair; executor, effect phases, and public boundary remain frozen |
| 2026-07-29 | bounded cleanup admission repair | repaired owned hash `fc55d94180d70f0e98045d9a947c19165f9ae9399297bbaa5c159e03589c6a6c`; Delete-only dispatch priority plus one same-cardinality mixed-rejection/RuleId/four-Delete canary; executor and Subsume unchanged | focused cleanup 10/10, DuckDB lib 48/48, feature CLI 4/4, scoped Clippy/build/fmt/diff green; all five probes retain `@rebuild_rule requests All` in 0.48--0.60 seconds | exact repaired surface returned to the admission reviewer; no second repair is authorized |
| 2026-07-29 | independent repaired cleanup admission re-review | owned hash `fc55d94180d70f0e98045d9a947c19165f9ae9399297bbaa5c159e03589c6a6c`; no writes/builds/tests | final `PASS`: valid Delete-only priority is non-vacuous, same-cardinality mixed heads still fail through exact path validation, the canary executes four Deletes, and rejected admission preserves RuleId | all frozen cleanup reviews pass; coordinator acceptance set authorized |
| 2026-07-29 | coordinator final cleanup-effect acceptance | reproduced owned hash `fc55d94180d70f0e98045d9a947c19165f9ae9399297bbaa5c159e03589c6a6c`; nonbundled DuckDB lib test and Clippy; feature CLI test/build/Clippy; format/diff; five rebuilt proof-mode probes; `make proof-tests`, every process externally capped at 110 seconds | fresh PASS: DuckDB 48/48; feature CLI 4/4; all Clippy/build/format/diff gates exit 0; Math 0.276083s, Eggcc 0.219817s, Pointer 0.302423s, Hardboiled 0.186774s, Luminal 0.262351s, each exits at `@rebuild_rule requests All` with no timeout; proof gate core 204/204 plus experimental 8/8 | direct Delete/body-bound Subsume vertical accepted for one local checkpoint commit; exact `ReadMode::All` rebuild lowering is the next bounded diagnostic frontier |
| 2026-07-29 | coordinator local checkpoint commit | `21b482b feat: execute native DuckDB cleanup effects`; seven expected paths; clean worktree immediately after commit; no push | accepted generic Delete/body-bound Subsume lowering, global cleanup phases, 10 cleanup canaries, census, and ledger are a durable rollback point | seated three disjoint read-only rebuild-frontier circles before any new writer |
| 2026-07-29 | rebuild IR census at committed `21b482b` | five capped proof-desugar passes: Math 0.02s, Eggcc 0.98s, Pointer 0.02s, Hardboiled 0.23s, Luminal 1.68s; no backend build/probe or source write | 3,892 maintenance rules: 2,139 eclass-output, 866 topology-level eq-key, 866 marker-key, 12 custom-output, 6 container-key, 3 container-output; all 7,775 table atoms are All; key width 0..27 | two standard non-container forms are one coherent first slice; marker reach was a static projection, while Pointer's executable path interleaves raw input after its first rebuild |
| 2026-07-29 | independent All/rebuild semantic audit at committed `21b482b` | current Backend contract, Reference stable execution/fixed point, DD versioned views, generated rebuild source, and accepted DuckDB executor; static/read-only | existing SPI suffices; Reference wins DD divergences; Live-to-subsumed must refire All/Subsumed once; Set cannot revive a subsumed owner; custom Delete-before-Set bypasses merge; all transactional state and telemetry roll back together | froze blocking semantic/review canaries without adding proof-aware storage or shared API |
| 2026-07-29 | safe-SQL rebuild architecture audit at committed `21b482b` | compared target-typed multi-statement queues with recursive `USING KEY`; current safe public DuckDB 1.5.4 and accepted path fold; static/read-only | choose View queue -> generated UF queue -> unbounded UF self-waves, with exact head-before-collision allocation and scalar-only Rust observations; recursive trace is fallback after one reviewed staged-queue failure | authorize one DuckDB-only writer for exactly eq-key/eclass-output forms and a marker boundary |
| 2026-07-29 | focused corpus correction during initial rebuild implementation | committed-source proof desugaring for Pointer, Eggcc, and Hardboiled; no writer-file edits by the census circles | eq-key body UF may differ from the View output-displacement UF (`ConsView`: `UF_Expr` vs `UF_ListExpr`; `CastView`: `UF_Type` vs `UF_Expr`); Pointer interleaves raw input after its first eclass-output rule; strict ordered-Block key counts are Eggcc 364 and Hardboiled 102, with later custom/Columns/container capabilities left fail-closed | corrected the executor model and public gate before freeze; no post-review repair budget consumed |
| 2026-07-29 | standard scalar rebuild worker freeze at committed HEAD `21b482b` | reproduced owned hash `fd1a712a55cb492d670b070a0cbcd9c7acd608387cb7cce0979d5311b512a28b`; five changed DuckDB source/test paths; nonbundled commands each externally capped at 110 seconds | focused rebuild 12/12 in 10.11s; DuckDB lib 60/60 in 0.40s; DuckDB Clippy pass in 1.94s; feature CLI 4/4 in 5.61s; feature Clippy/build pass in 1.15s/8.65s; format/whitespace clean | Math 0.39s, Eggcc 0.02s, Hardboiled 0.03s, Luminal 0.04s reach marker; Pointer 0.02s admits its first rebuild then reaches the expected raw-input Block-write boundary; freeze for three independent reviews |
| 2026-07-29 | three independent standard-rebuild reviews at frozen hash `fd1a712a55cb492d670b070a0cbcd9c7acd608387cb7cce0979d5311b512a28b` | static semantic, admission/topology, and safe-SQL/test/API audits; all reviewers reproduced HEAD/hash at start/end and made no writes/builds/tests | semantics `PASS`; admission `REVISE` because All validation precedes complete ordered-union-family discrimination for a custom/Columns+Live near-shape; SQL/API `REVISE` only for unexecuted 27-key SQL, zero-only rollback watermark, and incomplete negative admission matrix | authorize the one bounded repair: reorder family-vs-interior admission in `rebuild.rs` and close the named canaries in `rebuild_tests.rs`; executor and other production files remain frozen |
| 2026-07-29 | bounded standard-rebuild repair | reproduced repaired owned hash `4c3acea85587ff222842bcadde867c89557e7cb63959733078e7f0c6e14f175c`; repair delta only in `rebuild.rs` and `rebuild_tests.rs`; storage/executor/integration unchanged | ordered-union-family membership now precedes All/interior validation; added executed mixed 27-key queue, nonzero-watermark rollback/retry, join/alias/fake-primitive/index-type/container/custom-Live RuleId canaries; focused 13/13, DuckDB 61/61, feature CLI 4/4, Clippy/build/fmt/diff green | Math/Eggcc/Hardboiled/Luminal retain marker boundary in 0.02--0.40s; Pointer retains expected raw-input boundary in 0.01s; exact repaired surface returned to the two revising reviewers; no second repair authorized |
| 2026-07-29 | repaired standard-rebuild re-reviews at hash `4c3acea85587ff222842bcadde867c89557e7cb63959733078e7f0c6e14f175c` | admission and safe-SQL/test reviewers independently reproduced HEAD/hash at start/end; static/read-only | admission `PASS`: family discrimination precedes All/interior and both fallthrough/error sides retain RuleId; SQL/tests `PASS`: executed 27-key, nonzero-watermark retry, and complete mutation matrix are substantive; no forbidden API/scope growth | all frozen reviews pass; coordinator acceptance set authorized |
| 2026-07-29 | coordinator final standard-rebuild acceptance | reproduced owned hash `4c3acea85587ff222842bcadde867c89557e7cb63959733078e7f0c6e14f175c`; nonbundled DuckDB lib test/Clippy, feature CLI test/build/Clippy, format/diff, five rebuilt probes, and `make proof-tests`; every process externally capped at 110 seconds | fresh PASS: DuckDB 61/61 in 0.25s; feature CLI 4/4 in 3.11s; all lint/build/format/diff gates exit 0; Math/Eggcc/Hardboiled/Luminal reach marker in 0.241--0.336s, Pointer reaches raw-input boundary in 0.368s; proof gate core 204/204 plus experimental 8/8 in 28.09s | standard scalar All/ordered-union vertical accepted for one local checkpoint commit; marker rekey and raw SQL input become separate read-only diagnostic circles before another writer |

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

## Worker contract: checkpoint 1 shared proof-prefix slice

- **Hypothesis:** safe public DuckDB 1.5.4 APIs and the existing backend SPI can
  register and losslessly transport the complete 23-table prefix shared by the
  five frozen proof-mode workloads, while executing the scheduled one-output
  `MergeFn::AssertEq` natively in SQL and retaining every declared merge/default/
  identity property needed for later admission. No shared SPI change or host row
  enumeration is required.
- **Target artifact:** extend the DuckDB storage/config model and focused tests.
  `FunctionConfig` information needed for execution is retained losslessly;
  structurally valid but not-yet-executable merge plans may register as explicit
  deferred capabilities, but any input or rule write to them must fail during
  preflight, before a transaction, generation, rule ID, or watermark mutates.
  One-output `AssertEq` is executable, not deferred.
- **Typed representation:** preserve existing scalar types and add lossless
  physical representations for the reached exact numeric bases: native DuckDB
  `BIGNUM` for BigInt, a typed numerator/denominator representation for BigRat,
  and a typed 64-bit numerator/denominator representation for experimental
  Rational. Values remain typed inside SQL. Boundary construction and reads use
  only safe documented `duckdb-rs`/SQL APIs; canonical decimal projection and
  parsing is acceptable at the low-volume Rust boundary. Plain untyped text
  storage, a crate patch/fork, raw FFI, or backend-owned unsafe code is not.
- **Native `AssertEq`:** equal duplicate rows are idempotent. A different output
  for an equal key—whether two incoming rows conflict or an incoming row
  conflicts with existing state—returns an error and rolls back the complete
  bounded operation. Detect and fold conflicts set-wise in DuckDB; Rust may read
  a scalar success/conflict result but must not enumerate matches or rows. The
  same semantics apply to native input and to the current one-Set rule compiler.
- **Config admission:** retain schema, output count, identity-output count,
  default behavior, merge tree, subsumption flag, and diagnostic name. Validate
  recursive merge structure at registration. Preserve `peek_next_function_id`
  behavior for self-referential plans. Do not claim collision-free writes to a
  deferred target. Preflight every target in a heterogeneous input batch before
  opening its transaction.
- **Public boundary gate:** with the feature-enabled CLI and frozen inputs, each
  of the five workloads must register the common 23-table prefix and move its
  first failure to the generated union-find path-compression rule (or later).
  A capped timeout is censored; an earlier error is blocking. This does not claim
  first-iteration or complete-program support.
- **Canaries:** equal duplicate input, intra-batch conflict, conflict with an
  existing row, a later-target conflict rolling back earlier inserts/counters,
  generation and no-delta behavior, nullary/hostile exact numeric values,
  exact-number round trips, unsupported-target preflight, and no ordinary
  indexes/placeholders/user-derived identifiers. Rule canaries include rollback
  without advancing watermarks and stable pre-wave behavior.
- **Owned write set:** `egglog-experimental/duckdb/Cargo.toml`,
  `egglog-experimental/duckdb/src/{lib.rs,storage.rs,rule_sql.rs}` and focused
  DuckDB test/census files. `Cargo.lock` may change only mechanically for an
  exact-number parsing dependency. Stop before shared backend traits, frontend,
  bridge, DD, fixtures, Makefile, benchmark harness, or unrelated workspace
  files.
- **Owned commands:** focused DuckDB tests, public five-file boundary probes,
  scoped clippy, formatting, and diff checks through the nonbundled
  `DUCKDB_DOWNLOAD_LIB=1` route. Every subprocess gets a 110-second watchdog; no
  bundled build, full proof matrix, or broad benchmark run.
- **Stop:** a native exact representation cannot round-trip using two materially
  different safe public designs; set-wise `AssertEq` requires Rust row
  enumeration; the existing SPI cannot retain/admit the config without a shared
  change; the public boundary regresses before `@PCons`; two no-movement cycles
  occur; or a user decision is required. Preserve positive implementations and
  report the exact blocker rather than widening scope.

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

## Worker contract: checkpoint 0.5 production RuleSpec slice

- **Hypothesis:** current `RuleSpec` and safe public DuckDB APIs can execute a
  useful production subset entirely through generated SQL: one or more Live
  table atoms with typed variables/literals and exactly one table Set head into
  a one-output `MergeFn::Old` target. No shared SPI change is required.
- **Target artifact:** `duckdb/src/rule_sql.rs` plus the smallest storage/runtime
  additions and focused differential tests. `add_rule` validates and compiles;
  `run_rules` materializes every scheduled rule's matches before applying any
  effect, applies stages in scheduled rule order inside one transaction, and
  updates per-rule generation watermarks only after commit.
- **Required semantics:** stable pre-wave reads; Live filtering; repeated
  variables and literals lowered with typed `IS NOT DISTINCT FROM`; ordinary
  identifiers remain numeric/compiler-owned; literals use the existing central
  encoder; no SQL placeholders; no ordinary indexes; first existing/incoming
  row wins under KeepOld; second no-delta run reports unchanged; fresh rows in
  any body relation can join older rows in the others; rollback leaves target
  rows, generation, stages, and watermarks unchanged.
- **Supported IR only:** nonempty table-call bodies, variables/literals, Live
  read mode, one table Set action, all head variables bound, exact arity/types,
  and one-output `MergeFn::Old`. Fail closed on primitives, globals, lets,
  changes, unions, panics, non-Live reads, empty bodies, multiple heads,
  unbound variables, freed IDs, and every other merge/action form.
- **Differential gate:** build logically identical, backend-local typed
  `RuleSpec`s for main and DuckDB; never replay backend-local IDs or Values.
  Source-pin the Pointer five-way rule at
  `benchmarks/pointer-analysis-small.egg` and the Math Add commutativity rule at
  `egglog/tests/math-microbenchmark.egg`. Compare sorted typed witness rows and
  changed/no-change transcripts across initial, fresh-delta, and no-delta runs.
  Handwritten SQL probes remain feasibility-only until these pass.
- **Canaries:** a two-rule seed-to-middle-to-output schedule proves writes from
  one rule are not body inputs to another until the next bounded call; an
  unsupported-IR matrix proves fail-closed admission; a test-only later-target
  failure proves transaction and watermark rollback; generated SQL contains no
  `?` and no user-derived identifiers; catalog remains free of ordinary ART
  indexes/key constraints.
- **Owned write set:** `egglog-experimental/duckdb/Cargo.toml`, new
  `egglog-experimental/duckdb/src/rule_sql.rs`, existing DuckDB `lib.rs` and
  `storage.rs`, and focused DuckDB tests such as
  `tests/rule_differential.rs`. Dev-only dependencies are allowed. Stop before
  editing the shared backend trait, frontend, bridge, DD backend, fixtures, or
  benchmark harness.
- **Bounded performance evidence:** after correctness, one fixed-size Pointer
  and one fixed-size Math probe, at most one warm-up plus three measurements,
  with setup and bounded rule execution separated. No speed threshold and no
  tuning loop; a timeout is censored evidence.
- **Owned commands:** targeted DuckDB differential/unit tests, formatting, and
  scoped clippy under a 110-second external watchdog through the nonbundled
  `DUCKDB_DOWNLOAD_LIB=1` path. No bundled command or broad benchmark matrix.
- **Stop:** both production differentials and semantic canaries pass; two
  materially different SQL formulations disagree with main; safe public APIs
  cannot provide atomic staging; Rust would need to enumerate matches/retain
  rows; a shared-SPI expansion becomes necessary; or the two-cycle trigger
  fires.

## Worker contract: typed merge IR and atomic fresh-slot input prerequisite

- **Hypothesis:** the frontend already possesses every concrete sort and
  primitive identity needed by a native backend, and all three current backend
  implementations can resolve native-input fresh placeholders atomically without
  changing successful-program semantics. A narrow shared contract can preserve
  reference/DD execution while making DuckDB's later SQL lowering type-directed
  and its ID counter authoritative.
- **Target artifact:** enrich merge-expression primitive calls with their stable
  semantic name plus concrete input/output `ColumnTy`s, and make merge constants
  carry `ColumnTy`. Keep the runtime `ExternalFunctionId` so reference and DD
  continue calling their existing implementations. Add an object-safe native
  input batch value with `Existing(Value)` and a repeatable `FreshSlot(u32)`, plus
  one fallible backend method that resolves a dense slot set and inserts the
  complete batch atomically. Existing direct `add_values` remains available.
- **Frontend behavior:** `native_input` assigns deterministic dense fresh slots
  instead of calling `fresh_id` before `add_values`. Repeated occurrences of one
  slot resolve to one ID; distinct slots resolve in ascending slot order. The
  frontend does not need the resolved values after the batch commits. Invalid,
  sparse, or type-incompatible slots fail closed before mutation.
- **Reference/DD behavior:** preserve current row/merge/proof results. Resolve
  slots against each backend's existing ID counter inside an outer rollback
  boundary that includes both allocation and merge-aware insertion. A rejected
  batch restores the counter and all rows and leaves the backend reusable.
- **Fresh capability split:** distinguish a backend that supports native fresh
  allocation from one that exposes an executable host `CounterId`. Reference and
  DD retain the counter-backed default. DuckDB reports native fresh support but
  returns `None` from `id_counter()`; no dummy/non-authoritative host counter is
  permitted. Generic `get-fresh!` and proof-container registration gate on the
  capability rather than on `id_counter()`.
- **DuckDB behavior:** add a `fresh_id` row to the existing backend metadata
  counter table. Resolve slots and typed rows inside the same DuckDB transaction
  as conflict checks, insertion, and generation. `fresh_id()` and later native
  SQL lowering of registered `get-fresh!` calls draw from that same
  SQL-authoritative counter. DuckDB's registered external-function ID is only a
  fail-closed semantic token for the compiler; it must not execute a host
  callback into DuckDB. Reference/DD registrations remain executable. Use safe
  public SQL APIs only.
- **Typed-IR population:** build merge primitive metadata from the resolved
  call site (`SpecializedPrimitive::name`, concrete inputs, concrete output) and
  build typed constants from each resolved expression's output sort. Do not add
  SQL text, DuckDB types, proof tags, table names, or a closed proof-specific
  opcode to the shared IR. Reference and DD may ignore the descriptive metadata
  when executing by external ID, but validation/tests must prove it is retained.
- **Canaries:** typed metadata for polymorphic ordering/orientation calls and the
  string argument to `get-fresh!`; reference and DD merge behavior unchanged;
  one fresh slot reused across several rows; multiple slots remain distinct and
  deterministic; a late merge failure restores rows and the counter; the next
  successful batch reuses the rolled-back ID; DuckDB interleaves `fresh_id`, an
  atomic fresh-slot batch, and another `fresh_id` without collision; hostile
  sparse/out-of-order slot layouts, non-Id slots, invalid targets/arity, and the
  `u32::MAX` stale sentinel reject without consuming IDs; existing input/fail/
  proof gates remain green. Static review must prove `native_input` contains no
  direct `backend.fresh_id()` call and DuckDB contains no production host mint.
- **Owned write set:** `egglog/egglog-bridge/src/{lib.rs,tests.rs}`;
  `egglog/egglog-backend-trait/src/{lib.rs,backend_impl.rs}`;
  `egglog/src/lib.rs`, `egglog/src/proofs/{proof_fresh.rs,proof_container_rebuild.rs}`,
  and only a focused frontend regression file if required;
  `egglog-experimental/dd/src/{compile.rs,lib.rs}`; and
  `egglog-experimental/duckdb/src/{lib.rs,storage.rs}` plus focused existing test
  modules. No fixtures, proof generators, container implementation, benchmark
  harness, Makefile, dependency manifests, or snapshots may change.
- **Forbidden shortcuts:** proof/table/sort-name recognition; opaque primitive-ID
  ordering; host callback execution from DuckDB; a second production ID counter;
  mint-then-insert outside one rollback boundary; weakening the existing
  fallible input contract; unsafe/private DuckDB APIs; Appender/file readers;
  unrelated cleanup or benchmark work.
- **Owned commands:** targeted bridge/backend-trait/DD/DuckDB/frontend tests,
  scoped checks/clippy, formatting, and diff checks, every subprocess under an
  external 110-second watchdog. The coordinator owns the broad proof gate and
  public five-file probes after independent review. No bundled DuckDB build.
- **Stop:** two materially different type-carrier designs cannot preserve
  reference/DD behavior; fresh slots cannot be resolved atomically through the
  existing three backends without broad unrelated API changes; any implementation
  needs proof-specific metadata or unsafe/private APIs; two no-movement cycles
  occur; or a user decision is required. Preserve the accepted `f9d07eb` prefix
  and report the exact blocker rather than falling back to opaque callbacks.

## Planned contract after the prerequisite: native path compression

- Compile the exact structural rule vocabulary—Live table atoms, partial `!=`,
  action `get-fresh!`, aliases, and ordered Sets—without inspecting names.
- Compile the reached typed merge vocabulary—old/new columns, lets, constants,
  ordering/payload-selection primitives, tuple Columns, identity guard, ordered
  Sets, and fresh allocation—into staged DuckDB work queues.
- Materialize every scheduled rule's matches before effects. A logical merge
  wave contains repeated SQL fold passes, each selecting at most one pending
  candidate per logical key. Drain every original candidate for logical wave
  `w` before making Block-generated candidates tagged `w + 1` eligible; advancing
  the logical wave after each fold pass is incorrect. Continue until every
  queue is empty, with no semantic wave cap. Rust may schedule statements and
  read scalar counts/booleans, but may not enumerate matches, effects, or merge
  rows.
- Assign deterministic backend-local match/event ordinals after typed binding
  deduplication. Allocate all head fresh requests before any collision request;
  within each identity-changing UF Block allocate its Sym proof before its
  Trans proof. Missing/equal-identity candidates allocate nothing. Do not claim
  a portable global order between independent matches or collisions; compare
  proof graphs modulo a consistent fresh-ID renaming.
- Keep head IDs, collision IDs, proof rows, UF rows, generation, scratch state,
  and the SQL fresh counter in one transaction; update Rust watermarks/telemetry
  only after commit. Unsupported primitives/actions/dependencies fail during
  admission before a Rule ID is consumed.
- Differential canaries cover an ordered `a -> b -> c` chain, identity-equal
  no-op, old-min effects with unchanged retained row, new-min replacement,
  multi-wave self-writes, duplicate incoming keys, stable pre-wave visibility,
  late AssertEq rollback, phantom scratch cleanup, deterministic allocation, and
  a renamed non-proof instance of the same typed IR. Then all five public probes
  must move beyond `@uf_path_compress` to one precisely recorded later boundary.
- If staged work queues fail semantically after one bounded repair, test the
  independently proposed tagged `USING KEY` recursive CTE. If both designs fail
  the same semantic gate, stop the goal early with the preserved exact evidence.

## Worker contract: direct Delete and body-bound Subsume effects

- **Hypothesis:** the accepted typed body binder and stable pre-wave executor can
  support native cleanup through one generic direct-effect plan, with no shared
  SPI change, proof/table-name recognition, host row enumeration, or merge
  callback.
- **Target artifact:** replace the one-Set-only direct plan with a staged effect
  list that retains the existing exactly-one-Set language, admits any nonempty
  Delete-only table head, and admits exactly one table Subsume only when a Live
  body atom for the same target binds its complete typed row and identical key.
  All other mixed/Let/primitive/Union/Panic head languages remain fail-closed.
- **Typed admission:** every Delete key has exact target key arity/types and may
  be empty; deferred target merges are allowed because deletion does not invoke
  them. Subsume additionally requires `can_subsume`, a complete Live target body
  row, and exact action/body keys. Globals, primitive targets, unbound or
  inconsistent variables, malformed metadata, and unsupported mixtures fail
  before RuleId allocation.
- **Execution phases:** materialize and count every scheduled stage first; apply
  all Deletes in schedule/action order; apply existing AssertEq/Set effects;
  then apply Subsume. Delete addresses only keys and removes live or subsumed
  rows. Subsume preserves a same-wave Set value, otherwise the staged pre-wave
  value, and uses a staged-row fallback so same-wave Delete+Subsume ends present
  and subsumed like Reference. Rust reads scalar counts only.
- **Change split:** track `physical_changed` separately from
  `report_changed`. Any real Delete/Set/Subsume transition advances DuckDB's
  freshness generation. Pure Delete reports `changed=false` to match current
  main; Set insert or Live-to-Subsumed transition reports true. `fresh_id` is
  untouched. Delete/Subsume counts must not be laundered into the existing
  insert-count telemetry; add explicit internal telemetry only if useful.
- **Atomicity:** rows, flags, staged values, generation, scratch, run identity,
  and watermarks share one transaction. A late AssertEq or SQL failure restores
  the complete pre-run state. Session-scoped scratch is explicitly cleaned on
  both success and rollback. Watermarks publish only after commit.
- **Canaries:** include renamed nullary, mixed scalar/ID, and synthetic 27-key
  Delete rules; pending marker/reinsertion freshness; duplicate/same-target
  Deletes; stable pre-wave interference; Delete-before-Set in both schedule
  orders; deferred-merge and subsumed target deletion; exact Subsume value/flag/
  marker behavior; Set+Subsume and Delete+Subsume same-key outcomes; late-error
  rollback; hostile typed literals; admission/RuleId nonconsumption; and fresh
  counter stability. Pin the main/DD pure-Delete report divergence explicitly.
- **Public gate:** all five frozen proof-mode probes must register past both
  generated Delete and Subsume cleanup rules and stop at one precisely recorded
  later boundary. A timeout is censored, not a semantic pass or failure.
- **Owned write set:** `egglog-experimental/duckdb/**` only, excluding this
  coordinator-owned ledger. No frontend, Reference, DD, manifest/lockfile,
  harness, fixture, snapshot, report-cache, commit, push, Appender/file reader,
  unsafe/private API, or performance-tuning change.
- **Verification:** worker-owned focused tests, nonbundled DuckDB lib test,
  DuckDB and feature-CLI Clippy with warnings denied, feature CLI test/build,
  format/diff checks, and the five public probes; every subprocess has a
  110-second external watchdog. Broad `make proof-tests` remains coordinator
  owned.
- **Stop:** freeze after one implementation and at most one review-authorized
  repair. If exact main Delete reporting or either same-key Subsume canary cannot
  be expressed without host enumeration/shared proof knowledge, stop and
  reassess rather than adding a special-case fallback.

## Worker contract: standard scalar rebuild and ordered-union queues

- **Hypothesis:** the accepted typed path fold can be parameterized into a
  target-typed staged queue that executes both standard scalar rebuild forms
  without a shared SPI change, generated-name recognition, host row/effect
  enumeration, or proof-aware durable storage.
- **Exact admitted language:** seminaive, decomposed rules with exactly two All
  table atoms plus typed `!=(Id, Id) -> Unit`. Admit both structurally distinct
  heads: (1) eq-key rekey—one fresh proof, one AssertEq Congr Set, one canonical
  View Set, one stale-key Delete; and (2) eclass-output—fresh/Sym Set,
  fresh/Trans Set, then same-key canonical View Set. Keys are arbitrary already
  registered scalar/Id columns, width 0..27. The View is keys plus two Id values,
  identity count one, `DefaultVal::Fail`, subsumable, and has the complete
  standard ordered-union Block; the UF is `[Id, Id, Id]`, one-key/two-value,
  identity count one, non-subsumable, and has its orientation of that Block.
- **Admission discipline:** dispatch by an exact tri-state structural predicate,
  before the current cheap path arity discriminator. Stable primitive semantic
  names plus concrete signatures are valid; rule/table/sort/variable/proof names,
  opaque external IDs, FunctionId order, and corpus identities are not. Validate
  every mode, join, variable role, child-index literal, proof target, action
  order, fresh label, table config, and complete merge tree before RuleId
  allocation. A matching outer topology with a malformed interior is an error;
  a different topology falls through. Marker, custom-output/custom-Block,
  container, lookup, Union, Panic, Subsume, and arbitrary Deferred merges remain
  fail-closed.
- **Match phase:** materialize and count every scheduled rule before any effect.
  All omits the subsumption predicate but keeps the two-table seminaive OR
  watermark. Deduplicate complete typed bindings and assign explicit canonical
  match ordinals. Naive behavior is not implied by All.
- **Effect/merge phases:** read generation/fresh counters once; reject duplicate
  durable owners before mutation; reserve every head fresh slot in schedule,
  match, then action-slot order; apply all key-rekey Deletes; insert/conflict-check
  all independent head proof rows; enqueue every View candidate at logical wave
  zero. Drain `(wave, target FunctionId, event ordinal)` queues, selecting at most
  one candidate per logical key per pass. Missing owners insert live; equal
  leading identities retain the complete old tuple/status/generation and execute
  no merge actions; differing identities run the exact View or UF ordered-union
  orientation, reserve Sym/Trans IDs, preserve an existing subsumed bit, update
  only changed values, and enqueue displaced UF candidates at `wave + 1`. Drain
  every target at wave `w` before exposing `w + 1`; there is no semantic wave cap.
- **Atomicity/reporting:** rows, subsumption bits, generation, fresh counter,
  scratch queues/pass tables, run identity, rule watermarks, and published
  telemetry share one transaction/failure domain. Stamp physical insert/value
  changes at captured generation and bump the durable generation once if any
  physical row state changed. A different-identity old-min collision still emits
  merge side effects even if the retained View row stays byte-identical. Preserve
  Reference-compatible public change reporting and do not count recursive merge
  effects as per-rule head inserts. Rust may read only scalar counters, counts,
  and booleans.
- **Canaries:** renamed/shuffled instances of both shapes; mode/join/alias/fake
  primitive/admission rejection with RuleId preservation; live and subsumed All
  sources; live-to-subsumed one-time refiring; nullary, mixed scalar/Id, and
  synthetic 27-key Views; child-index bounds/type checks; missing owner;
  equal-identity full-old retention; new-min and old-min collisions with exact
  orientation; subsumed canonical owner not revived; duplicate incoming keys;
  View collision generating UF collision and multi-wave UF self-writes; stable
  pre-wave behavior; global Delete-before-Set; head and collision exhaustion;
  duplicate-owner/subsumed-UF rejection; late nonzero-watermark AssertEq rollback
  with exact fresh-ID reuse; scratch cleanup; deterministic SQL manifest; and
  continued fail-closed container/marker/custom variants.
- **Public gate:** Math, Eggcc, Hardboiled, and Luminal must register every
  standard eq-key/eclass-output rebuild and stop at the distinct generated
  `rebuild_to_subsume_rule` marker-rekey boundary. Pointer interleaves
  `(input function_name "function.csv")` immediately after its first standard
  eclass-output rebuild; it must admit that rebuild and then stop at the existing
  fail-closed raw-input/Block-write boundary. The committed cleanup checkpoint
  stopped before this input at the first `ReadMode::All` rule, so the earlier
  five-way marker projection was static-census evidence, not a prior executable
  boundary. Do not absorb raw-input semantics into this slice. No probe may time
  out. This is an admission/execution-frontier gate, not workload completion or
  a performance claim. Statement counts and wall times are reported only.
- **Owned write set:** `egglog-experimental/duckdb/**` only, excluding this
  coordinator ledger. No frontend, backend trait, Reference, DD, manifest,
  lockfile, harness, fixture, snapshot, report cache, causal branch, commit,
  push, Appender/file reader, unsafe/private API, host callback, or performance
  tuning change.
- **Verification:** focused rebuild tests plus the complete nonbundled DuckDB lib
  test; DuckDB and feature-CLI Clippy with warnings denied; feature CLI test/build;
  formatting/diff checks; and five public probes. Every subprocess receives the
  external 110-second watchdog; no bundled build. The coordinator owns the broad
  proof gate after independent frozen-artifact review.
- **Stop:** freeze the first reviewable staged-queue artifact without commit or
  push. One review-authorized repair is the maximum. If either exact topology or
  ordered-union orientation differs, another dependency is needed, deterministic
  allocation needs host rows, or a canary requires shared/proof-specific/unsafe
  machinery, stop with evidence. If the staged queue fails a semantic gate after
  the bounded repair, reassess the independently specified recursive `USING KEY`
  trace; if both designs fail the same semantic gate, exit the goal early. Reaching
  marker rekey is success for this slice and must not be absorbed opportunistically.

## Next action

Create one local checkpoint commit for the accepted standard scalar rebuild
artifact and this ledger, with no push. From that clean commit, seat two
disjoint read-only circles: one must census and specify marker-rekey semantics;
the other must specify the safe raw-SQL input path for Pointer's Rust-parsed
facts and Block-configured missing-row insertion. Compare reach and dependency
order before authorizing exactly one next writing circle. Do not combine either
with container/custom merge lowering or performance tuning.
