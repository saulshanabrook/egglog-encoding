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
  path compression, direct cleanup, standard scalar rebuild, and marker rekey
  are committed through `7a1ec52`. The DuckDB-local marker compiler and mixed
  Standard/Marker transaction passed all
  three independent reviews, the sole test-only repair, and fresh coordinator
  acceptance at owned patch-stream hash
  `fce5af5b1359614de29079f34309e57be69c9ff7264a43040ee37f615f4a21d1`.
  Math executes 18 markers before its first ordinary unsupported rewrite,
  Eggcc executes 77 before an empty-body action rule, Hardboiled executes 20
  before a container rebuild, and Luminal executes 38 before its first ordinary
  unsupported rewrite. Pointer retains the independently identified typed
  raw-input/Block-write boundary. The next implementation frontier after the
  local marker checkpoint is therefore complete ordered-union raw input, not
  performance tuning, containers, or ordinary rule lowering.
- **Scoreboard:** current-main pinned; loaded DuckDB v1.5.4; DuckDB backend
  tests 73/73, focused marker tests 12/12, and feature-enabled CLI tests 4/4
  pass; both scoped Clippy lanes with warnings denied, feature build,
  formatting, and diff checks pass. Fresh public probes exit at the intentional
  later boundaries in Math 0.45s, Eggcc 2.18s, Pointer 0.02s, Hardboiled 0.04s,
  and Luminal 0.04s, with no timeout. The repository proof gate remains green
  at core 204/204 plus experimental 8/8 (212/212) in 22.36s.
  All frozen reviews pass at owned hash
  `fce5af5b1359614de29079f34309e57be69c9ff7264a43040ee37f615f4a21d1`.
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
- **Next decision:** return to the committed raw-input audit and seat bounded
  read-only architecture/test circles before one DuckDB-only writer. Raw input must reuse
  the complete ordered-union semantics rather than admit a missing-only corpus
  shortcut. Preserve
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
| `/root/marker_rekey_census` | read-only marker-rekey frontier audit | pin the exact generated marker rules/configs, Reference semantics, smallest safe SQL lowering, next boundary, and existing-SPI verdict | clean committed `2914373`; no writes/builds/tests or other-agent contact; capped desugar/public probes only | exact distribution, structural predicate, executor reuse decision, canaries, and stop rule | completed; existing SPI passes and a combined Standard+Marker transaction is required |
| `/root/raw_input_block_census` | read-only typed raw-input frontier audit | trace Pointer's Rust-parsed fact batch into Block-configured View writes and determine the smallest sound raw-SQL capability | clean committed `2914373`; no writes/builds/tests or other-agent contact; capped source/desugar/probe inspection only | exact batch/config/conflict/fresh/proof semantics, safe-SQL design alternatives, canaries, and stop rule | completed; existing SPI suffices, but complete ordered-union queue reuse is required rather than missing-only insertion |
| `/root/post_frontier_dependency_census` | read-only workload dependency audit | distinguish registration blockers from executable program-order blockers after marker rekey and raw input | clean committed `2914373`; static source/config inspection only; no writes/builds/tests or other-agent contact | per-workload next-boundary table and one evidence-backed implementation priority | completed; marker rekey is first, raw-input ordered union second, ordinary proof-instrumented rules third |
| `/root/duckdb_marker_rekey_worker` | marker-rekey implementation | compile the exact generated marker family and execute mixed Standard+Marker schedules in one stable DuckDB transaction | `egglog-experimental/duckdb/**` except this ledger; no shared APIs, raw input, container/custom rules, harness, commit, or push | source-independent canaries plus four public workloads beyond marker while Pointer retains raw-input boundary | sole repair completed test-only and frozen at owned hash `fce5af5b...`; no second repair, commit, or push |
| `/root/marker_semantics_review` | independent frozen semantic review | audit stable mixed pre-wave, phases, one-hop behavior, generation/reporting, allocation, rollback, and watermarks | exact frozen owned hash only; no writes/builds/tests or writer contact | `PASS`, `REVISE`, or `REASSESS` with exact source evidence | completed `PASS`; no production semantic defect or counterexample |
| `/root/marker_admission_review` | independent frozen admission review | audit name-independent tri-state ownership, exact typed roles/configs/actions, fallthrough/error boundaries, and RuleId preservation | exact frozen owned hash only; no writes/builds/tests or writer contact | `PASS`, `REVISE`, or `REASSESS` with exact source evidence | repaired-surface re-review completed `PASS`; every requested classification/config axis closes at `fce5af5b...` |
| `/root/marker_sql_tests_review` | independent frozen SQL/test/API review | audit typed SQL safety, scratch lifecycle, forbidden surfaces, Standard regression risk, telemetry, and canary sufficiency | exact frozen owned hash only; no writes/builds/tests or writer contact | `PASS`, `REVISE`, or `REASSESS` with exact source evidence | repaired-surface re-review completed `PASS`; blocker closed test-only at `fce5af5b...` |
| `/root/raw_input_ordered_union_arch` | read-only ordered-union reuse architecture | design the smallest complete native input path by generalizing the accepted queue fold rather than adding missing-only insertion | committed `7a1ec52`; no writes/builds/tests/commits/pushes or other-agent contact; safe public API and literal SQL only | two concrete designs, reusable abstraction/write set, risks, recommendation, and stop rule | completed; extract the accepted queue kernel for input-specific admission, with a broader unified Set scheduler deferred |
| `/root/raw_input_semantic_canaries` | read-only raw-input oracle/test audit | freeze Reference-winning collision, allocation, rollback, telemetry, typed-literal, and negative-admission canaries | committed `7a1ec52`; no writes/builds/tests/commits/pushes or other-agent contact | exact focused matrix, public Pointer gate, blocking/descriptive split, and stop rule | completed; Reference differential plus eight focused canaries and the old-min/new-min/identity minimal gate are frozen |
| `/root/raw_input_integration_scope` | read-only Pointer integration/frontier audit | trace parsed facts through the typed batch and bound one writer slice at the next executable boundary | committed `7a1ec52`; no writes/builds/tests/commits/pushes or other-agent contact; no Appender/read_csv/COPY | verified target/config/input surface, owned paths, forbidden shortcuts, commands, and two-design early exit | completed; 23 calls/2,255 facts/13,530 rows/9,020 slots verified and the first ordinary user rule selected as the post-input boundary |
| `/root/duckdb_raw_input_worker` | complete typed ordered-union native-input implementation | extract the accepted queue kernel and seed it from Rust-parsed typed literal SQL in one atomic input transaction | `egglog-experimental/duckdb/**` except this ledger; no shared API/frontend/DD/Reference/ordinary-rule/container/harness/fixture/manifest/commit/push | Reference-differential minimal gate, focused canaries, complete DuckDB gates, and Pointer beyond all inputs | seated on frozen contract; first Design-A artifact only, no repair or commit |

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
| 2026-07-29 | coordinator local checkpoint commit | `2914373 feat: execute native DuckDB standard rebuilds`; six expected paths; clean worktree immediately after commit; no push | accepted exact tri-state compiler, split-UF target model, typed All/ordered-union staged executor, 13 canaries, and reconciled ledger are a durable rollback point | seated disjoint marker-rekey and raw-input diagnostic circles before any next writer |
| 2026-07-29 | post-frontier dependency census at committed `2914373` | static program-order trace of the five frozen sources and generated maintenance/config census; no edits/builds/tests/workload runs | marker support advances Math and Luminal to ordinary proof-instrumented rules, Eggcc to empty-body action evaluation, and Hardboiled to container rebuild; raw input alone advances only Pointer through 23 files/2,255 facts/13,530 rows and then to its first marker. Exact marker distribution is 866 total: 831 standard ordered-union scalar, 35 custom scalar, and 6 container-key rules. | marker rekey is the next writer front; raw input follows and must implement declared ordered-union collisions rather than a corpus-specific missing-only shortcut |
| 2026-07-29 | typed raw-input/Block audit at committed `2914373` | static trace from Rust TSV parsing through the proof-mode heterogeneous `NativeInputValue` batch, retained configs, and current DuckDB preflight; no edits/builds/tests/workload runs | existing SPI preserves batch order, dense fresh slots, and complete merge IR. Pointer has 23 unique-key files, 2,255 facts, 13,530 direct rows, and 9,020 frontend fresh IDs, but duplicate/existing-key correctness requires Sym/Trans allocation, displaced-UF writes, subsumed-owner preservation, unbounded waves, and full rollback. | missing-only admission is rejected; later input work must generalize the accepted ordered-union queues inside the DuckDB transaction with one bounded recursive-trace fallback |
| 2026-07-29 | marker-rekey semantic/IR/SQL census at committed `2914373` | five capped proof desugars plus committed Reference/SPI/DuckDB inspection; no edits/builds/tests/public reruns | 866 structurally identical seminaive rules over 363 marker targets, arity 1..27: two `All` tables plus typed `!=`, then canonical Unit Set and stale-key Delete. Existing SPI is complete. Stable mixed execution must materialize all Standard/Marker matches together, globally Delete before Set, keep Standard queue closure local, allocate no marker IDs, and roll back all state atomically. | select DuckDB-local `MarkerRekeyPlan` plus combined rebuilding executor; running markers as a second call or recursively closing marker chains is rejected |
| 2026-07-29 | marker-rekey writer freeze at committed HEAD `2914373` | reproduced owned patch-stream hash `9e192f268f13af2279b0a7157eb28b60f388a7b391bd612b05ebe726cf1fd339`; seven DuckDB-only paths; every worker subprocess capped at 110 seconds and nonbundled | focused marker 11/11; DuckDB 72/72; feature CLI 4/4; DuckDB/CLI Clippy, feature build, formatting, and whitespace gates pass. Math 18, Eggcc 77, Hardboiled 20, and Luminal 38 markers execute before distinct later fail-closed boundaries; Pointer retains raw-input boundary. | freeze Design A for three independent reviews; no writer repair, commit, broad proof gate, or next-front work authorized |
| 2026-07-29 | frozen marker admission review at owned hash `9e192f26...` | complete production compiler/config/typed-role/action and focused-test audit; reviewer reproduced HEAD/hash/status at both boundaries; no writes/builds/tests/writer contact | `REVISE` for canary evidence only: add `(Some,Some)` and explicit path/container/custom fallthrough plus naive, primitive-output, and marker default/identity/subsumability mutations with RuleId preservation. Production tri-state logic and ordering are correct. | hold repair until semantic and SQL/test reviews finish, then consolidate at most one bounded repair |
| 2026-07-29 | frozen marker semantic review at owned hash `9e192f26...` | Reference/SPI comparison plus complete compiler/executor/canary audit; reviewer reproduced HEAD/hash/status at both boundaries; no writes/builds/tests/writer contact | `PASS`: all matches share the pre-wave; Deletes precede heads; only Standard closure recurses; Marker IDs remain zero; one-hop, convergence, cross-delete, generation/report split, nonzero-watermark rollback/retry, scratch and telemetry publication are correct | no semantic repair required; retain wide-codec and commit-failure canaries as non-blocking inherited risks |
| 2026-07-29 | frozen marker SQL/test/API review at owned hash `9e192f26...` | complete generated-SQL, shared-executor, public-API, forbidden-surface, scope, accounting, and canary audit; reviewer reproduced HEAD/hash/status at both boundaries; no writes/builds/tests/writer contact | `REVISE` for the same canary gap: explicitly exercise marker non-ownership of path/container/custom near-shapes and add naive/wrong-primitive-output cases. Typed SQL, ranking, owner preflight, zero-ID behavior, transactions, Standard regression surface, and scope pass. | consolidate with admission feedback into the sole bounded repair; production changes only if a new canary proves a live classifier defect |
| 2026-07-29 | sole marker repair freeze at committed HEAD `2914373` | coordinator reproduced repaired owned hash `fce5af5b1359614de29079f34309e57be69c9ff7264a43040ee37f615f4a21d1`; delta only in marker tests plus test-only visibility of the existing path fixture constructor | repair stayed test-only: direct canaries now cover `(Some,Some)`, real path/container/custom-Block/no-outer/direct/Standard fallthrough and the full requested flag/primitive/action/config/alias/UF mutation matrix. Focused 12/12, DuckDB 73/73, feature CLI 4/4, all lint/build/format/diff gates pass; five public boundaries unchanged. | return only repaired surface to admission and SQL/test reviewers; repair budget exhausted and no production semantic re-review needed |
| 2026-07-29 | repaired marker admission re-review at owned hash `fce5af5b...` | direct initial-to-repaired test-surface review; reviewer reproduced HEAD/hash/status at both boundaries; no writes/builds/tests/writer contact | `PASS`: direct `compile_marker_rekey -> None` plus RuleId-0 canaries close both-ordered, real path, container, custom Block, no-outer, direct, and Standard fallthrough; selected flag/primitive/config/action/UF errors are complete | admission gate closed; no production correction or second repair |
| 2026-07-29 | repaired marker SQL/test re-review at owned hash `fce5af5b...` | direct initial-to-repaired test-surface/API/scope review; reviewer reproduced HEAD/hash/status at both boundaries; no writes/builds/tests/writer contact | `PASS`: the sole blocker closes through direct classifier/RuleId canaries; repair is test-only, accounting is 12 marker plus 61 prior tests, and no forbidden API/scope drift appeared | all frozen reviews pass; coordinator acceptance set authorized |
| 2026-07-29 | coordinator final marker-rekey acceptance | reproduced owned hash `fce5af5b1359614de29079f34309e57be69c9ff7264a43040ee37f615f4a21d1`; nonbundled DuckDB lib and focused marker tests; DuckDB and feature-CLI Clippy; feature CLI test/build; format/diff; five rebuilt proof-mode probes; `make proof-tests`; every process externally capped at 110 seconds | fresh PASS: DuckDB 73/73, marker 12/12, feature CLI 4/4, all lint/build/format/diff gates exit 0; Math/Eggcc/Hardboiled/Luminal execute 18/77/20/38 markers before distinct later fail-closed boundaries, Pointer retains raw input, and no probe times out; proof gate core 204/204 plus experimental 8/8 in 22.36s | marker rekey accepted for one local checkpoint commit; complete ordered-union raw input is the next bounded frontier |
| 2026-07-29 | coordinator local checkpoint commit | `7a1ec52c8a77edac7e0fc62ec029660af373a087 feat: execute native DuckDB marker rekeys`; nine expected paths; clean worktree immediately after commit; no push | accepted exact marker tri-state compiler, mixed stable Standard/Marker executor, 12 marker canaries, and reconciled ledger are a durable rollback point | seat ordered-union reuse and raw-input test-plan circles before another writer |
| 2026-07-29 | ordered-union reuse architecture audit at committed `7a1ec52` | current native input, exact ordered-union validator, accepted rebuild queue fold, Reference merge actions, and DD scheduling; static/read-only | Design A extracts typed queue preparation, seed admission, and global wave draining for input-specific use. It preserves caller ordinals, reserves frontend slots before collision IDs, keeps generic Direct Set admission deferred, and recursively validates the displaced-UF graph. Design B is a materially broader unified Set scheduler. | select Design A; after one reviewed repair only, Design B may be tried once, then stop rather than add a third design or host fallback |
| 2026-07-29 | Pointer raw-input integration audit at committed `7a1ec52` | Rust TSV parsing, proof-mode batch construction, DuckDB preflight/literal encoder, checked-in fact files, and source program order; static/read-only | 23 atomic calls contain 2,255 unique facts, 13,530 direct rows, 9,020 dense fresh slots, and 115 target groups. Pointer reaches only String/i64/Id/Unit; the sixth row of its first fact is the first rejected ordered-union View. The central hex/numeric typed literal encoder is complete for this surface. | no parser/SPI/fixture change; success is all inputs committed before the first ordinary proof-instrumented rule at source lines 70--74, with timeout reported rather than misclassified |
| 2026-07-29 | raw-input semantic/canary audit at committed `7a1ec52` | Backend contract, Reference atomic input and merge waves, DD diagnostic ordering, existing DuckDB input tests/hooks, proof ordered-union topology, and Pointer corpus; static/read-only | Reference is the blocking oracle. The irreducible gate is old-min, new-min, and identity-equal/payload-different with exact slots-before-Sym/Trans IDs. Eight focused tests cover heterogeneous order, duplicate/live/subsumed owners, self/cross waves, nullary/27-column hostile types, rollback/retry, negative/structural admission, direct-only telemetry, and synchronous flush. | freeze correctness as blocking; one Pointer attempt under 110 seconds is descriptive, and timeout is censored rather than a semantic result |

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

## Worker contract: marker rekey

- **Hypothesis:** the exact generated marker family can be recognized from
  typed/config topology and executed with Standard rebuild rules inside one
  stable DuckDB pre-wave and transaction, without shared SPI or proof-name
  knowledge.
- **Target artifact:** a DuckDB-local `MarkerRekeyPlan`, source-independent
  tests, and a combined `StandardRebuild | MarkerRekey` executor. The compiler
  is tri-state: unrelated families fall through, a selected malformed family
  errors before RuleId allocation, and only complete marker forms are admitted.
- **Exact family:** seminaive/decomposed; two `ReadMode::All` table atoms and
  typed `!=(Id, Id) -> Unit`; marker config is arbitrary safe scalar/Id keys
  plus Unit, `AssertEq`, `Fail`, no identity values, non-subsumable; the selected
  Id key joins an exact self-displacing KeyToParent UF; head order is canonical
  marker Set followed by stale marker Delete with no other action.
- **Execution:** materialize and count every Standard and Marker stage before
  mutation; reject any other mixed kind; validate owners and reserve only
  Standard fresh IDs; globally apply Standard eq-key plus Marker stale Deletes,
  then deterministic Standard heads plus Marker Sets, then drain only Standard
  ordered-union queues. Marker rules allocate no IDs and do not recursively
  close chains in the same bounded call. One physical generation bump covers
  all changes; deletion-only remains public `changed=false`; every row, counter,
  stage, run id, telemetry field, and watermark shares the transaction boundary.
- **Canaries:** unary and mixed typed 27-key/index-21 forms; body permutations;
  unfiltered `All`; converging keys; pre-existing canonical deletion-only;
  cross-delete chain across calls; reversed marker schedule; mixed stable
  Standard/Marker snapshot; exact Standard allocation with zero Marker slots;
  duplicate-owner and late nonzero-watermark rollback/retry; quiescence; and a
  complete fallthrough/error matrix for mode, flags, primitive, roles, configs,
  actions, aliasing, containers, custom rules, path rules, and ordinary direct
  rules with RuleId preservation.
- **Public gate:** Math must pass all 18 markers, Eggcc 77, Hardboiled 20, and
  Luminal 38 before stopping at their distinct next unsupported registration;
  Pointer must remain at raw-input Block preflight. No probe may time out and no
  timing is a completion threshold.
- **Owned write set:** `egglog-experimental/duckdb/**` only, excluding this
  ledger. Expected files are a new marker compiler/tests plus narrow
  `rule_sql.rs`, `storage.rs`, `rebuild.rs`, and module-wiring changes. No
  frontend/backend-trait/Reference/DD, manifest/lockfile, fixture/snapshot,
  benchmark harness/cache, raw input, container/custom merge, proof-name
  registry, unsafe/private API, UDF, host callback/mirror, performance tuning,
  commit, or push.
- **Verification:** focused marker tests; complete nonbundled DuckDB lib tests;
  DuckDB and feature-CLI Clippy with warnings denied; feature CLI test/build;
  formatting/diff checks; and five public probes. Every subprocess receives the
  external 110-second watchdog; no bundled build. Coordinator owns the broad
  proof gate after independent frozen-artifact review.
- **Stop:** freeze Design A's first reviewable artifact without commit or push.
  At most one independent-review-authorized repair may follow. If variant
  branching cannot preserve stable-prewave/global phases/rollback without
  shared or forbidden machinery, try one shared typed `RebuildingPlan` Design B.
  If both designs fail the same semantic gate, exit early; do not add a second
  `run_rules`, recursive marker closure, name special case, or third design.

### Sole authorized marker repair

- Add marker-specific RuleId-preserving canaries for the `(Some, Some)`
  ordered-union fallthrough and explicit path, container, and custom-Block
  near-shapes. The assertions must distinguish `Ok(None)` fallthrough from a
  selected marker-family error rather than merely checking that registration
  fails somewhere later.
- Complete the selected-family mutation matrix for `seminaive = false`, wrong
  primitive output/signature, and marker `DefaultVal`, identity-count, and
  subsumability changes. Include action-target/Unit and opposite-UF-orientation
  mutations if they can be expressed without unrelated fixture machinery.
- This is test-only by default. A narrow production admission correction is
  permitted only when one of the new canaries demonstrates a live classifier
  defect, and must be reported explicitly. Executor/storage semantics are
  frozen.
- Rerun focused marker and complete DuckDB tests, DuckDB/feature CLI Clippy,
  feature CLI test/build, format/whitespace, the owned hash, and five public
  boundaries, all individually capped at 110 seconds and nonbundled. Freeze the
  repaired artifact without commit/push and return it to both revising reviewers;
  no second repair is authorized.

## Worker contract: complete typed ordered-union native input

- **Hypothesis:** the exact scalar ordered-union `MergeFn::Block` already
  accepted by Standard rebuild can be admitted specifically for native input by
  extracting its DuckDB queue kernel. Rust-parsed values remain typed raw-SQL
  `VALUES`; every match, owner selection, collision, merge decision, and
  generated row remains inside DuckDB.
- **Frozen base:** committed
  `7a1ec52c8a77edac7e0fc62ec029660af373a087`. The Reference backend is the
  blocking semantic oracle. DD is diagnostic only where its stable
  `(merge_level, FunctionId)` ordering differs.
- **Admission:** classify the complete target graph structurally from retained
  `FunctionConfig`: a subsumable View is `EclassToTerm`; its displaced
  non-subsumable UF is `KeyToParent` and self-displacing; Sym/Trans are exact
  one-output AssertEq targets. Validate the full seven-action Block, typed
  schemas, primitives, slots, proof Sets, result tuple, and recursive displaced
  graph. A near-shape remains deferred. This is an input-only capability:
  ordinary Direct `Set` compilation must continue to reject the Block.
- **Execution:** preserve each caller row's original ordinal while grouping.
  Before durable mutation validate every target, row arity, stale sentinel,
  typed/dense slots, literal encoding, ordered-union graph, owner uniqueness,
  subsumed-UF prohibition, AssertEq conflicts, and fresh capacity. In one
  transaction, reserve all frontend slots first; apply direct KeepOld/AssertEq
  input; enqueue ordered-union seeds at wave zero; then drain target queues in
  `(wave, FunctionId, event ordinal)` order. Missing owners insert live;
  identity-equal owners retain the complete old tuple/status/generation and run
  no actions; identity-changing collisions emit exact Sym then Trans rows,
  preserve an existing View's subsumed bit, update the canonical owner, and
  enqueue the displaced UF write at wave plus one. No semantic wave cap is
  permitted. Increment generation once iff any direct or generated physical
  state changed. Any error restores rows, both fresh-ID classes, generation,
  scratch, input telemetry, rule telemetry, and the last committed SQL trace.
- **Telemetry:** preserve the existing local meaning: `rows` is requested
  direct rows; `target_statements` is unique direct input targets;
  `inserted_rows` is direct physical owner inserts only, excluding collision
  updates and generated Sym/Trans/UF effects. Failure publishes zeros. A
  successful input is synchronous, so the next `flush_updates()` is false.
- **Irreducible gate:** with slots beginning at 100, check Reference-equivalent
  old-min and new-min View collisions allocate slots 100/101, then Sym 102 and
  Trans 103, emit the direction-correct proof rows and displaced UF edge, and
  leave 104 next. An identity-equal/payload-different candidate consumes its
  explicit slot but retains the old payload, emits no effects, and does not
  advance generation. Failure of any one stops the larger implementation.
- **Focused canaries:** one opaque/renamed generic fixture instantiated
  independently on Reference and DuckDB; frontend-shaped heterogeneous order;
  missing/equal/two- and three-way live/subsumed collisions; self- and
  cross-target queue fixed points; nullary and synthetic 27-column mixed hostile
  keys; late direct/indirect AssertEq and capacity rollback with exact retry
  IDs; structural near-miss/unknown/arity/stale/wrong-slot/sparse-slot negative
  admission; generation/watermark/scratch/telemetry/SQL-trace preservation; and
  no parameter markers or forbidden input API. Do not add referential-integrity
  checks for a valid minted-but-not-stored Id.
- **Public gate:** one freshly built Pointer proof-mode attempt under the
  external 110-second watchdog. Success for this slice is all 23 input calls
  (2,255 facts, 13,530 direct rows, 9,020 slots) completing and execution
  reaching the first ordinary user rule at
  `benchmarks/pointer-analysis-small.egg:70`, or exiting zero. Capture the first
  live later diagnostic. A timeout is censored performance data and neither a
  semantic pass nor failure; statement count, wall time, and RSS are descriptive.
- **Owned write set:** `egglog-experimental/duckdb/**` except this ledger,
  normally `src/storage.rs`, `src/rebuild.rs`, `src/lib.rs`, and one focused
  input test module. No frontend, SPI, Reference/DD, marker, ordinary-rule,
  container, manifest/lockfile, Pointer fixture, harness/cache, commit, or push.
- **Forbidden shortcuts:** missing-only/rank-one final insertion; host row
  mirror/enumeration/matcher/merge; proof/table/sort-name or numeric-ID routing;
  Appender, Arrow, `read_csv`, `COPY`, parameters, SQL NULL-as-undefined,
  ordinary-row index/PK, unsafe/private/FFI APIs, fork/patch, durable metadata
  beyond generation/subsumed, or a nontransactional/fail-open fallback.
- **Verification:** focused input tests, complete nonbundled DuckDB lib tests,
  DuckDB Clippy with warnings denied, feature CLI tests/build/Clippy, formatting,
  diff/whitespace checks, and the Pointer public probe. Every subprocess gets an
  external 110-second watchdog. Freeze an exact owned patch-stream hash before
  three independent semantic, admission, and safe-SQL/test reviews; the
  coordinator alone runs the broad proof gate after review.
- **Stop rule:** Design A is the shared queue extraction. At most one
  review-authorized repair may follow. If it cannot meet the irreducible gate,
  Design B is one typed recursive SQL effect trace with the same ordering and
  transaction contract. If both materially different SQL-only designs fail the
  same minimal transcript, or correctness requires any forbidden shortcut,
  stop and preserve the smallest counterexample; do not try a third design or
  begin performance tuning.

## Typed ordered-union native-input implementation evidence

- **Frozen base:** `7a1ec52c8a77edac7e0fc62ec029660af373a087`.
- **Frozen owned paths:** `egglog-experimental/duckdb/src/lib.rs`,
  `rebuild.rs`, `storage.rs`, and the new `input_tests.rs`. The coordinator
  ledger is the only other dirty path.
- **Frozen patch-stream SHA-256:**
  `46c6e388470b066ce0c0cb72d68842f3ab852248b56b81bae9e6024c158663f1`,
  reproduced independently from the tracked binary diff plus the untracked
  no-index binary diff.
- **Implementation result:** Design A meets the irreducible Reference gate for
  old-min, new-min, and identity-equal collisions. Rebuild and native input
  share the extracted SQL queue kernel; input-specific admission does not
  change `WriteCapability::Deferred` for ordinary Direct Set. The input path
  preserves global caller ordinals, pre-encodes typed literals, reserves all
  frontend slots before collision IDs, recursively closes displaced UF queues,
  publishes direct-owner telemetry only, and commits effects atomically.
- **Writer gates, each externally capped at 110 seconds:** focused input 8/8
  passed in 0.08s; complete nonbundled DuckDB lib 81/81 in 0.29s; DuckDB Clippy
  with warnings denied in 1.05s; feature CLI 4/4 in 6.24s; feature CLI Clippy in
  1.28s; fresh feature build in 6.58s; formatting and diff checks passed. The
  coordinator-owned broad proof gate has not run yet.
- **Pointer attempt:** the single permitted attempt failed before process
  startup in 0.49s because dyld could not load `@rpath/libduckdb.dylib` and the
  executable had no `LC_RPATH`; 0/23 inputs ran. RSS was 704,512 bytes. This is
  an environment/load-path residual and provides neither semantic pass nor
  semantic failure. Do not retry without a material build/link change.

## Active review roster: typed ordered-union native input

| Agent | Circle/domain | Aim | Authority | Expected output | Stop |
| --- | --- | --- | --- | --- | --- |
| semantic reviewer | Reference/order/allocation/transaction/generation/subsumption | Check exact backend semantics against the frozen contract and first-principles code paths | Read-only feedback; no commands that build or mutate | PASS or evidence-bearing blocking findings with exact paths/witnesses | End after one complete frozen-diff review |
| admission reviewer | input-only classifier and fail-closed near-shapes | Prove native input admits exactly the ordered-union family while ordinary Direct Set remains deferred | Read-only feedback; no commands that build or mutate | PASS or exact over/under-admission findings | End after one complete frozen-diff review |
| safe-SQL/test reviewer | public APIs, forbidden shortcuts, typed SQL, telemetry, tests, Pointer evidence | Audit boundary purity and whether tests/gates substantiate the contract | Read-only feedback; no commands that build or mutate | PASS or exact live gaps, distinguishing missing evidence from defects | End after one complete frozen-diff review |

All reviewers must begin and end at HEAD
`7a1ec52c8a77edac7e0fc62ec029660af373a087`, reproduce patch-stream SHA-256
`46c6e388470b066ce0c0cb72d68842f3ab852248b56b81bae9e6024c158663f1`,
observe only the four frozen owned paths plus this coordinator ledger as dirty,
and make no writes, builds, tests, benchmark runs, commits, pushes, or contact
with the retired writer. Review against the frozen artifact, not mutable chat.

### Frozen review synthesis

- **Semantic review: PASS.** No live semantic defect found. The reviewer traced
  global ordinals, frontend-slot reservation, wave/FunctionId/event order,
  Sym-before-Trans allocation and orientation, complete-old identity retention,
  old/new minima, displaced UF recursion, subsumption, duplicate-owner
  preflight, rollback, generation, telemetry, trace publication, and Reference
  parity. Residual evidence only: Pointer did not start, and an interleaved
  two-key/second-same-key allocation canary would strengthen coverage.
- **Admission review: PASS for semantic row admission, REVISE classifier
  ownership.** No invalid family mutates and no valid ordered-union family is
  rejected. Native input currently claims a root seven-action outer shape
  before proving the displaced graph belongs to the ordered-union family; a
  custom View whose displaced target is a plain AssertEq therefore receives a
  selected-family validation error rather than generic deferred fallthrough.
  The row/state remain unchanged. The native-input mutation matrix also lacks
  recursive graph, config, slot, proof-target, and result-tuple canaries.
- **Safe-SQL/test review: runtime/data path PASS, REVISE documentation.** No
  forbidden API, host row decision, name/ID routing, parameter, nullable stored
  value, index/PK, or unsafe/private/fork path was found. The
  `last_input_inserted_rows` comment incorrectly implies all generated inserts,
  while the accepted metric is direct physical owner inserts only. The
  `WriteCapability` comment omits the narrowly validated input-specific
  ordered-union exception. Existing tests establish rollback structurally;
  direct KeepOld plus a later generated AssertEq failure is optional extra
  coverage, not a live defect.
- Every reviewer ended on the frozen HEAD/hash and exactly the expected five
  dirty paths, with no writes, builds, tests, binaries, commits, pushes, or
  writer contact.

### Sole authorized native-input repair

- Make input claim the ordered-union family only after the complete displaced
  graph passes the same structural ownership prefilter used by Standard
  rebuild. Unrelated custom seven-action Views must fall through to generic
  `Deferred`; selected malformed members of an owned graph must still fail
  closed before mutation.
- Add a native-input regression for the concrete custom-View/plain-AssertEq
  witness and expand the targeted mutation matrix across recursive Sym/Trans
  or fresh-label disagreement, displaced self-target/orientation, relevant
  config flags, Let slots/proof-target config, and result tuple where the
  existing fixture can express them without unrelated machinery. Assertions
  must distinguish fallthrough from selected-family rejection and prove no
  state/counter/generation change.
- Correct only the two inaccurate public/internal comments for
  `last_input_inserted_rows` and `WriteCapability`. Do not change the accepted
  telemetry behavior or globally widen ordinary Direct writes.
- The interleaved mixed-key allocation and direct-KeepOld-plus-late-generated-
  failure probes are optional only if they fit the existing fixture with no
  production expansion. They are not permission to redesign the executor.
- Owned write set remains the same four DuckDB source paths. No frontend, SPI,
  Reference/DD, manifest/lockfile, fixture, Pointer/harness, link/rpath,
  performance, commit, or remote change. Do not rerun Pointer: the dyld premise
  is unchanged and the single public attempt is already recorded.
- Rerun focused input tests, complete nonbundled DuckDB lib tests, DuckDB and
  feature-CLI Clippy with warnings denied, feature CLI tests/build, formatting,
  and diff checks under independent 110-second watchdogs. Freeze and report a
  new exact patch-stream hash. The coordinator owns the broad proof gate.
- This is the one permitted repair. If complete-graph ownership cannot preserve
  selected-malformed fail-closed behavior without broad classifier or SPI
  changes, stop with the smallest witness; do not attempt another design.

### Native-input repair evidence

- **Frozen repaired patch-stream SHA-256:**
  `bfd333cc9ad2795c575a2629934017190d06a537ba2ddb15573b82bced8a4cbc`,
  independently reproduced from the tracked DuckDB binary diff plus the
  untracked `input_tests.rs` no-index binary diff at unchanged HEAD
  `7a1ec52c8a77edac7e0fc62ec029660af373a087`.
- Complete-graph ownership now makes an unrelated custom seven-action View,
  including the plain displaced-AssertEq witness, fall through generically.
  Once the graph is owned, malformed members remain selected and fail closed.
- Added the concrete fallthrough regression and a seven-case admission mutation
  matrix with explicit no-row/counter/generation/trace/telemetry mutation
  assertions. The rollback canary now also includes a direct KeepOld insertion
  before a late generated failure. Corrected the two telemetry/capability
  comments without changing behavior.
- Writer gates under independent 110-second watchdogs: focused input 10/10;
  complete nonbundled DuckDB lib 83/83; DuckDB all-target Clippy with warnings
  denied; feature CLI 4/4; feature build; feature CLI Clippy with warnings
  denied; formatting and diff checks all passed. Pointer was not rerun. No
  commit or push occurred; dirty scope remains the four authorized files plus
  this coordinator ledger.

### Native-input repair reviews and coordinator acceptance

- **Admission re-review: PASS.** The complete-graph ownership prefilter closes
  the generic-fallthrough defect; the custom View/plain-AssertEq witness now
  defers with no mutation, the seven-case owned-graph matrix remains selected
  and fail-closed, and ordinary Direct Set remains globally deferred with
  RuleId preservation.
- **Safe-SQL/test re-review: PASS.** Both comments match the accepted behavior;
  direct KeepOld plus late generated failure rolls back and retries exact IDs;
  no forbidden API, host row decision, parameterized ingestion, unsafe/private
  path, index, or name routing was introduced. Both reviewers independently
  reproduced the unchanged HEAD, five-path dirty scope, and repaired hash, and
  made no writes or execution attempts.
- **Coordinator fresh gates, each externally capped at 110 seconds:** focused
  input 10/10 in 0.08s; complete DuckDB lib 83/83 in 0.29s; DuckDB all-target
  Clippy with warnings denied; feature CLI 4/4; feature build; feature CLI
  Clippy with warnings denied; `cargo fmt --all -- --check`; and
  `git diff --check` all passed.
- **Broad proof gate:** `make proof-tests` passed 204/204 core plus 8/8
  experimental proof tests in 22.68 seconds wall time under the external
  watchdog. The emitted unextractable-root diagnostics are expected passing
  fixture output; exit was zero.
- **Public integration residual:** Pointer remains unclassified because the
  sole attempt failed in dyld before program startup. Do not describe 0/23
  inputs as either a DuckDB semantic pass or failure. Link/rpath remediation is
  a distinct material change and was intentionally excluded from the sole
  semantic repair.

## Next action

The typed ordered-union native-input checkpoint is committed locally as
`ee71aa30d984a248c12bb2f34a01e450972cb59a` with no push; the worktree was
clean immediately after the commit. Begin a new Understand/Explore round before
another implementation slice.

### Active re-census roster

| Agent | Circle/domain | Aim | Authority | Expected output | Stop |
| --- | --- | --- | --- | --- | --- |
| runtime-link auditor | macOS Mach-O/DuckDB launch boundary | Identify why `@rpath/libduckdb.dylib` cannot load and the smallest public-API/runtime remedy; distinguish repository defect from invocation environment | Read-only inspection plus bounded loader-only `--help` probes; no build, workload, or edit | Exact cause, observed loader matrix, minimal material fix candidates, risks | Stop after one discriminating loader probe per materially distinct environment |
| workload-frontier auditor | five benchmark proof-mode compiler/runtime surface | Re-census the earliest likely post-input unsupported boundary from committed code, prior public diagnostics, and source rules; rank the next functional slice | Read-only source/log inspection; no builds, tests, workloads, or edits | Per-workload boundary table, shared mechanism, smallest canaries, next-slice recommendation | Stop when one shared frontier or explicit divergent ordering is evidenced |

Both auditors start from committed HEAD
`ee71aa30d984a248c12bb2f34a01e450972cb59a`, observe only this coordinator
ledger as dirty, and make no source edits, commits, pushes, benchmark/cache
changes, or contact with retired writers. Every loader-only process is capped
at 110 seconds and must not invoke Pointer or another workload. The coordinator
owns any subsequent five-workload public probes and must not retry Pointer until
the runtime-link audit establishes a materially different launch premise.

Synthesize both audits into one proposal with a concrete next writer, owned
write set, canaries, acceptance signal, and stop rule. Do not treat the dyld
failure as semantic evidence, implement two adjacent slices in parallel, or
begin performance tuning.

### Re-census audit synthesis

- **Loader cause:** the failed Pointer command placed
  `DYLD_LIBRARY_PATH` before SIP-protected `/usr/bin/time`; the platform binary
  stripped the `DYLD_*` environment before launching egglog. The retained
  DuckDB-feature executable loads `@rpath/libduckdb.dylib` and has zero
  `LC_RPATH` entries, while `target/debug/deps/libduckdb.dylib` is the correct
  universal DuckDB 1.5.4 image. Direct `env DYLD_LIBRARY_PATH=... <bin> --help`
  and `/usr/bin/time -lp env DYLD_LIBRARY_PATH=... <bin> --help` both exit zero;
  placing `env` before `/usr/bin/time` reproduces exit 134 and the exact dyld
  error. No Pointer retry occurred during the audit.
- **Immediate launch premise:** after recreating the top-level DuckDB-feature
  binary, place `/usr/bin/time -lp` before
  `env DYLD_LIBRARY_PATH="$PWD/target/debug/deps"`. A successful `--help` on
  that exact image authorizes one fresh coordinator-owned attempt per frozen
  workload, including exactly one Pointer retry. The missing final-target
  relative rpath is real packaging debt but is not required for this functional
  census and must not be mixed into the compiler slice.
- **Static workload frontier:** Math and Luminal retain the same first ordinary
  commutativity rule: one Live View body and a structurally isomorphic 34-action
  proof-instrumented head with literals/aliases, one action-side proof lookup,
  14 fresh IDs, ordinary proof/constructor Sets, and a final ordered-union View
  Set. Eggcc remains at an empty-body ground action rule. Hardboiled remains at
  an All/body-container-rebuild primitive. Pointer is predicted, but not yet
  observed, to finish 23 inputs and stop at a 28-action ordinary rule containing
  `set-if-empty` and a semantic View read.
- **Provisional priority:** implement a native nonempty scalar mixed-action
  scheduler for the shared Math/Luminal topology first. Keep Pointer semantic
  primitives, Eggcc empty-body execution, and Hardboiled containers as later
  separately gated slices. Reuse the existing ordered-union queue kernel; do not
  add host matching/merge, name routing, shared SPI, unsafe/private APIs, or
  adjacent capabilities.

### Authorized fresh public census

Build the nonbundled DuckDB-feature CLI under the 110-second watchdog. Verify
the corrected `/usr/bin/time -lp env DYLD_LIBRARY_PATH=... <exact-bin> --help`
premise once. If it passes, execute Math, Eggcc, Pointer, Hardboiled, and Luminal
once each in DuckDB proofs/no-messages mode, each in a fresh process with its
own 110-second watchdog and corrected environment order. Pointer alone receives
its fact directory. Capture exact exit, wall time, RSS, and first diagnostic.
Do not retry a timeout or any workload without a material change. A timeout is
censored performance data. Any input/transaction failure in Pointer is a live
checkpoint defect; reaching line 70 or a later ordinary-rule diagnostic closes
the native-input integration residual.

After the census, consent-check one mixed-action writer contract against the
observed boundaries. Do not implement rpath packaging, semantic primitives,
empty bodies, containers, or performance changes in that writer.

### Fresh public census at `ee71aa3`

The exact rebuilt feature binary SHA-256 was
`61bed546a5965e48c5321034bffd03cf7875197d34b84ab2f9af74148545c829`.
The corrected-order loader-only `--help` exited zero in 0.54 seconds with
13,107,200-byte max RSS. Every workload then ran once in a fresh process under
its own external 110-second watchdog, using `/usr/bin/time -lp env
DYLD_LIBRARY_PATH=... <binary>` in that order:

| Workload | Exit | Real | Max RSS | First live boundary |
| --- | ---: | ---: | ---: | --- |
| Math | 1 | 0.02s | 37,175,296 B | `(rewrite (Add a b) (Add b a))` unsupported action language |
| Eggcc | 1 | 1.99s | 73,596,928 B | `eval_actions` has an empty body |
| Pointer | 1 | 1.83s | 83,591,168 B | first `(allocation alloc) -> (A alloc)` user rule unsupported action language |
| Hardboiled | 1 | 0.03s | 44,793,856 B | `@rebuild_rule64` requests All; container rebuild body remains unsupported |
| Luminal | 1 | 0.04s | 59,490,304 B | `mul-comm` unsupported action language |

The Pointer run completed all 23 native input calls and generated maintenance
before reaching its ordinary user rule. This closes the native-input public
integration residual. None of the five timed out; no retry occurred.

### Active mixed-action proposal roster

| Agent | Circle/domain | Aim | Authority | Expected output | Stop |
| --- | --- | --- | --- | --- | --- |
| action semantic auditor | Reference/backend action evaluation and observable ordering | Freeze stable-prewave, action lookup/prediction, fresh-slot, Set/merge, generation/report, rollback, and seminaive semantics for the Math/Luminal topology | Read-only current source; no builds/workloads/edits | Exact semantic contract and smallest differential witnesses | Stop once every reached action motif has a source-backed ordering/failure rule |
| action SQL architect | accepted DuckDB compilers, staging, transaction, and ordered-union queue | Produce two SQL-only execution designs and recommend the smallest that preserves the semantic contract using public APIs | Read-only DuckDB/source/docs already pinned; no builds/workloads/edits | Plan IR, staging/phase/allocation algorithm, risks, second-design stop path | Stop after one recommended and one materially different fallback design |
| action admission/test auditor | Math/Luminal RuleSpec topology and fail-closed boundary | Define structural admission, canary/mutation matrix, public gates, and exact later-boundary exclusions | Read-only generated/source/compiler/tests; no builds/workloads/edits | Frozen family predicate, test plan, owned write set, stop rule | Stop once valid/invalid boundary and review gates are discriminating |

All three auditors start at committed HEAD
`ee71aa30d984a248c12bb2f34a01e450972cb59a`, observe only this coordinator
ledger as dirty, and make no source/cache/binary changes, commits, pushes, or
contact with prior writers. The action slice may target the reached nonempty
scalar Math/Luminal family, not every arbitrary action program. It must remain
typed/name-independent and fully DuckDB-native for match enumeration, action
lookups, merge decisions, and generated rows. Rust may orchestrate statements
and scalar counters only.

Synthesize the audits into one Design-A worker contract with a single owned
write set, irreducible semantic gate, negative family boundary, public
acceptance frontier, one review-authorized repair, and one materially distinct
Design-B fallback. Do not seat a writer until the contract is frozen.

### Mixed-action audit synthesis and locked decisions

- The reached Math/Luminal family is exactly one Live EclassToTerm View body,
  three literal/alias actions, one early Fail/Old action-side term-proof lookup,
  14 registered-token `get-fresh!` actions, and 16 Sets: 14 AssertEq, one Old,
  and one EclassToTerm ordered-union View Set. The View Set is zero-based action
  28 of 34; an alias plus two Fresh/AssertEq proof pairs follow it.
- Reference materializes a stable prewave, runs actions action-major over active
  lanes, flushes all ordinary action buffers, and invokes `merge_all` only after
  the complete action stream. The trailing actions do not read or predict the
  View, collision rows, or displaced UF. Therefore Design A must stage/apply all
  direct effects before draining the queued View candidate while retaining its
  source action/event ordinal. An action-28 queue barrier is rejected.
- Production admission for this checkpoint is the exact 34-action structural
  family, renamed and FunctionId-order independent. The plan IR may be generic
  over typed supported motifs and tests may exercise a reduced plan internally,
  but production must not claim an arbitrary five-motif program until its wider
  collision/error semantics receive a separate audit. Counts and topology are
  structural proof-encoding facts, not rule/table/sort-name routing.
- Explicit head IDs use deterministic `(schedule ordinal, fresh-action ordinal,
  canonical match ordinal)` allocation. One-match transcripts compare exact
  IDs; multi-match correctness compares typed state/proof topology modulo a
  sort-preserving fresh-ID bijection because Reference batching/parallelism does
  not provide stable global raw-ID-to-match order. Every explicit head ID is
  reserved before any ordered-union collision ID.
- The lookup reads durable prewave state, including subsumed current rows. It is
  Fail/Old, never lookup-or-insert and never prediction-producing; missing or
  duplicate owners abort atomically. Same-run Sets are invisible to it.
- Retain DuckDB's established atomic fail-closed policy: lookup failure, explicit
  fresh exhaustion, merge-time failure, conflict, overflow, or scratch failure
  rolls back rows, generation, counter, run identity, watermarks, telemetry, and
  trace. This intentionally differs from Reference's silent/partial head-fresh
  exhaustion and partial state after some errors; do not emulate that unsound
  failure state. Successful-state semantics remain the blocking oracle.
- Mixed-action telemetry is fixed as: matched rows are complete prewave matches;
  inserted rows are the 15 independent direct head installations per completed
  match (14 AssertEq plus one Old), excluding the queued View candidate and all
  collision-generated Sym/Trans/UF effects; changed is any physical direct or
  generated mutation; statement count is descriptive.
- Current rulesets may remain homogeneous for this bounded checkpoint. A mixed
  schedule containing scalar-mixed plus another plan kind must fail closed
  before mutation unless the writer can support it inside the same stable
  transaction without expanding the contract. If a public execution—not mere
  registration—requires mixing, stop and reassess rather than weakening phases.

## Worker contract: native scalar 34-action rules

- **Hypothesis:** the exact reached Math/Luminal commutativity family can compile
  into a typed tri-state `ScalarMixedPlan` and execute entirely through public
  DuckDB SQL using stable match/head/effect stages plus the accepted
  ordered-union queue, without a shared SPI change or host row enumeration.
- **Frozen base:** committed
  `ee71aa30d984a248c12bb2f34a01e450972cb59a`. The Reference backend is the
  successful-state semantic oracle. Error-state comparison follows the atomic
  fail-closed decision above. DD is diagnostic only.
- **Plan/dispatch:** add a separate scalar-mixed compiler after
  Standard/Marker/Path admission and before Direct; do not widen `DirectRule`
  or `WriteCapability`. Plans retain typed body/slot/literal refs, source action
  ordinals, semantic external-function tokens, target IDs/configs, Set kinds,
  fresh ranks, and the complete catalog-validated EclassToTerm/KeyToParent
  ordered-union graph. Plans/rendered SQL never route on diagnostic names,
  fresh-label text, opaque numeric allocation order, or corpus identity.
- **Tri-state ownership:** return `None` unless a multi-action rule has exactly
  one Live body table and a head Set back to that same table whose root and
  displaced merge both have the complete ordered-union outer graph. Once owned,
  require `seminaive && !no_decomp`, the exact 34-action kind/order above, exact
  typed SSA bind-before-use, one early `[Id] -> Id` Fail/Old/non-subsumable
  lookup, the retained DuckDB fresh semantic token with String-literal to Id
  signature, 14 scalar AssertEq/Unit targets, one scalar Old target, and the
  complete View/UF/Sym/Trans graph. Every selected deviation is `Err` before
  RuleId allocation; unrelated Direct/custom/Pointer/empty/container forms fall
  through to their existing exact diagnostic.
- **Stable execution:** before any durable mutation, validate every plan/target,
  materialize every scheduled body match at its seminaive watermark, assign a
  canonical ordinal from generation plus typed visible columns, and evaluate
  exact lookup cardinality against prewave durable state. Materialize the full
  typed 34-action head/effect stream. Rust reads only scalar counters/counts and
  issues statements; it never receives match, lookup, effect, or owner rows.
- **Allocation/effects:** checked-reserve all `14 * match_count` explicit slots
  in `(schedule, fresh action, match)` order. Apply ordinary Old/AssertEq stages
  in source-action order with setwise conflict checks and deterministic candidate
  folds. Enqueue the action-28 View candidates with source schedule/action/match
  event ordinals, apply actions 29--33, then drain the existing ordered-union
  queues to fixed point. Collision IDs start after the complete explicit range;
  missing/equal/old-min/new-min/subsumed owner and recursive UF semantics remain
  exactly those of the accepted queue kernel. There is no semantic wave cap.
- **Transaction/publication:** one transaction covers stable stages, rows,
  generation, explicit/collision counter reservations, scratch, run identity,
  watermarks, telemetry, and SQL trace. Bump physical generation once iff any
  direct or generated row state changed. Drop scratch inside the transaction;
  on failure roll back and clean connection-level residue, then preserve prior
  public state. Publish run identity/watermarks/telemetry/trace only after commit.
- **Irreducible gate:** a completely renamed one-match 34-action fixture with
  shuffled FunctionIds and fresh base 100 must match independently constructed
  Reference state/transcript exactly on a missing View owner: explicit IDs
  100..113, no collision IDs, 15 independent head inserts, one View install,
  next ID 114, changed true, and the new reversed View invisible to the same
  run. A differing-owner variant must allocate collision Sym/Trans 114/115 and
  leave 116 next with exact orientation and displaced UF state. Failure stops
  the larger implementation.
- **Positive canaries:** full renamed Math and Luminal equivalents; two matches
  proving fresh-action-major allocation and alpha-equivalent topology; stable
  prewave and seminaive quiescence; lookup hit including subsumed owner;
  View missing/equal/old-min/new-min/subsumed cases; ordinary Old and AssertEq
  setwise behavior; recursive UF fixed point; explicit-before-collision IDs;
  nullary and synthetic 27-key scalar Views where the exact fixture can express
  them; typed/hostile literals through the central codec; and a late trailing
  conflict/exhaustion rollback from nonzero watermarks followed by exact retry.
- **Negative canaries:** missing/duplicate lookup; moved/extra lookup; wrong
  seminaive/no-decomp/mode/body cardinality; use-before-bind/rebinding/type/arity;
  wrong fresh token/signature/count/action order; wrong ordinary target
  config/merge; incomplete/misoriented root/displaced ordered-union graph; a
  second View Set; mixed plan schedule; empty body; Pointer set-if-empty/View
  read; All/body primitives/containers; Delete/Subsume/Union/Panic/Change;
  tuple outputs/globals/unknown tokens/custom merges. Unrelated shapes preserve
  their current diagnostics; selected malformed shapes preserve RuleId zero.
- **Public gate:** with the corrected `/usr/bin/time -lp env
  DYLD_LIBRARY_PATH=...` order, Math must register lines 19--20 and Luminal
  lines 64--65 before reporting their next exact boundary. Eggcc must remain at
  empty-body `eval_actions`; Pointer must complete all 23 inputs and remain at
  its set-if-empty/View-read ordinary rule; Hardboiled must remain at its
  All/container rebuild. No probe may time out; timings/RSS/statements are
  descriptive only. Registration advance is the public signal; the synthetic
  34-action fixtures are the blocking execution signal because later unsupported
  registrations prevent these benchmark heads from running yet.
- **Owned write set:** new `egglog-experimental/duckdb/src/action_rule.rs` and
  `action_rule_tests.rs`; narrow `rule_sql.rs`, `rebuild.rs`, `storage.rs`, and
  `lib.rs` changes only. Exclude this ledger. No frontend/backend trait,
  Reference/DD, proof encoder, fixture/snapshot, census, manifest/lockfile,
  benchmark harness/cache, link/rpath, input/file loader, commit, or push.
- **Forbidden shortcuts:** host row/effect enumeration, matcher/merge/callback;
  proof/table/sort/rule/variable-name or FunctionId-order routing; Appender,
  Arrow, `read_csv`, `COPY`, parameters, SQL NULL-as-undefined, ordinary indexes
  or PKs, unsafe/private/FFI APIs, dependency fork/patch, proof-aware durable
  metadata, fail-open fallback, performance tuning, or adjacent empty-body,
  semantic-primitive, multi-body, container, or general action support.
- **Verification/review:** worker runs focused scalar-mixed tests, complete
  nonbundled DuckDB lib, DuckDB/feature-CLI Clippy with warnings denied, feature
  CLI tests/build, format/diff, and the five one-shot public boundaries, all
  under independent 110-second watchdogs. Freeze an exact owned patch hash.
  Three independent semantic, admission, and safe-SQL/test reviews follow; only
  the coordinator runs `make proof-tests` and commits an accepted checkpoint.
- **Stop/Design B:** freeze Design A's first reviewable artifact. At most one
  review-authorized repair may follow. If fused typed head/effect staging cannot
  meet the irreducible transcript, exact source ordering, or atomic failure
  contract, reassess one materially different typed action-bytecode/effect-trace
  executor with per-slot typed relations and explicit barriers. If both SQL-only
  designs fail the same reduced gate, or correctness requires a forbidden
  shortcut/shared API/adjacent capability, exit this goal early with the
  smallest witness; do not try a third architecture.

## Scalar-mixed contract amendment from the public API

The source/desugared proof form contains the 34 semantic actions documented
above, but the actual backend `RuleSpec` for the shared Math/Luminal
commutativity family contains 50 head actions. Core canonicalization prepends
one identity alias for the eliminated body equality and inserts one
call-result alias after the early Old lookup and each of the 14 `get-fresh!`
calls. The production admission contract is therefore the exact 50-action
frontend shape, with those 16 scaffolding aliases validated and collapsed to
the frozen 34-action semantic plan. Semantic action/event ordinals, 14 fresh
slots, 15 direct installs, and all expected poststates remain unchanged.

The earlier 34-action *backend-head* wording and action-28 physical index are
superseded. Action 28 remains the semantic View event ordinal after alias
normalization; it is not the raw frontend action index. Admission must reject
missing, moved, mistyped, or non-identity scaffolding aliases before RuleId
allocation. The tri-state selector must return `None` before inspecting actions
unless the rule has exactly one Live table body and a Set back to that same
complete nested ordered-union View table. This preserves Pointer, All,
container, UF-shaped, empty-body, and unrelated Direct diagnostics.

Fresh-token provenance is context-sensitive. Egglog registers the same generic
`get-fresh!` primitive separately for Write and Full contexts, so the ordered-
union graph token and the rule-head token may be distinct. Both must be live
tokens registered in this DuckDB backend; all 14 head calls must use the same
live head token and retain the String-literal-to-Id typed shape. Token numeric
IDs and diagnostic names are non-semantic.

## Frozen Design-A scalar implementation

The sole writer froze the six authorized source paths at committed base
`ee71aa30d984a248c12bb2f34a01e450972cb59a`. The coordinator independently
reproduced the complete owned patch SHA-256, including the two untracked files,
as `002a991b65b41bffb367bd19d8de6326aac65f0cb31e9f2f6dcc9dc92ac80a05`.
The only dirty path outside that owned set is this coordinator ledger.

The artifact contains the exact frontend/scaffolding compiler, transactional
native-SQL executor, ordered-union queue integration, live-token provenance,
strict tri-state ownership, and 19 focused tests. Internal review found and the
writer repaired: action-19 Old-table retargeting, name-sensitive `RuleVar`
comparison, unregistered fresh-token acceptance, overbroad scalar ownership,
the 34/35/50 frontend-count model, and incorrect equality between graph and
head context tokens. The accepted execution path retained direct-effects-first
ordering and one post-action-stream ordered-union drain.

Writer-reported bounded gates on the frozen hash:

- focused scalar tests 19/19;
- complete DuckDB library 102/102;
- DuckDB all-target Clippy with warnings denied;
- feature CLI tests 4/4, build, and Clippy;
- `cargo fmt --all -- --check` and `git diff --check`;
- independent minimal end-to-end commutativity registration advanced to the
  following associativity rule.

The writer's five one-shot public probes were evidence-producing but not final
acceptance probes because Math, Hardboiled, and Luminal exposed admission
defects repaired afterward. They were not retried by the writer. Initial
results were: Math 0.02s/37,208,064 B at the pre-repair 34-vs-50 mismatch;
Eggcc 2.54s/72,728,576 B at the expected empty-body boundary; Pointer
1.85s/83,820,544 B after all inputs at the expected allocation-rule boundary;
Hardboiled 0.03s/44,695,552 B at the pre-repair overbroad selector; Luminal
0.50s/59,326,464 B at the pre-repair graph/head token-equality check. None
timed out. The coordinator may run one fresh post-freeze acceptance probe per
workload after independent review; that is a materially changed artifact, not
a retry of the same premise.

### Independent review roster

| Agent | Circle/domain | Aim | Authority | Expected output | Stop |
| --- | --- | --- | --- | --- | --- |
| scalar semantic reviewer | Reference-success-state and DuckDB transaction semantics | Verify the frozen 50-to-34 normalization, prewave lookup, allocation, direct-before-queue ordering, collisions, rollback, generation, seminaive watermarks, and telemetry | Read-only frozen source and ledger; no edits/builds/tests/workloads/contact | Pass/fail findings with exact code evidence and smallest counterexample | Stop after every locked semantic invariant is traced or one blocker is proven |
| scalar admission reviewer | exact public RuleSpec family and tri-state fallthrough | Verify exact scaffolding/token/SSA/config admission, RuleId-zero failure, and preservation of unrelated Pointer/All/container/empty/custom diagnostics | Read-only frozen source/frontend/compiler/tests/ledger; no edits/builds/tests/workloads/contact | Pass/fail mutation matrix and any missing boundary | Stop once ownership and selected-vs-unrelated behavior are discriminated |
| scalar safe-SQL/test reviewer | public DuckDB boundary, native execution, and evidence quality | Verify no host rows/effects, private/unsafe/file/Arrow/Appender paths, proof-aware storage, or forbidden fallback; assess test canaries and writer gate claims structurally | Read-only frozen source/tests/ledger/diff; no edits/builds/tests/workloads/contact | Pass/fail findings, missing canary, and gate recommendation | Stop after the forbidden-shortcut audit and test sufficiency decision |

All reviewers must independently record start/end HEAD, owned hash, and status.
They may not contact the writer or each other. At most one consolidated,
review-authorized repair is available; no repair is presumed.

## Next action

The three frozen-hash reviews completed without changing HEAD, owned hash, or
the exact dirty set:

- **Semantic review: PASS.** The reviewer traced 50-to-34 normalization,
  prewave matching/lookup, explicit-before-collision allocation, all direct
  effects before the sole ordered-union drain, collision/recursive UF cases,
  rollback/publication, generation/watermarks, and telemetry. It found two
  nonblocking coverage gaps: a successful two-scalar-rule schedule and a
  scalar-specific subsumed-Live no-match canary.
- **Admission review: FAIL.** `scalar_mixed_owner` can claim a self-displacing
  UF-shaped rule because it does not require the selected body table to be a
  subsumable View before inspecting the action stream. The smallest repair is
  to return `None` for `!TableInfo::can_subsume`, then add a self-displacing UF
  fallthrough/RuleId-zero witness. It also requested exact scaffolding-alias
  mutation coverage.
- **Safe-SQL/test review: REVISE.** The SQL boundary itself contains no host
  row/effect enumeration, host merge, unsafe/private/FFI/fork/patch,
  Appender/Arrow/file SQL, parameters, indexes, proof metadata, or fail-open
  path. However ordered-union native semantics are currently authenticated by
  the strings `proof-of-min/max` and `ordering-min/max`, while the validator
  discards their `ExternalFunctionId`s. A same-token rename rejects and an
  expected-name spoof can select hard-coded SQL for a different callback in an
  adversarial `RuleSpec`; current tests do not discriminate those cases.

Do not spend the single repair or run broad gates until primitive provenance is
decided. Three read-only proposal-forming audits are active: (A) determine
whether `Primitive.name` is a trusted public source-language semantic identity
and whether the spoof/rename witnesses are reachable through the real frontend;
(B) design the smallest public semantic-tag SPI if names are insufficient; and
(C) decide whether public DuckDB vector/scalar UDFs can execute the exact
registered callback without forbidden host-row/reentrant state. After all
three return, consent-check exactly one repair contract containing the UF
prefilter, required negative canaries, and the chosen provenance design. If no
public, name-independent provenance path exists without a shared SPI change,
stop this scalar checkpoint and promote that SPI change to an explicit
prerequisite; do not add a heuristic or silently weaken the contract.

### Primitive-provenance decision and consolidated repair contract

All three proposal audits converged. Primitive names are stable frontend
metadata but are not authenticated semantics in the public Backend SPI:
`RuleSpec` fields are independently constructible, and Reference/DD execute the
`ExternalFunctionId` while using `name` only diagnostically. The ordinary
frontend co-derives name and token, so spoof/rename witnesses are not produced
by valid source programs, but they are valid public SPI inputs and Reference/DD
give them token semantics. DuckDB must not diverge by substituting SQL from the
string alone.

Public DuckDB UDFs are rejected for this prerequisite. In the pinned crate the
typed vector access needed by `VScalar` is unsafe (the safe alternative is the
forbidden Arrow path), there is no safe row-at-a-time UDF API, the erased
callback requires mutable `ExecutionState`, and UDF catalog lifetime does not
match freed/reused external-function IDs. Hard-coded typed SQL remains the
right executor only after registration-bound semantic authentication.

The one review-authorized repair is expanded into a shared prerequisite plus
the scalar repair, in one frozen artifact:

- Add a public, non-exhaustive, copyable/hashable `NativePrimitive` enum to
  `egglog-backend-trait` with the currently native semantics:
  `ValueNeq`, `OrderingMin`, `OrderingMax`, `SelectMinPayload`, and
  `SelectMaxPayload`. Semantics use strict raw-`Value` comparison; ties choose
  the right argument/payload; `ValueNeq` returns Unit only when unequal; wrong
  arity returns `None`.
- Add one defaulted object-safe
  `Backend::register_native_primitive(NativePrimitive) -> ExternalFunctionId`.
  The default registers the canonical callback, preserving Reference/DD and
  external Backend source compatibility. The method accepts no caller-supplied
  callback, so a native token cannot be bound to hostile behavior.
- Add a crate-private frontend registration helper that retains the existing
  primitive/type constraints/validators but asks each backend/context for a
  native token. Register source `!=`, `ordering-min`, `ordering-max`, and the
  two proof-payload selectors through it. Ordinary/user primitives remain on
  `register_external_func`; RuleSpec/MergeFn shapes and lowering remain
  unchanged.
- DuckDB overrides registration with a fail-closed callback slot plus
  `ExternalFunctionId -> NativePrimitive` map. Distinct context tokens may map
  to the same operation. `free_external_func` removes native and fresh-token
  provenance before freeing/reuse. No native executor invokes the placeholder.
- Authenticate every current hard-coded native primitive path by token/tag and
  exact typed signature/topology: marker rekey and path-compression `ValueNeq`;
  path compression, standard rebuild, native ordered-union input, and scalar
  ordered-union min/max/payload selection. Primitive names become diagnostics
  only. Existing get-fresh authentication continues through the live fresh
  token set; remove any `get-fresh!` string requirement while retaining exact
  signature/topology and required token relationships.
- Repair scalar tri-state ownership by returning `None` before action
  inspection for a non-subsume-capable body table. Add the self-displacing UF
  fallthrough/unchanged-diagnostic/next-RuleId-zero witness.
- Add blocking provenance canaries: genuine token with renamed diagnostic;
  expected name with ordinary/hostile token; swapped genuine tags;
  freed-token numeric reuse; distinct genuine context tokens; tie/wrong-arity
  default semantics; malformed signature/topology with genuine token; and
  native input/rule paths using the same registry with placeholders uninvoked.
  Add a table-driven scaffolding-alias mutation canary. The successful two-
  scalar schedule and subsumed-Live zero-match canaries are desirable within
  the same test module but remain coverage additions, not excuses to expand
  production behavior.

The expanded owned write set is limited to this ledger; the existing six
scalar files; `egglog/egglog-backend-trait/src/lib.rs` (and
`backend_impl.rs` only if the default test requires it); `egglog/src/lib.rs`,
`egglog/src/typechecking.rs`, and the existing proof helper only if needed;
plus DuckDB `path_compress.rs`, `marker_rekey.rs`, their focused test modules,
`rebuild_tests.rs`, and `input_tests.rs`. A single new focused frontend/backend
trait test file is allowed if inline coverage is materially worse. No manifest,
lockfile, shared RuleSpec/MergeFn shape, Reference/DD semantic implementation,
proof encoding/storage, fixture/snapshot, benchmark, rpath/loader, Appender,
Arrow, UDF, unsafe/FFI/private API, host row/effect/merge/callback, or
performance edit is authorized.

The writer starts from unchanged HEAD
`ee71aa30d984a248c12bb2f34a01e450972cb59a` and frozen rejected owned hash
`002a991b65b41bffb367bd19d8de6326aac65f0cb31e9f2f6dcc9dc92ac80a05`.
It must first prove the default canonical callback and DuckDB tag lifecycle,
then repair all name-authenticated native sites, then the UF selector. Run only
focused/shared/DuckDB/feature gates under independent 110-second watchdogs;
do not run public workloads, `make proof-tests`, commit, or push. Freeze one new
complete patch hash. If the default method cannot remain object-safe/source-
compatible, tags cannot reach every current native validator without changing
RuleSpec/MergeFn, or any path still needs names/callback execution for
correctness, stop the checkpoint. Do not attempt the larger first-class-IR
fallback in this cycle.

## Next action

The sole writer completed and froze the consolidated repair at unchanged HEAD
`ee71aa30d984a248c12bb2f34a01e450972cb59a`. The coordinator independently
reproduced the expanded owned patch SHA-256 as
`46934c83a6d63e5989f9f10a7612404b02501f0d62e9474039d0e6734d8c92a6`,
using the tracked binary diff over the shared trait/frontend and complete
DuckDB crate plus no-index binary diffs for `action_rule.rs` and
`action_rule_tests.rs`. Status is exactly this ledger, 13 authorized tracked
source/test files, and the two authorized untracked action files.

The artifact adds the object-safe canonical `NativePrimitive` registration,
frontend context-token registration, DuckDB token/tag lifecycle, tag-based
authentication at every current native SQL path, fresh-token lifecycle checks,
the non-subsumable UF fallthrough repair, and provenance/topology/lifecycle/
tie/arity/freed-ID/16-alias canaries. The writer reports that no semantic
primitive-name admission check remains.

Writer-reported bounded evidence on the frozen hash:

- workspace tests excluding DuckDB passed;
- DuckDB library 106/106 passed;
- feature CLI 4/4 passed;
- DD timing test 1/1 passed;
- all four `make rust-clippy` constituent stages passed;
- formatting and tracked/untracked whitespace checks passed.

The aggregate `make rust-test` was censored by its 110-second watchdog. The
writer then ran each constituent command independently under its own watchdog
and reports every constituent passed. The aggregate timeout is retained as
censored evidence, not converted into a pass. Public workloads and
`make proof-tests` have not run on this repaired hash.

### Re-review roster

| Agent | Circle/domain | Aim | Authority | Expected output | Stop |
| --- | --- | --- | --- | --- | --- |
| shared-SPI reviewer | public trait, default callbacks, frontend context registration, Reference/DD compatibility | Verify enum semantics, object/source compatibility, unforgeable registration, context/lifecycle behavior, and unchanged public IR | Read-only frozen hash; no edits/builds/tests/workloads/contact | Pass/fail with exact smallest public-SPI witness | Stop after every shared invariant is traced or one blocker is proven |
| admission/semantic reviewer | all native compilers plus scalar executor | Verify all five tag seams, fresh-token name independence/lifecycle, UF fallthrough, 50-to-34/scalar semantics, rollback/allocation, and canary discrimination | Read-only frozen hash; no edits/builds/tests/workloads/contact | Pass/fail with exact code/test evidence | Stop after all repaired blockers and locked semantics are decided |
| safe-SQL/test reviewer | forbidden-boundary and evidence quality | Prove no semantic name authority, host rows/effects/merge/callback, unsafe/private/FFI/UDF/Arrow/Appender/file SQL/proof metadata/fallback; assess gate sufficiency | Read-only frozen hash; no edits/builds/tests/workloads/contact | Pass/fail, residual gaps, gate recommendation | Stop after shortcut audit and sufficiency decision |

### Re-review decision

All three independent read-only reviews passed against source hash
`46934c83a6d63e5989f9f10a7612404b02501f0d62e9474039d0e6734d8c92a6`
at unchanged HEAD `ee71aa30d984a248c12bb2f34a01e450972cb59a` and unchanged source status:

- The shared-SPI review found the five `NativePrimitive` semantics exact,
  `register_native_primitive` object-safe and source-compatible, frontend
  context registration correct, Reference/DD behavior unchanged, and freed
  token provenance removed before numeric ID reuse. Its only nonblocking
  coverage note is the absence of a dedicated recording-backend count of the
  four frontend context registrations; the direct loop and distinct-context
  acceptance canary cover the contract structurally.
- The admission/semantic review found the non-subsume-capable UF fallthrough
  repaired before action inspection; all marker/path/rebuild/input/scalar
  native seams authenticate tag, signature, and topology; fresh names are
  diagnostic only; all 16 raw scaffolding aliases are discriminated; and the
  exact 50-to-34 scalar normalization, prewave, action-major allocation,
  ordered effects, rollback, generation, and publication semantics remain
  intact.
- The safe-SQL review found no semantic name authority, host row/effect/merge
  execution, callback invocation, unsafe/private/FFI/UDF/Arrow/Appender/file
  SQL, proof-aware storage, or fallback. User values use the central typed SQL
  codec, durable function rows retain only `__generation` and `__subsumed`,
  and scalar execution remains one transaction with post-commit publication.

The two anticipated nonblocking scalar coverage additions remain: no successful
two-scalar-plan schedule and no scalar-specific subsumed-Live zero-match
canary. No reviewer found a production defect or authorized another edit.

The coordinator must now independently reproduce focused/shared/DuckDB/CLI/
Clippy/format gates, one fresh post-repair public probe per workload, and
`make proof-tests`, each independently capped at 110 seconds. Preserve the
aggregate `make rust-test` timeout as censored evidence. Any new correctness or
admission blocker stops this checkpoint because the repair budget is exhausted.
If all blocking gates pass, record exact evidence and make one local commit.
Do not push or tune performance.

### Coordinator acceptance evidence

The coordinator reproduced every blocking gate independently under an external
110-second watchdog on unchanged source hash
`46934c83a6d63e5989f9f10a7612404b02501f0d62e9474039d0e6734d8c92a6`:

- canonical `NativePrimitive` default/object-safety canary: 1/1 in 0.49s;
- scalar action module: 21/21 in 0.97s;
- complete DuckDB library: 106/106 in 0.76s;
- workspace excluding DuckDB: passed in 53.90s, including 792 core file
  tests and all workspace doctests;
- DuckDB feature CLI: 4/4 in 0.43s;
- DD timing-summary constituent: 1/1 in 0.72s;
- all four `make rust-clippy` constituents: passed independently;
- DuckDB feature binary build: passed; the final probe binary was rebuilt
  after the workspace tests so its feature provenance could not be overwritten;
- `cargo fmt --all -- --check`, tracked `git diff --check`, and explicit
  no-index whitespace checks for both untracked action files: passed;
- `make proof-tests`: 204 core plus 8 experimental in 53.74s.

Two attempted commands were explicitly rejected as evidence rather than
laundered into passes. The first native-default invocation used `--exact` with
an incomplete module path and selected zero tests; the corrected filter then
ran 1/1. The first Math probe found that a later workspace build had replaced
the feature binary and exited before backend construction; the feature binary
was rebuilt and only the post-rebuild probe is accepted.

Fresh public probes, each run once against that final feature binary, produced:

| Workload | Exit | Wall | Max RSS | Accepted frontier |
| --- | ---: | ---: | ---: | --- |
| Math | 1 | 0.48s | 37,568,512 B | commutativity admitted; stops at the later associativity rewrite |
| Luminal | 1 | 0.07s | 59,949,056 B | add/mul commutativity admitted; stops at the later constant-fold primitive body |
| Eggcc | 1 | 2.42s | 73,515,008 B | unchanged empty-body `eval_actions` boundary |
| Pointer | 1 | 2.19s | 84,312,064 B | all inputs admitted; unchanged first allocation-rule boundary |
| Hardboiled | 1 | 0.04s | 44,597,248 B | unchanged `All`/container-rebuild boundary |

All five are expected fail-closed frontier exits, not completed benchmarks.
There were no timeouts, loader failures, earlier diagnostics, performance
retries, or public cache/report writes. Math and Luminal demonstrate the
checkpoint's intended new scalar coverage; the other three preserve their
prior boundaries.

The final source hash remained exactly
`46934c83a6d63e5989f9f10a7612404b02501f0d62e9474039d0e6734d8c92a6`.
Status remained exactly this ledger, the 13 reviewed tracked source/test files,
and the two reviewed untracked action files. The scalar/native-primitive
checkpoint is accepted for one local commit. Do not push.

## Post-scalar frontier census

The accepted checkpoint was committed locally as
`8f0520b` (`feat: execute authenticated DuckDB scalar actions`). The source
worktree was clean immediately after the commit. No push occurred.

Fresh accepted public frontiers are Math associativity, Luminal scalar
primitive bodies, Eggcc atomless `eval_actions`, Pointer ordinary relation
insertion, and Hardboiled `ReadMode::All`/container rebuild. Performance remains
descriptive; this is a semantic-coverage decision.

### Census roster

| Agent | Circle/domain | Aim | Authority | Expected output | Stop |
| --- | --- | --- | --- | --- | --- |
| Math scout | proof-instrumented associativity | Recover exact lowered topology and smallest native extension | Read-only HEAD `8f0520b`; no edits/builds/workloads/contact | Shape, gap, tests, next frontier, stop condition | Stop after exact ownership decision or one prerequisite blocker |
| Luminal scout | table plus pure scalar primitive bodies | Decide whether authenticated SQL scalar evaluation is a bounded next slice | Read-only HEAD `8f0520b`; no edits/builds/workloads/contact | Primitive surface, public-provenance requirement, tests, coverage | Stop if callbacks/UDFs/host rows or an unbounded primitive compiler are required |
| Pointer scout | ordinary relation insert actions | Recover proof-lowered insert topology and projected workload gain | Read-only HEAD `8f0520b`; no edits/builds/workloads/contact | Shape, reusable executor path, next boundaries, tests | Stop if the first rule requires unsupported merge/container/global behavior |
| Eggcc scout | atomless/global action semantics | Determine whether `eval_actions` is a bounded native rule or deferred surface | Read-only HEAD `8f0520b`; no edits/builds/workloads/contact | Exact semantics, UnstableFn/container dependencies, next boundary | Stop if the rule dynamically reaches deferred UnstableFn or host-only state |
| Coordinator | Hardboiled plus cross-workload decision | Analyze `All`/container rebuild and select one evidence-backed next slice | Read-only analysis until a new contract is frozen | Ranked scoreboard, accepted no-go facts, one bounded writer contract or early exit | Stop rather than authorize overlapping premises or a slice without a correctness oracle |

No implementation writer is authorized during this census. Active risks are
mistaking the first diagnostic for the true prerequisite, adding unauthenticated
primitive semantics, and implementing a one-workload special case instead of a
closed typed IR family. The progress signal is an exact lowered shape plus a
bounded native compiler/executor and differential oracle; source-line count or
registration count is not progress by itself.

### Design-audit roster

The coordinator reused three completed read-only circles because the agent
thread limit prevented new spawns. Reuse does not expand their authority.

| Agent | Circle/domain | Aim | Authority | Expected output | Stop |
| --- | --- | --- | --- | --- | --- |
| semantic auditor | Reference action semantics and observability | Recover exact 0..N-body/action/lookup/fresh/effect/merge ordering and the smallest sufficient typed plan IR | Read-only HEAD `8f0520b`; no edits/builds/workloads/contact | Invariant table, code evidence, plan fields, PASS/STOP | Stop after every listed invariant is decided or one no-host blocker is proven |
| SQL architecture auditor | generalized action staging | Compare per-rule typed stages with normalized shared effect staging, including multiple lookups and ordered-union graphs | Read-only HEAD `8f0520b`; no edits/builds/workloads/contact | Two-design comparison, recommendation, code seams, bounded migration and stop rule | Stop after both architectures are evaluated or one blocker is proven |
| admission/test auditor | ownership and differential gates | Define fail-closed compiler precedence plus minimal blocking conformance matrix for Math, Pointer, and Eggcc | Read-only HEAD `8f0520b`; no edits/builds/workloads/contact | Admission predicate, blocking/nonblocking gates, PASS/STOP | Stop after ownership and every requested oracle are decided |

### Coordinator Hardboiled finding

The first Hardboiled diagnostic is not an isolated `ReadMode::All` gap. The
exact desugared `@rebuild_rule64` reads `__CallView` in All mode, then calls
`__container_rebuild1` before `!=` and a proof-instrumented multi-effect head.
Its source constructor contains core `Vec Expr`. The DuckDB backend still
advertises no container support and owns none of the container registry,
counter, merge, or rebuild callbacks. Allowing All alone would only move the
diagnostic to the native-container boundary, so Hardboiled is not a candidate
for this scalar-action slice. Its prerequisite is a separately reviewed typed
container design.

### Completed scout evidence

- Math associativity is two chained Live `AddView` body atoms, 89 raw backend
  actions collapsed to 60 semantic actions, 25 authenticated fresh calls, one
  Fail/Old table lookup, 29 Sets, one set-if-empty call, and one view-column
  read. It is scalar-only but requires authenticated FD-view operations and a
  multi-body match relation. Mul associativity has the same name-independent
  topology. A Math-only 89-position recognizer is rejected as churn: Pointer,
  Eggcc, and Luminal need the same typed action vocabulary with different
  cardinalities.
- Luminal's first constant fold is three Live table atoms plus a checked i64
  addition body primitive and 151 raw head actions. The immediately following
  rules use checked subtraction, multiplication, remainder, division, signed
  min/max, bit-and, and comparisons in body or action positions. A one-op or
  fixed-151-position patch is rejected. The durable direction is a separately
  authenticated closed scalar-expression IR layered onto the general action
  trace; arbitrary Rust primitive callbacks and UDFs remain out of scope.
- Eggcc's first `eval_actions` command is a transient non-seminaive singleton
  match with 69 raw actions: 19 fresh calls, two set-if-empty calls, two view
  reads, 23 aliases, and 23 Sets. It dynamically reaches no container or
  UnstableFn surface. The 24 isomorphic seeds should share one body-empty
  scalar compiler. Registration of the FD-view operations precedes table
  creation, so DuckDB must retain their public-SPI descriptors and resolve the
  target lazily at rule admission. Persistent seminaive atomless rules fire
  once even if unchanged; the existing zero-to-nonzero per-rule watermark can
  encode that lifecycle without durable proof metadata.
- Pointer's first rule is one Live body atom and 41 raw actions collapsed to 28
  semantic actions: 11 fresh calls, one set-if-empty, one view read, and 13
  Sets. Its second rule is the same vocabulary with nested constructors and
  113 raw/76 semantic actions. The first source union is a larger but still
  typed target-directed View Set; it is a valid later boundary rather than a
  reason to add a relation-insert-only recognizer.

The cross-workload accepted premise is therefore a closed, typed, general
scalar action plan with 0..N table bodies, 0..N prewave table/FD-view reads,
authenticated fresh calls, ordered typed effects, and multiple independent
ordered-union graphs. It must replace or subsume the committed exact scalar
plan before mixed rulesets are accepted. Primitive expressions and containers
remain separate layers. This premise is not yet a writer contract; the three
independent design audits remain outstanding.

## General scalar-action checkpoint

All three independent read-only design audits passed at unchanged source HEAD
`8f0520b`. They found no need for a shared public-IR change, host execution, a
DuckDB extension API, or a second merge strategy. Architecture A—per-rule wide
typed SQL stages plus one global dependency-respecting ordered-union
fixed-point—is the accepted first design. The normalized shared-lane design is
the sole fallback architecture and is not authorized unless A fails a reduced
differential witness.

### Locked semantics and scope

- Body matching supports zero or more scalar-typed `ReadMode::Live` table
  atoms. Repeated variables and literals remain typed equality predicates. A
  seminaive N-body match fires exactly once iff at least one source row is at
  or beyond that rule's watermark. A non-seminaive empty body yields one lane
  on every invocation; a seminaive empty body yields one lane only at its zero
  watermark. Primitive, All, and Subsumed body atoms remain unowned.
- `LetAtomTerm` is compile-time SSA only. Typed literals and aliases fold into
  `ValueRef`; they retain raw source ordinals for diagnostics but consume no
  executable event or fresh ordinal. Runtime ops retain source order and may
  reference any prior binding.
- Table action calls initially admit exactly one-output `DefaultVal::Fail`
  lookups. They read the durable prewave, include a subsumed owner, require
  exactly one owner per lane, and publish no row to Rust. Const/Fresh-default
  prediction maps are deferred because their batching scope is a separate
  semantic design.
- DuckDB overrides the existing public `register_set_if_empty` and
  `register_view_column_read` methods. It creates fail-closed tokens and stores
  backend-private descriptors keyed by token. Registration precedes table
  creation, so admission resolves the descriptor's exact view name lazily,
  requires one catalog match plus exact arity/schema/output type, and never
  treats the diagnostic call name as authority or interpolates the view name
  into SQL. Freeing a token removes its descriptor before numeric ID reuse.
- A set-if-empty miss returns that lane's supplied first default and stages the
  complete supplied row. It does not become visible to later ordinary or
  view-column reads in the wave. A following view read of the same missing key
  returns its own fallback. Existing—including subsumed—owners are returned.
- Fresh calls require a live authenticated token, String literal label, and Id
  result. The label is opaque. All explicit successful head IDs are reserved
  deterministically by scheduled occurrence, executable fresh site, and
  canonical match before any collision-generated ID.
- Table Sets admit only catalog-validated AssertEq, KeepOld, or the already
  authenticated complete ordered-union graph. Set-if-empty candidates use the
  same typed effect path. All effects are materialized before mutation;
  AssertEq and KeepOld effects apply in canonical scheduled/action/match order;
  every ordered-union candidate is enqueued before one global fixed-point
  drain.
- Multiple graphs are ordered by the first scheduled source effect plus their
  validated generated-write dependency, never by `FunctionId`. Independent
  graph/collision order is backend-canonicalizable, but generated writes may
  not cross a dependency edge. Function IDs only locate typed tables/queues.
- One transaction owns matches, lookup/FD stages, head/effect stages, explicit
  and collision counters, direct effects, queue drain, generation, and scratch
  cleanup. Rust may observe scalar counts, booleans, ordinals, and scheduler
  selectors only. Failure rolls back all authoritative state and preserves
  rule watermarks, run identity, telemetry, and the prior accepted SQL trace.
- Duplicate seminaive RuleId occurrences in one schedule must not refire the
  same prewave delta. Either assign occurrence-relative effective watermarks as
  the Reference does or reject duplicate schedule entries before mutation;
  silent double execution is forbidden. Normal public schedules are unique.
- General `Change`, `Union`, `Panic`, native scalar expressions, arbitrary
  callbacks, deferred merges, containers, and dynamic UnstableFn remain
  fail-closed. Opaque schema-only Id values may be copied without authorizing
  construction or application.

### Compiler ownership and migration

Admission order is standard rebuild tri-state, marker rekey tri-state, path
compression tri-state, general scalar action tri-state, then Direct. Replace
path compression's current 3-body/4-action catch-all with a structural
tri-state owner so unrelated valid action rules fall through. General scalar
ownership requires only supported Live table bodies (or none), a nonempty
actionful head, and the closed action vocabulary above. Once owned, every
token, type, SSA edge, target, descriptor, merge graph, and action fails closed
before RuleId allocation.

The committed exact 50-raw-action compiler and its 21 differential tests are
the migration oracle, not a second final executor. Architecture A must provide
one production scalar-action executor and one ordered-union kernel. It may
temporarily dual-compile the exact family while developing, but the frozen
candidate must route the accepted exact family through the generalized runtime
or prove that both plan representations share that single runtime with no
homogeneous-plan scheduling restriction. Do not delete the positive exact
implementation until its full transcript suite passes through the replacement.

### Writer contract

One writer owns this checkpoint from source HEAD `8f0520b`; the coordinator
alone owns this ledger. The authorized production write set is limited to
DuckDB `lib.rs`, `rule_sql.rs`, `path_compress.rs`, `action_rule.rs`,
`storage.rs`, and `rebuild.rs`. Existing focused DuckDB test modules may be
edited and one new general-action test module may be added. No manifest,
lockfile, shared backend trait/frontend, Reference/DD implementation,
fixture/snapshot, proof storage, benchmark, loader/rpath, input codec,
container, Appender, Arrow, UDF, unsafe/private/FFI, host row/effect/merge, or
performance edit is authorized.

Blocking focused gates are:

1. Lazy FD descriptor registration, rename/spoof/free/reuse/ambiguity/schema
   canaries with no RuleId consumption on rejection.
2. Existing rebuild/marker/path/Direct precedence plus an unrelated
   3-body/4-action general rule.
3. Differential 0/1/2/N-body, atomless lifecycle, zero/one/chained reads,
   subsumed lookup, stable-prewave fallback, action-major fresh allocation,
   AssertEq/KeepOld, two independent ordered-union graphs, and deterministic
   dependency-respecting collision topology.
4. Late conflict and explicit/collision exhaustion rollback from nonzero state,
   exact retry, scratch cleanup, hostile typed literals, and no forbidden SQL
   boundary.
5. Every existing scalar-action differential test through the common runtime.
6. Static source-shape admission for Math associativity, Pointer's first rule,
   and Eggcc's first atomless fact while Luminal primitive-body and Hardboiled
   All/container shapes remain unowned.

The writer may run only focused compile/tests/format/Clippy checks, each under
its own 110-second watchdog. It must not run public workloads, the full
workspace/proof suite, commit, push, or tune performance. Freeze one complete
owned-patch hash for three independent read-only reviews.

Stop this checkpoint immediately if A requires host rows/effects/merges,
callback or UDF execution, primitive-name authority, proof-aware storage,
type-erased SQL payloads, a public API change, or dynamic containers/UnstableFn.
Also stop after one semantics-driven repair fails the same reduced witness; do
not drift into micro-variants or Architecture B without a new coordinator
decision. Runtime and statement counts are descriptive, not acceptance gates.

### Frozen writer candidate

The sole writer completed Architecture A at unchanged source HEAD `8f0520b`.
The coordinator independently reproduced the complete owned-patch SHA-256 as
`c8dd8f0e62a968872ec976bfdbe1534c6bfca0196ba709c0dacfb233719c80bb`.
The digest is the concatenation of binary tracked diffs for the six authorized
production files and two authorized existing test files, followed by the
binary no-index diff for new `general_action_tests.rs`; it excludes this
coordinator-owned ledger.

The candidate adds one generalized typed scalar-action compiler/runtime, lazy
authenticated FD descriptors, atomless and N-body matching, Fail lookups,
fresh/FD stages, typed direct and ordered-union effects, source-derived graph
ordering, schedule-time token reauthentication, duplicate-RuleId rejection,
and structural path ownership. The exact 50-action compiler remains as an
admission oracle, while its accepted rules execute through the generalized
transaction. No commit or push occurred.

Writer-reported bounded evidence on the frozen hash:

- Rust test compile passed after one type-inference repair;
- all 110 DuckDB package tests passed;
- formatting and Clippy with warnings denied passed;
- a plain link attempt failed because `-lduckdb` was unavailable, not because
  of Rust/semantic errors;
- two bundled dependency builds were timeout-censored at 110 seconds and are
  not passes; the accepted tests used the existing pinned DuckDB 1.5.4 dylib
  under `target/duckdb-download` with no manifest or loader edit.

The writer did not run public workloads, the full workspace/proof suite,
commit, push, or tune performance. Source status is exactly the authorized
tracked files, one authorized untracked test module, and this ledger.

### Candidate review roster

| Agent | Circle/domain | Aim | Authority | Expected output | Stop |
| --- | --- | --- | --- | --- | --- |
| admission reviewer | compiler ownership and token authority | Verify structural precedence, SSA/type validation, FD lazy resolution/lifecycle, RuleId atomicity, and exact-oracle migration | Read-only frozen hash; no edits/builds/tests/workloads/contact | PASS/REVISE with smallest admission witness | Stop after every ownership/authority seam is traced or one blocker is proven |
| semantic reviewer | generalized transaction | Verify stable prewave, atomless/N-body seminaive behavior, lookup/FD visibility, fresh/effect ordering, multi-graph dependencies, rollback, watermarks, and duplicate schedules | Read-only frozen hash; no edits/builds/tests/workloads/contact | PASS/REVISE with exact semantic witness | Stop after every locked invariant is decided or one blocker is proven |
| safe-SQL/test reviewer | forbidden boundary and evidence quality | Prove typed public SQL only, no host/name/proof fallback, scope fidelity, test discrimination, and static frontier claims | Read-only frozen hash; no edits/builds/tests/workloads/contact | PASS/REVISE, residual gaps, coordinator gate recommendation | Stop after full shortcut/scope/test audit |

No source edit is authorized during review. If all reviews pass, the
coordinator independently reruns focused/package/feature/format/Clippy gates,
static source-shape admission, one fresh capped public probe per workload, and
`make proof-tests`. Any live correctness blocker returns to one bounded repair;
performance measurements cannot trigger a repair in this checkpoint.

### Frozen-candidate review decision and bounded repair

All three independent reviewers reproduced source HEAD `8f0520b` and owned
patch SHA-256
`c8dd8f0e62a968872ec976bfdbe1534c6bfca0196ba709c0dacfb233719c80bb`.
The candidate is **REVISE**, not rejected: Architecture A's transaction,
ordering, authority, public-SQL boundary, and exact-family migration passed
static inspection, but three local correctness defects block coordinator
gates.

1. The count-only exact-transcript heuristic returns `None` when its stricter
   exact owner declines a rule, shadowing an otherwise valid generalized
   rule. Exact-oracle validation may run only when both predicates accept;
   owner `None` must continue through general admission.
2. A supported one-Live-body/one-Set rule targeting an authenticated deferred
   ordered-union graph falls through to Direct, which cannot execute it. The
   general compiler must own this shape. Direct may retain only shapes it can
   actually execute; diagnostic or fixture names cannot make a negative test
   pass accidentally.
3. A missing `DefaultVal::Fail` lookup currently creates a scratch slot whose
   semantic value is SQL `NULL` and rejects it afterward. The executor must
   check per-lane owner cardinality against the input stage before creating the
   output slot, then materialize the value through an exactly-one inner lookup.
   Neither durable nor scratch value columns may use SQL `NULL` as absence.

One semantics-driven Architecture-A repair is authorized. It is limited to
the existing writer's production/test write set and may additionally replace
the misleading deferred-view negative canary with a positive Reference versus
DuckDB differential. It must add high-discrimination coverage for:

- the exact-heuristic-shadow witness;
- one actionful unrelated three-body/four-action generalized rule;
- a lookup keyed by an earlier lookup result;
- two independent ordered-union graphs in one scalar schedule;
- the repaired single-Set deferred ordered-union shape; and
- missing/duplicate Fail-owner preflight proving no value slot is created
  before rejection.

Source-shape canaries for Math associativity, Pointer's first proof-mode rule,
Eggcc's first atomless fact, and fail-closed Luminal/Hardboiled frontiers remain
coordinator gates after the repair; they are not permission to edit fixtures
or widen production scope. The writer may run only separately capped focused
compile/tests/format/Clippy checks and must freeze a new owned-patch digest.
No public workload, proof suite, commit, push, benchmark, performance tuning,
host fallback, callback/UDF, container, frontend/shared-trait, manifest,
loader, or proof-storage edit is authorized.

If this one repair does not make the reduced witnesses pass, stop the
checkpoint and return to proposal formation. Do not attempt a second
Architecture-A micro-variant or silently fall back to Architecture B.

### Frozen repaired candidate

The sole repair writer completed the authorized repair at unchanged source
HEAD `8f0520b`. The coordinator independently reproduced the complete DuckDB
source patch SHA-256 as
`27c185023fdfe3fd3ffc0699d4f948f275741120981049af619ef3cfc3f11c71`
using the binary tracked diff for `egglog-experimental/duckdb/src` followed by
the binary no-index diff for new `general_action_tests.rs`; this ledger is
excluded.

The repaired candidate makes exact-oracle decline continue to general
admission, routes authenticated deferred single-Set rules through
`ScalarAction`, and preflights every Fail-lookup input lane before creating an
exact-owner value slot. It adds the six required discriminating witnesses,
including positive Reference differentials for the single deferred Set and
two independently ordered union graphs. The writer did not run public
workloads, proofs, the full workspace, commit, push, or widen production
scope.

Writer-reported capped gates on this exact digest:

- DuckDB library: 116 passed, 0 failed;
- focused action-rule module: 23 passed, 0 failed;
- generalized action module: 8 passed, 0 failed;
- formatting, Clippy with warnings denied, and `git diff --check`: passed.

These are writer evidence, not coordinator evidence. The three review circles
now re-review only the repaired seams plus their prior residual test concerns.
They must reproduce the new digest, remain read-only, and return PASS/REVISE
with a smallest witness. No coordinator compile, public workload, proof gate,
or commit occurs until all three verdicts are recorded.

A separate read-only runner audit established that the feature CLI accepts
`--backend duckdb --proofs`, but current `bench.py` still exposes only `main`
and `dd`. Current-checkpoint public probes therefore use the feature CLI with
fresh `/tmp` reports; adding DuckDB to the benchmark runner remains an explicit
later integration deliverable, not something to smuggle into this repair.

### Repaired-candidate review outcome

All three read-only circles independently reproduced HEAD `8f0520b` and source
digest `27c185023fdfe3fd3ffc0699d4f948f275741120981049af619ef3cfc3f11c71`.
All three verdicts are **PASS**.

- Admission/authority: exact-oracle decline falls through; structural
  precedence remains intact; only deferred single Sets move ahead of Direct;
  SSA, token, descriptor, RuleId, and exact-migration boundaries pass.
- Transaction/semantics: single deferred Sets still receive complete graph
  validation; prewave visibility, action-major IDs, source/dependency graph
  order, one fixed-point drain, rollback/retry, and scalar-only observations
  remain correct.
- Safe SQL/tests: Fail preflight creates no value slot and the succeeding inner
  join reads a durable non-null value; no forbidden interface or scope change
  appeared; all six repair witnesses discriminate the old failure modes.

One nonblocking suggestion remains: add a compiled-rule fresh-token revocation
canary in a later focused maintenance pass. FD revocation is directly tested,
fresh reuse is tested at admission, and the shared schedule-time authorization
loop statically covers both, so this does not block coordinator gates.

The repaired source is now accepted for independent coordinator validation.
Any coordinator correctness failure returns to proposal formation under the
existing one-repair stop rule; timeout or performance alone remains censored
data rather than a correctness failure.

### General scalar-action checkpoint accepted

Coordinator validation passed on unchanged source digest
`27c185023fdfe3fd3ffc0699d4f948f275741120981049af619ef3cfc3f11c71`:

- tracked and new-file whitespace checks passed;
- `cargo test -p egglog-experimental-duckdb --no-default-features --lib`:
  116 passed, 0 failed in 0.63 seconds;
- `cargo fmt --all -- --check`: passed;
- DuckDB package Clippy over all targets with warnings denied: passed;
- feature-selected `egglog-experimental` binary tests: 4 passed, 0 failed;
- `make proof-tests`: 204 core proof tests and 8 experimental proof tests
  passed within the 110-second watchdog;
- the final `bin,duckdb-backend` CLI built and its loader/help preflight passed
  in 0.51 seconds at 13,221,888 bytes maximum RSS.

One fresh feature-CLI DuckDB/proofs probe was then run for each frozen
non-Herbie workload with a separate external 110-second watchdog and a unique
`/tmp` report path. No probe timed out or crashed, every unsupported surface
failed closed, and no report was published because none completed:

| workload | exit / wall / max RSS | first unsupported frontier |
| --- | --- | --- |
| Math | 1 / 0.08 s / 38,256,640 B | native scalar expression at action 22 of `(rewrite (Add a (Const 0)) a)` |
| Pointer | 1 / 5.29 s / 353,353,728 B | final `check_facts` rule requests `All` |
| Eggcc | 1 / 2.87 s / 100,974,592 B | generated `@rebuild_rule166` requests `All` |
| Hardboiled | 1 / 0.04 s / 44,826,624 B | generated `@rebuild_rule64` requests `All` |
| Luminal | 1 / 0.09 s / 60,506,112 B | checked i64-add primitive body atom |

This is positive frontier movement: Math now clears the associativity family;
Pointer clears its proof-mode analysis rules and native input before the final
check; Eggcc clears its atomless fact and many later rules. The checkpoint is
accepted even though no full workload completes, because performance and
coverage gaps are reported rather than laundered into correctness results.

Evidence changes the next implementation order. Native `All` table-body
matching is now the common first blocker for three workloads, so it precedes
the closed native scalar-expression layer for Math/Luminal; typed containers
remain after those unless a fresh census shows otherwise. `bench.py` DuckDB
endpoint support remains required before final benchmark collection.

## Generic `ReadMode::All` proposal rejected as a standalone checkpoint

Fresh static audits at clean committed HEAD `a2163b3` corrected the provisional
ordering above. `All` matching is a small, reusable semantic prerequisite, but
an `All`-only patch advances none of Pointer, Eggcc, or Hardboiled past its
current `RuleSpec`. Under the goal's early-exit rule, no writer is authorized
for this isolated slice.

The verified generic semantics are retained for a later combined capability:

- `Live` adds `alias.__subsumed = FALSE`, `All` adds no visibility predicate,
  and `Subsumed` would add `alias.__subsumed = TRUE` when separately scoped.
- Every table atom contributes its generation column. One seminaive OR across
  those columns is extensionally equivalent to Reference's disjoint focus
  variants and fires a joined tuple once when more than one input is fresh.
- A live-to-subsumed transition must retimestamp the row and refire `All`
  exactly once; repeated Subsume is a no-op. Bodies and action reads remain a
  stable prewave, and failure rolls back rows, counters, watermarks, telemetry,
  and scratch state.
- A non-seminaive unconstrained all-`All` body must render `WHERE TRUE` (or omit
  the clause), not an empty `WHERE`.

The reached rules require deeper capabilities in the same admission unit:

| workload | exact reached shape after the visibility check | reason an `All`-only patch does not move it |
| --- | --- | --- |
| Pointer | two scalar `All` FD-view atoms and a zero-argument `check_facts_match` Let, with no durable Set | requires a separately authenticated SQL-native existential/result observation; generic host callback execution is forbidden |
| Eggcc | two `All` tables, authenticated `ValueNeq`, fresh/Congr Set, custom-view Set, and Delete | requires a structural custom min/max merge plus primitive body, mixed Set/Delete staging, and one shared rebuilding transaction |
| Hardboiled | one `All` table, typed `Vec<Expr>` rebuild, `ValueNeq`, a Full proof primitive, several Sets, and Delete | requires complete native container registry/rebuild/proof-effect semantics; an opaque Id treatment is unsound |

Storage also rejects a scheduled mixture of scalar-action and existing
rebuilding/direct plan kinds. Executing the existing transactions sequentially
would violate the global stable-prewave and Delete-before-Set contract, so a
later combined implementation must share one transaction rather than weaken
that guard.

Accepted no-go facts:

1. Do not implement generic `All` merely to change the first diagnostic.
2. Do not authenticate Pointer's callback by its name or execute it in Rust.
3. Do not interpret Eggcc's arbitrary `MergeFn::Block` or split a rebuilding
   ruleset across transactions.
4. Do not treat Hardboiled container IDs as scalar payloads.
5. Preserve Standard/Marker/Path ownership precedence and reject every
   malformed or unsupported shape before RuleId allocation.

The next active proposal is the closed authenticated scalar-expression layer:
Math and Luminal each have a reached scalar-only rule that this capability can
actually advance. `All` remains available as part of a later combined Pointer,
Eggcc, or container checkpoint, with the differential canaries above.

### Scalar-expression design roster

| Agent | Circle/domain | Aim | Authority | Expected output | Stop |
| --- | --- | --- | --- | --- | --- |
| Math scalar frontier | proof-instrumented Math union actions | Recover the exact authenticated operation at action 22 and every following scalar-only family through the next non-scalar boundary | Read-only `a2163b3`; no edits/builds/tests/workloads/network/contact | token/signature/context census, source semantics, canaries, benchmark-moving verdict | Stop at exact next non-scalar prerequisite or one forbidden host/container requirement |
| Luminal scalar frontier | checked scalar primitive bodies/actions | Freeze the reached primitive family, undefined/error behavior, and workload order | Read-only `a2163b3`; no edits/builds/tests/workloads/network/contact | typed operation matrix, zero/one-row SQL contract, differentials, stop rule | Stop if the reached slice needs callbacks/UDFs/containers or an unbounded compiler |
| scalar IR architecture | shared authentication and SQL lowering | Select one closed typed representation for body and action expressions and one materially different repair design | Read-only `a2163b3`; no edits/builds/tests/workloads/network/contact | Design A/B, authority/type/failure/rollback contract, write set and gates | Stop once a bounded public-API SQL design passes or one semantic blocker is proved |

No scalar writer is authorized until all three design circles finish and the
coordinator freezes one contract. Performance is descriptive; each later
probe is separately capped at 110 seconds and a timeout is censored data.

## Frozen authenticated scalar-expression contract

All scalar design circles completed against unchanged committed HEAD
`a2163b3`. The source remains clean; this ledger is the only modified file.
The reached workload evidence authorizes one implementation checkpoint.

### Workload-moving scope

Math requires exactly the existing authenticated raw-value operations
`OrderingMax` and `OrderingMin` in action expressions. They are applied only
to `(Id, Id) -> Id`, compare the stored raw `Value` handles, and choose the
right operand on ties. Four variable-RHS rewrites each use the sequence
`max, min, max, min`, for 16 calls total. No later static non-scalar Math
boundary is visible, although a fresh capped run remains the runtime gate.

Luminal requires one closed typed scalar layer. Its frozen reachable surface
is:

- checked i64 `Add`, `Sub`, `Mul`, `Div`, and `Rem`;
- total i64 `BitAnd`, `Min`, and `Max`;
- i64 `Ge` and `Lt` predicates;
- f64 `Gt` and `Lt` predicates with `OrderedFloat` semantics; and
- typed `ValueNeq` over `Id`, `i64`, `f64`, and `String`.

The exact static census contains 172 calls: 152 body calls and 20 action
calls. Body failure removes the lane. Action failure is a hard rule error and
must roll back the transaction; it is never represented by SQL `NULL`.
Source `Subsume` at Luminal line 66 has already become a marker-table `Set` in
the proof-lowered action stream, while the generated cleanup remains an
already-supported Direct Subsume rule. This checkpoint therefore adds neither
Delete nor Subsume to the generalized executor.

### Selected architecture

Introduce a separate, closed `NativeScalarPrimitive` descriptor rather than
adding decoded arithmetic to the raw `NativePrimitive` enum. The backend SPI
gets one object-safe registration method accepting the semantic descriptor
and a canonical boxed `ExternalFunction` fallback. Its default implementation
registers that fallback unchanged, preserving every existing backend. DuckDB
overrides the method, registers a fail-closed callback token, and stores the
exact token-to-descriptor authority. Diagnostic names never authorize
lowering.

The primitive macro/type-registration path must retain and pass its existing
canonical implementation to this registration method. Other backends keep
executing that canonical implementation. DuckDB plans retain every token and
descriptor dependency and reauthenticate them immediately before opening the
execution transaction; freed or reused tokens fail before SQL or observable
state change.

DuckDB uses one closed scalar-expression renderer shared by body predicates,
body bindings, and action slots. Existing raw `OrderingMin`/`OrderingMax` are
adapted into it only for exact `Id` signatures. Typed i64/f64 operations stay
semantically distinct from raw-value ordering. Existing specialized standard,
marker, and path ownership remains ahead of generalized scalar admission.

General scalar admission owns only Live table bodies plus authenticated scalar
primitive atoms and the already-supported Let/alias/Set head family. It does
not absorb `All`, `Subsumed`, Change, Delete, containers, arbitrary merge
blocks, callbacks, or mixed plan-kind schedules. Empty bodies remain allowed.
Malformed signatures, unknown variants, unbound inputs, spoofed tokens, and
unsupported types reject before RuleId allocation.

### Exact SQL semantics

Every expression renders as a non-null value expression plus an explicit
definedness predicate. Body expressions are evaluated in source/dependency
order in the frozen match stage; false definedness prunes that lane. Action
expressions are materialized in action order. Every fallible action slot is
preflighted before fresh-ID reservation or durable effects; any undefined
survivor aborts and rolls back. Primitive Lets consume runtime ordinals but do
not themselves change rows, generations, or insert telemetry.

Checked i64 add/sub/mul compute in `HUGEINT`, test the inclusive i64 bounds,
and only then cast a safe totalized branch to `BIGINT`. Division/remainder are
defined only when the divisor is nonzero and the operands are not
`i64::MIN / -1`; an invalid divisor is replaced with a safe value inside the
arithmetic expression so DuckDB cannot raise before the explicit guard.
Division truncates toward zero and remainder has the dividend's sign.
`BitAnd`, typed min/max, and comparisons use signed `BIGINT` semantics.

F64 equality and ordering must reproduce `OrderedFloat`: all NaNs compare
equal and above ordinary values, and signed zeros compare equal. The two
reached predicates therefore use explicit `isnan` logic. Ordinary DuckDB
comparison alone, `LEAST`, and `GREATEST` are forbidden. Typed `ValueNeq`
must reuse the same equality relation for f64 and ordinary exact equality for
Id, i64, and String.

Raw Id max/min use strict `>`/`<` and the right operand in `ELSE`; they may not
be generalized to decoded base values. No expression may use `TRY`, SQL NULL
as absence, a UDF/callback, host row enumeration, Arrow, Appender, unsafe/FFI,
or a private DuckDB API.

### Transaction, statements, and tests

Freeze all body survivors before RHS work. Preserve the existing one-transaction
action-major staging, dependency-ordered graph application, fixed-point queue
drain, generation publication, telemetry publication, and rollback contract.
Body expressions should be fused into the match CTAS. One CTAS per action
expression and one aggregate preflight per fallible action are acceptable;
statement count is reported, not a hard acceptance ceiling.

Required focused canaries cover:

1. Reference-versus-DuckDB results for every reached typed operation, including
   i64 bounds, negative division/remainder, zero divisors, `MIN / -1`, negative
   bitwise inputs, NaNs, infinities, and signed zeros.
2. Body output bind versus bound-output predicate behavior, chained body and
   action expressions, empty-body actions, and body-lane pruning.
3. Action undefinedness before fresh reservation, full late rollback/retry,
   stable prewave visibility, action-major IDs, generation/watermark/telemetry
   preservation, and unchanged/no-delta reruns.
4. Raw Id min/max strict comparison and right-tie behavior across the exact
   Math `max,min,max,min` shape.
5. Token spoofing, diagnostic-name mismatch, free/reuse after rule creation,
   wrong arity/types/output, unbound inputs, unsupported variants, and RuleId
   preservation on every admission failure.
6. Structural SQL assertions excluding diagnostic names, UDFs, `NULL`, `TRY`,
   `LEAST`, and `GREATEST` from the relevant renderings.
7. Static proof-lowering evidence that Luminal's source Subsume remains one
   marker Set plus the existing Direct cleanup rule.

### Writer contract and stop rule

One implementation writer owns only the backend trait/type-registration
plumbing, i64/f64 primitive registrations, DuckDB scalar IR/admission/execution,
and focused tests. Expected files are:

- `egglog/egglog-backend-trait/src/lib.rs`;
- `egglog/src/typechecking.rs`;
- `egglog/src/sort/add_primitive/src/lib.rs`;
- `egglog/src/sort/i64.rs` and `egglog/src/sort/f64.rs`;
- `egglog/src/lib.rs` only if required for the closed registration path;
- `egglog-experimental/duckdb/src/{lib.rs,rule_sql.rs,action_rule.rs,storage.rs}`;
- a new DuckDB-local scalar-expression module; and
- focused trait/scalar/general-action tests.

The writer must not edit this ledger, fixtures, manifests/lockfiles, loaders,
benchmark runner, proof storage, containers, `All`, Change effects, or other
backends beyond the compatible default SPI behavior. It may run only separately
capped focused checks and must freeze a complete source-patch digest. It may
not run public workloads, the proof suite, full workspace, commit, or push.

After the freeze, three independent read-only reviews cover (1) SPI authority
and fallback compatibility, (2) SQL semantic and transaction correctness, and
(3) test discrimination and scope. At most one bounded repair is allowed. If
the design cannot express the exact frozen operations through public SQL, if
another backend cannot retain its current callback behavior, if any reached
operation needs a host callback/UDF/container/private API, or if the focused
witnesses remain incorrect after that repair, stop the checkpoint and return
to proposal formation. Performance or a capped workload timeout alone is
censored evidence, not a correctness failure.

## Frozen authenticated scalar-expression candidate

The sole source writer completed against unchanged committed HEAD
`a2163b33d436876b6dce929bdbe215c7f3b37b88`. The coordinator independently
reproduced the deterministic source-patch SHA-256
`5a159cf28c48ef8c4d717556d9317e82fcb76e6aa872473fbd729277c40734cf`.
That digest contains the tracked binary diff excluding this coordinator-owned
ledger, followed by sorted no-index binary diffs for the two untracked scalar
source/test files. `git diff --check` is clean.

The frozen source write set is:

- `egglog/egglog-backend-trait/src/lib.rs`;
- `egglog/src/{lib.rs,typechecking.rs}` and
  `egglog/src/sort/{add_primitive/src/lib.rs,i64.rs,f64.rs}`;
- `egglog-experimental/duckdb/src/{lib.rs,rule_sql.rs,action_rule.rs}`;
- focused existing tests in
  `egglog-experimental/duckdb/src/{rule_sql_tests.rs,action_rule_tests.rs,
  general_action_tests.rs}`; and
- new `egglog-experimental/duckdb/src/{scalar_expr.rs,
  scalar_expr_tests.rs}`.

No fixture, manifest, lockfile, loader, benchmark runner, proof-storage,
container, Appender, Arrow, file-reader SQL, unsafe/FFI, UDF, callback
execution, commit, or remote state changed.

Writer-owned capped evidence is green:

- scalar integration tests: 9/9 pass, including full reached-operation
  differentials, body binding/pruning, primitive-only and empty bodies,
  action failure rollback/retry, exact Math min/max shape, stable prewave, and
  same-descriptor ABA token reuse;
- generalized-action regressions: 8/8 pass;
- displaced ordered-union merge-token reauthentication canary: pass;
- native-token lifecycle canary: pass;
- backend-trait/core checks and clippy: pass;
- DuckDB crate check and `-D warnings` clippy: pass;
- feature-gated `egglog-experimental` DuckDB CLI check: pass; and
- formatting and source diff checks: pass.

Two live read-only findings were repaired before the freeze: descriptor-kind
diagnostics now precede the epoch ABA guard, and scalar plans retain authority
from both root and displaced ordered-union merges. The no-table match path now
retains scalar projections/definedness, and every generalized scalar plan is
reauthenticated before storage execution.

For this checkpoint, "DuckDB plans retain every token and descriptor
dependency" means every newly generalized `ScalarAction` plan and all of its
raw, typed, fresh, FD, root-merge, and displaced-merge dependencies. Previously
accepted Standard/Marker/Path plan envelopes remain compile-time authenticated;
retrofitting them is a recorded lifecycle-hardening follow-up, not an
authorized expansion of this scalar checkpoint.

The source patch is frozen for the required three independent read-only
reviews. No source writer is active. Coordinator gates and public workload
probes remain pending; no checkpoint is accepted or committed yet.

## Independent scalar review verdicts and sole repair authorization

Three independent read-only reviewers authenticated committed HEAD
`a2163b33d436876b6dce929bdbe215c7f3b37b88`, reproduced frozen source digest
`5a159cf28c48ef8c4d717556d9317e82fcb76e6aa872473fbd729277c40734cf`,
and confirmed the exact authorized dirty set before reviewing. None edited,
built, tested, ran workloads, accessed the network, or contacted another
agent.

- The SQL/transaction reviewer returned **PASS**. Checked i64 and OrderedFloat
  f64 semantics, explicit definedness, body and action staging, preflight,
  fresh-ID order, merge-graph order, rollback/publication, generation, and the
  forbidden SQL/host paths all matched the frozen contract.
- The test/scope reviewer returned **REVISE** for one admission regression:
  generalized scalar binding had made diagnostic `RuleVar.name` semantic for
  an otherwise identical variable ID and `ColumnTy`. This contradicts the
  retained renamed-variable regression and the frozen name-independent
  authority contract. The bounded repair must restore identity to ID plus
  type and add a cross-body/scalar/action rename canary.
- The SPI/lifecycle reviewer returned **REVISE** because the new public
  `NativeScalarPrimitive` enum was exhaustively matchable. Since later scalar
  descriptors are expected, adding a variant would be a downstream source
  break. The bounded repair must add `#[non_exhaustive]` and explicit
  fail-closed wildcard arms in DuckDB production and test matches.

The reviews otherwise passed dispatch precedence, the exact closed operation
surface, canonical fallback compatibility, descriptor authentication,
RuleId preservation, and ScalarAction retention/reauthentication of raw,
typed, fresh, FD, root-merge, and displaced-merge dependencies. Direct
same-kind ABA canaries for fresh and FD tokens and a checked-in Luminal census
remain nonblocking follow-ups; the shared epoch machinery and frozen static
provenance already cover their production mechanisms.

One and only one repair writer is authorized. Its source write set is limited
to the backend-trait scalar enum plus DuckDB scalar binding/rendering and their
focused action/scalar tests. It may not edit this ledger, storage, fixtures,
manifests, loaders, benchmarks, other backends, or committed history. It must
run only separately capped focused gates, freeze a new deterministic source
digest, and stop rather than broaden either repair into an architecture
change. Coordinator gates and public workload probes remain pending.

### Sole repair result

The one authorized repair completed against unchanged committed HEAD
`a2163b33d436876b6dce929bdbe215c7f3b37b88`. The coordinator independently
reproduced the new deterministic source digest
`ccd499f337d833ee5e28ffbb7a2287a494eeeccd384dd4d00d39919aaf2693e0`.
The source dirty set remains exactly the previously frozen set; only this
coordinator ledger is modified outside it.

Variable identity in the generalized scalar compiler is now ID plus
`ColumnTy`; use-site names remain diagnostic only. Same-ID/wrong-type reuse
still fails closed. `NativeScalarPrimitive` is now `#[non_exhaustive]`, and
DuckDB production and test matches contain explicit unsupported future-variant
fallbacks rather than guessing a lowering. One scalar witness deliberately
renames the same logical variable across table binding, scalar body
input/output, and action input.

Repair-writer evidence is green: scalar-expression tests 9/9, action-rule
tests 24/24, the backend-trait canonical-fallback canary, DuckDB and
backend-trait `-D warnings` clippy, formatting, and tracked/untracked diff
checks. No commit, push, ledger edit, workload, proof suite, full package, or
out-of-scope source change was made by the writer. The source is frozen again;
coordinator-owned gates and public probes remain pending.

## Accepted authenticated scalar-expression checkpoint

The two reviewers that raised blockers independently authenticated repaired
source digest
`ccd499f337d833ee5e28ffbb7a2287a494eeeccd384dd4d00d39919aaf2693e0`
and returned **PASS** on their exact repaired boundaries. Variable identity is
ID plus `ColumnTy`, the renamed-use witness discriminates the original bug,
same-ID/wrong-type reuse still rejects, the public enum is non-exhaustive, and
the sole DuckDB production descriptor match plus all test helpers fail closed
on future variants. No source moved during these confirmations.

Coordinator-owned separately capped gates are green:

- scalar-expression tests 9/9, action-rule tests 24/24, generalized-action
  tests 8/8, native-token lifecycle, and canonical fallback;
- full `egglog-experimental-duckdb` library tests 126/126 and all-target
  `-D warnings` clippy;
- changed backend-trait/core/frontend library tests 69 + 2 + 58, plus check
  and `-D warnings` clippy;
- DuckDB-feature CLI check, binary tests 4/4, and `-D warnings` clippy;
- formatting and tracked/untracked diff checks; and
- all selected proof identities. The main proof binary passed 204/204,
  including full Math and Hardboiled. Seven small experimental proof fixtures
  passed in the aggregate run, and the sole unfinished fixture,
  `eggcc_2mm_pass1_proof_testing`, passed in an isolated bounded run in
  66.37 seconds. The aggregate `make proof-tests` process itself reached the
  110-second watchdog after compilation and those 211 passes; that aggregate
  timeout is censored orchestration data, while complete correctness coverage
  is evidenced by the split runs.

The final DuckDB-feature build completed in 53.40 seconds and its direct
dynamic-loader preflight succeeded. Pointer's live fact-directory identity is
`c15261f17ff692435f41beafa4de893bb1cca0a36874aafa472bce78781f6e78`,
matching the frozen corpus. Fresh proof-mode workload probes produced:

| Workload | Exit and wall | Maximum RSS | New fail-closed frontier |
| --- | --- | --- | --- |
| Math | exit 1, 0.13s | 38,436,864 bytes | ordered-union target 22 `View` has an unsupported standard-rebuild configuration |
| Luminal | exit 1, 0.16s | 61,472,768 bytes | the same target-22 `View` configuration, first exposed by `add-zero` |
| Eggcc | exit 1, 3.27s | 100,220,928 bytes | `@rebuild_rule166` requests `ReadMode::All` |
| Pointer | exit 1, 5.81s | 354,107,392 bytes | `check_facts` requests `ReadMode::All` after native raw-SQL fact ingestion |
| Hardboiled | exit 1, 0.04s | 45,006,848 bytes | `@rebuild_rule64` requests `ReadMode::All` |

No workload timed out, crashed, invoked a host fallback, or published a
partial report artifact. All five moved beyond the prior scalar-operation
frontier to one of two explicit non-scalar prerequisites. Performance remains
descriptive.

This checkpoint is accepted for a local commit. The next proposal-formation
round must independently census (1) the exact target-22 standard-rebuild
configuration reached by Math/Luminal and (2) the exact `All` rule shapes
reached by Eggcc/Pointer/Hardboiled. No implementation writer is authorized
until those read-only circles separate a bounded native SQL slice from any
container, callback, host matcher/merge, or private-API requirement.

## Proposal formation after scalar checkpoint

The accepted scalar checkpoint is local commit
`b94da058fe57ca195f2efc752ee3ab9db720e98b`; the source worktree was clean
immediately after commit. Nothing was pushed. The current frontier contains
two independently observed fail-closed surfaces, so implementation pauses for
one bounded Understand -> Explore -> Decide round.

| Circle/domain | Aim | Authority | Expected output | Stop |
| --- | --- | --- | --- | --- |
| target-22 `View` census | Explain the exact Math/Luminal standard-rebuild configuration rejected as an ordered-union target | Read-only `b94da05`; inspect source/ledger only; no edits, builds, tests, workloads, network, or agent contact | exact functions/types/config/merge topology, why existing admission rejects it, Design A and B, minimum canaries and workload-moving verdict | Stop at the first callback/container/private-API requirement or once one bounded public-SQL lowering is exact |
| `ReadMode::All` census | Classify the first All rule in Eggcc, Pointer, and Hardboiled and determine whether one bounded family covers them | Read-only `b94da05`; inspect source/fixtures/ledger only; no edits, builds, tests, workloads, network, or agent contact | exact rule/body/action/read shapes, subsumed-row semantics, overlap/divergence, minimum native SQL contract and canaries | Stop when the three shapes diverge beyond one honest checkpoint or require host enumeration/callbacks |
| next-checkpoint architecture/oracles | Select ordering and architecture for the two frontiers without weakening fail-closed ownership | Read-only `b94da05`; inspect source/fixtures/causal-testing evidence already present in the repo/ledger only; no edits, builds, tests, workloads, network, or agent contact | Design A/B, authority/transaction/generation/rollback contract, discriminating tests, write set, statement/cost observations, early-exit rule | Stop after a bounded public-API native-SQL proposal passes, or prove the next goal unreachable under locked constraints |

No writer is authorized while these circles run. Their verdicts must identify
which frontier moves the largest part of the frozen corpus without combining
unrelated semantics merely to reduce checkpoint count. Performance is
descriptive and every later command remains capped at 110 seconds.

## Frozen standalone-UF scalar target contract

All three read-only proposal circles completed against committed HEAD
`b94da058fe57ca195f2efc752ee3ab9db720e98b` with only this coordinator ledger
dirty. None edited source, built, tested, ran workloads, accessed the network,
or contacted another agent. They independently agree to fix the standalone UF
admission gap before implementing `ReadMode::All`.

### Exact reached shape and workload leverage

The diagnostic target 22 is allocation-order evidence only. In Math it is
`@UF_Math`; in Luminal it is `@UF_Expression`. Each is a typed equality-sort
UF table with schema `[Id, Id, Id]`, one key, two values, one identity value,
`DefaultVal::Fail`, `can_subsume=false`, `WriteCapability::Deferred`,
`KeyToParent` orientation, and a self-displaced target equal to itself.

Its authenticated seven-action merge selects max/min payloads, mints Sym and
Trans proof IDs, writes the ordinary Sym and Trans AssertEq tables, recursively
sets the displaced maximum into the same UF, and retains the minimum parent
with the corresponding proof payload. Primitive/fresh authority, exact
signatures, schemas, proof targets, action order, and topology authorize this
shape; function IDs, rule names, diagnostic names, proof labels, and workload
paths never do.

The scalar compiler currently sends every deferred Set through the
subsumable-View graph validator. Constructor Views correctly use the existing
two-node View -> UF graph, while native input already admits the exact
non-subsumable self-UF. This is therefore an admission/representation gap, not
missing SQL execution.

Static workload evidence finds four direct variable-RHS UF rewrites in Math
and ten direct UF Sets across Luminal's Expression, EList, and IR sorts. The
same capability is expected later in Eggcc. Pointer and Hardboiled currently
contain no later standalone direct source UF. Fresh capped probes remain the
runtime gate.

### Selected Design A

Extend `validate_scalar_action_ordered_union` with the structural
`can_subsume` split already used by native input:

- a subsumable target retains the existing View plus distinct displaced-UF
  validation;
- a non-subsumable target must pass the exact UF schema validator and the exact
  self-displacing `KeyToParent` ordered-union validator with displaced target
  equal to itself.

Represent the standalone component using the existing `OrderedUnionGraph`
with `root == displaced`. Existing scalar storage deduplicates graph targets
by FunctionId, maps self-displacement back to the same queue, and drains
generated candidates at the following wave to a public-SQL fixed point. No
storage or executor change is authorized initially.

Design B, authorized only if a reduced witness disproves that singleton-alias
invariant, replaces the fixed pair with an explicit component containing one
or two plans. It is not a second production mode. Host recursion, host merge,
UDFs, callbacks, benchmark-specific authorization, or private APIs are never
fallbacks.

### Semantic and test gate

The existing transaction contract remains exact: authenticate before RuleId,
freeze every body/slot/effect before mutation, reject owner/subsumption
conflicts before counters, apply direct actions in schedule/action/match order,
drain global merge queues including self-waves, advance generation once iff a
physical change occurred, commit before publishing run ID/watermarks/trace/
telemetry, and on any failure restore rows, proof IDs, counters, generation,
watermarks, telemetry, trace, and scratch so retry reuses the same IDs.

Blocking focused witnesses cover:

1. Reference/DuckDB missing-owner, identity no-op, old-min, new-min, duplicate
   candidates, and a recursive self-displacing chain of at least two waves.
2. Exact Sym/Trans proof rows, strict comparison/right-tie payload behavior,
   explicit-head-before-collision fresh order, stable prewave, generation, and
   unchanged reruns.
3. Wrong schema, identity count, default, subsumption flag, orientation,
   displaced target, proof targets, action order, primitive tag/signature,
   fresh token, freed/reused token, and same-kind ABA rejection before RuleId.
4. Late AssertEq conflict and fresh exhaustion rollback followed by a
   deterministic successful retry.
5. Structural SQL evidence excluding host enumeration/merge, callbacks/UDFs,
   Arrow/Appender, private APIs, `NULL`, and `TRY`.
6. Separately capped fresh Math and Luminal proof-mode probes. A timeout is
   censored; if neither workload moves beyond target 22, stop and recensus.

One implementation writer owns only `rebuild.rs` and focused general/action
tests; `action_rule.rs` may change only if admission wiring or a precise
diagnostic requires it. It may not edit this ledger, storage, frontend/SPI,
fixtures, manifests, loaders, benchmarks, other plan families, committed
history, or remote state. It runs only separately capped focused checks and
freezes a deterministic source digest. Three read-only reviews and at most one
evidence-driven repair follow.

Stop Design A plus one repair rather than broaden it. Design B may be tried
once only on proof that graph representation caused the failure. If both
designs fail the same reduced differential or exact semantics require a host
callback/row/merge, container, UDF, private API, or second transaction, stop
the checkpoint and return to proposal formation. Performance remains
descriptive.

### Recorded later frontiers

`ReadMode::All` is shared visibility plumbing but the first three sites are not
one honest semantic family. Pointer is a pure two-table existential check and
justifies a later authenticated SQL-native `MatchObservationPlan`; it should
complete Pointer. Eggcc immediately needs a separate custom scalar merge plus
mixed rebuild Set/Delete. Hardboiled immediately needs a public typed-container
descriptor and native container-proof effects; it remains intentionally
fail-closed while public `ColumnTy::Id` cannot distinguish containers. These
frontiers must not be laundered into the standalone-UF checkpoint.

## Frozen standalone-UF Design A candidate

The sole writer completed against unchanged committed HEAD
`b94da058fe57ca195f2efc752ee3ab9db720e98b`. The coordinator independently
reproduced deterministic source digest
`e003a9c62e3996decf6fee4c4c07f995bec99cc630ae57128bb76cb9aa62f59b`.
The exact source dirty set is `rebuild.rs`, `action_rule.rs`, and
`action_rule_tests.rs`; this ledger is the only other dirty path.

Design A now splits scalar ordered-union validation by `can_subsume`, aliases
the exact standalone `KeyToParent` UF plan as root and displaced, and gives a
self-aliased UF effect the stronger non-subsumed owner check consistently at
both compiler occurrences. Storage, queue execution, public SPI, fixtures,
manifests, loaders, benchmarks, and other plan families are unchanged.

Writer-owned separately capped evidence is green: standalone-UF witnesses
6/6, action-rule tests 29/29, generalized-action tests 8/8, scalar-expression
tests 9/9, DuckDB all-target check, `-D warnings` clippy, formatting, and diff
checks. No command timed out, no public workload or proof suite ran, and
nothing was committed or pushed.

The candidate preserves the pre-existing queue SQL's physical outer-join
sentinel `old_generation IS NULL`. It adds no semantic NULL value, `CAST(NULL`,
`TRY`, callback/UDF, Arrow, Appender, unsafe, private API, or host row/merge
path. The frozen prohibition on SQL NULL as semantic absence does not require
an unrelated rewrite of an existing physical join sentinel; reviewers must
still verify this distinction rather than waive it by assertion.

The source is frozen. Three independent read-only reviews now own (1)
structural admission/authority/owner checks, (2) self-queue SQL semantics,
transaction/order/rollback and the NULL-sentinel boundary, and (3) test
discrimination/scope/workload movement. No source writer is active;
coordinator gates and public probes remain pending.

### Standalone-UF review verdicts and sole repair

All three reviewers authenticated HEAD, source digest
`e003a9c62e3996decf6fee4c4c07f995bec99cc630ae57128bb76cb9aa62f59b`,
and the exact frozen dirty set before and after review. None edited, built,
tested, ran workloads, accessed the network, or contacted another agent.

- Structural admission/authority: **PASS**. Exact table/merge topology,
  descriptor and fresh authority, proof targets, epoch reauthentication,
  RuleId preservation, stronger self-UF owner checks, and unchanged View
  admission all pass.
- Queue/transaction/SQL: **PASS**. Root/displaced dedup creates one queue;
  recursive wave ordering, payload retention, Sym-before-Trans fresh order,
  freeze/mutation/commit/publication/rollback, generation, telemetry, and
  scratch semantics pass. `old_generation IS NULL` is confirmed to be only
  scratch-local outer-join match detection over NOT NULL durable/queue
  columns; no semantic or persisted NULL, callback/UDF, host row/merge,
  Arrow/Appender, unsafe/private path was added.
- Tests/scope: **REVISE** for one blocking witness gap. The new stronger
  standalone-UF owner check has no focused test with a physically subsumed UF
  owner. Configuration mutation and the opposite subsumed-View policy cannot
  discriminate a regression that weakens both aliased occurrences.

The sole repair is test-only in `action_rule_tests.rs`: seed a UF owner and
candidate, mark that durable UF row subsumed, prove failure before fresh IDs,
generation, watermark, trace, rows, or scratch change, clear subsumption, and
retry to the exact Sym/Trans/UF rows using fresh IDs 0 and 1. Production files,
this ledger, all other tests, storage, SPI, fixtures, manifests, loaders,
benchmarks, commits, and remotes are outside repair authority. The original
reviewer must confirm the new witness after the repaired source digest freezes.

Nonblocking follow-ups record a future mixed View plus standalone-UF schedule
sharing one UF, strongest-owner-check aggregation if a future FD slot can read
the same UF, and wording insert telemetry as ordered-union rather than View
telemetry. None is reached or required by this checkpoint.

The sole test-only repair completed against unchanged HEAD. The coordinator
independently reproduced repaired source digest
`43223186edec6457b06bb327a6ea83872edfcd1c281f72d53344cfa58a4d7736`;
the source dirty set remains the same three files, and only
`action_rule_tests.rs` changed during repair.

`standalone_uf_subsumed_owner_rejects_then_retries_exactly` now seeds a
physical UF owner/candidate, marks the owner subsumed, requires failure while
generation, fresh counter, watermark, trace, rows, telemetry, and scratch stay
unchanged, clears only subsumption, and retries to exact `Sym(70, 0)`,
`Trans(0, 80, 1)`, and UF rows `[1,10,80]` plus `[20,10,1]`. It reuses fresh
IDs 0 and 1 and would fail if both aliased owner checks were weakened.

Repair evidence is green: exact witness 1/1, standalone-UF witnesses 7/7,
action-rule tests 30/30, formatting, and diff checks; no timeout. Production,
this ledger, storage, other tests, manifests, committed history, and remote
state were untouched by the repair. The source is frozen again pending the
original test reviewer's confirmation, coordinator gates, and public probes.

## Accepted standalone-UF scalar checkpoint

The original test reviewer independently authenticated repaired source digest
`43223186edec6457b06bb327a6ea83872edfcd1c281f72d53344cfa58a4d7736`
and returned **PASS**. The repaired witness physically subsumes a UF owner,
requires the specific owner rejection with all state unchanged, clears only
subsumption, and retries to exact rows using fresh IDs 0 and 1. No review
blocker remains.

Coordinator-owned separately capped gates are green:

- exact subsumed-owner witness 1/1;
- standalone-UF witnesses 7/7 and complete action-rule module 30/30;
- full DuckDB library tests 132/132;
- DuckDB all-target `-D warnings` clippy;
- formatting and diff checks; and
- a fresh DuckDB-feature CLI build in 13.15 seconds.

The preceding scalar checkpoint already established complete split proof-suite
coverage at committed HEAD `b94da05`. This checkpoint changes only DuckDB
admission/compiler code and DuckDB-local tests; no frontend, proof encoder,
shared SPI, fixture, or other backend changed, so the unchanged proof suite was
not redundantly rebuilt. Full DuckDB differentials and fresh proof-mode public
probes are the relevant runtime gates.

Fresh primary-corpus results are:

| Workload | Exit and wall | Maximum RSS | Frontier |
| --- | --- | --- | --- |
| Math | exit 124 at 110s | not published by killed process | no target-22 rejection; native execution continued until the watchdog, so result is censored |
| Luminal | exit 1, 0.07s | 68,190,208 bytes | moved beyond target 22 to `@rebuild_rule73` requesting `ReadMode::All` |
| Eggcc | exit 1, 2.95s | 102,137,856 bytes | unchanged `@rebuild_rule166` `ReadMode::All` boundary |
| Pointer | exit 1, 5.17s | 349,503,488 bytes | unchanged `check_facts` `ReadMode::All` boundary |
| Hardboiled | exit 1, 0.04s | 45,154,304 bytes | unchanged `@rebuild_rule64` `ReadMode::All` boundary |

No workload crashed, fell back to host execution, regressed to an earlier
boundary, or published a partial report artifact. Math's timeout is censored
performance data, not correctness evidence in either direction. Luminal
provides the required positive workload movement; the other three remain at
their previously classified explicit frontier.

This checkpoint is accepted for a local commit. The next bounded checkpoint is
Pointer's authenticated SQL-native MatchObservation plus exact `All`
visibility, because it should complete one frozen benchmark without conflating
Eggcc custom-merge rebuilds or Hardboiled typed containers. Nothing is pushed.

## Pointer MatchObservation proposal formation

The accepted standalone-UF checkpoint is local commit
`7c578c6959534975ccd0e7bc1354dcbf67e26a40`; the source worktree was clean
immediately after commit and nothing was pushed. Pointer's final
`check_facts` rule is now the selected frontier. Implementation pauses for one
bounded Understand -> Explore -> Decide round before any writer edits source.

| Circle/domain | Aim and progress signal | Authority and forbidden shortcuts | Expected output | Stop and no movement |
| --- | --- | --- | --- | --- |
| observer SPI/frontend semantics | Specify the smallest backend-neutral semantic observer registration that preserves Reference/DD behavior while DuckDB never invokes an arbitrary callback | Read-only `7c578c6`; public backend SPI, frontend lowering, and lifecycle tests only; no edits/builds/tests/workloads/network/contact; no callback-name or function-ID authorization | Design A/B, handle/token/epoch/ABA contract, allocation/free/publication behavior, exact write set and blocker | Stop once one object-safe public API preserves canonical behavior and authenticated native lowering, or prove that post-commit observation cannot be represented; repeated API reshuffling without a new discriminating witness is no movement |
| DuckDB SQL/transaction semantics | Compile the exact two-table `All` existence query and return only scalar match telemetry after a successful transaction | Read-only `7c578c6`; DuckDB compiler/storage and exact Pointer rule only; no edits/builds/tests/workloads/network/contact; no host matcher/row export/callback/UDF/Arrow/Appender/unsafe/private API/proof-aware storage | Dedicated-plan versus scalar-plan decision, visibility SQL, authority recheck, transaction/publication contract, statement shape, write set and stop rule | Stop at any need for host match enumeration or callback execution; two SQL designs failing the same reduced semantic witness is no movement |
| differential/oracle matrix | Freeze the smallest Reference/DuckDB and fail-closed canaries that discriminate existence, `All` visibility, authority, rollback, and output publication | Read-only `7c578c6`; source/tests/fixture and existing hooks only; no edits/builds/tests/workloads/network/contact | Blocking test matrix, capped commands, exact Pointer completion criterion, censored/performance reporting split | Stop when every selected invariant has one smallest witness; more tests without new semantic discrimination are no movement |

All commands in later implementation and review remain externally capped at
110 seconds. Performance is descriptive: Pointer completing is expected but a
timeout is censored rather than converted into a correctness result. The
checkpoint may run more than one SQL statement and has no statement-count
ceiling. It must retain raw typed SQL through public DuckDB/duckdb-rs APIs and
must not change the durable metadata boundary of `__generation` plus
`__subsumed`; proof columns remain opaque ordinary program columns.

## Frozen Pointer MatchObservation Design A contract

All three read-only circles completed against committed HEAD
`7c578c6959534975ccd0e7bc1354dcbf67e26a40` with only this coordinator ledger
dirty. None edited source, built, tested, ran workloads, used the network, or
contacted another agent. They found no API, SQL, transaction, or oracle blocker.

An independent encoding audit also resolves the union-find terminology. The
DuckDB backend has no native/hidden union-find: `get_canon_repr` remains the
identity and no host mirror is authorized. Current HEAD and local
`origin/main` nevertheless have identical encoder sources that still reify
equality as ordinary per-sort `@UF_*` function tables, merges, and maintenance
rules. The already accepted standalone-UF checkpoint executes that ordinary
encoded relation; it does not add a second disjoint-set authority. Removing
those tables would require a separately reviewed encoding change.

### Selected public API and lifecycle

Add a public clonable, monotone `MatchObserver` value whose state starts false,
may be marked true, and remains readable after token release. Add one
object-safe default backend method:

```text
register_match_observer(observer: MatchObserver) -> ExternalFunctionId
```

The default registers the canonical zero-argument, Id-valued callback, marks
the supplied observer, and returns the existing sentinel Id. This preserves
Reference and DD behavior through their public external-function APIs; a
nonzero-argument use fails closed. The frontend replaces only `check_facts`'
private side-channel registration with this semantic method and retains its
current lifecycle: allocate after fact lowering, enroll the token in
`BackendRule` rollback, transfer it only after successful `add_rule`, execute,
free the rule, free the token, handle a backend error, then read the observer.

DuckDB overrides registration. It installs only a deferred-panic placeholder,
stores `token -> MatchObserver`, and records the existing monotonically
increasing authority epoch. Freeing removes observer authority and the epoch
before returning the numeric slot to the reusable external registry. Admission
captures token plus epoch; every run checks both kind and exact epoch before
opening SQL. Reuse as an ordinary callback fails kind authentication and reuse
as a new observer fails same-kind ABA authentication. DuckDB never invokes the
callback.

### Exact compiler and execution slice

Add a dedicated effectless `MatchObservationPlan`, dispatched before scalar
actions and selected only by a live observer token. Names, paths, numeric table
or function IDs, diagnostic labels, and the spelling `check_facts_match` never
authorize it. An owned malformed use errors rather than falling through.

This checkpoint admits exactly the reached shape:

- `seminaive=false` and `no_decomp=false`;
- exactly two complete typed table atoms, both `ReadMode::All`;
- typed variables/literals only, no globals or body primitive;
- exactly one head `Let` using the observer token with zero arguments;
- matching Id output metadata and an otherwise unused Id result; and
- no other Let, Set, Delete, Subsume, Union, Panic, lookup, fresh operation, or
  durable effect.

Table arity and column types come from registered metadata rather than fixed
Pointer names. Variable semantic identity is numeric ID plus `ColumnTy`; names
remain diagnostic and may differ at repeated occurrences. Literals use the
central typed raw-SQL encoder, including UTF-8 hex construction for Strings.
The two proof columns reached in Pointer are opaque unused ordinary Id columns.

The plan uses the existing direct-rule transaction without a storage change.
Its materialized temporary stage projects one Boolean per SQL match, never a
user/proof row. `ReadMode::All` contributes no `__subsumed` predicate, and the
non-seminaive query contributes no watermark predicate. Existing direct
execution freezes every scheduled stage before effects, queries exact stage
counts as Rust scalars, applies any mixed direct effects, drops scratch, and
commits. Only after successful commit and after run state is ready does DuckDB
mark observers whose counts are nonzero and publish run ID, watermarks, trace,
and telemetry.

Hit and miss both report `changed=false`, leave rows, subsumption, generation,
and fresh IDs unchanged, set each successful rule watermark to the captured
pre-wave generation, report exact match cardinality and zero inserts, and leave
no scratch. Any admission, authorization, CTAS/count/effect/drop/commit failure
publishes none of observer state, run ID, watermarks, trace, or telemetry; an
identical retry reuses the same run/stage identity. The SQL path may use any
measured number of statements. It must use public typed SQL only and contain no
host row enumeration or matching, arbitrary callback/UDF execution, Arrow,
Appender, unsafe/private API, bound parameters, semantic NULL, `TRY`, or
proof-aware storage.

### Blocking witnesses and public report

The implementation must give each of these one smallest discriminating
witness, reusing existing direct-rule test helpers rather than duplicating a
second executor harness:

1. Object-safe Reference default behavior and existing DD check compatibility,
   including independent handles and free-before-read lifecycle.
2. Exact Pointer-shaped Reference/DuckDB hit and miss differential with
   `changed=false`, exact count, and zero inserts.
3. Absent, one-match, and three-match SQL cardinalities.
4. Live/live, live/subsumed, subsumed/live, and subsumed/subsumed visibility,
   all matching without a subsumption predicate.
5. Hostile typed literals, shared and repeated variables, decoys, renamed
   same-ID/same-type occurrences accepted, and same-ID/wrong-type rejected.
6. Ordinary callback name spoof, wrong token/arity/output/read/flags, extra
   action, one/three body atoms, primitive/global body, and diagnostic mutations
   reject or accept exactly as specified before RuleId allocation.
7. Ordinary-token reuse and same-kind observer ABA reject before SQL with all
   observer/backend state unchanged.
8. Two scheduled observation rules where the first stage succeeds and a
   renamed physical table makes the second fail: neither publishes; sentinel
   trace/telemetry, generation, fresh counter, watermarks, run ID, rows, and
   scratch stay unchanged; restoring the table makes the exact retry publish
   both counts with `changed=false`.

SQL inspection additionally requires central hex literals and shared-Id
equality, no raw source/user names or `?` parameters, no subsumption or
generation predicate, no function-table DML/counter update, and statement
telemetry equal to the executed manifest without freezing an incidental count.

Because shared SPI/frontend code changes, backend-trait, egglog, existing DD,
complete DuckDB, feature CLI, formatting, Clippy, and the complete split proof
corpus are blocking. An aggregate proof command timing out only after the split
corpus passes is censored orchestration data.

The coordinator owns one fresh Reference and DuckDB Pointer proof-mode run with
source/fact hashes and fresh timing-summary paths, each capped at 110 seconds.
DuckDB exit 0 with a valid complete artifact earns a `Pointer completed` claim.
Exit 124 is censored performance data and does not reject a semantically green
checkpoint. Exit 1, check failure, backend error, panic/crash, fallback, or a
stale/partial artifact is blocking. Wall time, RSS, and statement count are
descriptive; no optimization loop is authorized here.

### Writer, review, and stop rules

One implementation writer may edit only:

- `egglog/egglog-backend-trait/src/lib.rs`;
- `egglog/src/lib.rs`;
- `egglog-experimental/duckdb/src/lib.rs`;
- `egglog-experimental/duckdb/src/rule_sql.rs`; and
- `egglog-experimental/duckdb/src/rule_sql_tests.rs`.

This ledger, storage/action/rebuild modules, Reference/DD production, core IR,
proof encoding, fixtures, manifests/lockfile, loaders, benchmark harness,
committed history, and remotes are coordinator-owned or forbidden. The writer
runs only separately capped focused/package gates, creates no commit, and
freezes a deterministic source digest excluding this ledger.

Three independent read-only reviews then cover (1) SPI/lifecycle/authority,
(2) SQL/transaction/publication/forbidden interfaces, and (3) oracle strength,
Reference/DD compatibility, and scope. Permit at most one evidence-driven
repair to Design A. A first-class observer action/ID is Design B and may be
proposed once only if a reduced witness proves the primitive-token form cannot
preserve semantics; it is not a parallel production mode. Stop rather than
broaden if correctness needs callback inspection/execution in DuckDB, a host
row/matcher, proof/container metadata, name-based authority, publication before
commit, a second transaction, storage changes, or a new action family. Two
materially different designs failing the same reduced witness ends this
checkpoint and returns the smallest counterexample.

## Frozen Pointer MatchObservation implementation candidate

The sole writer froze Design A against committed HEAD
`7c578c6959534975ccd0e7bc1354dcbf67e26a40`. The deterministic source diff,
excluding this ledger, is
`27917b2075c98fa9970699c66951a764fd2f4a4b51e0d6e4cbf48989b7c80bf8`.
The dirty production/test set is exactly the five authorized paths above; no
storage, action/rebuild, other-backend production, IR, proof encoding, fixture,
manifest, harness, history, or remote path changed.

The candidate adds the public monotone observer and object-safe default,
preserves the frontend free-before-read lifecycle, and adds DuckDB's
epoch-authenticated effectless two-`All` SQL plan with post-commit marking.
The writer reports all eight canary groups green, together with backend-trait
3/3, complete DuckDB library 139/139, egglog library 69/69, validator 2/2, DD
compatibility 1/1, DuckDB-feature CLI 4/4, warnings-denied scoped Clippy,
formatting, and diff checks. Every command had an external 110-second watchdog
and none timed out. The coordinator independently reproduced HEAD, dirty-set,
digest, and diff-check authentication before opening read-only review.

The writer did not run the coordinator-owned split proof corpus or public
Pointer workload. Three independent reviewers now own the frozen SPI,
SQL/transaction, and oracle/scope surfaces. No source edit, build, test,
workload, network operation, agent contact, commit, or remote write is
authorized during review.

## Pointer MatchObservation independent review

All three read-only reviewers reauthenticated unchanged HEAD
`7c578c6959534975ccd0e7bc1354dcbf67e26a40`, unchanged source digest
`27917b2075c98fa9970699c66951a764fd2f4a4b51e0d6e4cbf48989b7c80bf8`,
the exact five-path source/test dirty set plus this ledger, and returned
**PASS** without edits or execution.

- SPI/lifecycle review passed object safety, default Reference/DD callback
  compatibility, monotone shared state, rollback ownership, free-before-read,
  ordinary-token reuse, same-kind epoch ABA rejection, pre-SQL authorization,
  and post-commit publication.
- SQL/transaction review passed structural two-`All` admission, registered
  table metadata and central typed literals, effectless scalar-count staging,
  stable shared transaction and rollback behavior, exact telemetry, and the
  ban on callback/UDF/host matching or rows, Arrow, Appender, unsafe/private
  APIs, parameters, semantic NULL, `TRY`, and proof-aware storage.
- Oracle/scope review found all eight witness groups discriminating, confirmed
  the fixtures use the public production registration and execution paths,
  found existing Reference proof/check and DD check/fail-check coverage for the
  shared frontend route, and confirmed the public Pointer CLI run remains the
  necessary end-to-end shape gate rather than a missing unit test.

No review repair is authorized or needed. Coordinator-owned capped runtime
gates begin on this same frozen source.

## Pointer public-gate repair witness

Coordinator validation reproduced complete DuckDB library coverage at 139/139
and the full proof corpus at core 204/204 plus experimental 8/8. The
DuckDB-feature CLI build also completed within its watchdog. A fresh Reference
Pointer proof-mode run exited 0 and published
`/tmp/egglog-duckdb-pointer.tCmgTt/reference.json`.

The corresponding frozen DuckDB run executed for 7.05 seconds, reached timing
artifact construction, then exited 1 with:

```text
[ERROR] failed to create timing summary: split pre-merge timing is unavailable for ruleset ""
```

It published no DuckDB report and therefore fails the exact public completion
gate even though this is a report-contract boundary rather than a check or SQL
semantic rejection. Maximum RSS was 357,613,568 bytes. The failure is reduced
to DuckDB returning the default `Combined` pre-merge timing from `run_rules`,
while `TimingSummaryV2` correctly requires `Split` timing for every successful
ruleset. This behavior predates observer matching but becomes observable only
when a DuckDB workload reaches successful report construction.

Exactly one Design-A repair is authorized. It must add the smallest public
report witness and make DuckDB report an honest serial `Split` timing without
claiming unavailable search/apply attribution. Unattributed elapsed time is
permitted; fabricated phase measurements are not. The repair remains inside
the existing five-path write set, may not touch the report crate or storage,
and must not weaken timing-summary validation, suppress the report, special
case Pointer, or run another public workload. After a new frozen digest, the
SQL/publication reviewer re-reviews the repair and coordinator gates restart.

The sole writer reduced and repaired that witness at unchanged HEAD. The new
complete source digest excluding this ledger is
`e745da37643ad40e7eef27dc583534d24a96013134adbe4d948f104b0e25e0ab`;
the complete dirty set remains exactly the five authorized paths plus this
ledger. Only DuckDB `lib.rs` and `rule_sql_tests.rs` changed within the repair.
Nonempty serial executions now measure the `execute_rules` outer interval and
report `Split { search: 0, apply: 0, unattributed: elapsed }`; empty schedules
report Split zeros. This closes the artifact schema without inventing an
internal phase boundary.

The writer reports the focused timing witness 1/1, complete DuckDB library
140/140, DuckDB-feature CLI 4/4, timing-summary CLI 6/6, warnings-denied DuckDB
and feature-CLI Clippy, formatting, and diff checks green, with no timeout or
public workload. The coordinator independently reproduced HEAD, dirty set,
digest, and diff-check. The original SQL/publication reviewer now owns one
read-only repair review before coordinator gates restart.

The original SQL/publication reviewer reauthenticated the repaired digest and
returned **PASS**. It confirmed the monotonic measurement surrounds exactly the
successful serial `execute_rules` transaction, the three Split components are
additive and honest, error and observer publication paths are unchanged, empty
schedules truthfully report zero work, the focused witness covers both forms,
and no timing masking or forbidden scope appeared. Coordinator gates restart
on the repaired digest; no further repair is authorized.

## Accepted Pointer MatchObservation checkpoint

Coordinator-owned final gates on repaired source digest
`e745da37643ad40e7eef27dc583534d24a96013134adbe4d948f104b0e25e0ab`
are green, every command externally capped at 110 seconds:

- complete DuckDB library 140/140;
- complete proof corpus, core 204/204 plus experimental 8/8;
- DuckDB-feature CLI 4/4 and a fresh feature binary build;
- warnings-denied backend-trait/egglog, DuckDB all-target, and DuckDB-feature
  CLI Clippy;
- formatting, diff, frozen digest, and exact dirty-scope checks; and
- fresh Reference and DuckDB Pointer proof-mode public runs.

The frozen workload hash is
`dbb091872559ee71f685986f2f49c80ee6c929d72de2843c19688c4677b3f76f`
and its fact-directory hash is
`c15261f17ff692435f41beafa4de893bb1cca0a36874aafa472bce78781f6e78`.
Fresh artifacts are retained under
`/tmp/egglog-duckdb-pointer-repaired.uo4WSi/`. Both executions exited 0,
produced empty stdout, and published schema-v2 timing summaries containing the
same ordered ruleset vector: default, `@delete_subsume_ruleset`, `@parent`,
`@rebuilding`, and `@rebuilding_cleanup`.

Reference completed in 0.49 seconds with 38,977,536-byte maximum RSS. DuckDB
completed in 6.35 seconds with 352,108,544-byte maximum RSS. DuckDB is therefore
about 13x slower and 9x higher-RSS on this small workload; this is descriptive
performance evidence, not a correctness failure. Crucially, this is the first
frozen real `.egg` benchmark to complete end to end through the fully
DuckDB-authoritative proof-mode path. No host matcher, merge, row mirror,
callback execution, proof-aware storage, unsafe/private API, Arrow, or Appender
was introduced.

The Pointer checkpoint is accepted for one local commit. Per the user's regroup
request, stop after committing and reporting this checkpoint; do not recensus,
plan, or begin another implementation frontier. Nothing is pushed.

## 2026-08-05 standalone SQL compiler restart

### Steering frame

- **Mission:** merge one freshly frozen `origin/main` into
  `agent/duckdb-native-sql`, then compile proof-instrumented Egglog into a
  deterministic standalone typed SQL artifact executed only by the stock
  DuckDB 1.5.4 safe CLI. The real proof-mode EqSat program is the blocking
  architectural gate; Math, Pointer, bounded current-main Eggcc, and Luminal
  are the positive generalization corpus.
- **Non-goals:** no host fallback, callbacks, UDFs, extensions, Appender,
  `read_csv`, `COPY FROM`, unsafe/private DuckDB API, proof-specific storage,
  compiler fuel, patched DuckDB, or benchmark-result substitution. Hardboiled
  is a required preflight rejection for active `Vec`; Herbie is excluded from
  positive DuckDB completion. Neither is removed from repository regressions.
- **Current frontier:** checkpoint 0 merge/refreeze. No network operation has
  occurred in this restart. The pre-fetch branch is
  `37fc161a698d7793d62182ec369a891e20fce295`, and the pre-fetch local
  `origin/main` ref is `6ef88f13b6b6be244e961807a19d95cb35c4140b`.
- **Progress signal:** a checkpoint patch or artifact that passes its stated
  semantic gate under an external 110-second cap. Counts, table sizes, or a
  timeout alone never establish semantic success.
- **No movement:** a same-domain cycle with no passing gate, reviewable patch,
  new minimized counterexample, or decision-narrowing measurement. Two such
  cycles force diagnosis/proposal formation. Two materially different typed
  execution designs failing the same kernel or EqSat gate trigger the plan's
  early exit.
- **Active risks:** a 129-commit main divergence; occurrence-indexed proof
  rebuild overlap; safe-CLI DuckDB recursion limits; generated-SQL depth;
  schedule/effect transactional semantics; proof-relation oracle fidelity;
  and bounded performance on the four positive workloads.
- **Exact next command:** run the separately capped pre-merge focused DuckDB
  library gate on unchanged `37fc161`, then fetch `origin/main` exactly once
  and record its SHA before beginning `git merge --no-ff --no-commit`.

### Preserved pre-merge state

| Item | Value |
|---|---|
| branch | `agent/duckdb-native-sql` |
| HEAD | `37fc161a698d7793d62182ec369a891e20fce295` |
| status | only untracked `.codex/duckdb-native-sql/artifacts/` |
| `eqsat-basic-desugared-proofs.sql` | SHA-256 `b4a704a281beff5221922c61826fc3e0c3fd74ca7833a11159e8b2492dc73b75`, 1,961,440 bytes |
| `eqsat-basic.sql` | SHA-256 `d33be24d636e17274f3a69dcef51845e511e01c00bc3ef722a18ac3a4fbd518a`, 1,952,346 bytes |

These two untracked SQL files are diagnostic history. They must remain
unmodified and are not standalone-compiler acceptance artifacts.

### Circle roster

| Agent | Circle/domain | Aim | Authority and write set | Artifact | Verification | Stop / no movement |
|---|---|---|---|---|---|---|
| `/root` | coordinator/integration | preserve mission, perform merge integration, own shared ledger and broad/final gates | merge resolutions, `.codex/duckdb-native-sql/STATE.md`, narrow integration repairs; no push | accepted checkpoint commits and synthesized evidence | checkpoint-specific capped gates, staged diff review | goal complete, early-exit evidence, or user authority needed |
| integration/API circle | checkpoint 0 occurrence-index and frontend snapshot | reconcile current-main APIs and expose a backend-free resolved snapshot | assigned after merge census; disjoint explicit files | patch plus API/IR census | focused Rust tests and compile-only panic-backend canary | pass or two designs fail the minimized indexed-rebuild witness |
| engine semantics circle | stock DuckDB kernel | freeze 1.5.4 CLI probes, recursive-state invariants, and depth cap | tracked capability SQL and probe harness only | checksummed CLI/probes/hot SCC | exact safe CLI under 110 seconds | primary plus LIST fallback fail the same semantic kernel |
| compiler lowering circle | standalone compiler | implement typed SQL, schedules, effects, audits, CLI, and atomic publication | compiler/CLI modules and focused tests only | deterministic bundle and conformance suite | compile twice, safe-CLI parse/bind, focused tests | EqSat cannot admit or two state designs fail |
| semantic oracle circle | differential correctness | define and run Reference/live/standalone normalized relation and output oracles | read-only fixtures/oracle artifacts; no production edits | canonical comparisons and minimized failures | two clean compiles/replays plus negative mutations | one reproducible mismatch or complete PASS |
| artifacts/benchmark circle | corpus and `bench.py` | add four-workload suite, cache identity, censored-run reporting | harness/config/tests only after EqSat passes | workload manifests and bounded benchmark report | harness tests and one capped attempt/workload | timeout is censored; semantic mismatch blocks |
| independent review circle | checkpoint reviews | review merge, kernel, EqSat, and final corpus against frozen criteria | read-only | `PASS`, `REVISE`, or `REASSESS` report | raw diff/artifacts and exact commands | one verdict plus at most one bounded re-review |

Only the checkpoint-relevant circles are seated concurrently. Each worker gets
an explicit disjoint write set, forbidden-shortcut list, verification command,
and stop rule before editing; broad shared commands remain coordinator-owned.

### Checkpoint 0 evidence log

| Time | Surface | Evidence | Result |
|---|---|---|---|
| 2026-08-05 | pre-merge focused baseline, ambient loader | `/opt/homebrew/bin/timeout --signal=TERM --kill-after=5s 110s cargo test -p egglog-experimental-duckdb --no-default-features --lib` | 137/140 passed; the three failures all observed Homebrew DuckDB `v1.5.5` where the tests require `v1.5.4`. This is retained as secondary-engine drift evidence. |
| 2026-08-05 | pre-merge focused baseline, pinned loader | same command with `DYLD_LIBRARY_PATH=$PWD/target/debug/deps`; the dylib has embedded `v1.5.4` and SHA/source provenance under `target/duckdb-download/aarch64-apple-darwin/1.5.4` | PASS, 140/140 in 1.60s after the cached build; no timeout. |
| 2026-08-05 | one permitted main fetch | `git fetch origin main`; then `git rev-parse FETCH_HEAD origin/main` | both resolve to `6ef88f13b6b6be244e961807a19d95cb35c4140b`; merge base is `853fbfd533a3f73b390de364d980f3f939427eae`; branch-only/main-only counts are 15/129. No further main fetch is authorized for this frozen merge. |

### Active checkpoint 0 seats

| Agent | Domain | Status | Expected artifact | Stop condition |
|---|---|---|---|---|
| `/root/merge_overlap_audit` | twelve auto-merged API/semantic overlaps | read-only active | per-file three-way semantic verdict and exact repair candidates | all overlaps classified or one blocker minimized |
| `/root/index_rebuild_audit` | occurrence-indexed proof rebuild and DuckDB lowering | read-only active | implementation-ready Design A or evidence requiring the one allowed Design B | exact IR/lowering contract and regression matrix frozen |
| `/root/merge_gate_audit` | capped test/rustdoc/current-main gate matrix | read-only active | exact commands and minimal rustdoc-lane recommendation | complete non-overlapping gate matrix |

The coordinator retains broad command ownership and performs only merge-index
inspection, shared compilation diagnostics, state integration, and later final
gates while these circles are active.

### Checkpoint 0 merge diagnosis

The merge completed without textual conflicts and remains deliberately
uncommitted. `git diff --check` and `git diff --cached --check` pass; the merge
index contains 114 current-main paths and no unresolved entries. The twelve
auto-merged files preserve the branch's observer/fresh/native-input APIs and
main's occurrence-index APIs, but the combined build exposes a real new
backend surface rather than compiling accidentally.

| Evidence | Result |
|---|---|
| pinned 1.5.4 `cargo check -p egglog-experimental-duckdb --no-default-features` | FAIL with exactly three non-exhaustive `RuleBodyCall::IndexTable` matches: scalar body at `action_rule.rs`, plus two standard-rebuild table destructures at `rebuild.rs`; no other merged API error |
| `cargo test -p egglog index_binding_tests` | PASS 4/4; frontend binder/literal cases retained |
| `cargo test -p egglog-core-relations --lib occurrence_atom` | PASS 5/5; the current suite still treats a repeated probe at an unindexed row column as rejection, so the requested public `(EdgeOcc x a x c)` regression remains to be pinned explicitly |
| overlap/API audit | all twelve files classified; no architectural blocker; Makefile rustdoc must inherit `DUCKDB_PREBUILT_ENV`; public backend `IndexTable` specs need complete typed validation before RuleId allocation and structured errors instead of reference-backend `expect`s |
| gate audit | froze the separately capped occurrence, generated proof-rebuild, direct DuckDB RuleSpec, rollback/retry, Eggcc no-container, proof, rustdoc, and split `make check` matrix |

The occurrence-index circle remains active to settle the exact repeated-value
semantics and specialized DuckDB rebuild design before any writer is seated.

### Consented checkpoint 0 implementation contract

The occurrence-index circle completed with an implementation-ready Design A.
The reached generated rule is exactly one `Table(All)` UF atom, one
`IndexTable(All)` View atom shaped `(probe, complete base row..., Unit)`, one
authenticated `ValueNeq` guard, descriptor-backed proof/canonicalization Lets,
then one stale-View Delete followed by one canonical-View Set. The current
specialized rebuild compiler is the owner; the general action compiler remains
the second and final design only if the binary-constructor witness proves the
typed head cannot coexist in the rebuilding transaction.

Required Design A invariants:

- validate complete arity, literal typed Unit, nonempty/in-range homogeneous
  `any_of`, probe/indexed-column type agreement, binder reachability, UF-probe
  identity, `All` modes, exact Delete key, and exact canonical Set before
  allocating a `RuleId`;
- lower one typed View scan plus one typed UF scan, with the occurrence filter
  as one parenthesized `IS NOT DISTINCT FROM` disjunction;
- one View row yields one match even when the value or an indexed column is
  repeated; never lower occurrence columns as `UNION ALL` branches;
- preserve Live/Subsumed/All predicates in generic direct index lowering and
  include every underlying generation plus typed row columns in seminaive and
  deterministic ordering metadata;
- freeze all matches before effects and reuse the existing rebuilding phases
  so all Deletes precede Sets/merges and proof queues close before publication;
- retain atomic rollback/retry for rows, subsumption, generation, watermarks,
  fresh IDs, scratch, telemetry, and SQL trace.

Repeated-value resolution is now explicit: a single-column index with the
probe repeated at an unindexed row column is valid and preserves both
equalities; a multi-column occurrence whose probe is only repeated at an
unindexed same-row column remains a preflight rejection. Add public-syntax
regressions for `(EdgeOcc 1 a b c)` and `(EdgeOcc x a x c)` over `(any 0)`;
these normal-mode fixtures must not be term encoded.

#### Integration writer contract

- **Aim:** deliver the complete checkpoint-0 merge integration slice: frontend
  binder alignment and public regressions, structured reference/DD validation,
  specialized DuckDB indexed rebuild, direct RuleSpec canaries, and rustdoc
  prebuilt environment.
- **Owned write set:** `Makefile`; `egglog/src/lib.rs`; the two public index
  fixtures/snapshots or their existing normal-mode harness assertions;
  `egglog/egglog-backend-trait/src/backend_impl.rs`; DD validation and its
  focused tests; `egglog-experimental/duckdb/src/{rebuild.rs,action_rule.rs,
  rule_sql.rs,storage.rs,rebuild_tests.rs,rule_sql_tests.rs,
  general_action_tests.rs}`. Any additional file requires a stop-and-report.
- **Forbidden shortcuts:** no wildcard acceptance, host matching/rows/callback,
  proof/name-specific recognition, `UNION ALL` per occurrence column, term
  encoding of user-declared index fixtures, weakening `All`, Set-before-Delete,
  fallback, unsafe/private API, dependency/lock changes, artifact edits,
  ledger edits, commits, pushes, broad `make check`, or proof corpus run.
- **Worker verification:** every subprocess separately capped at 110 seconds;
  focused occurrence/frontend/DD/DuckDB declared-index tests, pinned-engine
  DuckDB check, formatter, and diff checks. Broad rustdoc, proof, EqSat, Eggcc,
  and `make check` gates remain coordinator-owned.
- **Stop:** freeze a deterministic patch digest when Design A focused gates
  pass, or report the smallest binary-constructor witness proving Design A
  cannot represent the head. Two no-movement cycles force diagnosis. Design B
  is not authorized without that witness.
- **No movement:** status-only reporting, compile-only wildcard arms, or tests
  that do not discriminate the typed occurrence/effect contract.

### Checkpoint 0 integration handoff (2026-08-05)

The single writer completed Design A without using the general-action fallback.
The 13-file unstaged integration slice is frozen at SHA-256
`6f807e07f6e46ccfe5e0ccccb2e90343f9cf6f0b0660c0f1e5528a318b3994cf`
over the exact intended paths; the staged `origin/main` merge remains separate.
The two preserved untracked EqSat traces remain byte-identical at
`b4a704a281beff5221922c61826fc3e0c3fd74ca7833a11159e8b2492dc73b75`
and `d33be24d636e17274f3a69dcef51845e511e01c00bc3ef722a18ac3a4fbd518a`.

The final focused circle closed every refreshed blocker: canonical Unit output
binding and raw-SPI totality; duplicate `any_of` rejection across frontend,
reference, DD, and DuckDB; exact Live index-row reuse for direct Subsume;
fail-closed rejection of proof-payload indexed positions; authenticated
proof/fresh prefix closure; one-scan parenthesized occurrence SQL; and atomic
indexed Delete, Set/merge, queue closure, rollback, retry, generation,
watermark, fresh, scratch, telemetry, and trace behavior. Focused tests,
warnings-denied Clippy, formatting, and diff checks passed. Broad proof, EqSat,
Eggcc, rustdoc, and `make check` gates remain coordinator-owned.

Independent frozen-diff review seats are now active for API/validation,
DuckDB semantics/atomicity, and test/scope coverage. No integration files will
move until those reviews complete; any concrete finding returns to one bounded
repair cycle before the coordinator-owned gate matrix.

#### Coordinator broad-gate blocker

`make rust-doc-links`, `make proof-tests` (216 selected tests), and the exact
bounded Eggcc no-container shape test passed under separate 110-second caps.
The first real current-main EqSat DuckDB proof run did not pass: after a clean
build, `egglog-experimental --backend duckdb --proofs
egglog/tests/web-demo/eqsat-basic.egg` exited 1 with
`DuckDB path rule '@uf_path_compress' merge Block must have seven ordered
actions`. This is a current-main generated path-rule compatibility blocker,
not a timeout and not a stock-SQL compiler result. Checkpoint 0 remains open.
The next action is one bounded repair cycle in the existing DuckDB integration
write set, followed by the same exact EqSat command and refreshed reviews.

#### Writer scope amendments

Two narrow additions to the original writer path list were explicitly
authorized during implementation and are recorded here for provenance:

- `egglog/src/typechecking.rs` was authorized to reject duplicate declared
  index positions at source admission, keeping frontend, reference, DD, and
  DuckDB direct-SPI behavior coherent instead of fixing only one backend.
- `egglog-experimental/duckdb/src/lib.rs` was authorized to register canonical
  Unit idempotently in the raw DuckDB backend constructor so malformed direct
  `IndexTable` specs return structured errors rather than panicking.

Both amendments are limited to checkpoint-0 admission totality and their
focused canaries; neither authorizes manifests, lockfiles, artifacts, or other
runtime behavior.

### Checkpoint 0 bounded repair freeze (2026-08-05)

The single authorized repair cycle is frozen at 16-path binary-diff SHA-256
`607b5d621e355ef25f747cfdb8e98dc766f097f4c95dee33a435f59d60b47a61`.
The three added DuckDB paths are `path_compress.rs`,
`path_compress_tests.rs`, and the test-only `cleanup_effect_tests.rs`; their
scope was explicitly authorized after the real EqSat failure and normalized
RuleVar identity invalidated an old diagnostic-name assertion.

The repaired path compiler and executor retain the authenticated legacy
seven-action Sym/Trans collision proof and add the exact current-main
five-action packed-proof collision shape. The exact capped current-main EqSat
DuckDB proof command now exits 0. The repair also closes the frozen-review
findings: exact generated packed-prefix wiring, late post-Delete conflict
rollback plus identical retry, driver and auxiliary UF merge-token retention
and epoch reauthorization, ID-and-type variable identity, source-order-neutral
synthetic Unit binder rejection, discriminating literal occurrence coverage,
and pre-RuleId DD fused-frontier width rejection.

Worker gates passed: DuckDB 150/150, DD rewrite-join 4/4, frontend index
binding 7/7, DuckDB/DD/egglog warnings-denied Clippy, formatting, and diff
checks. Coordinator broad gates must be rerun against this repaired digest,
followed by refreshed independent review.

Post-merge Eggcc fixture provenance is now refrozen: staged/current
`egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg` is SHA-256
`66709c4f646722eb3e26db34a483e8501b5a8053a4d3c8146355beeebe480268`.
The earlier `23efdf1b...` entry remains historical pre-merge evidence.

### Checkpoint 0 final repair and coordinator gate freeze (2026-08-05)

The final four-path DuckDB repair closes the two remaining independent-review
blockers without changing the authorized 16-path surface. `IndexedProofContext`
now carries and validates the exact authenticated packed-constructor
`FunctionId`; canonicalizers are attributed through final result variables in
ascending View-column order, cannot be reused for repeated source columns, and
cannot be reordered with their proof steps. Direct negative regressions cover a
same-schema decoy target, `(x, x)` canonicalizer reuse, and reversed
canonicalizer order. The final 16-path binary-diff SHA-256 is
`cc3ec2b2ba0a5610554ca5428e826fe447a0b00cf1247e8e1a9ce5f320f3192d`.

Final focused worker gates passed: DuckDB library 151/151, the new packed-proof
regressions, DuckDB Clippy with warnings denied, formatting, diff checks, and a
proof-enabled EqSat replay. No general-action fallback was used.

The coordinator independently bound the real EqSat result to the final digest
with this exact capped invocation:

```text
/opt/homebrew/bin/timeout --signal=TERM --kill-after=5s 110s env -u DUCKDB_LIB_DIR -u DUCKDB_INCLUDE_DIR -u DUCKDB_STATIC DUCKDB_DOWNLOAD_LIB=1 DYLD_LIBRARY_PATH=/Users/saul/p/wt/egglog-encoding/duckdb-native-sql/target/debug/deps cargo run --locked -p egglog-experimental --features duckdb-backend -- --backend duckdb --proofs egglog/tests/web-demo/eqsat-basic.egg
```

It exited 0 in 5.52 seconds and emitted no program output, as expected for
successful checks. The loaded dylib remains the cached DuckDB v1.5.4 runtime.

The one required `make check` invocation was externally censored at 110 seconds
during the workspace Rust-test lane after Python lock/format/lint/typecheck,
Rust formatting/Clippy/rustdoc, and all 172 Python tests passed. Its separately
capped Rust leaves then all passed: workspace excluding DuckDB; DuckDB library
151/151; the feature-enabled DuckDB CLI binary 4/4; and DD timing-summary CLI
1/1. This is timeout-censored aggregate coverage with complete passing leaf
coverage, not a test failure.

Checkpoint 1's stock engine is also pinned locally under ignored `target/` for
the next checkpoint. The official `duckdb_cli-osx-arm64.zip` v1.5.4 archive is
SHA-256 `d6c35195683fd1378e5624b01ca390069d399f8341c38986b7e3dfa0b3470d10`,
matching the GitHub release asset digest; the extracted arm64 CLI is SHA-256
`6c5abaff49f07ba3f6b2e41ed1adf338d10fcb2d98777331b285cc97938fb00a`,
reports `v1.5.4 (Variegata) 08e34c447b`, and executes
`-safe -no-init -batch -bail -json :memory:` successfully. Homebrew v1.5.5
remains the secondary compatibility engine only.

After the final digest freeze, the coordinator reran both broad semantic/doc
gates under separate 110-second watchdogs: `make proof-tests` passed all 216
selected tests (208 core plus 8 experimental) in 20.75 seconds, and
`make rust-doc-links` passed with warnings denied in 1.75 seconds. The frozen
16-path digest remained `cc3ec2b2...`; unstaged and staged diff checks pass and
the merge index has zero unmerged entries. The final independent DuckDB review
remains the only checkpoint-0 acceptance item before staging and committing.

### Checkpoint 0 current-main EqSat refreeze (2026-08-05)

Two clean proof desugarings of the post-merge EqSat source were byte-identical.
The current desugaring is 28,474 bytes / 492 lines with SHA-256
`4ec9cc9e8085da2d1f1f859e4300f1a81835538b1bbf68486f0c3c1cc5cc0f18`.
This census is pinned to HEAD `37fc161a698d7793d62182ec369a891e20fce295`,
MERGE_HEAD `6ef88f13b6b6be244e961807a19d95cb35c4140b`, and final
16-path digest `cc3ec2b2...`.

| Surface | Current post-merge census |
|---|---|
| source commands | 9: datatype 1, lets 2, rewrites 4, run 1, check 1 |
| resolved commands | 95: rulesets 4, sorts 3, functions 49, indexes 6, rules 27, action blocks 2, schedules 3, check 1 |
| resolved control ordinals | begin 76/85; schedules 91/92/94; check 93 |
| rule placement | default 4; `@parent` 1; `@rebuilding` 10; `@delete_subsume_ruleset` 12; `@rebuilding_cleanup` 0 |
| rule modes | Live 17, All 10; unsafe-seminaive 10, default 17; no naive/no-decomp |
| rendered rule-head actions | 155: let 74, set 53, delete 22, subsume 6 |
| top-level action-block actions | 168: let 82, set 86 |
| function merges | no-merge 41; old 1 (`@MathProof`); action-block 7 (`@UF_Math` plus six logical views) |
| typed output shapes | Unit 41; scalar `@Proof` 1; `(Math, @Proof)` tuple 7 |
| structured schedules | Repeat 1, Sequence 6, Saturate 6, static Run leaves 13 |

The schedule paths are:

```text
ResolvedCommand[91]/Repeat(10)/Sequence[0] => default
ResolvedCommand[91]/Repeat(10)/Sequence[1]/Saturate/Sequence[0] => @rebuilding_cleanup
ResolvedCommand[91]/Repeat(10)/Sequence[1]/Saturate/Sequence[1]/Saturate => @parent
ResolvedCommand[91]/Repeat(10)/Sequence[1]/Saturate/Sequence[2] => @rebuilding
ResolvedCommand[91]/Repeat(10)/Sequence[2] => @delete_subsume_ruleset
ResolvedCommand[92]/Sequence[0]/Saturate/Sequence[0] => @rebuilding_cleanup
ResolvedCommand[92]/Sequence[0]/Saturate/Sequence[1]/Saturate => @parent
ResolvedCommand[92]/Sequence[0]/Saturate/Sequence[2] => @rebuilding
ResolvedCommand[92]/Sequence[1] => @delete_subsume_ruleset
ResolvedCommand[94] repeats the ResolvedCommand[92] shape as final maintenance.
```

Code-backed inference through `BackendRule::query` gives 27 `RuleSpec`s, all
with seminaive true: 18 Live Table atoms, 4 All Table atoms, 6 All IndexTable
atoms, 1 Live primitive atom, and 10 All primitive atoms, for 39 body atoms and
no Subsumed reads. The six occurrence indexes are:

```text
@NumOcc_Math    -> @NumView    any_of=[1]
@VarOcc_Math    -> @VarView    any_of=[1]
@AddOcc_Math    -> @AddView    any_of=[0,1,2]
@MulOcc_Math    -> @MulView    any_of=[0,1,2]
@$expr1Occ_Math -> @$expr1View any_of=[0]
@$expr2Occ_Math -> @$expr2View any_of=[0]
```

Display metadata contains 43 `internal_hidden`, two `internal_let`
(`@$expr1View`, `@$expr2View`), six `term_constructor` mappings, and 29
`internal_term_node` entries. Constructor views map `@NumView`, `@VarView`,
`@AddView`, and `@MulView` to the user names `Num`, `Var`, `Add`, and `Mul`;
the two `$expr` views are excluded by `internal_let`. All-`print-size` therefore
has exactly `Add`, `Mul`, `Num`, `Var` in lexical order.

EqSat has no print/input/output/extraction/push/pop/filesystem-output command.
Source ordinal 8 is its sole check, resolved ordinal 93; successful output is
silent and resolved ordinal 94 is the separately generated final maintenance
schedule. The debug desugar surface cannot expose backend ColumnTy IDs,
unsanitized resolved objects, assigned FunctionId/RuleId, structured MergeFn
objects, primitive authority tokens, or a general source-to-resolved ordinal
map. That observed limitation is the reason the compile-only public snapshot is
the next frontend API boundary rather than an optional convenience.

Current core corpus hashes:

```text
c0fa15ae2849bfbb65b53b5168ee7ec338be4ff371d473668b94d25bf2ea7fa0  egglog/tests/web-demo/eqsat-basic.egg
aaa8942131b4db57e76710486718790e1d7f2cb9288aeb702c0c17019439cf16  egglog/tests/math-microbenchmark.egg
dbb091872559ee71f685986f2f49c80ee6c929d72de2843c19688c4677b3f76f  benchmarks/pointer-analysis-small.egg
66709c4f646722eb3e26db34a483e8501b5a8053a4d3c8146355beeebe480268  egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg
4bd1d2f346de94b81b359c50d5fb4129f04011128f7442b53adde3731b740dad  benchmarks/luminal-llama.egg
bd82a9cd8036d123826926ec0189e59a652aa2a9a155dd280d5ea3935b10c005  egglog/tests/hardboiled_conv1d_32.egg
00ae7db6f5792416a438a1d2957e5dbb1caff1dba25ce65dcddb10c6ab2cba4a  egglog/tests/web-demo/herbie.egg
c15261f17ff692435f41beafa4de893bb1cca0a36874aafa472bce78781f6e78  benchmarks/data/pointer-analysis-small/ (directory hash)
```

Pointer facts contain 23 files, 356,973 bytes, and 2,255 headerless rows.

### Checkpoint 0 final-review correction (2026-08-05)

The claimed `cc3ec2b2...` final repair is not accepted. A fresh independent
review authenticated that exact 16-path digest and found five blocking
surfaces; checkpoint 0 therefore remains uncommitted:

1. Legacy indexed packed-constructor admission still selects the sole
   schema-compatible catalog table, so a sole decoy self-authenticates. The
   negative test only created ambiguity and would also reject the unchanged
   canonical target. Packed PathCompression has the corresponding head-proof
   ID gap.
2. Indexed packed proof steps retain only `(target, source_body)`, not exact
   result/action/column identity, so repeated `(x,x)` steps can be swapped.
3. Frontend synthetic IndexTable Unit binding is installed only when that atom
   is visited; an earlier primitive can capture a distinct unbound RuleVar.
4. Packed support widens post-admission authority gaps in PathCompression,
   non-indexed EqKey/EclassOutput rebuilds, and MarkerRekey: their plans do not
   retain/recheck every native/fresh descriptor epoch before execution.
5. DD does not refresh `All` on live-to-subsumed transitions, and Reference
   incorrectly exposes live rows to `Subsumed` reads of non-subsummable tables.

The review passed the one-scan parenthesized occurrence OR, global
Delete-to-Set/merge-to-closure rollback/retry, indexed driver/auxiliary
authority retention, duplicate-any-of admission, and DD pre-RuleId width
validation. One consolidated repair cycle owns the five blockers above. The
earlier green gate results remain useful evidence but cannot authorize a merge
commit until focused regressions, EqSat, the affected broad gates, and a new
frozen independent review pass.

### Checkpoint 0 early-exit diagnosis (2026-08-05)

Both permitted indexed-rebuild designs have now reached the plan's explicit
stop condition.

Design A cannot authenticate the exact internal relation identities required by
the final decoy canaries. `FunctionConfig` exposes schema, merge, name, and
subsumption/storage behavior; `RuleSpec` exposes the rule core and options.
Neither carries authenticated internal-role provenance. A legacy ordered-union
merge directly identifies its Sym/Trans relations, and a packed ordered-union
merge directly identifies only its Packed_2 relation. Nothing in the backend
vocabulary links a legacy graph to Packed_N, Packed_2 to Packed_N for N > 2,
or a packed path-compression graph to its separate EqTrans head relation.
Catalog uniqueness, registration order, fixed offsets, generated-name parsing,
and schema matching are all spoofable on the public raw Backend surface.

Design B, the general action compiler with All reads and atomic global
Delete-before-Set, cannot satisfy the same exact-ID canary by construction. It
faithfully executes the FunctionId supplied by the rule; changing only that
target to a compatible decoy is valid generic rule semantics, not something a
generic compiler can infer should be rejected.

The smallest sound expansion is a shared, admission-only authenticated internal
relation role registry, with at least EqTrans and PackedProof{width}, registered
by the frontend immediately after add_table and cross-checked by the backend
before RuleId allocation. That is a shared API/provenance change outside the
authorized repair write set and may conflict with the milestone requirement
that DuckDB receive no proof-aware metadata. No name/schema/ordering fallback is
accepted. The repair worker therefore retained no partial authority changes;
the source surface remains at ordered 16-path digest `cc3ec2b2...`, DuckDB
`cargo check --lib` and diff checks pass, and findings 2-5 remain uncommitted
because the foundational exact-identity gate cannot be met.

Per checkpoint 0, the next command is `git merge --abort`, followed by exact
status/ref/trace-hash verification. The current-main merge must not be committed
and checkpoints 1-5 must not proceed unless the user explicitly authorizes the
shared provenance API expansion or changes the exact-ID/no-metadata contract.

The first `git merge --abort` correctly refused because the 16 uncommitted
integration paths were not at the merge-index versions. After verifying that
the complete unstaged set was exactly `STATE.md` plus those 16 owned paths, the
coordinator restored only the 16 integration paths to the merge index and
retried `git merge --abort`. The abort then succeeded. Final state:

```text
HEAD=37fc161a698d7793d62182ec369a891e20fce295
ORIG_HEAD=37fc161a698d7793d62182ec369a891e20fce295
frozen-origin-main=6ef88f13b6b6be244e961807a19d95cb35c4140b
MERGE_HEAD=absent
tracked-dirty=.codex/duckdb-native-sql/STATE.md only
untracked=.codex/duckdb-native-sql/artifacts/ only
```

Both diff checks pass. `STATE.md` was SHA-256
`3d63b71ac87dcf4e14e101a31c2329c9b4a12b15f014f17e4b4aaa44bcd8f551`
before this final append. The two preserved diagnostic traces remain exactly
`b4a704a2...` and `d33be24d...`. The merge and failed integration slice were
intentionally removed from the worktree; their diagnosis, frozen digests,
tests, and census remain recorded above. The official ignored DuckDB 1.5.4 CLI
pin under `target/` remains available, but checkpoint 1 is intentionally not
started.

### User decision: Design B is authoritative (2026-08-05)

The user explicitly selected Design B and rejected Design A as the intended
architecture. This resolves the prior acceptance ambiguity:

- A same-schema decoy FunctionId is valid generic `RuleSpec` semantics. The
  general compiler must execute that exact target and match Reference; it must
  not reject the target merely because it lacks a proof-specific role.
- Exact-role/decoy rejection applies only to a proof-specialized recognizer.
  Design B must not invoke such a recognizer, so that canary is replaced by
  generic Reference-parity plus an assertion that no specialized route ran.
- No internal proof-role registry is authorized or needed. Proof relations
  remain ordinary typed relations; MergeFn/action lowering is the sole
  production path.

The earlier conclusion that both designs failed was therefore too strong:
Design A failed its optimizer proof obligation, while Design B was dismissed
using an inapplicable specialized-path canary before it was implemented. The
frozen `origin/main` SHA `6ef88f13b6b6be244e961807a19d95cb35c4140b` was merged again with
`--no-ff --no-commit` without another fetch; the merge again completed with no
textual conflicts and remains uncommitted.

#### Resumed checkpoint 0 implementation circle

| Field | Contract |
|---|---|
| mission | merge current main and preserve generic, fail-closed standalone-SQL semantics without proof-specific backend metadata |
| aim | reconstruct the lost occurrence-index integration, then make the general action compiler own `Table(All) + IndexTable(All) + guard + Lets + Delete -> Set` |
| domain | prior checkpoint-0 frontend/reference/DD paths plus DuckDB generic action/rule/storage tests; specialized proof recognition may only be removed or bypassed |
| authority | one implementation writer; coordinator owns state, preservation, broad gates, diff integration, and commits |
| acceptance | literal decoy target executes generically with Reference parity; exact EqSat proof run, rollback/retry, read-mode, authority-epoch, focused tests, proof tests, rustdoc, and split `make check` gates pass |
| forbidden | proof/name/schema/registration-order role inference, role registry, specialized fallback, host callbacks, Set-before-Delete, weakened All, artifact edits, staging/commit/push by worker |
| stop | a minimized semantic counterexample shows the general compiler cannot faithfully implement the reached action shape, or two cycles show no measurable frontier movement |

The exact next command belongs to the implementation writer: restore the
previous validated occurrence-index admission slice, then add a direct generic
All-read/Delete-before-Set decoy parity canary before broadening the compiler.

### Design B generic-path audit and checkpoint-1 pre-probe (2026-08-05)

The read-only generic-path audit confirmed that Design B is viable without a
shared proof-role registry: `RuleSpec`, `TableInfo`, and `MergeFn` already retain
the exact `FunctionId`s needed to execute literal program semantics. The actual
integration boundary is broader than an `IndexTable` scan. The general scalar
compiler currently follows `StandardRebuild`, `MarkerRekey`, and
`PathCompression`, admits only Live table/primitive bodies and Let/Set heads,
and converts deferred merges into an inferred `OrderedUnionGraph`. Storage also
rejects a bounded ruleset that mixes scalar-action and rebuilding plans.

Design B therefore requires the general compiler to claim the complete reached
All/Index rebuilding action vocabulary before the proof-shaped recognizers and
to lower the exact retained `MergeFn`, not infer proof roles. Its committed
semantic phases remain frozen matches and Lets, global Delete, Set/merge queues
to closure, then global Subsume. The correct decoy canary registers both
same-schema functions, changes only the literal target ID, and requires both
Reference and DuckDB to write that decoy through the generic plan. The old
exact-transcript compiler may remain only as a test oracle.

A read-only `/tmp` probe against the pinned official DuckDB CLI independently
advanced checkpoint 1 without repository writes. The binary remained
`v1.5.4 (Variegata) 08e34c447b`, SHA-256
`6c5abaff49f07ba3f6b2e41ed1adf338d10fcb2d98777331b285cc97938fb00a`,
and the exact `-safe -no-init -batch -bail -json :memory: -f` invocation passed.
Observed kernel facts:

- one nested typed `STRUCT` key and nested `STRUCT`/`UNION` payload work with
  `USING KEY`; a constant non-null Boolean key is required for nullary state;
- a zero-working recurring-only arm and a one-working arm with multiple
  `recurring.state` reads work; DuckDB accepts two working scans, so the
  compiler must reject that shape in IR and rendered-fragment audits;
- the complete multi-branch recursive arm must be parenthesized;
- duplicate-key replacement is order-sensitive, while an explicit non-null
  unique ordinal makes the fold deterministic;
- strict payload anti-diff terminates naturally without fuel;
- tombstone/reinsert/subsume, transaction rollback, lazy `error(...)`, and
  checked native overflow behave as required.

The public CLI has no whole-dependent-script bind-only mode. `EXPLAIN` can bind
individual statements, but dependent DML requires catalog declarations to be
executed first. Artifact validation must therefore use a disposable in-memory
catalog, execute only declarations, and bind runtime statements with
`EXPLAIN`/`PREPARE` while suppressing their plans.

The exact next implementation action remains with the checkpoint-0 writer:
finish a compiling generic All/Index/Delete/Subsume phase slice, then reuse or
extract existing merge semantics into an exact-ID generic merge-program plan
before running DuckDB gates. The coordinator's next action is the read-only
generic-merge reuse audit; no overlapping repository writer is authorized.

### Compile-only frontend snapshot audit (2026-08-05)

The read-only checkpoint-2 API audit found that the current frontend cannot
publish the required snapshot by exposing `resolve_program` or by recording a
backend. `EGraph` registers sorts and primitives with a backend during
construction/typechecking; function and rule configs are built only inside
`run_command` and immediately consumed; current IDs and values are registry
relative; source-command grouping is flattened; and the nominal non-running
resolver still executes push/pop.

Design B therefore requires a frontend-owned, backend-free vocabulary and a
live adapter rather than backend objects in the public artifact. The proposed
boundary is after proof instrumentation, the second typecheck/global
elimination, capability admission, stable catalog/core lowering, and source
origin attachment, but before any runtime ID conversion or command execution.
Stable declaration-order frontend IDs, owned typed literals, portable column
types, closed primitive semantic tags, exact typed merge expressions, typed
rules, structured schedules, catalog-prefix ruleset membership, typed input
events, output ordinals, and display metadata all live in that snapshot.

Implementation dependencies are now frozen for checkpoint 2:

1. add a pure frontend state and stable typed IDs instead of a capture backend;
2. split pure sort/primitive metadata registration from runtime registration;
3. extract function/merge and core-rule lowering from `run_command`;
4. preserve source-command envelopes before macro/desugar/proof flattening;
5. extract TSV parsing into a byte-based typed helper preserving row order,
   duplicates, trim behavior, Unit arity, and exact errors;
6. pre-resolve print sites against the catalog prefix with constructor-view
   first resolution and frozen hidden/let/display metadata;
7. retain structured schedule paths because flat `RunReport` cannot recover
   nested last-child versus aggregate reports.

Whole-program preflight must precede published IDs and fact-row materialization.
For this milestone, `include` joins push/pop, containers, dynamic unstable
functions, extraction, output, print-function, file-targeted prints/stats,
custom schedulers, unknown callbacks, and unsupported proof forms in the
fail-closed set unless the source-hash contract is explicitly broadened.

### Design B generic MergeFn reuse audit (2026-08-05)

The read-only reuse audit found no generic DuckDB merge evaluator to extract.
Registration validates the full `MergeFn` AST but collapses execution to
Old/AssertEq/Deferred; both input and scalar-action Deferred writes then enter
the same exact seven-action, two-value proof-shaped ordered-union recognizer.
Only transaction ownership, typed queue DDL, event/wave bookkeeping, durable
owner joins, counters, rollback, and scratch cleanup are reusable. DD's
`MergeTransaction` is the closest complete semantic oracle.

The authorized Design B implementation is a new typed SSA merge program,
compiled once per function config and stored with its table catalog entry. It
normalizes contextual Old/New to explicit columns, types every constant/slot/
primitive/lookup, preserves ordered Block actions before result evaluation,
retains exact read/write FunctionIds and all authority epochs, and emits complete
typed results atomically. Current EqSat reaches AssertEq, Old, and seven action
Blocks using OldCol/NewCol, Const, LetVar, authenticated ordering/payload
selection primitives, fresh sites, ordered Let/Set, and Columns. It does not
currently reach New, Function, Lookup, or UnionId. Residual UnionId and
`MergeAction::Union` must fail closed in proof-mode post-instrumentation because
silently taking a minimum would omit Reference's equality side effect.

The safe initial executor is event-at-a-time rather than an unsound simultaneous
per-key fold: freeze action effects, apply Delete globally, enqueue Set
candidates, process targets by merge dependency level then FunctionId and
stable event/action ordinal, put generated Sets in the next wave, preserve
subsumed ownership and identity short-circuits, reach genuine closure, then
apply Subsume globally. The surrounding SQL transaction owns all durable rows,
fresh/generation counters, rollback, and publication. Performance must be
measured immediately; a later set-at-a-time optimization requires a static
independence proof.

Patch order is frozen: typed catalog/authority admission; generic queue kernel
while retaining the old implementation as an oracle; action Set wiring and
generic rule routing; input wiring; then exact decoy, DD-derived merge parity,
rollback/retry, EqSat, and broad gates. The current writer is authorized to add
`egglog-experimental/duckdb/src/merge_program.rs` and narrow module/tests for
this work. Production `classify_effect` must stop calling the proof-shaped
ordered-union validator before checkpoint-0 acceptance.

### Current-main merge-census refinement (2026-08-05)

An independent SQL-design audit corrected the conservative event-at-a-time
baseline using the current-main rather than historical trace shape. The seven
reached action Blocks are self-describing five-action programs: payload-max and
payload-min Lets, one fresh mint plus exact Packed_2 Set, one exact UF Set, and
a two-column result. Every actionful target has one identity value; current
EqSat reaches no Function, Lookup, New, UnionId, native Union, non-Fail default,
or actionful no-identity merge. `UF_Math` is the sole cyclic merge SCC.

That census admits a safe set-at-a-time checkpoint-0 renderer across distinct
keys. Each target/pass ranks candidates by typed logical key plus a unique
non-null event ordinal and selects one candidate per key; missing keys insert
live, existing keys apply the identity-prefix guard, dense Lets and exact Block
Sets materialize in action order, all result columns update atomically while
preserving subsumption, and generated Sets enter the next wave. Repeated passes
reach closure without fuel. This does not assume commutativity or implicit
last-row replacement and avoids event-at-a-time whole-state copying.

The event-at-a-time design remains the semantic fallback for later arbitrary
Blocks, not the preferred current EqSat implementation. Dependency levels use
read dependencies only, matching DD; write targets are next-wave edges. If the
setwise renderer approaches 110 seconds, one balanced-CTE stage fusion is the
only authorized immediate optimization before applying the stated stop rule.

### Active SetIfEmpty predicted-state mismatch (2026-08-05)

Status: checkpoint-0 blocker after the first green Design-B candidate.

The first generic candidate passed all 151 pinned DuckDB 1.5.4 crate tests and
ran live `eqsat-basic.egg --proofs` silently, but an independent reduced probe
found the first meaningful semantic divergence. Two scheduled rules call the
same absent-key `SetIfEmpty` with defaults 10 and 20. Reference's serial action
flush returns 10 from both calls and stores owner 10; DuckDB returned 10 and 20
while ultimately storing owner 10. Reversing the schedule reverses the winning
source event.

The confirmed mechanism is plan-local prediction reconstruction. The current
SQL sees preceding `SetIfEmpty` slots from the same rule only, whereas the
Reference action state carries the first predicted owner across scheduled
actions in the Run. The earlier action-major-order hypothesis was fixed and is
not the remaining cause. `ViewColumnRead` remains intentionally durable-only.

The current SQL also tests `lookup.__value IS NULL` for absence, which violates
the no-semantic-NULL contract, and delays FD seed-effect materialization until
after later slots can remove a lane. The accepted next experiment is a typed,
per-target transactional prediction ledger with a non-null unique global event
ordinal, durable-first tagged choice, and a per-site winner stage. Required
canaries cover two scheduled rules in both orders, complete multi-output
defaults, subsumed durable ownership, a later lane-filtering action, and
fresh/rollback/retry behavior. The previously green full crate and live EqSat
runs remain the regression set.

A separate fail-closed admission canary is also active: `MergeFn::Old`, `New`,
and `AssertEq` must have the owner value-column type for their `self_col`; the
compiler may not relabel one of these values with a nested target's expected
type merely because two Egglog types share a DuckDB representation.

### Checkpoint 0 accepted: current-main merge plus Design B (2026-08-05)

Checkpoint 0 is accepted at `2026-08-05T21:04:45Z` for the frozen,
wave-scoped contract. The uncommitted merge still has parents
`37fc161a698d7793d62182ec369a891e20fce295` and
`6ef88f13b6b6be244e961807a19d95cb35c4140b`; the latter is the single frozen
`origin/main` fetch for this campaign. There are no unmerged paths. The next
operation is the intentional merge staging and commit recorded below; no push
is authorized.

The user's architecture decision is final: Design B is the sole production
path for the reached scalar action vocabulary. A typed `MergeProgram`, compiled
from the exact registered `MergeFn`, exact `FunctionId`s, exact primitive
authority tokens, and exact `RuleSpec`, owns generic merge behavior. Same-schema
decoys execute literally. Production contains no `ScalarMixed`, scalar
`OrderedUnion`, proof-role/name/schema/registration-order classifier, callback
fallback, or second `compile_scalar_action` routing branch. The remaining
Standard/Marker/Path specialists are compatibility paths for rules outside the
general compiler's owned vocabulary; general admission precedes all three and
owned errors fail closed.

The current-main occurrence-index integration is part of the same accepted
slice:

- frontend index outputs are marked known Unit before fixed-point
  reachability, and canonical Unit values are installed before any body atom is
  lowered, so either atom order is valid;
- frontend, Reference, DD, and DuckDB validate row arity, trailing literal
  canonical Unit, type-compatible nonempty `any_of`, indexed-column range, and
  fixed-point binder reachability before allocating `RuleId`;
- the typed base table is scanned with the exact Live/Subsumed/All predicate;
- repeated columns and repeated probe values use one parenthesized,
  deduplicated `IS NOT DISTINCT FROM` disjunction, so a base row matches once;
- general scalar execution freezes matches and Lets, applies global Delete,
  drains Set/merge queues to closure, then applies global Subsume; reported
  change, physical change, generation, fresh counter, watermarks, telemetry,
  and transaction publication remain distinct.

#### Final Design-B queue correction

The final independent audit found and closed one test-visible Design-B bug.
The old queue selector chose sibling targets by
`(wave, dependency_level, FunctionId)`, which could reverse source actions.
The discriminating program registers low-ID `L` before high-ID `H`, emits
`Set(H)` then `Set(L)`, and makes two collisions in each target feed crossed
keys in one `MergeFn::Old` sink. Before the fix, DuckDB retained `[100, 100]`
while Reference retained `[200, 200]`.

The accepted selector is
`(wave, dependency_level, earliest_event_ordinal, FunctionId)`. Selection pins
one `(wave, target)` and drains that target's complete current-wave batch in
event order before considering a sibling. Consequently the distinguishing
trace is `H1,H3,L2,L4`, not global-event interleaving or FunctionId order.
Both native input and scalar action use this shared drain. Generated Sets stay
at `wave + 1`; parent/action event ordinals remain stable. The original exact
two-independent-graph Reference comparison and source-order fresh-ID oracle
were restored; the temporary alpha-normalized/FunctionId-first expectation was
removed.

Reference's `merge_simple` can let a generated write join a later target in the
same internal sweep, and its implementation switches to registration-ordered
strata at four dirty tables. Those are real Reference implementation details,
but they are not the frozen SQL contract: they depend on fast-path thresholds,
database size, and possible parallelism, while this design intentionally
separates generated work into the next SQL-owned wave. Independent review found
neither behavior observable in the current-main EqSat collision-bearing route:
initial four/five-view batches contain only missing-owner inserts, while
collision-bearing batches contain at most two views and generate only the
newly queued `@UF_Math` target. The existing general-path wave canary requires
all wave-zero allocations before generated wave-one allocations. A cross-level
ordering canary becomes mandatory before Function/Lookup admission; both remain
fail closed now.

#### Final checkpoint-0 evidence

The final source freeze before this STATE append is:

```text
tracked diff excluding .codex/**
bf7be29504abbe2114fd2c553739f15f323d21a1e68908f0f240d7c6bc9e1258

same diff plus raw untracked merge_program.rs
89501d83bdb5f3519cb75a7b9772d6277836dcb22e617a7e7a8447b48f3b3e57

egglog/src/lib.rs
d5a0b2fb3f21362bad685c388424c79102adf37e52ef03011f3556273d2108ac
egglog/egglog-backend-trait/src/backend_impl.rs
0d80851230d735235e0103cd0c03d652398a77b31c4305764baeda619183abae
egglog-experimental/dd/src/lib.rs
8da185b214d10b995aed8b6e7a3526487f415ba5be74495e42de9188a71a0cd2
egglog-experimental/dd/tests/rewrite_join.rs
6496d67a3c0d4892febe59a1901176e3d1f71c7f0f055ad5f90b0438fd4e6ea4
egglog-experimental/duckdb/src/action_rule.rs
3e9182a8f1d64946c57a378e8520d95b443ab6764adddd5e17ab75ad44e9609a
egglog-experimental/duckdb/src/merge_program.rs
46bb5c4fe70b68cc584e409495ce201f6a01b18db2fb9048bc657a6337e74403
egglog-experimental/duckdb/src/storage.rs
b004ea6185b106b503b998e53c250645363f3c95155911229ec8878922ff0217
egglog-experimental/duckdb/src/rule_sql.rs
54695ca7e877b49260b676af593372d5e1fd3a5617c442434aa0339dcd65a04e
egglog-experimental/duckdb/src/action_rule_tests.rs
443d53f11c8ccebef3faf81d7f04f24f352ff8904ffc3818b3148ec88baec031
egglog-experimental/duckdb/src/general_action_tests.rs
d2caf04978878326b56b1521330ca05e5d3022165fcfc38387b13a32dc699f33
egglog-experimental/duckdb/src/lib.rs
0cd749d10d1a857c2834ba1480a6e3178ea5a53daf453ceb05cf10dc6cb8b9f4
```

The focused and broad gates on that code freeze are green:

- frontend index admission/execution: 9/9;
- backend-trait admission: 5/5;
- Reference bridge: 30/30;
- DD crate: 64/64;
- pinned DuckDB 1.5.4 crate: 167/167;
- crossed-target pre-fix observation: 0/2 with DuckDB `[100,100]` versus
  Reference `[200,200]`; post-fix: 2/2;
- restored exact two-graph canary: 1/1;
- DuckDB all-target Clippy with warnings denied, workspace formatting, and
  staged/unstaged diff checks;
- `make proof-tests`: 216/216 (208 core plus 8 experimental);
- `make rust-doc-links`, using the established prebuilt DuckDB environment;
- current-main Eggcc no-container fixture: 1/1;
- `index_probe.egg`: 3/3 and `index_any.egg`: 3/3 in their direct intended
  paths;
- the live DuckDB `--proofs egglog/tests/web-demo/eqsat-basic.egg` run exits
  zero with silent check output, and the explicit
  `egglog/tests/proofs/eqsat-basic-proof.egg` fixture also succeeds.

The required umbrella `make check` was attempted once under the 110-second
watchdog. It passed Python lock/format/lint/mypy, 172 pytest cases, workspace
tests/docs, and the DuckDB library, then was censored while compiling the final
feature CLI. Its remaining dependency leaves were run separately under their
own watchdogs: the CLI tests passed 4/4 and the DD timing test passed 1/1. The
aggregate is recorded as timeout-censored, not as a failed or completed
110-second run; every owned leaf is green.

Checkpoint 0 proves that current-main occurrence-indexed proof rebuild executes
through Design B in live DuckDB. It does not yet prove the checkpoint-3
standalone/canonical oracle. The web-demo EqSat command contains a plain silent
`check`; it discards proof columns. `make proof-tests` uses Reference. Therefore
proof-relation fidelity still requires the planned DuckDB proof-testing or
graph-aware Reference/live/standalone typed-relation comparison. Table sizes or
the silent check may never substitute for that gate.

The two pre-existing diagnostic traces remain untracked and byte-preserved:

```text
b4a704a281beff5221922c61826fc3e0c3fd74ca7833a11159e8b2492dc73b75  eqsat-basic-desugared-proofs.sql
d33be24d636e17274f3a69dcef51845e511e01c00bc3ef722a18ac3a4fbd518a  eqsat-basic.sql
```

### Checkpoint 1 frozen engine frontier (2026-08-05)

The primary engine is the official stock DuckDB 1.5.4 arm64 CLI at
`target/duckdb-cli/v1.5.4/duckdb`:

```text
release zip  d6c35195683fd1378e5624b01ca390069d399f8341c38986b7e3dfa0b3470d10
CLI binary   6c5abaff49f07ba3f6b2e41ed1adf338d10fcb2d98777331b285cc97938fb00a
version      v1.5.4 (Variegata) 08e34c447b
```

Homebrew DuckDB 1.5.5, SHA-256
`3d53a878a79787adcaaee28757e86f281366a062bebbffdb9ab57775a323be7e`,
is compatibility-only. All artifact execution remains exactly
`duckdb -safe -no-init -batch -bail -json :memory: -f program.sql`; generated
artifacts emit no `SET` statements.

Exact-safe-CLI depth probes on both engines found these first failures on the
smaller 1.5.4 boundary: nested expression 988, left-deep set operation 9979,
and CTE dependency edge 998. The compiler cap is therefore 75% of the smallest
first failure, rounded down to a multiple of 32: **736**. All three shapes pass
at 736 on 1.5.4 and 1.5.5; the cap is above the mandatory minimum 128.

The reduced stock kernel proves nested typed `STRUCT`/`LIST` keyed state,
zero-working full recompute, one-working seminaive branches with multiple
`recurring.state` reads, strict anti-diff termination, deterministic explicit
duplicate-key folds, parenthesized multi-branch recursion, a non-null surrogate
for nullary state, tombstone/reinsert/subsumption, checked error paths,
transactional durable counters, hostile strings, and the current one-Fresh
Packed_2 proof-maintenance hot SCC. Its exact final hot-SCC oracle has Packed
ids 100/101/102, View owners 1->10/41 and 2->15/42, UF owners 20->10/100 and
15->10/102, next fresh 103, eight steps, and an empty queue.

Accepted engine no-go facts are equally important:

- unqualified recursive CTE reads see only the working wave;
  `recurring.state` sees accumulated keyed state;
- DuckDB accepts two working reads, so IR construction and rendered-fragment
  lint must reject them;
- duplicate keyed output silently uses last-row replacement and identical
  replacement does not imply quiescence, so explicit folds and anti-diffs are
  mandatory;
- DuckDB has no recursive DML or mutually recursive named CTEs; one tagged
  nested state must represent a recursive region;
- sequences are not rollback-safe counters, and raw exceptions alone do not
  implement committed output-prefix semantics;
- arithmetic needs explicit definedness, and volatile error/fresh expressions
  cannot be hidden behind `TRY`;
- the historical two-Fresh proof recognizer and the two multi-megabyte SQL
  traces are stale relative to the current one-Fresh Packed_2 shape.

The next checkpoint-1 write set is intentionally narrow:
`egglog-experimental/duckdb/tests/fixtures/stock-duckdb-1.5.4-kernel.sql`, a
stdlib-only `scripts/check_duckdb_kernel.py`, and an optional explicit Make
target that requires a caller-supplied/provisioned `DUCKDB_CLI`. The harness
must verify the pinned SHA/version, reject `SET`, run the positive kernel twice
with byte-identical JSON, generate expected negative/two-working/#23677/depth
probes in a temporary directory, and leave normal `make check` independent of
an ignored local binary.

### Checkpoint 2 API frontier and scoreboard (2026-08-05)

The compile-only seam remains the final proof-instrumented, second-typechecked,
second-global-eliminated `Vec<ResolvedNCommand>` immediately before
`run_command`. Exposing current backend objects is unsound: `FunctionId`,
`RuleId`, primitive tokens, interned `Value`s, and existing `MergeFn`/`RuleSpec`
objects are backend-registry relative and lose source/catalog metadata.

The public snapshot must therefore own stable declaration-order symbolic IDs,
nominal sorts, typed literals, exact logical merge/rule IR, complete structured
schedules and ruleset membership, input provenance/typed rows, source command
and output ordinals, primitive requirements, and display/hidden/let/constructor
metadata. A linker may convert it to live backend objects; the standalone SQL
compiler consumes it without any connection. Whole-program capability
preflight precedes runtime IDs, counters, fact materialization, SQL publication,
or backend calls. A capture/no-op backend is not an accepted substitute.

| Checkpoint | State | Next proof obligation |
|---|---|---|
| 0 merge/current-main | accepted, uncommitted | intentional staging and merge commit |
| 1 stock engine | probes and hot SCC proven in `/tmp` | tracked deterministic kernel/harness |
| 2 compile-only API | seam and symbolic vocabulary frozen | lossless final-vector capture, then linker |
| 3 standalone EqSat | not started | compile/replay plus proof and canonical typed-relation oracle |
| 4 positive corpus | not started | Math, Pointer, Eggcc, Luminal static lowering and bounded replay |
| 5 benchmark integration | not started | compile-outside-timing backend and bounded correctness-first rounds |

#### Circle roster

| Circle | Artifact and write set | Forbidden shortcuts | Verification | Stop condition | No movement |
|---|---|---|---|---|---|
| integration/API | current merge; next symbolic snapshot/frontend linker | proof-role inference, backend capture, stale downstream helpers | focused frontend/Reference/DD/DuckDB tests, then root gates | a minimized current-main rule cannot be represented symbolically | no lossless command/catalog field added and no gate flipped |
| engine semantics | tracked stock kernel SQL plus Python harness only | UDFs, extensions, `SET`, host feedback, implicit last-row folds | exact safe CLI twice on pinned 1.5.4; 1.5.5 secondary; negative/depth probes | two materially different typed state layouts fail the semantic kernel within 110 seconds | no new engine fact, reduced reproducer, or passing kernel assertion |
| compiler lowering | snapshot and standalone SQL compiler/CLI after API slice | fallback, runtime Rust execution, callbacks, observed IDs/iterations in SQL | panic-on-backend compilation test, double-compile byte identity, safe-CLI parse/bind | two materially different typed-state compiler designs fail EqSat | no newly admitted IR node or lowered semantic canary |
| semantic oracle | read-only Reference/live/standalone comparison helpers and tests | size-only success, raw-ID equality for independent allocations, silent-check substitution | proof verification plus graph-aware alpha-normalized typed relations and reports | normalized durable/proof topology diverges after two distinct designs | no reduced discriminator or oracle surface added |
| artifacts/benchmarks | atomic bundle publisher, manifest, then `bench.py` DuckDB backend | partial publication, timed compilation, default cache pollution, timeout reported as pass/fail | double compile/replay digests, exact output events, fresh bounded run | completed workload mismatches canonical oracle | no new deterministic artifact or correctly classified workload |
| independent review | read-only refs, hashes, reached-shape census, gate reauthentication | workspace edits, staging, inferred success from table sizes | hash freeze plus code-backed PASS/BLOCKER and exact command evidence | concrete uncaught semantic counterexample | no new discriminator, authenticated hash, or closed blocker |

Immediate exact next command, after one final status/diff readback, is:

```text
git add -u
git add egglog-experimental/duckdb/src/merge_program.rs
git diff --cached --check
git status --short --branch
```

Then inspect the complete staged scope and create the no-ff merge commit. Do
not add `.codex/duckdb-native-sql/artifacts/` and do not push.

### Checkpoint 1 accepted stock-kernel slice (2026-08-05)

Checkpoint 0 was committed as merge commit
`f8d2f6ddc77cb76f2e8edcc9d5974168400e3f5a`; the earlier scoreboard wording
"accepted, uncommitted" is historical. Checkpoint 1 is now accepted by both
the implementation circle and an independent read-only review on these exact
candidate bytes:

```text
Makefile                 de18ecd2066711d4d38cf852f8c7685cc67397576b921d525e201bd5020bc802
kernel checker           511116c78a85a55ddd6904c792c8e918d6bc9d65f06ad3bf473c1e02f5e87d69
stock kernel fixture     a4b7c005dec22952ae2ae94edae256aaf016f325776601beb277545f21c81529
deterministic stdout     f93283bfa9f6f918d29574e3be82cf8abc9eb3f2237ecfc5f24f028ea5d11c66
```

The exact tracked gate is:

```text
DUCKDB_CLI=target/duckdb-cli/v1.5.4/duckdb make duckdb-kernel-check
```

It authenticates the official 1.5.4 CLI SHA/version, snapshots the pinned SQL
and a private copy of the CLI, executes that copy with only `LANG=C`,
`LC_ALL=C`, and a fixed system `PATH`, and runs the fixture twice under the
exact safe argv. The 27 statements produce 16 unique success documents and
byte-identical stdout. The optional 1.5.5 compatibility run uses the same
authenticated private-copy/minimal-environment path.

The tracked kernel covers typed nested state; zero-working full recompute and
one-working seminaive branches; multiple recurring reads; explicit ordered
duplicate folds; strict anti-diff; Delete -> Set/reinsert -> Subsume including
an omitted survivor; nullary keys without SQL `NULL`; Repeat 0/1/100000;
mandatory first Saturate iteration; nested last-child versus aggregate flags;
non-short-circuiting Sequence; the sticky target-batch latch; the current
one-Fresh proof-shaped hot SCC; checked arithmetic and lazy errors; explicit
rollback/retry of rows, generation, watermark, and fresh state; hostile
strings; and partial values represented by non-null `(defined, value)` state.
Twelve semantic mutations fail their intended oracle.

Rendered-fragment admission counts all unqualified working-source occurrences,
allows only exact `recurring.<cte>` qualification to escape that count, and
rejects more than one working read. Zero-working and one-working probes admit;
join/comma two-working, other-qualified, and quoted-source mutations reject.
The nullable filtered-rank canary reproduces the vulnerable two-row result and
the explicit three-term total-key mitigation returns all three rows.

Pinned 1.5.4 first-failure depths are unary expression 988, explicitly
parenthesized left-deep set operation 9979, and CTE dependency 998; flat
`UNION ALL` passed through 50,000 operators. The compiler-owned cap remains
736 and adjacent-boundary probes agree on 1.5.5.

One obligation is explicitly deferred rather than claimed: with
`-bail -json :memory:` a fatal statement closes the sole process/connection,
so the harness cannot inspect automatic post-error rollback. Checkpoint 1
proves explicit rollback. Automatic rollback of one source command while
retaining earlier committed commands and output events is a blocking
checkpoint-3 standalone command-transaction test.

The production architecture is **Design B** by user decision. Exact stable
function identity, resolved generic `RuleSpec`, and the exact typed logical
`MergeFn` determine semantics. The generic merge program is the sole
scalar-action production path. Function names, proof-role names, schema shape,
and registration order are metadata only and may not select behavior;
same-schema decoy functions must execute literally in snapshot/compiler tests.

The next frontier is checkpoint 2: introduce the public owned nominal snapshot
at the final proof-instrumented/typechecked/global-eliminated seam, together
with pure capture and round-trip/linker tests that panic if capture invokes a
backend. Preserve both proof-check/provenance and execution streams, parse each
input batch once, and keep exact target identity plus typed merge/rule IR.

### Checkpoint 2 slice A accepted: backend-free resolution substrate (2026-08-05)

The first checkpoint-2 slice establishes a real backend-free frontend mode. It
does not install a no-op backend: `BackendSlot::CompileOnly` contains only
deterministic frontend sort/primitive token state and no `dyn Backend`. Any
accidental execution-backend dereference panics at the access boundary.

The crate-private `EGraph::new_compile_only` and
`resolve_program_compile_only` path now reaches the complete proof
instrumentation, second typecheck, and second global-removal pipeline while
returning both finalized execution and pre-proof-check streams. `Push` and
`Pop` remain in the stream for fail-closed standalone preflight but are never
executed. Proof resolution registers the typed `get-fresh!`, set-if-empty, and
view-column operations using synthetic typechecking tokens without evaluating
backend registration callbacks.

Accepted bytes:

```text
egglog/src/lib.rs                              9069b1e0c21f242311938440c89da505a6f7eb3a1328a4c8c431f7a57cffc9a8
egglog/src/typechecking.rs                     4735a59359d7443bf7e615b45ab37741fdc5bcf579cf5dfbd8b186d6219044a5
egglog/src/proofs/proof_fresh.rs               830c8713757771bcfee604060fc00ded0d3061ef22e4177c2a78c0481be910cf
egglog/src/proofs/proof_container_rebuild.rs   e8376e63defdae550c2aa4d6c3bcdafcb206848db8b8c7b151da20022fb971d4
```

Validation passed: three focused compile-only tests, all 97 egglog library
tests, runtime Push/Pop regression, EqSat term-encoding roundtrip, library
check, clippy with warnings denied, formatting, diff check, and an independent
read-only review. The root reauthenticated the exact hashes and focused tests.

This is substrate only, not the public snapshot and not a checkpoint-2
completion claim. Current finalized commands still contain registry-relative
primitive context tokens, and term/proof input preparation still parses a fact
file once for proof-check actions while standalone execution would otherwise
parse it again. The next slices must:

1. publish owned nominal sort/function/primitive/rule IDs and typed literals;
2. retain explicit primitive authority descriptors rather than infer from
   names or backend `ExternalFunctionId`s;
3. prepare the exact typed lazy merge program and generic `RuleSpec` once, then
   structurally bind stable IDs for live execution or consume them directly for
   SQL;
4. own each typed input batch from one read and feed proof and execution views
   from that same ordered payload;
5. add command/source/output ordinals and the exact print/check/schedule
   metadata before exposing the public snapshot API.

The public merge IR must preserve root-driven evaluation: ordered action roots,
then result roots; lazy Function argument evaluation behind the owner old/new
guard; Lookup's old-value fallback; and all Union/UnionId operands even when a
consumer rejects them. DuckDB-private linked `MergeProgram` is not this public
IR and must not be promoted as one.

### Checkpoint 2 slices B/C accepted: nominal core and typed input (2026-08-05)

The next checkpoint-2 substrate is accepted on parent commit
`529e3a23fd5e008e038a40c762c97043e2f05a17`. This remains an intermediate
slice, not completion of the public compile-only snapshot and not a standalone
SQL compiler claim.

`frontend_snapshot` now publishes a backend-neutral, command-neutral core DTO
with dense nominal `SortId`, `FunctionId`, specialized `PrimitiveId`, `RuleId`,
`RulesetId`, merge-value IDs, rule variables, and merge-let slots. It owns exact
typed literals; scalar and Eq/container sort semantics; function schemas,
defaults, identity-value prefixes, subsumption and display metadata; explicit
primitive authority; generic rule atoms/actions including occurrence-index
reads; and exact ruleset membership.

Design B remains the only semantic route. All references use exact IDs. A
function or primitive name is diagnostic only, and same-schema/same-name decoys
remain distinct. The public lazy merge arena specifies ordered action roots
followed by result roots, explicit old/new owner guards, Lookup fallback to the
owning old value, exact Function/Lookup/Set targets, and every Union operand.
`SetIfEmpty` intentionally accepts tuple proof-FD views: its input is the full
key-plus-all-values schema and its fixed scalar result is value column zero.

Validation is fail-closed and iterative. It checks dense identity arenas,
nominal arity and type equality, scalar-sort uniqueness, ruleset-local rule-name
uniqueness, union authority, subsumption capability, fixed-point occurrence
reachability, exact index probe/full-row/Unit shape, lazy merge roots and slots,
and the global Function/Lookup/SetIfEmpty/ViewColumn read-dependency DAG. A
20,000-node merge-chain canary establishes stack-safe validation.

Primitive registrations now receive a deterministic frontend-owned
`PrimitiveRegistrationId` and an explicit `PrimitiveAuthority` at their
registration site. Resolved primitive equality/hash uses that registration ID
plus exact specialization sorts, never backend callback tokens. Runtime
dispatch still uses its context-specific external-function token. Proof fresh,
set-if-empty, view-column, and UF-column registrations retain their exact target
view/column authority for later fail-closed nominal linking.

`typed_input` owns the exact byte buffer from one logical file read, path
metadata, resolved/effective schema, ordered duplicate rows, source row and
physical-line ordinals, and exact scalar values including f64 bits. Its target
is the snapshot's concrete nominal `FunctionId`; arbitrary generic/backend
handles cannot enter the DTO. Schema preflight rejects invalid constructor and
custom-function output arities before I/O while preserving the current TSV,
trim, Unit, constructor/custom, nullary, and all-Unit behavior.

Accepted bytes:

```text
egglog/src/frontend_snapshot.rs               ac74d48bf13d97ae1d3e9712e36ff540cecda929bb83df695298bf8ee511f1c9
egglog/src/typed_input.rs                      dcfd7935e3d35b8a06602ffea6f76904300a26e1872f0dcb75f3b5f626aa39ca
egglog/src/core.rs                             0b668ce565ffc2522a583f3acefd353fc8ff7f2f1e6d3f9b9b0a7a60f042a929
egglog/src/typechecking.rs                     26d6a53e20c07f49ee942771a09de3cb98874698730f5badce7f31def1f36693
egglog/src/lib.rs                              39464a1b82c4ec052ccaecfb6697170dbf4dd49ce762a8328b8ee8b272ad3e27
egglog/src/proofs/proof_fresh.rs               b90ab4b66592346591decbd59857879231df8b8df50e119002233d9168808216
egglog/src/proofs/proof_container_rebuild.rs   646d93bb60b817864d25f17f15b1ce500a7ae7bd76d7c3b69d57f203f72dd171
```

Validation passed on the final bytes: 16/16 nominal-snapshot tests, 13/13
typed-input tests, 128/128 Egglog library tests, all 810 file/proof corpus
cases, all remaining package integration and doctest groups, workspace/all-
target compilation, strict Clippy, rustdoc with warnings denied, formatting,
and `git diff --check`. Independent read-only review reauthenticated the two
new public modules and returned PASS after its findings were repaired.

One non-admission debt is frozen explicitly. Compile-only resolution retains
Push/Pop without restoring frontend scope, so declarations inside a pushed
scope can remain in its private `TypeInfo`. Push/Pop are unsupported by the
standalone compiler. The next public snapshot entrypoint must scan and reject
either command before nominal catalog, rule, primitive, or input capture; no
leaked state may become an admitted snapshot or artifact. Do not broaden this
substrate by invoking `run_command` or installing a backend.

Checkpoint 2 still requires:

1. a full public envelope with explicit index declarations, primitive context
   and effect masks, full rule evaluation/include-subsumed modes, costs and
   unextractable metadata, structured schedules, commands, checks/prints/input,
   and source/output ordinals;
2. a pure capture/linker from both finalized compile-only streams to nominal
   catalogs, exact merge programs, and generic `RuleSpec`s;
3. registration-ID plus authority linking to exact nominal primitive and
   function IDs, with same-name/schema and registration-order decoys;
4. one owned input payload shared by proof and execution views; and
5. panic-on-backend and double-capture byte/digest determinism gates.

The next implementation slice is the early command preflight plus full snapshot
envelope and pure nominal capture mapper. Its first focused verification command
after adding the mapper tests is:

```text
cargo test -p egglog frontend_capture --lib
```

### Checkpoint 2 slices D/E accepted: exact bindings, source groups, and reached scalar authority (2026-08-05)

Design B remains the sole production architecture. This accepted intermediate
slice removes three more post-resolution inference surfaces without claiming a
complete public capture mapper or standalone SQL compiler.

Resolved variables now carry exact `ResolvedVarBinding` authority:

- lexical occurrences use a monotone `ResolvedBindingId` allocated by the
  frontend and shared by their declaration and every use;
- globals carry the exact `FunctionRegistrationId` selected at their source
  position, including historical registrations whose names have left scope;
- merge `old`/`new` values and action lets carry exact owner-local column/slot
  roles rather than being recovered from `old0`/`new0` spellings;
- equality, hashing, query/action lowering, global removal, proof
  instrumentation, proof replay, normal-form generation, and head planning
  consume those authorities while preserving names only for diagnostics and
  public proof rendering.

The trusted proof-substitution boundary now records only exact lexical body
bindings. An all-program global with the same later spelling cannot suppress
or capture an earlier rule local; the full parse/run/check/prove witness passes.
Synthetic proof binding generators observe the source high-water before
allocating, so independently generated names cannot alias exact authorities.

The source DTO now owns one lossless UTF-8 `SourceDocument`. Its exact byte
partition consists of dense physical `SourceGroupId` transaction boundaries,
group-local `SourceSubcommandId`s, leading trivia, command ranges, and one EOF
trailer. Direct and generated origins are exact, nested `Fail` commands cannot
cross a physical group, input comparisons are group-keyed, and every parsed
subcommand is covered directly. `Run` remains silent; only admitted
`print-size` and displayed no-file `print-stats` commands consume output
ordinals. The grouped parser is the sole source of these ranges; text/comment
reconstruction is forbidden.

Reached corpus scalar authority is now registration-site data for fallible i64
`>`, fallible i64 `<=`, total `bool-<`, and polymorphic proof `select-eq`.
The DuckDB scalar lowering authenticates the exact primitive tag and checked
signature. Same-name/same-schema opaque registrations remain literal decoys.
`select-eq` lowers `(T,T,P,P)->P` with raw value equality, including the
frontend's f64 NaN behavior, rather than inferred proof-table meaning.

Accepted hashes after formatting:

```text
egglog/src/frontend_program.rs                 e1c8573ab8f877194c29e50bc2996d0eb46d805458c9791b25eb562255cc2ca6
egglog/src/ast/parse.rs                        8bedec512837ffe493fc3ec398d3be89eb47fd79574cf0ed5427e338551f086a
egglog/src/ast/expr.rs                         24c5073022739df67ecf4dcec8b03f1f80d22a4d9aeb5fe4dffa5202b21c4e40
egglog/src/typechecking.rs                     ba5bf82a54130fd809091a8ff0397bc1b87ed2d8e30ba7d668ccf598b68247d0
egglog/src/proofs/proof_checker.rs             481863e2116c638ccd845585e1cd32c12a6f3138ba8d8b4012df87301e30953f
egglog/src/proofs/proof_format.rs              ff5d836d0edb66c3a6707a0423dc0b7628548caa3d0e832bad14656c42bad8d0
egglog/src/frontend_snapshot.rs                908c70451a4f0df692836916e28edb0e3804dad7157ff5404bb761aef9f488f3
egglog/src/typed_input.rs                      fc2801a980cb759bd38803560f348d6132d2a2298cd12b38092a84b0ec8da150
egglog/egglog-backend-trait/src/lib.rs         f88016e9427de0aec829dcd26cdb0096a20c10fbcebeae4f71292b6cb1738d34
egglog/src/sort/i64.rs                         0ab09802d0b5091d82ae74dbb85f14bdfe07c99d5093baef3ec73e96c7eae41a
egglog-experimental/duckdb/src/scalar_expr.rs  a1444f7b52fe5674b4a0de528a925b549b591c15a5a4e429b44b549d659f20a6
```

Validation on the final formatted bytes:

```text
cargo test -p egglog --lib                                      208 passed
cargo test -p egglog-experimental-duckdb scalar_expr_tests:: --lib  10 passed
cargo check -p egglog-experimental-duckdb --lib                 passed
cargo clippy -p egglog --lib --tests -- -D warnings             passed
make proof-tests                                                passed
cargo fmt --all -- --check                                      passed
git diff --check                                                passed
```

Independent reviews passed the lexical/proof authority surface and the exact
source-document DTO. The remaining review blockers are deliberately outside
this accepted slice:

1. sorts still lack a stream-local `SortRegistrationId` ledger, so resolved
   primitive specializations and `Values` still compare sort spellings;
2. runtime function/index lowering still resolves typechecked `FuncType`s by
   diagnostic name instead of exact registration ID;
3. `term_constructor`, targeted proof primitives, and `unstable-fn` still need
   exact target authority (including catalog-local UF forward reservations);
4. compile-only processing still flattens source groups before the pending pure
   mapper, and proof/native input preparation is not yet one shared read.

Accepted no-go facts: raw registration ordinals are view-local and may never be
compared between execution and proof-check streams; sort/function/primitive
names, schemas, Rust value types, and declaration order cannot recover semantic
authority; an exact lookup miss fails closed; generated proof roles may not be
recognized from table shape or prefix.

Circle roster for the next frontier:

- integration/API owns the grouped compile-only entrypoint and public mapper;
  write set is `frontend_capture.rs` plus narrow `lib.rs` plumbing; forbidden
  shortcut is flattened text reconstruction; verify with
  `cargo test -p egglog frontend_capture --lib`; stop on any backend access;
- engine semantics owns the already-pinned stock kernel and makes no writes in
  this slice; forbidden shortcut is host feedback; verify with
  `make duckdb-kernel-check`; no movement means no new accepted kernel claim;
- compiler lowering owns exact sort/function/primitive target carriers and the
  runtime exact registry; forbidden shortcut is a name/schema fallback; verify
  with diagnostic-mutation and same-name decoy tests; stop on any unresolved
  nonbuiltin sort arc;
- semantic oracle owns proof substitution and later-global regressions; write
  set is proof-only canaries; forbidden shortcut is table-size-only evidence;
  verify with `make proof-tests`; no movement means no new proof parity witness;
- artifacts/benchmarks remain read-only until the public snapshot validates;
  forbidden shortcut is trace harvesting; verification is byte-identical
  double capture; no movement is expected before mapper admission;
- independent review is read-only across each finished carrier slice; forbidden
  shortcut is accepting diagnostic inference as nominal identity; stop on the
  first concrete counterexample.

Exact next command after committing this accepted substrate:

```text
cargo test -p egglog sort_registration --lib
```

### Checkpoint 2 slice F accepted: producer-stamped sort authority (2026-08-06)

Design B is now the sole architecture. Exact resolved function, index,
primitive, binding, and sort registrations are semantic authority. Names,
textual schemas, Rust storage types, declaration order, and equal numeric
ordinals from different frontend views are diagnostic/display data only. No
Design A fallback or proof-role inference remains in this slice.

Every admitted sort now receives a monotone, stream-local
`SortRegistrationId`. `TypeInfo` owns O(1) indexes for its canonical arcs,
explicitly linked sibling-view arcs, and the seven exact builtin definitions.
Resolved specializations retain canonical local arcs; an unstamped lookalike
fails closed. Pop, parser replacement, proof-view cloning, and compile-only
rollback preserve the high-water marks so retired authority is never reused.
Primitive registrations are view-qualified, while raw `ResolvedCall` and
`FuncType` equality is explicitly local-catalog only.

`FinalizedProgram` carries a private recursive `SortAuthorityAt` sidecar. Its
command paths cover exactly every nested `Sort`, and producer stamps are
remapped through macro expansion, proof normalization, input lowering, global
elimination, term encoding, append, and nested `Fail`. Proof admission and
proof instrumentation consume that exact sidecar. Container meaning is read
from the producer-stamped registration rather than `presort_and_args`, a sort
name, or a storage shape. The constructor/custom-function proof gate likewise
uses the exact resolved `FunctionSubtype` and exact output sort; a regression
canary protects ordinary constructors from the custom `:no-merge` rejection.

`BaseSort` and `ContainerSort` expose a canonical-self registration hook, and
presort families are stamped by exact producer `TypeId`. Maybe, Either, Vec,
MultiSet, Set, Map, Pair, and UnstableFn specializations use those identities.
Same-name, same-schema, and same-storage decoys remain literal decoys. A legacy
extension that constructs a fresh custom `to_arcsort()` inside a later
constraint must migrate to the canonical-self hook; guessing its meaning would
reintroduce Design A and is intentionally forbidden.

Authenticated implementation digest before this state append:

```text
HEAD before checkpoint commit                     6eb81a06ba5f35fa2883be88bbdb752983f7fda3
independent scoped Design B digest                 81db004d05843ff121f19fcc739fd9dbf981e5902895b0a760332543e9eef496
egglog/src/frontend_program.rs                     e59486472c1b418e314a00b9b16f395a4b700c65384c0e4b5dff29462f605630
egglog/src/frontend_snapshot.rs                    fb0336f418f5f1cbdc9ce7f305a105984e5a810d706a398c1c26d5607c3f89aa
egglog/src/core.rs                                 5e8d831fa2f2218d8917e0ab0e69aeec87a06abe8b37adec78b495edb5afdfa6
egglog/src/typechecking.rs                         d8df448d9a8a0e70d319e184f09475b585073cb18c5c75acfd4a0c227fc8aaa3
egglog/src/proofs/proof_encoding.rs                3f01ccab5f715971ea89b8e895813724c2754ff96c698170d068e64d1e316bb9
egglog/src/proofs/proof_encoding_helpers.rs        b6c35c4742b7245c228a2068a4f0a0f2f26c3de7780b71c22494cf08623c64ef
egglog-experimental/src/container_primitives.rs    79cb75010ae9435236de82cae72479924af238cee71edd0831c2ff1d80cd98d9
```

Validation on the final implementation bytes:

```text
cargo test -p egglog --lib                                      236 passed
cargo test -p egglog-experimental --lib                           2 passed
cargo clippy -p egglog --lib --tests -- -D warnings              passed
cargo clippy -p egglog-experimental --lib --tests -- -D warnings passed
make proof-tests                                                  passed (216 cases)
cargo fmt --all -- --check                                       passed
git diff --check                                                  passed
independent final-byte Design B review                            PASS
```

Accepted no-go facts and risks:

1. Raw resolved-call equality is local-catalog only; the snapshot mapper must
   qualify execution and proof streams separately and must never compare raw
   ordinals across them.
2. Fresh legacy custom-sort wrappers fail closed. The supported migration is
   the explicit canonical-self registration hook, never name/type/shape
   recovery.
3. `TypeInfo::add_presort` now requires a `'static` producer so it can carry
   exact `TypeId` authority; lifetime-parameterized downstream presorts require
   an explicit redesign rather than heuristic compatibility.
4. Primitive-registration callback panics restore the detached proof view, but
   the broader registration operation is not promised transactional if an
   external caller catches that panic.
5. Runtime `Fail` stops at its first failing child while typechecking remains
   eager. The standalone mapper must model the runtime first-error/output-prefix
   contract and may not treat later typechecked auxiliaries as executed.

Scoreboard: checkpoint 0 merge/integration and checkpoint 1 stock-DuckDB kernel
are complete. Checkpoint 2 now has exact nominal function/index/primitive,
binding, scalar, and sort authority, but grouped physical-source capture and
the pure two-view mapper remain open. SQL emission, EqSat standalone replay,
the four-workload corpus, and benchmark integration remain pending.

Circle roster for the next frontier:

- integration/API owns `frontend_capture.rs` plus narrow parser/`lib.rs`
  plumbing; it must preserve physical groups, zero-command groups, exact
  subcommand ranges, and EOF trivia; flattened text reconstruction is
  forbidden; verify with `cargo test -p egglog frontend_capture --lib`; stop
  on any backend access or ambiguous producer fan-out;
- engine semantics is read-only because the stock kernel is already pinned;
  host feedback and backend callbacks remain forbidden; no movement is
  expected until a real snapshot reaches lowering;
- compiler lowering owns the later exact runtime-function registry and pure
  mapper link; it may consume exact IDs only; verify with same-name/schema
  decoys and cross-view qualification; stop at the first unresolved carrier;
- semantic oracle owns source-group, first-error, proof-sidecar, and output
  prefix canaries; table-size-only evidence is forbidden; verify with
  `make proof-tests` after each captured-view change;
- artifacts/benchmarks remain read-only until whole-program preflight and
  byte-identical double capture pass; trace harvesting is forbidden;
- independent review remains read-only and reauthenticates every accepted
  carrier slice; accepting diagnostic inference is an immediate stop.

Exact next command after this checkpoint commit:

```text
/opt/homebrew/bin/timeout 110 cargo test -p egglog frontend_capture --lib
```
