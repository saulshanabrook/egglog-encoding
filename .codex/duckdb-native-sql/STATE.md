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
