# Standalone DuckDB SQL campaign: reviewed status and evidence

Campaign window: 2026-07-21 through 2026-08-06. Reviewed against the branch on
2026-08-12.

| Field | Value |
| --- | --- |
| Branch | `agent/duckdb-native-sql` |
| Pre-review branch head | `a8ddcf111e347f99f29ee68186b0ce7938ecfb4b` |
| Accepted main snapshot merged at checkpoint 0 | `6ef88f13b6b6be244e961807a19d95cb35c4140b` |
| `origin/main` at the final review refresh | `7600c1927f6a4bb1834e63ae1b0a5f563631e578` |
| Divergence at the final review refresh | branch has 27 unique commits; `origin/main` has 39 unique commits |
| Durable campaign ledger | [`.codex/duckdb-native-sql/STATE.md`](.codex/duckdb-native-sql/STATE.md) |

This document is both an implementation handoff and a condensed retrospective.
“Accepted” below means that the recorded checkpoint received its required gates
and independent review. “Validated now” means a command was rerun during this
2026-08-12 review. “Diagnostic” means useful evidence that is not a product
artifact or correctness oracle.

> **Status: incomplete.** Checkpoints 0 and 1 are accepted at their recorded
> commits. Checkpoint 2 has accepted substrate through `4d3fa0e`, followed by
> unaccepted WIP commit `37b48ca`. There is no `StandaloneSqlCompiler`,
> `egglog-duckdb-compile`, generated `program.sql`, or `manifest.json` in the
> repository. Checkpoints 3–5 have not started. The committed SQL files are
> Rust-driven transcripts or a hand-written bounded feasibility probe, not
> compiler deliverables. A fresh `make check` also remains red on the two known
> ungrounded-variable snapshot mismatches.

## Executive assessment

The target-compiler decision remains **Design B**: every admitted resolved
`RuleSpec` and typed merge must lower by its generic semantics. Unsupported
forms fail closed. No production compiler path may infer an internal proof role
from a name, schema, registration order, or familiar rule shape. Design A, the
specialized proof-maintenance recognizer, was correctly rejected because those
properties are spoofable. The existing live backend is narrower: its generic
path covers the reached scalar-action vocabulary, while compatibility-only
rebuild, path-compression, marker, observer, and direct routes remain. Those
specialists are evidence sources, not authority for the standalone compiler.

The evidence supports continued work, but it proves less than the previous
version of this report claimed:

- The live Rust-orchestrated DuckDB backend has executed the repository's
  occurrence-indexed proof rebuild and real EqSat and Pointer workloads. This
  is evidence for the generic typed execution semantics, not for a standalone
  compiler.
- The stock-DuckDB kernel and bounded hand-written prototype show that the
  required recursive-state mechanisms are available. They do not prove that
  the repository's post-instrumentation program can be lowered, executed, and
  compared across the three execution paths or proof-checked.
- The compiler frontend is partly built, but its exact-authority carrier is not
  yet complete enough to activate. SQL emission has not begun.
- Performance is descriptive. The campaign does not require DuckDB to beat the
  reference backend, and there is no standalone performance result to report.

The immediate risks are frontend authority and source drift, not a newly found
DuckDB expressiveness blocker. The current `origin/main` changes four of the
eight WIP files and has since removed the backend-trait and Differential
Dataflow crates. That upstream architectural change also affects how the
Reference/live-DuckDB/standalone oracle can be integrated. The original plan
deliberately froze main once, so a second merge must be an explicit maintainer
decision and architectural reassessment. Until then, “current-main” claims
refer only to the main snapshot frozen on 2026-08-05.

### Decision required before further implementation

| Choice | Consequence |
| --- | --- |
| Keep frozen `6ef88f1` | Preserves the byte-specific checkpoint-0 acceptance and current checkpoint-2 review base, but knowingly defers integration with 39 newer upstream commits. |
| Merge and refreeze on `7600c192` | Preserves the continuation brief's current-main requirement, but reopens checkpoints 0 and 2 and requires an architectural reassessment. Upstream changes four WIP-overlap files—`ast/desugar.rs`, `ast/mod.rs`, `lib.rs`, and `typechecking.rs`—by 517 insertions and 712 deletions. Since the earlier review fetch, upstream changed 85 files (`+808/−8983`), including deletion of the backend-trait and Differential Dataflow crates and a `lib.rs` rewrite. |

If “current main” remains a hard requirement, merging and refreezing is the
recommended choice, but the reassessment must explicitly replace or retire the
campaign's deleted backend-trait and DD dependencies and redefine the oracle's
live-backend integration. Do not extend checkpoint 2 or start the emitter until
the choice and disposition are recorded; this report-only review does not make
them implicitly.

## Continuation target contract

The continuation brief supplied for this review defines the following planned
contract. This section preserves its public names and design decisions in the
repository; it does not imply that those APIs have been implemented or
accepted. The target is stricter than the historical recursive-CTE plan
committed under `reports/duckdb-sql/`:

1. Resolve, proof-instrument, typecheck, and eliminate globals without invoking
   any backend. Compile one filesystem Egglog source plus an optional fact
   directory into an atomic bundle containing deterministic `program.sql` and
   `manifest.json`. Compilation captures, hashes, types, and embeds all
   referenced input bytes; runtime performs no input-data file reads.
2. Execute the artifact only as:

   ```text
   duckdb -safe -no-init -batch -bail -json :memory: -f program.sql
   ```

   The generated SQL contains no `SET`, extensions, UDFs, callbacks, host
   feedback, Appender, `read_csv`, `COPY FROM`, unsafe code, or private API.
3. Use ordinary typed program relations plus SQL-owned schedule/counter state.
   Proof relations and encoding-generated union-find relations go through the
   same generic path as user functions.
4. Compile the exact structured core schedule. `Repeat` and `Saturate` use one
   recursive controller rather than textual unrolling; `Run` retains stable
   pre-wave matching and global Delete → Set/merge → Subsume effects.
5. Fail closed before publication on unsupported constructs or missing
   authority. No fallback is permitted.
6. Preserve source-ordered `print-size` events and normalized no-file
   `print-stats`. A silent check, equal table sizes, or a trace replay may not
   substitute for proof verification and canonical typed-relation comparison.
   The three-way relation oracle compares the Reference backend, the live
   Rust-driven DuckDB backend, and standalone SQL under graph-aware,
   sort-preserving alpha-normalization of allocated IDs; proof checking is a
   separate required gate.
7. Gate architecture first on the real
   `egglog/tests/web-demo/eqsat-basic.egg --proofs`, then statically lower and
   make one bounded stock-CLI attempt for Math, Pointer, bounded Eggcc, and
   Luminal. Hardboiled and Herbie are not positive standalone milestones.

The [historical recursive-CTE plan](reports/duckdb-sql/recursive-cte-plan.md)
predates the merge, targets an earlier proof encoding, and permits a generic
host driver as a second artifact tier. It is useful engine research but is not
the current product specification. Its companion
[plan review](reports/duckdb-sql/plan-review.md) reviews a saved plan that is not
itself committed; its empirical amendments were folded into the stricter
contract above.

## Checkpoint status

| Checkpoint | Reviewed status | What is and is not established |
| --- | --- | --- |
| 0. Merge frozen main and repair generic Design B execution | **Accepted** at merge `f8d2f6d` | The 2026-08-05 main snapshot, including occurrence-indexed proof rebuild, executes through the live backend. This is not a claim about the 39 newer upstream commits or standalone SQL. |
| 1. Stock engine capability gate | **Accepted** at `26e558c`; validated again 2026-08-12 | The SHA-pinned official DuckDB 1.5.4 CLI passes the tracked reduced kernel, admission lints, and depth probes. The checkpoint review also ran twelve semantic mutation canaries. Automatic rollback after a fatal source-command statement remains deliberately deferred to checkpoint 3. |
| 2. Compile-only frontend API | **In progress** | Accepted slices `529e3a2` through `4d3fa0e` provide backend-free resolution, nominal DTOs, exact identities, typed input parsing, grouped source capture, command origins, and transactional originated type/global lowering. WIP `37b48ca` is not accepted. |
| 3. Standalone EqSat compiler gate | **Not started** | No compiler/emitter, CLI, manifest, generated golden bundle, safe-CLI bind, three-way oracle, or proof verification exists. |
| 4. Four-workload positive corpus | **Not started** | No full-program standalone preflight or replay exists for Math, Pointer, Eggcc, or Luminal. |
| 5. Benchmark integration | **Not started** | `bench.py` has no compile-then-stock-DuckDB standalone backend or four-workload DuckDB suite. |

### Validation refreshed on 2026-08-12

The pre-review head was clean and equal to its remote before this report edit.
These fresh bounded commands were run:

| Command | Result |
| --- | --- |
| `cargo test -p egglog --lib` | 294 passed |
| `make proof-tests` | 208 core + 8 experimental passed |
| DuckDB crate library test under the established prebuilt environment | 167 passed |
| live `egglog-experimental --backend duckdb --proofs egglog/tests/web-demo/eqsat-basic.egg` | exit 0, silent check output |
| `make rust-nits` | format, all Clippy lanes, and private-item rustdoc passed |
| `DUCKDB_CLI=<official-1.5.4-cli> make duckdb-kernel-check` | authenticated kernel gate passed in a read-only artifact-audit temporary directory |
| `make check` | **failed** in `rust-test`: 808 passed and 2 snapshot assertions failed, `fail-typecheck/ungrounded_3` and `ungrounded_4` |

The focused DuckDB, proof, and lint gates pass, but the branch is not
workspace-green. In the failing snapshots, the expected first ungrounded
variables were `b` and `c`; the current result selected `a` in both cases. The
test also proposed routine snapshot source-metadata changes. Generated
`.snap.new` files were removed without accepting either semantic change. This
review did not rerun an archived checkout, but the prior checkpoint audit
reproduced the same failures on clean archived HEAD. The evidence therefore
does not attribute them to the WIP, though the full-gate failure remains a
branch-level blocker.

None of these results convert `37b48ca` into an accepted checkpoint: the
schedule work still lacks its required independent review and producer
integration, and the runtime-registry draft is not compiled at all. The live
EqSat command checks a user relation while discarding proof columns; it is not
the planned canonical proof-relation oracle.

## Evidence and planning artifacts—not compiler deliverables

| Artifact | Classification | Current finding |
| --- | --- | --- |
| [Stock 1.5.4 kernel fixture](egglog-experimental/duckdb/tests/fixtures/stock-duckdb-1.5.4-kernel.sql) and [checker](scripts/check_duckdb_kernel.py) | Accepted reduced engine gate | The 1,207-line, 27-statement fixture yields 16 deterministic success documents; its runner also executes generated admission, filtered-rank, failure-prefix, Repeat-shape, and depth probes. Twelve semantic fixture mutations were checkpoint-review evidence, not part of every tracked rerun. The gate covers selected dependencies, not “every behavior the compiler will rely on.” |
| [Proof-mode transcript with desugared comments](.codex/duckdb-native-sql/artifacts/eqsat-basic-desugared-proofs.sql) | Historical diagnostic transcript | Rust emitted 5,795 statements after observing a run. It contains two configuration `SET` statements, 58 `UPDATE` statements, and 29 unmatched `ROLLBACK`s; exact safe 1.5.4 rejects it at the first configuration change. Tolerant replay plus an appended audit readout reaches generation 8, fresh ID 318, and 48 tables. |
| [Proof-mode transcript with source-level comments](.codex/duckdb-native-sql/artifacts/eqsat-basic.sql) | Historical diagnostic transcript | After comments are removed, its executable SQL is byte-identical to the other transcript. Both files identify themselves as `--proofs`; the earlier report's “plain and proofs mode” description was wrong. Both reflect the stale two-Fresh encoding rather than the accepted one-Fresh `Packed_2` shape. |
| [Recursive-CTE EqSat-style prototype](reports/duckdb-sql/recursive-cte-prototype-eqsat.sql) | Hand-written feasibility probe | Passes exact safe DuckDB 1.5.4. It runs 10 bounded rewrite waves because its reassociation/commutativity system does not terminate, then lets maintenance reach a fixed point under a safety cap of 500. It models EqSat-style mechanisms; it is not this repository's encoding or compiler output. |
| [Recursive-CTE plan](reports/duckdb-sql/recursive-cte-plan.md) | Historical research plan | Useful for `USING KEY`, tombstones, deterministic folding, and recursive-state design. Superseded where it permits host iteration, textual `run N` unrolling, compiler fuel, extraction/output, or pre-merge proof shapes. |
| [Merge-first plan review](reports/duckdb-sql/plan-review.md) | Historical review evidence | Correctly caught large-`N` unrolling, output-command scope, safe-mode/depth constraints, and the working-reference lint. Some engine wording is corrected below. |

The transcript replays are not acceptance tests: they embed observed match
counts, fresh bases, generations, and loop decisions; they expose internal
queries; and they cannot execute under the target safe/bail invocation. Their
recorded state is useful for diagnosis only.

## Checkpoint-2 frontier and exit criteria

Commit `37b48ca` was created only to preserve interrupted work. Its actual diff
is **2,029 insertions and 42 deletions across eight files**, not the six-file
`+569/−42` diff reported previously.

It contains two materially different drafts:

- `schedule_origin.rs` and related plumbing are compiled. Fresh tests cover
  total recursive preorder addresses, exact source/generated anchors,
  Repeat-shape independence, composition, append rebasing, global elimination,
  and several corruption cases. This is promising but unaccepted until an
  independent review authenticates the carrier and proof producers emit the
  required adjacent maintenance topology.
- `runtime_function_registry.rs` is a 407-line unreferenced module. Because
  `lib.rs` does not include it, neither compilation nor the fresh test runs
  exercised it. It must be reviewed and integrated as a separate slice or
  removed; its presence is not checkpoint progress.

Checkpoint 2 cannot activate until all of the following are true:

1. Replace the sparse caller-supplied `Vec<SourceSortAuthorityAt>` with a total,
   private, producer-bonded disposition for every recursive `Sort`, including
   exact view and linked/local-only intent.
2. Replace the legacy live `desugar_term_encoded_command`/`SortLineage` adapter
   atomically. No final snapshot or compiler path may route through its
   assertion-based association.
3. Integrate exact schedule origins into every producer, including proof
   maintenance adjacent to each `Run` and the separately generated final
   maintenance schedule. Preserve nested `Repeat`, `Saturate`, and `:until`
   topology rather than reconstructing it from shapes.
4. Produce exact authority for proof-generated functions/rules, logical Input
   occurrences and payloads, function/ruleset lineage, and command-macro
   fanout. Positional zips and name/schema inference remain forbidden.
5. Publish one owned public snapshot containing the final execution and
   proof-check streams, typed function/rule/merge arenas, structured schedule,
   output ordinals, and display metadata. Validate it before any SQL or output
   directory is created, with a backend that panics on every execution call.
6. Pass focused corruption matrices, full library/proof gates, byte-identical
   double capture, and independent read-only review on frozen bytes.

Only after these criteria pass should checkpoint 3 create SQL lowering code.

## Resume procedure

1. Reproduce the branch and upstream identities before editing:

   ```text
   git fetch origin main agent/duckdb-native-sql
   git status --short --branch
   git rev-list --left-right --count HEAD...origin/main
   git merge-base HEAD origin/main
   ```

2. Resolve the upstream choice in the decision table above. Do not silently
   merge: the newer upstream proof encoding and frontend changes overlap the
   current carrier work.
3. Review `37b48ca` as two scopes. Reauthenticate the schedule-origin carrier
   against the required proof-maintenance topology; treat the uncompiled runtime
   registry separately.
4. Diagnose the two ungrounded-variable snapshot failures before claiming a
   green workspace. Complete and accept the total sort/schedule/producer
   authority carrier and public two-view snapshot, then run the complete
   `make check` gate once under the watchdog. If its aggregate target exceeds
   the limit, run its exact `nits` and `test` dependencies, subdividing only
   through targets that the Makefile declares. The remaining commands below
   are additional focused diagnostics, not substitutes for `make check`:

   ```text
   /opt/homebrew/bin/timeout 110 make check
   /opt/homebrew/bin/timeout 110 make python-nits
   /opt/homebrew/bin/timeout 110 make rust-nits
   /opt/homebrew/bin/timeout 110 make python-test
   /opt/homebrew/bin/timeout 110 make rust-test
   /opt/homebrew/bin/timeout 110 cargo test -p egglog --lib
   /opt/homebrew/bin/timeout 110 make proof-tests
   /opt/homebrew/bin/timeout 110 env -u DUCKDB_LIB_DIR -u DUCKDB_INCLUDE_DIR \
     -u DUCKDB_STATIC DUCKDB_DOWNLOAD_LIB=1 \
     cargo test -p egglog-experimental-duckdb --no-default-features --lib
   DUCKDB_CLI=/path/to/authenticated/duckdb-1.5.4 \
     /opt/homebrew/bin/timeout 110 make duckdb-kernel-check
   ```

5. Implement compilation and atomic publication only after checkpoint 2 is
   accepted. The first production success criterion is generated EqSat SQL
   passing the stock CLI, the separately required proof check, and the
   three-way relation oracle defined above—not the prototype or transcript
   replay.

## DuckDB facts, corrected and scoped

Official DuckDB documentation and project-local probes support different
levels of claim. Keeping that distinction avoids turning a pinned observation
into a portable engine guarantee.

### Documented behavior

- Within a recursive term, the CTE name reads the immediately preceding
  working iteration, while `recurring.T` reads accumulated union-table state.
  `USING KEY` adds unseen keys and replaces payloads for existing keys. See the
  [current `WITH` documentation](https://duckdb.org/docs/current/sql/query_syntax/with)
  and [`USING KEY` article](https://duckdb.org/2025/05/23/using-key).
- DuckDB 1.5 still accepts deprecated bare `UNION` syntax for `USING KEY` by
  default. The target deliberately emits `UNION ALL`; the documented default
  acceptance is planned to change in DuckDB 2.0, not “the next 1.5 release.”
- If an iteration emits multiple rows for one key, DuckDB retains the last
  row. Because joins, grouping, and set operations do not generally preserve a
  total order, the compiler must deterministically fold to one candidate per
  key and anti-diff unchanged payloads before emission. See DuckDB's
  [order-preservation guarantees](https://duckdb.org/docs/current/sql/dialect/order_preservation).
- [CLI safe mode](https://duckdb.org/docs/current/clients/cli/safe_mode) disables
  filesystem-facing operations and external access. DuckDB describes these
  settings as defense in depth, not a sandbox for untrusted SQL. The generated
  artifact is trusted compiler output and still uses an external 110-second
  watchdog.
- The nested [`UNION` type](https://duckdb.org/docs/current/sql/data_types/union)
  has a documented 256-member limit. The documented default
  [`max_expression_depth`](https://duckdb.org/docs/current/configuration/overview)
  is 1,000; **736 is the planned standalone compiler's conservative admission
  cap**, currently exercised by the kernel checker, not a DuckDB limit.

### Pinned local evidence and open canaries

- The authenticated 1.5.4/1.5.5 probes found first failures at 988 nested unary
  expressions, 9,979 explicitly parenthesized left-deep set operations, and
  998 CTE dependency edges. Seventy-five percent of the smallest boundary,
  rounded down to a multiple of 32, gives the planned admission cap of 736
  (`KERNEL_DEPTH_CAP` in `scripts/check_duckdb_kernel.py`).
- The exact safe CLI used by the kernel rejects configuration changes, so the
  artifact cannot rely on raising expression depth or disabling an optimizer.
  The official safe-mode page does not itself promise that every `SET` is
  locked; treat this as pinned CLI behavior plus an explicit admission rule.
- [DuckDB issue #13974](https://github.com/duckdb/duckdb/issues/13974) is closed
  as **not planned**, not “wontfix.” It demonstrates incomplete results from
  multiple bare recursive references on older versions. The historical plan
  review records a local 1.5.5 wrong-result reproduction, but the tracked
  pinned-engine gate proves an admitted single-working-reference query and
  linter rejection of a mutated two-working-reference fragment; it is not a
  preserved engine-level wrong-result reproducer. The IR and final
  rendered-fragment lint therefore admit at most one bare working-table
  reference per recursive branch while allowing multiple `recurring.T` reads.
- [DuckDB issue #23677](https://github.com/duckdb/duckdb/issues/23677) remains
  open and reproduced as of 2026-08-12. Its report includes v1.5.4 and shows a
  top-N/window rewrite dropping a row when `ROW_NUMBER` orders by a nullable
  expression. Every filtered rank therefore needs a proven non-null total key
  or explicit nullness/value/unique-key ordering—never an arbitrary sentinel.
- The kernel proves explicit rollback/retry of durable metadata. It does not
  yet prove automatic rollback of one failed source command while preserving
  earlier committed commands and their complete JSON-event prefix; that is a
  blocking checkpoint-3 test.
- [DuckDB 1.5.5](https://github.com/duckdb/duckdb/releases/tag/v1.5.5) is current
  stable as of this review. The campaign intentionally pins 1.5.4 as the
  primary target and treats 1.5.5 as compatibility evidence.

## Technical findings retained from the campaign

### Phase 1: DuckDB used only as a row store

The first architecture stored rows in DuckDB while keeping matching and merges
in Rust. An H1–H17 ladder with subvariants made the mini benchmark roughly 100
times faster, but four of five proof workloads still exceeded the 105-second
inner cutoff. Pointer, the sole completion in the consolidated benchmark, was
10.731–11.775×
slower than main and used 6.649–6.716× its maximum RSS.

Profiling explained the ceiling: 84.4% of pooled samples were in host-side join
matching, and a representative round performed 717,584,348 candidate/environment
clones for 324,661 survivors. A measurement-only partial-index design projected
candidate-plus-build work down to 2.3041% and passed both predeclared D0 gates,
authorizing one production H17 slot. That production slot never ran, so the
measurement does not establish either wall-time or RSS improvement on a full
workload. The completed phase-1 evidence still established the architectural
bottleneck: storing rows in a database had little value while the dominant
joins remained in the host.

The phase-1 ledger is machine-local at
`/Users/saul/p/wt/egglog-encoding-duckdb-backend.goal.md`; its SHA-256 during
this review is
`b33e7be16c6c8bea4f5e2e91977ebc774548b53dfb2dc9f9a29253aeb5691f3a`.
That makes the figures locally traceable but not portable with this branch.

### Phase 2: live generic typed DuckDB backend

The next architecture pushed matching, merges, effects, and rebuilds into
generated typed SQL while Rust continued to compile, schedule, transact, and
observe each run. The checkpoint sequence established typed storage, generic
execution for the reached scalar-action language, SQL-owned fresh IDs, and
specialist compatibility routes for path compression, cleanup, rebuilds,
marker rekey, ordered input, scalars, and MatchObservation without proof-aware
backend storage.

At pre-merge checkpoint `37fc161`, Pointer completed end to end in proof mode:
Reference took 0.49 seconds and 38,977,536 bytes maximum RSS; DuckDB took 6.35
seconds and 352,108,544 bytes—about 13× wall time and 9× RSS. Both exited 0
with empty stdout and the same ordered ruleset vector. That is a useful
correctness smoke, but the campaign neither compared every typed/proof relation
nor verified an extracted DuckDB proof, so the previous report's “bit-parity”
wording was too strong. The referenced raw timing directory no longer exists,
so these remain historical ledger measurements rather than confirmed
current-head performance.

One fresh diagnostic at pre-review head `a8ddcf1`, using the same frozen source
and fact hashes, completed main/reference mode in 0.06 seconds with 43,974,656
bytes maximum RSS and live DuckDB mode in 15.05 seconds with 5,082,578,944
bytes maximum RSS. It was not repeated because of the 5 GB peak, so it is not a
benchmark estimate or a new correctness oracle. It does confirm that the
historical performance ratio cannot be treated as current.

### Phase 3: standalone compiler restart

The compiler restart first attempted Design A, a recognizer for generated proof
maintenance. Although its EqSat smoke passed, independent review showed that a
same-shaped decoy could self-authenticate. The implementation was rejected.
The early-exit rule was then applied too broadly to Design B; the user corrected
the decision and selected generic Design B as the sole production architecture.

Design B exposed and repaired two order-sensitive semantic bugs before
checkpoint 0 was accepted:

- two same-wave `SetIfEmpty` actions on one absent key must both observe the
  first staged default; and
- merge queues drain by earliest source event, not by `FunctionId` order.

Checkpoint 1 then froze a stock-SQL kernel around typed keyed state, explicit
working/recurring reads, deterministic folds, strict anti-diff, tombstones,
schedule-controller semantics, checked arithmetic, fresh/generation/watermark
rollback, failure-prefix behavior, and the current one-Fresh proof-shaped hot
SCC. This is the strongest direct engine evidence in the branch. The complete
source-command transaction/output-prefix contract remains a checkpoint-3 gate.

The hand-written prototype adds evidence that one tagged `USING KEY` relation
can carry a bounded EqSat-style rewrite/rebuild state machine. On this review
machine it completed on DuckDB 1.5.5 in 0.09 seconds; the historical run was
0.19 seconds. Neither timing is a compiler benchmark.

## Evidence manifest and limitations

| Evidence | SHA-256 at review |
| --- | --- |
| `STATE.md` | `285da7582c4f2d01e553b923492bb8ab46ea795da1c97428d582f7d5af3eae58` |
| EqSat source | `c0fa15ae2849bfbb65b53b5168ee7ec338be4ff371d473668b94d25bf2ea7fa0` |
| Stock-kernel fixture | `a4b7c005dec22952ae2ae94edae256aaf016f325776601beb277545f21c81529` |
| Desugared-comment transcript | `b4a704a281beff5221922c61826fc3e0c3fd74ca7833a11159e8b2492dc73b75` |
| Source-comment transcript | `d33be24d636e17274f3a69dcef51845e511e01c00bc3ef722a18ac3a4fbd518a` |
| Recursive-CTE prototype | `baf2e74c92f2fc2614f7ed01d645c1eacfbd6b5a82d1c5975b98b08b74c1c24e` |
| Historical recursive-CTE plan | `a30c559bb35d3bbf08098f059810b23c549aaed95c3a659a027e98d3c100fa44` |
| Historical plan review | `30f76a3e881092ca1132464f40b432dbcce2e32e63aa3e19179c8d3873a1bf06` |

The official 1.5.4 CLI used by the artifact audit authenticated as binary
SHA-256
`6c5abaff49f07ba3f6b2e41ed1adf338d10fcb2d98777331b285cc97938fb00a`;
its release ZIP SHA-256 was
`d6c35195683fd1378e5624b01ca390069d399f8341c38986b7e3dfa0b3470d10`.
The audit's temporary copy was intentionally not retained in the worktree.

The earlier report also claimed approximately 81.2 union wall-clock agent
hours, 329.9 summed agent-hours, and 892 rollout files, using a 30-minute gap
heuristic. Those are report-author estimates, not acceptance evidence: the
mining script and manifest were not committed, and the cited volatile Claude
research output under `/private/tmp` is no longer present. Keep the figures only
as approximate process history.

The process lessons remain useful: append-only ledgers and predeclared bounded
gates preserved a long campaign; independent read-only review caught several
green-but-unsound designs; and profiling should precede a long tuning ladder.
The main failure mode was allowing historical, empirical, accepted, and WIP
claims to blur together. This revision keeps those categories explicit.
