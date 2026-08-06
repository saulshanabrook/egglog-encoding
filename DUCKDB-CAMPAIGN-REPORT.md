# DuckDB campaign report: from row store to standalone SQL compiler

July 21 – August 6, 2026. Written at the pause point on 2026-08-06 so the work
can be picked up without any agent context. Everything here is grounded in the
two campaign ledgers, the git history, and the raw agent logs; citations point
at those sources. A companion report for the parallel proof-slicing campaign
lives at `SLICING-CAMPAIGN-REPORT.md` on the PR #42 branch.

## Summary

The goal evolved across three phases, each ending in a deliberate pivot:

1. **Phase 1 (Jul 21–22): DuckDB as a row store.** Store egglog function rows
   in DuckDB but keep matching and merging in host Rust. Seventeen optimization
   hypotheses (H1–H17) improved the mini benchmark ~100x, but the full math
   workload never beat a 115-second watchdog. Final measurement: the one
   workload that completed (Pointer) was **10.7–11.8x slower than main with
   6.6–6.7x the memory**, and profiling showed **84.4% of time in host-Rust
   join matching that never touched DuckDB at all**. Verdict: the architecture
   was wrong, not the tuning.

2. **Phase 2 (Jul 27–29, Aug 4): fully DuckDB-native typed backend.** All
   matching, merging, effects, and rebuilds execute as generated SQL; Rust only
   orchestrates. Fifteen reviewed checkpoints on branch `agent/duckdb-native-sql`
   got one full workload (Pointer) running end-to-end through the
   DuckDB-authoritative proof-mode path — correct, exit 0, but ~13x slower
   than the reference backend at small scale.

3. **Phase 3 (Aug 4–6): standalone SQL compiler.** The question "What does Rust
   still select and observe? Why can't it be fully in SQL?" restarted the
   effort as a compiler: egglog source in, one `program.sql` out, executed by
   an unmodified stock DuckDB 1.5.4 CLI with no Rust during execution. A
   working prototype proved full equality saturation runs in a single recursive
   CTE (0.19s); a merge-first plan was written, externally reviewed, and
   executed through checkpoint 0 (merge + generic "Design B" execution engine,
   167/167 backend tests), checkpoint 1 (stock-CLI kernel capability gate), and
   most of checkpoint 2 (compile-only frontend snapshot). Work stopped at
   04:51 EDT on Aug 6 when Codex hit its usage limit (resets Aug 12) — not by
   decision. SQL emission (checkpoint 3, compiling `eqsat-basic.egg`) has not
   started.

Total effort: **16 calendar days end to end, of which 8 were active. Codex
agents ran ~81 wall-clock hours (~330 agent-hours summed across parallel
sub-agents, 892 session files). Claude sessions added ~4.5 focused hours plus
several multi-agent research workflows.** Details in "Time and scale" below.

## Cast and places

| Thing | Identity |
| --- | --- |
| Codex thread (all three phases) | `019f85eb-eaee-7620-aa83-d9e7343ec67b`, named "duckdb"; resume with `codex resume 019f85eb-eaee-7620-aa83-d9e7343ec67b` |
| Phase-1 worktree / branch | `~/p/wt/egglog-encoding-duckdb-backend`, `agent/duckdb-backend` |
| Phase-1 ledger | `~/p/wt/egglog-encoding-duckdb-backend.goal.md` (390 lines) |
| Phase-2/3 worktree / branch | `~/p/wt/egglog-encoding/duckdb-native-sql`, `agent/duckdb-native-sql` (this branch) |
| Phase-2/3 ledger | `.codex/duckdb-native-sql/STATE.md` (4,925 lines; phase 2 is lines 1–3092, phase 3 starts at line 3093) |
| Claude review sessions | "duckdb review" #1 (`71779847…`, Jul 27–29, plan gatekeeper) and #2 (`26fdade1…`, Aug 4–6, phase-3 feasibility/review/this report) |
| Side worktrees (phase 1) | `-duckdb-change-kind-probe` (delete-census probe), `-duckdb-h17-d0` (detached diagnostic), `-duckdb-positive-stack` (consolidated benchmark stack) |
| Claude-side artifacts | `reports/duckdb-sql/` in this commit (feasibility plan, plan review, prototype SQL) |

The parallel proof-slicing campaign (codex threads `019f8841…` and `019fa127…`,
claude session "slicing review") shared the repo and the calendar. It is a
separate effort; it matters here only because it owned Jul 23–26, when DuckDB
work was idle, and because the two campaigns' logs are easy to confuse.

## Chronology

### Prior art (before Jul 21)

An earlier standalone `egglog-duckdb` crate existed at
`~/p/egglog-encoding/egglog-duckdb` (commit `03ee12c9`); the directory is now
gone from disk. It was cited as "inspo" in the phase-1 kickoff and never used
again (goal.md line 15).

### Phase 1: DuckDB as a row store (Jul 21–22, post-mortem Jul 27)

Kickoff, Jul 21 14:25 EDT, verbatim: *"can you open a worktree/branch off of
…/pull/22 to add a duckdb backend? look at ../egglog-duckdb for inspo. It
should ideally work on all the current egglog proofs tests."* The base was the
head of PR #22 ("Relations-based term/proof encoding", `6b82140`), i.e. the
then-unmerged relations encoding, not main.

The agent set up a goal ledger, a roster of ~30 sub-agents (one persistent
writer, a coordinator, read-only reviewers), and an acceptance matrix (194
proof trials, "No DuckDB-specific fixture exclusions or snapshot masking",
goal.md:29). It then ran a hypothesis ladder. Committed wins (mini math
workload wall time): H3 exact-match index 304s → H1 snapshot-only-participating
208s → H2 lazy overlays 108s → H4 overlay PK index 55.5s → H5 cached prepared
statements 35.7s → H7 FxHash env 37.7s. H6 (chunked set-based writes) was
rejected by its own pre-declared profile gate despite a 74.3% mini win —
commit-window rebind share came in at ~30% against a 10% threshold
(goal.md:179–190).

Two user interventions reshaped the phase on Jul 22. First: *"Dont run anything
for more than 2 minutes, thats our benchmark cut off"* — formalized in the
ledger as a binding 120-second ceiling on every command (goal.md:214), which
became the 115-second watchdog that then rejected every following hypothesis.
Second, that evening: *"Can you consolidate all results that had positive
impacts … and see what our timing is? … I am worried we are just churning."*

H9 found that 97.7% of keyed DELETEs were for rows never modified
(change-kind census, goal.md:219) and got mini to 6.71s — but full math still
timed out. H10–H15 were six more variants (overlay reuse, copy-on-write images,
sparse per-key edits…), every one rejected at the same full-math gate even as
mini fell to 2.68s. H16, a pure diagnostic, finally explained why: **host-side
join matching was 84.4% of pooled profile samples; round 10 did 717,584,348
candidate/environment clones for 324,661 surviving matches (~2,210 clones per
survivor)** (goal.md:332–340). H16a rewrote the matcher (iterative DFS, flat
arenas) and gained only 1.08x against a binding 2x gate. H17-D0 measured that a
lazy partial index could cut candidate work to 2.3% — the production slot was
authorized (goal.md:80) but never run, because the phase was over.

The consolidated benchmark (branch `agent/duckdb-positive-stack`) recorded the
final verdict (goal.md:389): four of five workloads timed out at 105s; Pointer,
the sole completion, was 10.7–11.8x slower with 6.6–6.7x RSS. On Jul 27 the
agent's own post-mortem concluded beating main was "not plausible" from
indexing alone (optimistic Amdahl ~5.7x vs the >18.6x needed for math). Saul
ended the phase: *"I dont want least churn, I want complete and working
system … typed columns mapped into duckdb, everything compiled natively."*

One correctness fight is worth remembering: a `fibonacci_demand` proof
mismatch was root-caused to head-execution order and fixed by action-major
execution in 128-binding chunks (goal.md:262–278) — an early sighting of the
ordering-semantics theme that dominated phase 3.

### Interlude (Jul 23–26)

No DuckDB work at all. The slicing campaign ran instead. The thread resumed
Jul 27 at 09:48 EDT.

### Phase 2: fully DuckDB-native typed backend (Jul 27–29, Aug 4)

Jul 27 was a planning day: eight plan revisions in ~5 hours, iterated between
the codex thread and claude "duckdb review" #1, with Saul manually carrying
text both ways. The claude review supplied several rulings that became ledger
law in STATE.md's mission and non-goals: the backend must be **proof-agnostic**
(proof IDs are ordinary typed columns); **timeouts are censored data, never
pass/fail**; no duckdb-rs fork, no Appender/COPY/read_csv (deferral "arguably
an upgrade"); the phase-1 prepared-statement premise was simply false (DuckDB
re-binds and re-optimizes `EXECUTE` every time). Final review verdict that
evening: "Yes — this one is ready. No blockers."

Implementation ran Jul 28–29 as a strict checkpoint machine (STATE.md's
recurring shape: read-only census → frozen worker contract → sole writer
freezes a patch-hash → three independent read-only reviews → at most one
authorized repair → coordinator re-runs all gates → one local commit, never
pushed). Twelve checkpoints landed in ~36 hours (commits `2162850` → `a2163b3`):
scaffold, rule compiler, typed AssertEq storage, merge/fresh SPI, path
compression (174 generated `@uf_path_compress` instances), cleanup effects
(2,169 generated Delete rules), standard rebuilds (3,892 rules in 6 classes),
marker rekey (866 rules over 363 targets), typed ordered-union native input
(Pointer's 13,530 fact rows as one atomic SQL transaction), then the scalar
series. The review machine repeatedly caught real soundness bugs pre-commit,
most notably: ordered-union semantics were being **authenticated by primitive
name strings, spoofable through the public SPI** — fixed by a public
`NativePrimitive` token enum so tokens, not names, carry meaning
(STATE.md:1445–1527).

After the shared five-day repo pause (Jul 30–Aug 3), Aug 4 delivered three
more checkpoints: authenticated scalar expressions (`b94da05`), standalone-UF
scalar targets (`7c578c6`), and Pointer MatchObservation (`37fc161`) — the
last giving the campaign its first complete benchmark: **Reference and DuckDB
both exit 0 on Pointer with valid timing artifacts; DuckDB 6.35s / 352MB RSS
vs Reference 0.49s / 39MB — "descriptive performance evidence, not a
correctness failure"** (STATE.md:3080–3087). Math ran to the 110s watchdog
(censored); Eggcc, Luminal, Hardboiled sat at known `ReadMode::All` /
container frontiers. Backend tests had grown 7 → 140/140. Saul asked the agent
to stop after this checkpoint and regroup.

### Phase 3: standalone SQL compiler (Aug 4 night – Aug 6 04:51)

The pivot questions, Aug 4 ~23:20–23:45 EDT, to both agents at once: *"What
does rust still select and observe? Why can't it be fully in SQL?"* and *"Could
you make a plan to do it as recursive CTEs looking at
https://duckdb.org/2025/05/23/using-key so its entirely standalone? Find any
blockers that would make this impossible in duckdb."*

Claude ("duckdb review" #2) ran a three-phase research workflow (~15 agents)
plus an empirical prototype, and answered: **no blocker**. The prototype is the
strongest single artifact of the night: complete equality saturation — union
find, congruence closure, hashcons, all four eqsat-basic rewrites — in **one**
`WITH RECURSIVE … USING KEY` query, deterministic, 0.19s
(`reports/duckdb-sql/recursive-cte-prototype-eqsat.sql`). The feasibility plan
(`reports/duckdb-sql/recursive-cte-plan.md`) recorded the verified engine
facts: USING KEY gives semi-naive evaluation for free (CTE name = delta,
`recurring.` = accumulated state); keys are never deletable; unchanged
re-emission loops forever, so no-op guards are mandatory; same-key multi-branch
emission is plan-order dependent and must be pre-collapsed; sequences and hash
IDs are unusable for fresh-ID minting but counter + `row_number()` over a total
order is bit-deterministic even at 8 threads.

Codex independently produced the "Merge-First Standalone DuckDB SQL Compiler"
plan (posted 01:17 EDT Aug 5): merge current main first, compile
proof-instrumented egglog to typed SQL run by `duckdb -safe -no-init -batch
-bail -json :memory: -f program.sql`, checkpoints 0–5 with eqsat-basic as the
blocking architectural gate. The claude review verified every load-bearing
premise empirically (merge overlap exactly 12 files; the CLI incantation works
verbatim on 1.5.5; UNION type cap exactly 256; two engine bugs #13974 and
#23677 reproduced) and returned "no blocker" plus four required amendments —
large-N `(run 100000)` must lower as a loop, not unroll; `print-size` /
`print-stats` must be lowered or stripped; `-safe` locks all `SET` so the
compiler must structurally avoid the depth limit and the top-N NULL-drop bug;
the one-working-table-reference rule must be a compiler-enforced lint
(`reports/duckdb-sql/plan-review.md`). Saul relayed the review into codex at
01:30 EDT; implementation started in a fresh context at 02:14 EDT.

Checkpoint 0 nearly died. The merge surfaced the expected `IndexTable`
breakage; "Design A" (a specialized compiler that recognizes generated
proof-maintenance rules) was implemented, went green on EqSat (5.52s), and was
then **rejected by an independent five-blocker review** — the fatal class:
nothing in the public backend vocabulary can authenticate which relation plays
which internal proof role; catalog names, schemas, and registration order are
all spoofable, so a decoy relation self-authenticates (STATE.md:3477–3521).
The agent concluded both permitted designs had failed, executed its
pre-declared early-exit (merge abort, worktree restored), and stopped. Claude's
log analysis found the exit was premature: generic "Design B" had been
dismissed using a canary that only applies to specialized recognizers.
Saul: *"Definately we want design B, its much better than design A anyways."*

Design B — a generic compiler that executes any RuleSpec faithfully, with no
proof-role classifier anywhere in production — was then built and hardened.
Reference-parity probes caught two real semantic defects before acceptance:
two rules calling SetIfEmpty on the same absent key must both observe the
first default (Reference: 10,10; DuckDB pre-fix: 10,20 — fixed with a
transactional prediction ledger), and merge-queue draining must follow event
order, not `FunctionId` order (Reference keeps [200,200]; pre-fix DuckDB kept
[100,100] — fixed by adding `earliest_event_ordinal` to the queue selector)
(STATE.md:3761–3852). Checkpoint 0 was accepted 17:04 EDT Aug 5 and committed
as merge `f8d2f6d`: frontend 9/9, DD 64/64, DuckDB 167/167, proof tests
216/216, live `--proofs` eqsat-basic exit 0.

The overnight run then landed nine more commits:

| Commit | When (EDT) | What |
| --- | --- | --- |
| `26e558c` | Aug 5 18:45 | Checkpoint 1: stock-kernel gate — SHA-pinned official DuckDB 1.5.4 CLI, tracked 1,207-line SQL capability fixture run twice byte-identically, 12 mutation canaries, depth probes (first failures at 988/998) fixing the compiler's expression-depth cap at 736 |
| `529e3a2`–`4d3fa0e` | Aug 5 19:09 – Aug 6 04:15 | Checkpoint 2 substrate, 8 slices: backend-free `CompileOnly` resolution, nominal snapshot DTOs, exact binding/registration authority, producer-stamped sort authority, grouped lossless source capture, per-view source anchors, producer-stamped desugar origins, transactional originated type-state + atomic global production |

At 04:51 EDT Aug 6, mid-way through a test run in a single 16.4-hour turn,
Codex stopped: `usage_limit_exceeded`, "try again at Aug 12th". The uncommitted
in-progress slice (exact schedule-node provenance: new
`egglog/src/schedule_origin.rs` + `runtime_function_registry.rs`, +569/−42
across six frontend files) is preserved on this branch as a clearly labeled
WIP commit.

## Where this leaves us

Checkpoint scoreboard (STATE.md:4023–4030 and later sections):

| Checkpoint | Status |
| --- | --- |
| 0. Merge current main + Design B generic execution | **Done** (`f8d2f6d`; 167/167, 216/216, EqSat exit 0) |
| 1. Stock engine capability gate | **Done** (`26e558c`; `make duckdb-kernel-check`) |
| 2. Compile-only frontend API | **In progress** — substrate committed; activation blocked on total per-sort dispositions and the schedule-origin carrier (the WIP commit); then proof producers, shared input payload, exact runtime registries, and the public two-view mapper |
| 3. Standalone EqSat (`eqsat-basic.egg --proofs` → tracked golden `program.sql`, stock-CLI run, three-way oracle parity) | Not started — this is the first actual SQL emission |
| 4. Positive corpus (Math, Pointer, bounded Eggcc, Luminal) | Not started |
| 5. Benchmark integration | Not started |

What "eqsat-basic as SQL" exists today, none of it a compiled artifact:
the Rust-driven trace `eqsat-basic-desugared-proofs.sql` (committed here;
replays standalone in stock DuckDB in ~1.05s and reproduces the exact recorded
final state, generation=8 / fresh_id=318 / 48 tables, with 29 benign
unmatched-ROLLBACK errors — it is a recording with baked-in literals, not a
program); the recursive-CTE prototype (committed here; eqsat semantics but not
this repo's encoding); and the live Rust-orchestrated backend (phase 2's
engine, green on this branch).

To resume: `codex resume 019f85eb-eaee-7620-aa83-d9e7343ec67b` after the usage
window resets (Aug 12), or hand any agent STATE.md from line 3093 plus this
report. The ledger's own recorded next step is the schedule-origin test lane
(`timeout 110 cargo test -p egglog command_origin --lib`, STATE.md:4921–4925),
then closing checkpoint 2's activation blockers, then checkpoint 3.

## Artifacts committed with this report

- `.codex/duckdb-native-sql/artifacts/eqsat-basic.sql` (1.9MB) and
  `eqsat-basic-desugared-proofs.sql` (1.9MB) — the Rust-driven SQL traces of
  eqsat-basic (plain and proofs mode), ~5,800 statements each, produced Aug 4–5
  by the phase-2 backend; the proofs one has each desugared egglog command as a
  comment above its SQL. Diagnostic artifacts, not compiler output.
- `egglog-experimental/duckdb/tests/fixtures/stock-duckdb-1.5.4-kernel.sql` —
  already tracked (checkpoint 1): the Rust-independent stock-CLI capability
  fixture, with `scripts/check_duckdb_kernel.py` as its authenticated runner.
- `reports/duckdb-sql/recursive-cte-prototype-eqsat.sql` — the one-query
  equality-saturation prototype (claude, Aug 5).
- `reports/duckdb-sql/recursive-cte-plan.md` — the recursive-CTE feasibility
  plan with verified engine facts and sources.
- `reports/duckdb-sql/plan-review.md` — the review of the Merge-First plan
  (verdict + four amendments), which was folded into the executed plan.

## Findings

Technical facts this campaign established, each paid for with evidence:

1. **A row store is not a backend.** With joins in host Rust, DuckDB
   contributed ~0.4% of runtime while host matching took 84.4%; no amount of
   overlay/index/statement tuning moved the full-workload gate (16 hypotheses
   of evidence). Any competitive design must push the joins into the engine.
2. **Full DuckDB-native execution is semantically achievable.** One real
   workload (Pointer) runs end-to-end through generated SQL with proof
   encoding on, bit-parity with the reference backend — at ~13x wall and ~9x
   RSS on a small workload, unoptimized.
3. **Standalone SQL execution is feasible and now partially proven.**
   Equality saturation fits in one recursive `USING KEY` query (0.19s
   prototype); the full proofs-mode statement trace replays in stock DuckDB in
   ~1.05s; and a 1,207-line capability fixture pins every engine behavior the
   compiler will rely on, on an authenticated stock 1.5.4 CLI.
4. **The engine facts that shape the compiler** (verified on 1.5.4/1.5.5):
   `USING KEY` recursion is semi-naive by construction but keys can never be
   deleted, unchanged re-emission diverges without no-op guards, and same-key
   multi-branch emission is plan-order dependent (pre-collapse with GROUP BY +
   arg_min). `-safe` locks every `SET`, so limits must be respected
   structurally: expression depth capped at 736 (probed failures at 988/998),
   UNION type cap exactly 256, issue #13974 (multiple working-table references
   → silently wrong results, wontfix) and #23677 (top-N NULL drop, live) must
   be avoided by construction. Fresh IDs: counter-in-state +
   `row_number()` over a total order — sequences and hash IDs are both
   disqualified. `error()` is lazy and poisons transactions; scalar subqueries
   read pre-statement snapshots.
5. **Internal identity cannot be authenticated from the public vocabulary.**
   Three independent incidents (phase-2 primitive name-strings, phase-3
   packed-constructor decoy, catalog-name inference) all failed the same way:
   names, schemas, and registration order are spoofable. The viable design
   (Design B) executes every rule generically and never asks "which proof role
   is this relation?" — a conclusion strong enough that a proof-role registry
   was explicitly ruled out of production.
6. **The semantic contract is mostly about ordering.** The bugs that reached
   Reference-parity probes were all order bugs: SetIfEmpty first-owner
   prediction, merge-queue event-order draining, phase-1's action-major proof
   mismatch. Any future backend should treat the wave/ordering contract as the
   spec, with parity probes as the oracle.
7. **A trace is not a program.** The committed eqsat SQL traces execute
   standalone but embed observed run values (fresh-ID bases, iteration counts)
   and host-consumed probe queries. The compiler (checkpoint 3) exists
   precisely to produce SQL *before* execution.

## Time and scale

All times US Eastern. "Union" hours merge overlapping parallel sub-agent
activity; "raw" sums it. Codex activity was segmented at >30-minute gaps, so
short idle stretches count as active; treat these as ±10%.

| Day | Codex union h | What happened |
| --- | --- | --- |
| Jul 21 | 9.6 | Phase-1 kickoff, scaffold, H3–H5 |
| Jul 22 | 13.8 | H6–H9 ladder, 2-minute rule, consolidation + verdict |
| Jul 23–26 | 0 | Idle (slicing campaign) |
| Jul 27 | 4.1 | Post-mortem + 8 plan revisions (phase-2 pivot) |
| Jul 28 | 9.4 | Checkpoints: scaffold → cleanup effects |
| Jul 29 | 14.6 | Checkpoints: rebuilds → general scalar actions |
| Jul 30–Aug 3 | 0 | Idle (everything idle) |
| Aug 4 | 6.5 | Last 3 phase-2 checkpoints; night: phase-3 pivot |
| Aug 5 | 18.4 | Plan, review, checkpoint 0 crisis + Design B, checkpoints 0–1, checkpoint-2 start |
| Aug 6 | 4.9 | Checkpoint-2 slices until usage cutoff 04:51 |
| **Total** | **81.2** | 329.9 raw agent-hours, 892 rollout files (~4x average parallelism; sub-agent trees nested up to 8 deep; 295 sub-agent sessions on Aug 5 alone) |

Claude sessions: "duckdb review" #1 ~2.3 active hours (Jul 27–29), #2 ~2.2
active hours of main-thread time (Aug 4–6) plus its research workflows (the
feasibility fleet, the prototype agent, two plan-verification agents, and the
8-agent log-mining fleet behind this report). Calendar span of the whole
campaign: Jul 21 14:25 → Aug 6 04:51, 15.6 days.

Cost asymmetry worth noting: the phase-3 feasibility answer (prototype + plan)
took one claude evening; each codex implementation day consumed 10–20 wall
hours of heavily parallel agent time. Verification is cheap relative to
implementation, and it repeatedly changed the implementation's direction.

## How the agents worked (meta-analysis)

What worked, with the evidence:

- **Append-only evidence ledgers.** `goal.md` and `STATE.md` recorded every
  hypothesis, gate, verdict, and repair with reproducible commands. The effort
  survived two multi-day pauses, several context resets, one machine restart,
  and two usage-limit cutoffs, and this report could be reconstructed from the
  ledgers + logs alone. The discipline of "failed commands are rejected as
  evidence rather than laundered into passes" (STATE.md:1653) is the single
  most transferable practice.
- **Hard pre-declared gates.** The user's 2-minute rule turned an open-ended
  tuning exercise into falsifiable experiments; six phase-1 hypotheses died
  cleanly at the same 115s watchdog instead of lingering. H6's rejection —
  killing a 74% improvement because its pre-registered profile gate failed —
  is the standout example of the machine honoring its own rules over the
  scoreboard.
- **Writer/reviewer separation with a one-repair budget.** Independent
  read-only reviews caught soundness bugs before commit at least five times
  (name-string spoofing, decoy self-authentication, SetIfEmpty prediction,
  queue ordering, NULL-as-sentinel). The five-blocker review that stopped a
  *green* checkpoint (EqSat passing!) is the system working as designed:
  passing tests were not accepted as proof of soundness.
- **Cross-agent review with a human in the loop.** Claude never talked to
  Codex directly; Saul carried text both ways. That loop was slow but every
  transfer was auditable, and it caught what the implementing agent was
  structurally blind to: false engine premises (prepared statements), plan
  contradictions with the actual workloads (`(run 100000)` unrolling,
  `print-size` rejection), and — decisively — the misdiagnosis that killed
  Design B. The pattern "implementer + independent empirical reviewer with
  its own tools" beat either agent alone.
- **Prototype before plan.** The 0.19s recursive-CTE eqsat settled "is this
  possible at all?" in one evening and gave the plan review teeth (its
  amendments cited probe results, not opinions).
- **Decisive human pivots.** Three user sentences did more than any amount of
  agent autonomy: the 2-minute rule (Jul 22), "I don't want least churn"
  (Jul 27), and "Definately we want design B" (Aug 5). Each ended a loop the
  agents could not exit on their own.

What didn't work, or cost time:

- **Variant churn before diagnosis (phase 1).** H9–H15 were seven attempts at
  the same gate while the mini benchmark improved 20x and the binding gate
  never moved. The decisive profiling (H16) happened only after six
  rejections. Running the diagnostic *first* would have saved roughly a day —
  optimizing the measurable-but-unbinding metric is a recognizable agent
  failure mode.
- **Frozen contracts stop at judgment calls.** The early-exit rule fired
  "correctly" by its letter on a wrong premise (Design B judged by a
  Design-A-only canary) and the agent then could not un-freeze itself; the
  branch sat aborted for ~4 hours until a human adjudicated. That is the price
  of review contracts that bind the reviewer too — probably still a good
  trade, but unattended runs will stall at exactly these moments.
- **Scope was declared out, then became the goal.** Phase 2's mission
  explicitly excluded "a standalone full-Math SQL program" from blocking scope
  (STATE.md:32–33); nine days later that exact artifact became the whole
  campaign. The user's simplest question — "Does eqsat basic compile to sql
  yet?" (Jul 29) — was already pointing there. Asking "what single end-to-end
  artifact would prove the point?" earlier might have pulled the pivot forward.
- **Evidence is fragile at the system level.** /tmp profiles were lost to a
  reboot (capping H6's evidence); SIP stripped an env var under `/usr/bin/time`
  and produced a phantom dyld failure that consumed a review cycle; the
  prototype machine hit ENOSPC mid-session. The ledgers' habit of recording
  exact hashes and re-runnable commands is what made these recoverable.
- **Both hard stops were usage limits, not decisions.** Aug 5 morning and
  Aug 6 04:51. The second cut off a 16.4-hour turn mid-test-run. Long
  autonomous turns multiply this risk; the checkpoint cadence (commit every
  1–3 hours overnight) is what kept the loss to one uncommitted slice.
- **Parallel campaigns in one repo confused everything downstream.** Two
  claude sessions share the name "duckdb review"; the slicing thread was
  repeatedly mistaken for a duckdb thread during this report's research; 199
  slicing rollouts and a pre-effort ancestor contaminated the first time
  accounting. Naming threads and sessions after their branch would have made
  the history self-describing.
- **Fan-out has diminishing returns without attribution.** ~330 raw
  agent-hours compressed into 81 wall hours, but at peak (~6x parallel) much
  of the raw time was reviewers re-verifying unchanged surfaces, and nested
  sub-agent trees (depth 8) make it genuinely hard to answer "who concluded
  this and why" without the ledger. The ledger, not the log tree, is the
  usable record.

## Provenance of this report

Written 2026-08-06 by the claude "duckdb review" #2 session at the pause
point, from: the two campaign ledgers; git history of `agent/duckdb-backend`,
`agent/duckdb-positive-stack`, and this branch; 892 codex rollout files
(~6GB of JSONL) mined by an 8-agent workflow; and the three claude session
transcripts. Time figures use a 30-minute activity-gap threshold. Codex thread
IDs and resume commands are listed in "Cast and places" above.
