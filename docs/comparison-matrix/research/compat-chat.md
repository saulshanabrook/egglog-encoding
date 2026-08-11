# "compat" session: egg-equivalence comparison data for the benchmark harness

Source: `/Users/saul/.codex/sessions/2026/07/13/rollout-2026-07-13T09-28-53-019f5baa-9491-7853-b9b0-b2192322600c.jsonl`
(85 MB, 40,652 lines, session id `019f5baa-9491-7853-b9b0-b2192322600c`, cwd `/Users/saul/p/egglog-encoding`, forked from
`019f5307-…`). The session spans **2026-07-13 → 2026-08-11 (active today**; last event 17:49Z, file mtime 13:50 local).
It is a long-running thread that pivoted several times (PR #4 DD-backend review → FlowLog research → profiling/markdown-report
tooling → <2x proofs-overhead goal → **paper-benchmark "compat"**). Only the Aug 4–11 tail is the "compat" work.

## 1. What "compat" is building

**"Compat" = compatibility with the egglog paper's benchmark suite**, converging on one concrete deliverable: run **current
egg (0.11.0) as a first-class engine inside `./bench.py`** on the paper's Math microbenchmark, with proofs/explanations
("egg equivalences") as extra treatment lanes, so egglog-with-proofs can be compared against egg-with-explanations
apples-to-apples.

Naming origin — user, 2026-08-04 (verbatim):

> "OK we merged this PR and now I want to re-understand with egglog paper how we are on all benchmarks, which ones do we have and which do we not?"
> "You can checkout a new branch in a worktree for future work off of main for adding compat"

The Aug 4 audit concluded: coverage is "**3/3 by family, 0/3 by strict experimental parity**" against the paper's three
experiment families (100-iteration Math curve, 31 PostgreSQL pointer-analysis inputs, 289 Herbie programs).
Paper: *Better Together: Unifying Datalog and Equality Saturation* (Zhang, Wang, Flatt, Cao, Zucker, Rosenthal, Tatlock,
Willsey; PLDI 2023) — https://arxiv.org/abs/2304.04332; artifact DOI 10.5281/zenodo.7709794 — https://zenodo.org/records/7709794.

Aug 5 detoured into **backoff-scheduler semantics** (egg's BackoffScheduler vs egglog): egg/egglog agree exactly without
backoff for N=1..7 (egg `egraph_nodes` equals the sum of egglog's 13 `print-size` tables: 69, 118, 208, 389, 784, 1576,
3160) and first diverge at N=8 where backoff bans a rule. User (verbatim, Aug 5):

> "OK for this work, it seems like there are two pieces:
> 1) getting proofs and term encoding working with custom backoff
> 2) getting custom backoff in egglog working with similar semantics as egg for an easier apples to apples comparison...
> For ordering we should probably do 2) first right?"

That produced a scheduler API rework plus a 14-module standalone `paper_benchmarking/` harness (2,873 lines + 1,117 test
lines) that rebuilt the 2.2 GB Zenodo artifact. A separate **Claude session "Update benchmarking comparison with egg and
herbie"** (`2e89524f-f7b9-4fad-abe4-3fffd758a0b0`, worker `cbc44064-…`, project dir
`~/.claude/projects/-Users-saul-p-wt-egglog-encoding-full-pointer-math-checkpoints/`) then **killed the artifact
reproduction**. User message there (verbatim):

> "1. benchmarking of math is the only comparison with egg. It should be based on the egglog paper. We can just benchmark the non backoff version to get the same node counts. We can do run (1-n) where $n$ is the max for egg where it uses max 5gb of memory of 10 minutes whichever is less.
> 2. points to analysis can be added just as a benchmark, not as part of the egg paper comparison story
> 3. herbie can be removed fully since we are gonna add a more realistic recent herbie benchmark"

Its authoritative plan is `/Users/saul/.claude/plans/compiled-petting-thompson.md` ("Math benchmark: egg vs current egglog
in `./bench.py`, no backoff, no Zenodo artifact"), whose rationale is explicit: *"`./bench.py` already computes
candidate/baseline ratios with Fieller confidence intervals … so everything lives in `./bench.py`: egg becomes a set of
treatments."* Today (Aug 11) the codex session located that Claude session on request —

> "Can you find the claude session ' Update benchmarking comparison with egg and herbie' and make a plan to update things based on the conversation there?" → "Implement the plan."

— produced three successive `<proposed_plan>` revisions, and is **currently implementing the third** (fixed N=10, no
calibration machinery, no OOM watchdog/report-schema change).

## 2. Data model: where egg-equivalence data comes from

New workspace crate **`egg-math-benchmark`** (exists on disk, uncommitted): vendored paper Math language, 24 `rw!` rules,
7 seeds from the artifact's `micro-benchmarks/src/math.rs` (originally egg 0.9.3), pinned `egg = "=0.11.0"` with the
`deterministic` feature (https://crates.io/crates/egg). Driver contract (from `egg-math-benchmark/src/lib.rs`):
`SimpleScheduler`, 1 thread, unlimited node/time limits, exactly N iterations; `with_explanations_enabled()` **before**
seeding; e-graph/table counts read **before** `explain_equivalence` (which takes `&mut self` and can mutate the e-graph).

**"Egg equivalences" = egg's Explanations API** — the equivalence-proof machinery
(`explain_equivalence` → `make_flat_explanation()` → `Explanation::check_proof(&rules)`), egg's analogue of egglog's
proof modes. CLI: `egg-math-benchmark --iterations N --check-left EGG_SEXPR --check-right EGG_SEXPR
[--proof-mode off|enabled|extract|check] [--timing-summary PATH]`.

Single fixture `benchmarks/math-microbenchmark/math.egg`: `(include base.egg)` + `(run-schedule (seq (run) ×10))` + a
terminal equality **deliberately established exactly at iteration 10** — `(* 7 (+ (d x x) (d x x)))` ≡
`(* (+ 7 7) (d x x))`, proven false at N=9 / true at N=10 **in both engines** — encoded as the fixture's `(check …)` and
as shared constants in `benchmarking/engines.py` (`EggWorkloadSpec(iterations=10, check_left=…, check_right=…)`).
Regression tests require identical per-table counts (13 `print-size` tables vs egg e-nodes bucketed by an exhaustive
`match` with no `_` arm) at N=10, making cross-engine ratios semantically grounded.

## 3. New dimensions/measures added to benchmarking

**Dimension: the treatment axis grows from 5 to 9 values and now encodes an engine.** From the on-disk
`benchmarking/engines.py` (worktree `/Users/saul/p/wt/egglog-encoding/full-pointer-math-checkpoints/`):

| Treatment | Engine | Mechanism |
| --- | --- | --- |
| `off` / `term` / `proofs` / `proof-extraction` | egglog | unchanged |
| `proof-testing` | egglog | `--proof-testing` (**new** benchmarkable treatment) |
| `egg` | egg | SimpleScheduler, explanations off |
| `egg-proofs` | egg | `--proof-mode enabled` (explanations recorded, none extracted) |
| `egg-proof-extraction` | egg | `--proof-mode extract` (flat explanation built) |
| `egg-proof-testing` | egg | `--proof-mode check` (`check_proof` validates it) |

`main` backend supports all nine; `dd` stays at `("term","proofs")` — so the existing `validate_backend_treatment`
rejects `dd`+egg for free. The DD/backend axis is explicitly untouched ("Removing that axis is a separate PR"), so the
harness briefly carries **two orthogonal-ish axes** (backend and engine), acknowledged as follow-up debt.

**Measures: unchanged schema, engine-mapped.** The egg driver emits the same `TimingSummaryV2` egglog emits:
`search_ns`/`apply_ns`/`rebuild_ns` from egg's `Report` floats, **`merge_ns: 0`** (egg folds congruence repair into
rebuild), `unattributed_ns = total − search − apply − rebuild`, one ruleset named `""`; explanation time deliberately
lands in the derived "outside" phase. Cache identity: per-treatment **engine-selected binary SHA-256** (an egg row and an
egglog row from the same checkout no longer collide); `cache_identity` stays a 3-tuple. Egg treatments are rejected on
any workload except `math.egg` before building. Semantic side-data (not per-observation metrics): the 13 table counts and
the N-boundary equality act as committed oracles, not report fields. The earlier plan iterations' `calibration.json`,
`oracle.json`, RSS watchdog, and `out-of-memory` status were **cut** in the final revision.

## 4. Comparisons the data implies / the user mused about

The load-bearing user musing (Aug 5, verbatim):

> "Can you make a plan to do that? and test it against the examples in the egglog paper (which might also need node limits or other things...) so that we can at least run egglog today, against paper comparisons, and compare to egg with performance, then we can see what proofs adds?"

I.e. a **two-stage decomposition**: (engine gap: egglog/off ÷ egg) × (proof overhead: proofs ÷ off) — and now, with egg's
own explanation lanes, the **cross-engine overhead-of-provenance comparison**:

- `egg-proofs ÷ egg` — cost of merely *recording* equivalence provenance in egg;
- `egg-proof-extraction ÷ egg` and `egg-proof-testing ÷ egg` — cost of materializing/checking one explanation;
- `proofs ÷ off`, `proof-extraction ÷ off`, `proof-testing ÷ off` — egglog's ladder of the same concept;
- `proofs ÷ egg-proofs`, `off ÷ egg` — like-for-like cross-engine cells;
- the interaction: **is egglog's proof overhead worse than egg's explanation overhead?** (ratio of ratios).

The intended invocation is pair-per-run: `./bench.py benchmarks/math-microbenchmark/math.egg --treatment proofs
--compare-treatment egg --rounds 3`; the plan's final validation step runs "**every egg and egglog treatment against
plain `egg`**" — i.e. a 9-cell column of pairwise ratios against one baseline, assembled manually. Phase-level
comparisons (search/apply/rebuild across engines) come along for free from the shared TimingSummaryV2, with the caveat
that `merge` is structurally zero for egg and explanation time is unattributed. This is the concrete instance of the
"more than one pair" pressure: 9 treatments × ≥1 target × (main, dd where legal) on one workload already outruns the
pair-only CLI, before adding old-vs-new-commit target axes.

## 5. Current status

- **Chat + worktree, not merged.** PR **#54** "Add egglog paper comparison" — draft, open, base `main`, head
  `codex/paper-seminaive-scheduler` — https://github.com/saulshanabrook/egglog-encoding/pull/54.
- Worktree `/Users/saul/p/wt/egglog-encoding/full-pointer-math-checkpoints` at `ac4984c` ("paper benchmarks"), rebased
  onto current `origin/main` today, with a **large uncommitted migration in flight**: `paper_bench.py`/`paper_benchmarking/`
  and the 11 sparse `math-run-*.egg` checkpoints deleted; `egg-math-benchmark/` (292 Rust lines), `benchmarking/engines.py`,
  and `benchmarks/math-microbenchmark/math.egg` added; `benchmarking/{models,targets,workloads,collection,benchmark,profile}.py`
  and report modules modified. Session's last visible step: replacing checkpoint-oriented tests with N=10 invariants.
- The primary checkout (`/Users/saul/p/egglog-encoding`, branch `relations-encoding`) is untouched by this work; today's
  agent deliberately avoided the "dirty primary checkout".
- Related but separate: worktrees `bench-comparison-matrix` and `remove-dd-benchmark-backends` (both at `6333234`) exist —
  the backend-axis removal the plan defers, and a comparison-matrix branch, are already staged as follow-ups.

## Implications for this harness

1. **The pair-only model breaks this month, by design.** The compat work's own validation step ("run every egg and egglog
   treatment against plain egg") is a 9-cell one-baseline star, executed as 8 manual pair invocations. A first, cheap step:
   accept multiple `--treatment` values and render a column of ratios against one declared baseline cell — no new stats
   needed, Fieller per pair as today.
2. **Model cells as (target × backend × engine × treatment × workload), but derive engine from treatment**, exactly as
   `engines.py` already does. Do not add a `--engine` flag; the treatment registry is the single source of truth and
   already encodes legality (dd×egg rejected, egg×non-math rejected). A comparison-matrix spec needs precisely this
   **legality predicate** — most of the full cross product is invalid, and the display must distinguish
   "illegal cell" from "missing data" from "failed run".
3. **Comparability is semantic, not just dimensional.** Cross-engine ratios are only meaningful because of the committed
   N=9/N=10 equality boundary and per-table count parity. A matrix language should let a workload declare which endpoint
   sets are comparable (here: engines proven state-equivalent), and the report should surface that proof obligation —
   otherwise the matrix invites egg-vs-egglog ratios on workloads where the engines compute different things.
4. **Measures have per-engine semantics.** `merge_ns` ≡ 0 for egg; explanation cost hides in "outside". Any per-phase
   comparison row crossing engines needs a per-cell caveat mechanism (footnote/annotation), or phase comparisons should be
   restricted to within-engine contrasts.
5. **The interaction the user wants ("did proofs overhead get worse") is a contrast of contrasts**: log-ratio differences,
   i.e. (proofs−off) within engine A minus within engine B, or within new-commit minus old-commit. The harness's existing
   per-cell means + Fieller machinery extends naturally on the log scale; specify comparisons as contrasts over the factor
   space rather than enumerating pairs.
6. **Don't build the general matrix inside PR #54's scope.** The compat plan deliberately kept two axes unreconciled and
   cut the OOM/status machinery to ship one comparison. The right sequencing is visible in the user's own worktrees:
   land compat (engine axis via treatments) → land `remove-dd-benchmark-backends` (collapse backend axis) → then a
   `bench-comparison-matrix` design over the cleaned factor space.
