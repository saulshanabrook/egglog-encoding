# Check-Directed Slice Replay: Campaign Report

*Written 2026-08-06, at the pause point. This is the definitive record of the causal-slicing
effort so it can be picked up without any agent context. Every number is traced to a source:
a commit, a ledger file, a benchmark row, or a session log. Paths to all of these are in the
appendix.*

## Summary

Between 2026-07-20 and 2026-08-05 (16.9 calendar days, with a gap Jul 31–Aug 3), a series of
agent campaigns built **check-directed slice replay** for egglog: run a program once with a
tracing recorder on, compute the backward causal cone of each successful `(check ...)`, and
emit a small standalone `.egg` artifact that replays just that cone under the existing proof
encoding. The motivating idea (from the IJCAR 2026 proof-skeletons paper) is that producing a
proof for a tiny sliced program is far cheaper than running full proof instrumentation on the
whole program.

**What shipped:** PR #42 "Add check-directed slice replay" (open, head `83c0444`,
+43,601/−2,281 lines). On the five-workload benchmark suite (Herbie excluded), sliced proofs
cost **0.47–0.64×** the wall time of full proof mode, and **1.72–2.23×** a plain run with
tracing off. Earlier in the campaign, against the frozen July baseline, the suite ratio vs
proofs was 0.13× — the gap narrowed because proof mode itself got ~2× faster when `main` was
merged in, not because slicing regressed. All 194 supported corpus files replay correctly;
artifacts are deterministic and validated by strict proof replay.

**What did not ship:** a recorder cheap enough to leave tracing on casually. The end goal of
the final phase was total sliced-pipeline cost under **1.5×** a normal run. That was
falsified on 2026-08-05: with *all* premise-witness recording disabled, capture alone still
measured **2.213×** normal (paired median). The cost is the recording floor — copying fact
rows, terms, equalities, and mutations — not the witness machinery every redesign had
targeted. The final experiment (a "substitution journal") was stopped by its own
pre-registered stop rule before any production code was written.

**Contract decisions made at the end, which shape any future work:** (1) slicing is an
opt-in debugging mode; the 1.5× budget applies only to runs that produce a slice; an
always-on mode would need ~1.1× and is out of scope. (2) The output contract can relax from
"the exact historical derivation" to "any valid support that proves the check" — this was
adversarially reviewed, shown sound with specific amendments, and is encoded in five test
canaries on the `agent/support-journal-experiment` branch. It removes most of the machinery
that makes the recorder complicated, but it does not fix the recording floor, so it was not
implemented.

Total effort: 5 top-level Codex (GPT-5) sessions plus ~1,870 subagent runs (~2,070 summed
agent-hours, ~4.9B input tokens, 97.5% cached), one long-running Claude reviewer session
(~16 active hours, seven multi-agent review fleets, ~3M subagent tokens), and 189 recorded
human interventions.

---

## Chronology

### Prehistory: hook-proof RFC (May 18–20)

A May session in `/Users/saul/p/egglog-proofs-new` (thread `019e3970`) revised and partly
implemented an RFC for a witness-based proof backend, organized around validated "slices"
(direct equality, source-rule equality, congruence, merge replay). It stalled on an ambiguous
premise but established principles that carried through everything that followed: fail closed
on ambiguity, one canonical lookup, no inverse solving or final-state reconstruction. Its
handoff document was regenerated on Jul 20, minutes before the slicing effort began.

### Slicing 1, part one: v0 and arena-v0 (Jul 20–22, session `019f7d26`)

The effort started with a paper: *"2026ijcar-skeletons.pdf — could this approach be applied
to this repo?"* Within two hours the user had sketched the whole architecture that
eventually shipped: record which rules fired with which arguments, slice the program
backward from a check, and re-run the minimum program under the existing proofs mode. The
`(run-rule ...)` replay primitive was designed the same night (PR #23; later closed, the
primitive shipped inside the slicing branch).

Two implementations followed in quick succession:

- **v0** (`agent/causal-slice-v0`, 5 commits, +4,899 lines): a feasibility spike. The first
  end-to-end sliced artifact — 504 bytes, passing strict proof testing — existed ~14 hours
  into the campaign.
- **arena-v0** (`agent/causal-slice-arena-v0`, 97 commits, +35,215 lines): a causal DAG
  arena with post-run elaboration and a *selector-based* replay: generated rules re-found
  each firing's premises by querying. `egglog/src/causal_slice.rs` grew to **15,911 lines**.

Results at review (Jul 21, checkpoint `ef15a734`): Eggcc replayed at 0.53× proof mode,
Pointer and Luminal near parity — but **Hardboiled was 46.5–47.7× slower than proof mode**
(29.9–30.5 s vs 0.64 s; source: `causal-slice-v0/RESULTS.md:123` in the arena worktree).
The selector was the problem: 5,119 selector plans, and one rule with 84 groundings that
stable bindings could not uniquely identify, which the fail-closed design correctly refused
to guess. A parallel read-only Codex session (`019f84fb`) reviewed the live agent's worktree
on request — the first appearance of the "independent reviewer" pattern.

### Slicing 1, part two: receipts (Jul 22–27, session `019f8841`)

On Jul 22 the user ordered a full retrospective ("look at all logs, all commits") and then
made the decisive architectural ruling of the whole campaign (15:57 UTC):

> "drop direct replay and proof-side translation entirely … native run with exact receipts →
> backward slice → source-level projection → run the EXISTING proof mode on that projection,
> unchanged. No selector rules, no per-firing queries."

That is the architecture that shipped. The same day the user overruled a premature agent
stop, distinguishing the real stop signal ("a second interpreter" — the v0 failure mode)
from instrumenting the single existing execution path. The `causal-receipts-spike` branch
was stopped and documented; **receipts-v1** (`agent/causal-slice-receipts-v1`) implemented
exact `FactId` receipts with `let-check` aliases and list-form `run-rule`, tracked in a
3,258-line experiment ledger (55 dated entries, Jul 22–28).

The gate on Jul 23 read: Eggcc 1.49× — but **Math 27×** (11.0 s vs 408 ms). One day of
recorder research (Jul 24, `RESEARCH-recorder-cost-2026-07-24.md`) produced the ablation
triple that would steer — and later mislead — everything after: exact recording **2.27×**,
count-only observation **0.97×**, record-then-discard **1.90×**. The conclusion "the hooks
are cheap; eager exact attribution is expensive" justified pivoting to a
**logical-support fact graph** (Jul 23, 23:44: the old branch is "the completed, failed
exact-physical-history experiment") on a fresh branch: `agent/causal-slice-logical-v1`.
Recorder performance work was explicitly frozen; the gate became end-to-end-vs-proofs. The
session closed Jul 27 handing off a "minimize LoC" plan (+23,268 net lines at that point).

### Slicing 2: correctness, review, and PR #42 (Jul 27–30, session `019fa127`)

The second main session (confirmed as "slicing 2" by the recovery thread `019fa3e9`) ran the
feature to review quality:

- **Correctness sweep** (Jul 27): a 96-file corpus sweep found capture panics and replay
  failures; 25 panics reduced to 12 mechanisms, then to 8 known bugs, then to zero
  (checkpoint `8598ad4`). The user's ruling: fix panics and replay failures now, defer
  compatibility and performance — "the important thing is it's faster than proofs."
- **The eqsolve discovery** (Jul 28): one file kept failing replay. The user ordered it
  treated "as knowledge … something important about how egglog works," minimal repro first.
  The root cause is the campaign's most important technical finding (see Findings): a
  replayed action's *denotation* depends on equality state, so a slice must close over the
  pre-event denotation of every structural read. A 7-command reproducer (3 of 6 allocation
  orders fail) pinned it; the fix landed Jul 29 (`ff14371`).
- **Review campaign** (Jul 29): the user's line-by-line CLI review was generalized into
  review patterns applied repo-wide by an eight-worktree cleanup constellation; the five
  `.codex` experiment ledgers were retired into git history (`fd4a4fd`); Diátaxis-style docs
  were written (`egglog/src/slicing/check_directed_replay.md`, 573 lines, plus the
  provenance module reference). A four-agent Claude audit the same day found write-only data
  structures (waves stored five places, read in two; the EdgeHorizon coordinate derivable
  from history positions) that were then deleted.
- **PR #42 published** Jul 29 23:28 UTC with benchmarks in the description. The frozen-
  baseline per-file benchmark (Jul 27): causal-proofs vs proofs, suite **0.132–0.135×**
  (Math 0.22×, Pointer 0.06×, Luminal 0.035×).

### Merge, simplification, and the performance wall (Aug 4–5)

After a four-day pause: `MergeFn` provenance was simplified to "an effective merge creates
one computed fact depending on both prior and incoming facts" (user ruling: depend on both,
delete the origin-inference machinery), `origin/main` was merged (`83c0444`), and the
benchmarks re-run: sliced/proofs **0.470–0.643×**, sliced/off **1.72–2.23×** — but Math's
advantage was gone (proofs dropped 3.84 s → 1.92 s from main's faster native input loading;
sliced stayed ~1.95 s). That observation opened the final phase: get the whole sliced
pipeline under **1.5× of a normal run**.

The Aug 5 phase profile (medians of 6, single-threaded): off 0.543 s; capture 1.125 s;
selection 0.753 s; lowering 0.004 s; proof replay 0.044 s. Capture alone was 2.10×. A
term→producer index was tried and rejected empirically (selection 0.69 s → 1.70 s). The
proposal on the table became an "exact substitution journal": record (rule, action site,
wave, cutoff, bindings) per firing instead of premise FactIds, and reconstruct premises
cold.

What followed was a day of structured cross-review between the Codex session and the Claude
reviewer session (seven-agent and two-agent fleets on the Claude side; independent audit
circles on the Codex side), with the user arbitrating. The highlights, all
evidence-verified:

- Claude's review: the budget arithmetic didn't close (1.35× capture + 80 ms selection
  ≈ 1.64×, not 1.5×); the journal's uniqueness claim failed on three constructible programs
  (dead variables resolved by physical row order; decomposed-plan duplicate lanes;
  presence-relation delete/reinsert); the July ablations were stale and statistically weak;
  Eli's old table-backed proofs (upstream egglog #725/#837) validate "record a substitution,
  reconstruct cold" but refute storing provenance in engine tables.
- Codex's counter-review caught real errors in Claude's review: the benchmark harness
  already runs everything at `-j 1` (a proposed calibration was redundant), and the claimed
  "worst case equals today" for a fallback search was wrong.
- The user then changed the contract twice: slicing is a **debug mode** (1.5× applies only
  to sliced runs), and — the larger change — *"any valid support that proves the check is
  fine"* (Aug 5, 18:49 UTC). Adversarial review of that pivot found it sound with
  amendments: a syntactic containment audit is mandatory (strict proof replay validates an
  artifact against *itself* — an invented union becomes a legitimate axiom), removals are
  semantically necessary (a `min`-merge counterexample proves it), and merge reads must be
  kept within the supported merge boundary.

The final plan ("producer-guided support journaling") was falsification-first: re-measure
before building. It stopped at the first gate, 23:51 UTC, with the independent circles'
consent:

> "With every rule-premise witness disabled, Math capture remains **2.213×** off by paired
> median [2.041–2.488]. Any correct all-variable journal additionally needs an ephemeral
> lane-coherence carrier, so it cannot improve on that measured lower bound."

Full capture measured 1.008 s; witness-free capture ~1.03 s. **The premise-witness pipeline
— the target of every redesign since July — costs approximately nothing on current source.**
The July ablations that attributed ~0.4× to it were measuring code that the intervening
review campaigns had already optimized away. The recording floor (fact rows, terms,
equalities, mutations) is the entire overhead. No journal code was written; the experiment
branch holds only five contract-canary tests (+185/−1, commit `4a2b530`).

---

## Where things stand now

- **PR #42 is open** at `83c0444` (+43,601/−2,281), unreviewed. Nothing from the slicing
  lineage is merged to `main`. The feature works: 194/194 supported corpus files, artifacts
  deterministic, strict proof replay green, every benchmark file faster sliced than full
  proofs except Math (now ~1.04× proofs, within noise).
- **Per-file cost of the debug run today** (`.reports.jsonl` at `e9f7b97`, Aug 4, sliced
  vs off): Pointer 1.21×, Luminal 1.52×, Eggcc 1.66×, Hardboiled 2.32×, Math 3.29×.
- **The 1.5× goal is blocked by the recording floor**, not by witnesses or the selector.
  Ideas on the table, none costed: profile the floor's 1.0 s composition (nobody has);
  fact-local capture that reads the still-live native database at slice time instead of
  copying rows; capture that stops at the target check's wave; two-pass (count-only always,
  full capture on demand); or accept current cost for a debug mode.
- **The any-valid contract** is designed, reviewed, and encoded in the five canaries on
  `agent/support-journal-experiment` (local branch, one commit past PR head). Its LoC case
  (net −1,400 to −2,000 estimated, occurrence-exactness machinery deleted) is intact; its
  performance case died with the journal. If picked up, the required amendments are in the
  canaries and in the Aug 5 review record: containment audit, keep removals, keep the merge
  boundary, artifact-size gate.
- **Herbie remains excluded** (needs push/pop support, sized at 2–4 days in July).
- The experiment ledgers are all recoverable: `git show fd4a4fd~1:.codex/causal-slice-v1/EXPERIMENTS.md`
  (and siblings); the support-journal ledger is on disk in its worktree (see appendix).

---

## Findings

Technical knowledge this campaign produced, most durable first.

1. **The denotation-dependency law.** In an e-graph, no syntax has a fixed denotation.
   Capture records events after canonicalization; replay re-executes source-level actions.
   A slice is sound only if every structural read replayed from an event retains enough
   earlier equality evidence to reproduce the denotation it had at capture time (strict
   pre-event closure, horizon = event − 1). Discovered via the eqsolve failure; minimal
   repro: `(A)(B)(C); (union (A)(B)); (union (B)(C)); (check (= (A)(C)))` — 3 of 6
   allocation orders fail without the closure. Documented in
   `egglog/src/slicing/check_directed_replay.md`.

2. **The recording floor is the wall.** Capture with all premise-witness work disabled is
   2.213× a normal run (Aug 5, paired median, n=6). The floor is fact-row copies, term
   installation, equality proposals, and mutation records. Witness transport is ~free.
   Consequence: no premise-representation redesign (journal, annotations, compression) can
   reach 1.5×; only recording less, or reading state instead of copying it, can.

3. **Stale measurements are architecture poison.** The July ablation triple (0.97× / 1.90×
   / 2.27×) was 12 days old, at older commits, with weak statistics (the 0.97× CI included
   parity; the 1.90× was a one-round diagnostic). Three days of design debate rested on it;
   one afternoon of re-measurement invalidated it. Two subagent audits had recommended
   re-measuring first; the recommendation was dropped from a synthesis and had to be
   restored by external review.

4. **Exact-history selectors don't scale; grounded receipts do.** The arena-v0 selector
   (re-finding premises by query at replay time) hit 47× on Hardboiled and an ambiguity
   wall (84 non-unique groundings). Recording exact receipts and replaying grounded
   list-form `run-rule` commands — no joins, no search — is the shape that works.

5. **The any-valid contract map.** Relaxing "the exact historical derivation" to "any valid
   support" dissolves occurrence-identity machinery (~1,300 lines of `explain.rs`, witness
   transport, presence tombstone-for-identity), but three things are load-bearing
   regardless: **removals** (proven by a `min`-merge counterexample where every valid
   artifact must include a delete), **the merge boundary** (fold-fidelity is not
   subset-monotone; reads of merged values are gate-invisible), and **containment**
   (replay + proof-testing validates the artifact against itself; top-level actions become
   `Fiat` axioms, so a smuggled union verifies — a syntactic artifact⊆original audit is
   mandatory). Rule attribution can stay historical at zero cost; only groundings float.

6. **Prior art calibration.** Soufflé's annotation-based provenance measures 1.27–1.31×
   runtime (its contract is any-valid, monotone Datalog only). Record-replay systems (rr)
   pay 1.5–1.8× for exact-original. Eager witness systems run 2–3×. Nothing published
   handles egglog's combination (canonicalization, deletions, merge functions) — and
   upstream egglog's own table-backed proofs (#725) validated substitution-recording but
   cost 5–7% *with tracing off* because capture leaked into engine id semantics; it was
   removed as unused (#837). Lesson: keep capture strictly behind the hook boundary.

7. **Benchmark discipline.** Only same-binary, same-session ratios are trustworthy. The
   proofs denominator improved ~2× under the main merge and silently erased Math's headline
   advantage; cross-session absolute comparisons produced multiple false alarms. All
   benchmarks run `-j 1` (and slicing requires `--threads 1`), so serial-vs-parallel was
   never a factor.

8. **Cost of the artifact:** the shipped implementation is ~9,820 lines of provenance
   recording (`egglog/core-relations/src/provenance/`) plus ~5,300 lines of slicing
   (`egglog/src/slicing/` incl. tests) plus engine hooks; production net vs main was
   +26,182 lines at PR time. The "minimize LoC" goal of slicing 2's opening plan was missed;
   deletions succeeded only when campaigns named concrete targets (write-only structures,
   EdgeHorizon, dead enum branches).

---

## Meta-analysis: how the agents worked

### Accounting

| Measure | Codex (GPT-5) | Claude |
|---|---|---|
| Top-level sessions | 5 core (+observer, +2 utility) | 1 long reviewer session (+1 SDK one-off) |
| Subagent runs | ~1,868 files, ~2,070 summed agent-hours | 7 multi-agent fleets (4+7+2+4 agents + 3 clusters), ~3M tokens |
| Tokens (top-level) | 4.9B input (97.5% cached), 9.6M output | ~16.4 active hours over 15 days |
| Human interventions | 189 recorded across 4 sessions (peak: 43 on Jul 22) | continuous review dialogue |
| Calendar | Jul 20 → Aug 5 (16.9 days, idle Jul 31–Aug 3) | Jul 22 → Aug 6 |

Seven distinct implementation starts (v0, arena-v0, receipts-spike, receipts-v1,
count-floor, logical-v1, support-journal) across five architectures. Two were stopped by
explicit stop rules, one was demoted to an oracle, one froze as an experiment record, one
shipped.

### What worked

- **Pre-registered stop rules and falsification-first ordering.** The two cleanest moments
  of the campaign are both *stops*: the receipts spike (Jul 22) and the support journal
  (Aug 5), each killed by its own pre-declared gate, each leaving a clean ledger and zero
  stranded code. Contrast the arena-v0 era, which grew a 15.9k-line monolith before its
  architecture was falsified. The Aug 5 stop is the model: the plan's first step was
  "re-measure the premise," and the premise died in a day.
- **Short, well-timed human rulings.** The intervention log shows the user steering with
  single sentences at inflection points: the Jul 22 architecture decree (the shipped
  design), "prioritize minimization of overall complexity," "treat this as knowledge …
  not something to paper over" (which produced the denotation law), and "any valid support
  is fine" (which re-opened the whole design space in one line). 189 interventions, almost
  all direction-setting rather than code-level.
- **Cross-model adversarial review with an evidence requirement.** The user's standing
  instruction — refute with evidence or concede — made the Codex↔Claude exchanges converge
  instead of oscillate. Concrete catches in both directions: Claude found the budget
  arithmetic error, three soundness counterexamples, and the proof-gate containment hole;
  Codex found Claude's redundant `-j 1` experiment, the false worst-case claim, and the
  live-evaluator assumption. Several of these were errors *neither* side found alone.
  The earlier same-model observer session (Jul 21) added less: it summarized but did not
  falsify.
- **Ledger discipline.** `EXPERIMENTS.md` / `STATUS.md` files with dated entries, exact
  commands, SHAs, and hypothesis verdicts made every restart cheap and made this report
  possible. When subagents were accidentally closed (Aug 5), the campaign resumed from the
  ledger in minutes. The retired ledgers remain fully recoverable from git history.
- **Fail-closed engineering as an epistemic tool.** Refusing to guess (Hardboiled's 84
  groundings, eqsolve's replay failure) converted would-be silent wrongness into the
  campaign's two most valuable discoveries.
- **Minimal reproductions.** The 7-command eqsolve repro and the 5 relaxed-support canaries
  compress days of debate into runnable artifacts.

### What didn't work

- **Architecting on stale numbers.** The single biggest waste: the July recorder ablations
  steered the receipts pivot, the logical-v1 recorder freeze, and the entire Aug 5
  journal debate, and were wrong about current source by the end. Two audits flagged this;
  the flag was dropped in synthesis. Rule for next time: any measurement older than the
  current commit is a hypothesis, not a premise.
- **The LoC objective never held.** Three campaigns aimed at net code reduction
  ("minimize LoC" plan, review constellation, journal's −233 gate); the branch still adds
  +26k production lines. Simplification succeeded only as targeted deletion with named
  structures, never as a general pressure.
- **Evidence loss in agent-to-agent channels.** Codex subagent task payloads and
  inter-agent messages are encrypted in the on-disk logs; at least one detailed audit
  (Eli's table-backed proofs) reached the coordinator through a channel this report cannot
  read, and its headline claim was initially untraceable (later verified true by direct
  fetch). Synthesis steps also dropped subagent caveats (statistical weakness, re-measure
  recommendations). Conclusions that live only in a synthesis message are fragile;
  conclusions in ledgers survived.
- **Benchmark denominator drift as a recurring false alarm.** "Math got slower" (it
  hadn't — proofs got faster) consumed most of an investigation day. Ratios must be pinned
  to both endpoints in-session.
- **Long-session context management is the tax.** Both stacks paid it: Codex sessions
  ended by handing plans to fresh sessions (the S1b→S2 handoff worked well); the Claude
  session survived via compaction plus memory files. The handoff artifacts that worked
  were self-contained plan documents and ledgers, not chat history.

### Verdict on the pattern

One writer + independent read-only reviewers + binding stop rules + a human who intervenes
rarely but decisively is the configuration that produced everything of value here. Fleets
of parallel subagents were effective for *evidence gathering* (audits, sweeps, archaeology
— the 96-file corpus sweep, the 4,212-file session inventory behind this report) and for
*adversarial verification*, and were never the bottleneck. The bottleneck both times things
went wrong was a trusted-but-unverified premise (a stale number, a selector that "should"
scale) surviving into an implementation phase. The fix that worked was procedural, not
architectural: put the premise's re-verification first in the plan, and give the stop rule
teeth.

---

## Appendix: evidence index

**Branches/worktrees** (all under `/Users/saul/p/wt/egglog-encoding/` unless noted; shared
object store, root commit `aae942a1`):
`agent/causal-slice-v0` (`ecabeb7`) · `agent/causal-slice-arena-v0` (`d98c112`; 15.9k-line
`egglog/src/causal_slice.rs`; 47× evidence in `.codex/causal-slice-v0/RESULTS.md`) ·
`agent/causal-receipts-spike` (`788fa6e`) · `agent/causal-slice-receipts-v1` (`0d7ffbb`) ·
`experiment/causal-count-floor` (`96ab7be`) · `agent/causal-slice-logical-v1` = **PR #42**
(worktrees `causal-slice-logical-v1` at `e9f7b97` and `pr42-agent-causal-slice-logical-v1`
at `83c0444`) · `agent/support-journal-experiment` (`4a2b530`, local only; canaries +
`.codex/support-journal/STATUS.md` + measurement jsonl files).

**Retired ledgers** (deleted in `fd4a4fd`, recover with `git show fd4a4fd~1:<path>`):
`.codex/causal-slice-v1/EXPERIMENTS.md` (3,258 lines, Jul 22–28) ·
`.codex/causal-slice-logical-v1/EXPERIMENTS.md` (515 lines, Jul 24) ·
`.codex/causal-slice-v1/RESEARCH-recorder-cost-2026-07-24.md` (the ablation triple) ·
`LITERATURE-REVIEW.md` · `REVIEW.md`.

**Benchmark data:** `.reports.jsonl` in the `pr42-…` worktree (Aug 4 per-file rows);
`pr42-support-journal/.codex/support-journal/math-phase-…jsonl` and
`math-capture-only-…jsonl` (the 2.213× floor measurement); PR #42 description (Jul 29 and
Aug 5 six-round results).

**Session logs** (`/Users/saul/.codex/sessions/2026/…`, top-level ids): precursor
`019e3970` (May, egglog-proofs-new) · trigger `019f7ce5` (Jul 20) · slicing-1 `019f7d26`
(Jul 20–22) + observer `019f84fb` · receipts `019f8841` (Jul 22–27) · slicing-2 `019fa127`
(Jul 27–Aug 5) · recovery `019fa3e9`. Narrative summaries:
`/Users/saul/.codex/memories/rollout_summaries/2026-0{5,7}-*` (six slicing-related files).
Claude reviewer session: `~/.claude/projects/-Users-saul-p-egglog-encoding/4f831045-….jsonl`
(Jul 22–Aug 6) with review-fleet outputs preserved in its `subagents/workflows/` directory.

**Shipped docs:** `egglog/src/slicing/check_directed_replay.md` (the model; its
"annotation-only" paragraph at lines ~405–418 anticipated the final contract debate) and
the field-by-field reference in `egglog/core-relations/src/provenance/mod.rs`.
