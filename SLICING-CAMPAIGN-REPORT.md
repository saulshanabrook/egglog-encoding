# Check-Directed Slice Replay: Campaign Report

> **Status updated 2026-08-12.** This is an archival report for a closed,
> unmerged experiment. The implementation snapshot is `83c0444`; commit
> `06557b1` added the original version of this report, and later report-only
> revisions do not change the benchmarked code. PR
> [#42](https://github.com/saulshanabrook/egglog-encoding/pull/42) was closed on
> 2026-08-06 because it did not fit the paper narrative. Its latest validation
> applies to that branch and merge base `6ef88f1`, not current `main` at
> `7600c192`.

This report reconstructs the causal-slicing campaign from git history, the
retired experiment ledgers, benchmark records, CI, machine-local diagnostics,
session logs, and primary literature. It distinguishes current repository
state from historical measurements and distinguishes measured results from
design hypotheses.

## Executive summary

Between July 20 and August 5, 2026, the campaign implemented **check-directed
slice replay** on an experimental branch:

1. run one ordinary, serial egglog execution while recording causal history;
2. take the closed union of the historical support cones for all successful
   `(check ...)` commands;
3. lower that selection to one ordinary egglog replay program; and
4. execute the program on a fresh graph, optionally under the existing proof
   encoding and strict proof testing.

The trace is causal evidence, not a proof certificate. The replayed proof
system remains the proof authority. The slicer claims sufficient historical
support for the observed checks, not global minimality.

At code endpoint `83c0444` (binary
`9296bc238757dfca1f33ff0355fe89e5d27f7b7a46d293b4be88ea61fb9a8a7e`),
the published clean six-round, five-workload comparison reported:

- sliced proofs versus full proofs: **0.470–0.643×** suite wall time;
- sliced proofs versus ordinary execution: **1.72–2.23×** suite wall time;
- four workloads significantly faster than full proofs; and
- Math statistically inconclusive at **0.707–1.48×** full proofs.

All 90 benchmark observations succeeded. The published report SHA-256 is
`6f71ee754ef11fb58ac300c0408d9052ce0af1bb3a58b02c4f1eb98f9c6c1cdf`, but
that 90-row JSONL is no longer present locally, so the intervals cannot now be
independently recomputed from raw samples. They remain durable as the PR's
published result. Earlier, against a slower July proof baseline, the same
architecture measured **0.132–0.135×** full proofs; that number is historical
and not interchangeable with the final comparison.

The branch's clean CI also passed a 194-trial disposition suite over 192 unique
input paths. Forty-eight trials produced artifacts and invoked strict replay;
the rest verified explicit no-root or fail-closed boundaries. It is therefore
incorrect to describe the result as “194 supported files replayed.”

The final performance experiment established a narrower negative result. On a
check-free Math fixture ending at `(run 11)`, with all **rule-premise witness**
construction, validation, resolution, and publication disabled, six
post-warmup interleaved pairs measured a **2.213× paired-median**
capture-only/ordinary ratio (observed range **2.041–2.488×**). That is an
optimistic empirical floor for journal designs that retain the rest of the
recorder, and it already misses the preregistered 1.5× gate. The experiment
did not measure the incremental cost of witness transport and did not
decompose the residual recorder cost.

No slicing code was merged or released. The current branch is useful as a
validated research artifact and as a source of engine and provenance lessons,
but it is not integrated with current `main`.

## Scope and source method

Statements in this report use four evidence classes:

- **Current facts:** live git and GitHub state checked on 2026-08-12.
- **Durable historical facts:** commits, PR descriptions, CI, and ledgers
  recoverable from git.
- **Machine-local evidence:** ignored benchmark caches, diagnostic JSONL, and
  session logs. These remain useful but are not carried by the branch.
- **Inference or proposal:** interpretations, estimated line reductions, and
  future directions. These are labeled rather than presented as results.

Benchmark ratios are meaningful only with their endpoint, treatment, input,
and sample protocol. The public runner uses independent samples and
Fieller-style confidence intervals; the custom 2.213× diagnostic instead used
interleaved pairs and a paired median. Its 2.041–2.488× span is an observed
range, not a confidence interval.

In the tables below, `off` means ordinary execution, `proofs` means proof
generation without strict extraction/testing, and `sliced-proofs` means an
ordinary captured run followed by fresh proof-generation replay of the slice.
Strict validity was exercised separately through `--proof-testing` in the
corpus and proof suites.

## What the branch implements

```text
ordinary serial execution
        + causal trace
              |
              v
successful checks -- backward closure --> one closed support selection
                                                |
                                                v
                                   ordinary replay program
                                                |
                                                v
                                  fresh ordinary/proof graph
```

### Capture

The main backend records events at the native sites that know whether an
effect was real: fact creation, grounded firings and exact premises, equality
application, merge reads, rekeys, replay-observable removal, container
refresh, and successful check roots. Logical `FactId`s distinguish identical
syntax created at different times. `Wave` and `HistoryPosition` preserve the
temporal boundaries needed by replay.

Capture is serial-only (`-j 1`), main-backend-only, and opt-in. Unsupported
paths fail closed; there is no prefix or original-program fallback.

### Backward closure

All successful checks are roots of one selection. The slicer follows facts to
their causes, firings to premises, equality obligations to earlier edges, and
structural terms to the earlier state that gave them their historical
denotation. It additionally preserves whole visible action bundles, required
removals, merge dependencies, and occurrence lifetimes.

The result is a sufficient historical support cone. It is neither a smallest
program nor one artifact per check.

### Grounded replay

Replay uses ordinary engine semantics instead of interpreting backend events
directly. `let-check` re-establishes recorded structural values without
turning them into Fiat axioms. List-form `run-rule` validates fully grounded
premises against a common pre-wave state, then executes the existing compiled
head actions. Firings from one captured wave publish together.

No recording-graph runtime value crosses to the proof graph. In-process replay
executes the owned `Vec<Command>` directly; only exported source text is
reparsed when independently run. The proof graph constructs proofs
independently. Architecturally, proof production remains unchanged as the
authority; the branch nevertheless changes proof-side code to support
`let-check`, grounded `run-rule`, input literals, and action blocks.

`--slice-output` writes the rendered artifact without production-time strict
validation. Corpus and CI tests perform strict replay; a user asking only for
output does not receive that second pass automatically.

### Supported boundary

The branch supports successful positive checks, source facts and input rows,
grounded ordinary rules, typed equalities, rekeys, selected keyed removals,
and a bounded scalar merge language. It fails closed when a selected cone
reaches unsupported scheduler state, source behavior, occurrence indexes,
merge programs, or container shapes. Herbie is excluded because its source
uses push/pop state.

The corpus records this boundary explicitly:

| Disposition | Trials | Validated behavior |
|---|---:|---|
| Normal | 36 | Build an artifact and run strict replay |
| `ChecksOnly` | 8 | Preserve checks, omit extract roots, run strict replay |
| `ExtractRootsUnsupported` | 4 | Build an artifact without checks, run strict replay |
| Runtime `Unsupported` | 52 | Controlled failure and no artifact |
| `StaticUnsupported` | 49 | Proof-support exclusion before capture |
| `NoReplayRoot` | 45 | No successful replay root, so no capture artifact |

The 194 named trials cover 192 unique paths because Math and Hardboiled each
appear twice. Forty-eight trials call strict replay; 44 of those retain
positive check roots.

## Genealogy

The campaign was not a linear sequence of seven independent implementations.
It was a branch DAG with several experiments and two parallel design lanes:

```text
1cc0e8a
  └─ aae942a → 4940be3                  PR #23: targeted run-rule
       ├─ ecabeb7                        v0 feasibility spike
       ├─ d98c112 → 788fa6e             arena-v0 → receipt-spike stop note
       └─ receipts-v1 → 8c4e60d
            ├─ 96ab7be                  count-floor experiment
            └─ logical-v1 → 83c0444     PR #42 implementation snapshot
                 ├─ 4a2b530             relaxed-support canaries
                 └─ 06557b1             original campaign report

parallel: PR #22 relations-based proof encoding
parallel: PR #49 relational causal-slicing design only
```

PR [#23](https://github.com/saulshanabrook/egglog-encoding/pull/23) closed
unmerged, but its work is ancestral to PR #42. PR
[#22](https://github.com/saulshanabrook/egglog-encoding/pull/22) merged the
relations-based proof encoding and later entered logical-v1 through `main`.
PR [#49](https://github.com/saulshanabrook/egglog-encoding/pull/49) was Eli
Rosenthal's separate, five-commit, design-only relational slicing proposal;
it copied no PR #42 implementation and closed unmerged after three minutes.

## Technical chronology

### May 18–20: precursor proof-backend work

A session in `egglog-proofs-new` developed a witness-oriented proof-backend
RFC around validated slices, canonical lookups, and fail-closed ambiguity. It
did not produce this implementation, but it established constraints that
reappeared in the July design.

### July 20–22: v0 and arena-v0

The immediate trigger was Reeves et al.'s proof-skeleton paper. Within the
first hour, the user proposed the core analogy: record a native run, slice
backward from the desired result, and defer expensive proof work to the small
retained problem.

The v0 branch (`ecabeb7`) was a five-commit feasibility spike
(+4,899/−129 against `1cc0e8a`). It produced a 504-byte artifact that passed
strict proof testing roughly 14 hours after the opening request.

Arena-v0 (`d98c112`) grew to 97 commits (+35,215/−417 against `1cc0e8a`) and
a 15,911-line `egglog/src/causal_slice.rs`. It replayed retained firings by
generating selectors that searched the replay database. That approach failed
decisively on Hardboiled: final causal proofs took 29.9–30.5 seconds versus
0.637–0.644 seconds for full proofs, or **46.5–47.7×**. The trace also exposed
one partial selector matching 84 groundings. Search-based replay was both slow
and unable to name an exact grounding reliably.

Earlier encouraging Eggcc, Pointer, and Luminal results came from different
intermediate commits, not one common `ef15a734` checkpoint; they should not be
treated as a single final cross-workload comparison.

### July 22–24: exact receipts and repeated contract changes

The next design moved recording into the backend sites where match, merge,
equality, and rebuild information existed. Direct proof-side value translation
and selector replay were rejected. A source-projection design was considered;
the eventual implementation instead selected exact grounded events and
replayed them through the existing engine using checked aliases and list-form
`run-rule`.

The receipts branch introduced stable facts, precise premise transport,
reasoned equality edges, container and rebuild landmarks, check roots, and
source catalogs. A preliminary one-round screen reported Math at 27.0× ordinary
and Eggcc at 1.49×. After the first fixes, the accepted three-round gate still
measured Math at 5.44× (95% CI 4.36–6.95×) and Eggcc at 1.46×
(1.36–1.59×). The preliminary 27× result should not be confused with that
post-fix gate.

Three July ablations then influenced the redesign: exact recording 2.27×,
count-only observation 0.97×, and record-then-discard 1.90×. They were useful
signals but weak evidence: two were one-round diagnostics, while the
count-only three-round point estimate had a 0.857–1.103× interval. Later
decisions treated them too strongly and for too long.

### July 24–29: logical support, end-to-end replay, and correctness

The logical-support branch stopped optimizing the recorder in isolation and
built the missing end-to-end path. The first all-five run had suite ratio
0.177× full proofs, but Hardboiled still lost at 2.42×. Profiling showed that
its small slice produced 1,564 aliases for only 121 distinct structural calls.
Deduplicating aliases at a wave boundary reduced the artifact to 121 aliases
and brought proof replay to about 72 ms.

The first accepted six-round endpoint (`5de2fa8`) measured suite wall time
0.134–0.137× full proofs. A subsequent cleanup endpoint measured
0.132–0.135×. Those comparisons used the same binary for the two treatments
and all five workloads passed unchanged checks.

A broader correctness campaign then exercised the repository corpus and
converted capture panics or replay errors into implemented cases or explicit
fail-closed boundaries. One stubborn equality case yielded the campaign's
most durable semantic result: replaying an action requires the equality state
that determined the action's **denotation before it ran**, not merely the
action text and the equality edge it eventually created.

The implementation was reorganized into provenance capture/view/explanation
and slicing backward/replay modules. The experiment ledgers, literature
review, recorder report, and architectural review were removed from the tree
but remain recoverable from the parent of `fd4a4fd`.

PR #42 opened on July 29. It received no submitted GitHub review; CodeRabbit's
final attempt skipped because 113 selected files exceeded its 100-file limit.
This is separate from the extensive internal read-only review recorded in the
ledgers.

### August 3–5: parallel design, main merge, and recorder stop

PR #49 supplied a separate relational slicing design on August 3. Therefore
the July 31–August 3 gap applies only to the primary Codex implementation
session, not to all repository work on slicing.

After merging `main` into the feature branch, the final same-binary benchmark
reported sliced proofs at 0.470–0.643× full proofs. A cross-revision diagnostic
found full proofs falling from 3.843 seconds to 1.923 seconds while sliced
proofs moved from 1.866 seconds to 1.953 seconds. This is consistent with the
merged proof-mode optimizations shrinking the denominator; it does not isolate
one cause or establish a slicing regression.

A later machine-local phase probe on Math measured median ordinary-process wall
at 0.4628 seconds. Within sliced runs, median internal phases were capture-run
1.0081 seconds, view-and-select 0.6837 seconds, replay-run 7.47 ms, and the full
in-process pipeline 1.7198 seconds. It showed that capture and selection, not
proof replay, dominated the sliced run.

The proposed “producer-guided support journal” then started with a falsifying
lower-bound experiment. Disabling rule-premise witnesses did not bring the
remaining capture pipeline under 1.5× ordinary, so the journal stopped before
production implementation. The exact diagnostic patch was not archived,
which limits independent reproduction; the raw interleaved output and binary
and input hashes remain machine-local.

### August 6–12: report, closure, and drift

Commit `06557b1` added the original report at 13:35 UTC on August 6. All PR
checks completed successfully by 13:44. The author closed PR #42 unmerged at
13:51 with the explanation “Closing due to not fitting into paper narrative.”
The remote feature branch has received no later implementation commits.

As of August 12, `origin/main` is `7600c192`, 39 main-side commits past the old
merge base. Sixty-two paths are modified on both sides. That is overlap, not a
claim of actual merge conflicts, but no rebase, integration test, or sliced
benchmark against current `main` has been performed.

## Measurements

### Final published benchmark at `83c0444`

Ratios are `sliced-proofs / comparison`; below one is faster/lower.

| Workload | Versus proofs, wall (95% CI) | Versus ordinary, wall (95% CI) |
|---|---:|---:|
| Math | 0.707–1.48× | 2.48–5.56× |
| Eggcc | 0.569–0.706× | 1.34–1.59× |
| Pointer | 0.419–0.558× | 1.38–1.96× |
| Hardboiled | 0.499–0.710× | 1.72–2.16× |
| Luminal | 0.165–0.306× | 1.27–1.96× |
| **Five-file suite** | **0.470–0.643×** | **1.72–2.23×** |

The setup was the main backend, `-j 1`, a 120-second timeout, six rounds per
treatment and file, and 90/90 successful observations. Herbie was excluded;
Pointer used its configured fact directory. Math's proof comparison is
inconclusive at 95% confidence, not a demonstrated slowdown or win.

Peak RSS was less uniformly favorable:

| Workload | Versus proofs, RSS (95% CI) | Versus ordinary, RSS (95% CI) |
|---|---:|---:|
| Math | 1.30–1.32× | 5.78–5.86× |
| Eggcc | 0.687–0.698× | 3.86–4.04× |
| Pointer | 0.637–0.646× | 1.54–1.56× |
| Hardboiled | 0.514–0.545× | 1.82–1.94× |
| Luminal | 0.243–0.248× | 1.27–1.29× |

Thus sliced proofs used less memory than full proofs on four workloads, but
more on Math, and used more memory than ordinary execution on all five.

### Witness-disabled capture lower bound

| Quantity | Result |
|---|---:|
| Fixture | Math source through `(run 11)`, final check omitted |
| Post-warmup paired samples | 6 |
| Ordinary median | 0.4565 s |
| Capture-only wall median | 1.0631 s |
| Internal `run_program` median | 1.0306 s |
| Paired-median capture/off ratio | **2.213×** |
| Observed paired range | 2.041–2.488× |

This experiment excludes rule-premise witness construction and publication,
but retains fact/equality/cause recording, zero-premise firing publication,
trace hooks, and capture-aware effect execution. It rules out premise-only
journal changes under the same remaining recorder. It does **not** prove that
witnesses cost zero, attribute the residual to individual data structures, or
rule out fact-local, annotation-only, or two-pass designs that change recorder
responsibility.

### One-round August 4 diagnostic

The local `e9f7b97` cache contains one dirty-checkout point per file for
sliced-proofs versus ordinary execution: Pointer 1.21×, Luminal 1.52×, Eggcc
1.66×, Hardboiled 2.32×, and Math 3.29×. These are descriptive single samples,
not the final clean estimates; the six-round intervals above supersede them.

## Validated technical findings

### 1. Structural syntax has historical denotation

Consider:

```lisp
(datatype E (A) (B) (C))
(A)
(B)
(C)
(union (A) (B))
(union (B) (C))
(check (= (A) (C)))
```

At the second union, `(B)` may already denote the class represented by `(A)`.
Replaying only the second textual union in a fresh graph changes its native
endpoints. A selected equality carrier therefore needs strict pre-event
closure over the history that gave its source terms their recorded denotation.
The selected edge cannot justify its own prerequisites.

### 2. Syntax is not occurrence identity

A constructor row may be deleted and recreated with identical syntax but a
different native value and causal history. Stable `FactId`s, rekey history,
and tombstones are not presentation metadata: they delimit which occurrence a
later grounded event read.

### 3. Search-based replay is the wrong cost center

Arena-v0 paid plan construction and database search once per retained event
and still could not distinguish every grounding. Recording exact matched
premises when the engine has them and replaying fully grounded events removes
both the selector ambiguity and the replay joins.

### 4. Trace validation and proof validation are distinct

Strict proof replay can prove an emitted program against that program's own
axioms. It does not by itself establish that every top-level action in the
artifact came from the original program. Any future “any valid support” design
therefore needs an independent syntactic containment check; proof testing
cannot replace it.

### 5. Non-monotone effects remain observable

The relaxed-support review produced a merge counterexample in which omitting a
delete changes a later merged value. “Any valid proof” does not make removals
or merge reads disappear. It only relaxes which valid grounding supplies a
positive dependency.

### 6. Performance conclusions expire with their endpoints

The dramatic July proof speedup and the later witness-disabled result show why
architecture decisions cannot rest on a point estimate from an older binary.
Every performance claim in a continuation should name both endpoints, input
hashes, treatments, and the code revision.

## Rejected, paused, and open directions

| Direction | Status | Evidence boundary |
|---|---|---|
| Selector queries over the replay graph | Rejected | 46.5–47.7× on Hardboiled and non-unique selectors |
| Direct ordinary-to-proof value translation | Rejected | Would duplicate proof-side semantics across graphs |
| Exact engine receipts plus grounded replay | Implemented on branch | Correct for the explicit supported boundary; not merged |
| Producer-guided support journal | Stopped before production code | Witness-disabled lower bound misses the 1.5× gate under the retained recorder |
| “Any valid support” | Characterization only | Sibling commit `4a2b530` adds five tests, not an implementation or proof of completeness |
| Herbie support | Deferred | Push/pop history is not modeled |

The any-valid-support idea remains a plausible **contract change**, not a
completed simplification. The five canaries identify required cases, including
coherent lanes, bounded over-retention, removals, and ordered checks. They do
not implement a journal, containment audit, merge-boundary enforcement, or
artifact-size gate. Earlier estimates of 1,400–2,000 removable lines were not
validated.

If this work resumes, the evidence suggests this order:

1. Rebase or re-derive the feature on current `main`; resolve the 62-path
   overlap and repeat the corpus and five-workload validation.
2. Choose the product contract explicitly: exact historical execution or any
   contained valid support.
3. If 1.5× ordinary remains mandatory, change what the recorder stores rather
   than redesigning premise witnesses again. Archive the diagnostic patch and
   remeasure an optimistic lower bound before production work.
4. Add push/pop semantics only if Herbie is part of the target corpus.

## Related work and calibration

The campaign began from an analogy to Reeves et al., [*A General Approach for
SMT Proof
Skeletons*](https://link.springer.com/chapter/10.1007/978-3-032-32589-1_10)
(IJCAR 2026). That work logs a partial SMT proof, trims propositional support,
and lazily justifies retained theory lemmas. It does not rerun a sliced source
program; applying its trim-first/delayed-justification idea to egglog was the
campaign's inference.

Zhao, Subotić, and Scholz's [*Provenance for Large-scale
Datalog*](https://arxiv.org/abs/1907.05045) is the closest recorder-cost
calibration. The 2019 version reports 1.27× average runtime and 1.45× memory;
the [TOPLAS version](https://doi.org/10.1145/3379446) reports 1.31× and 1.76×.
It stores rule/minimal-height tuple annotations and reconstructs a
minimal-height proof, under monotone Datalog semantics. Those numbers are
precedents, not direct performance targets for egglog's equality, merge, and
removal history.

The equality side follows a separate literature: Nieuwenhuis and Oliveras's
[*Proof-Producing Congruence
Closure*](https://doi.org/10.1007/978-3-540-32033-3_33) recovers explanations
from an annotated forest, while Flatt et al., [*Small Proofs from Congruence
Closure*](https://arxiv.org/abs/2209.03398), retain redundant edges and use a
greedy algorithm to reduce proof size without asymptotic overhead. These works
address equality explanation, not grounded rule-firing provenance.

Köhler, Ludäscher, and Smaragdakis's [Datalog debugging
experiment](https://www.cs.ucdavis.edu/~ludaesch/pubs/DeclarativeDebugging.pdf)
gives one concrete warning about eager firing bindings: a reported case grew
from 15.4 seconds to 51.3 seconds while storing 64 million firings. It does not
justify a generic “all eager witness systems cost 2–3×” claim.

Record/replay is only an analogy. The [rr
paper](https://arxiv.org/abs/1705.05937) reports 1.49–1.79× recording on four
low-parallelism workloads and 7.85× on parallel `make`; there is no single
universal “exact replay overhead.”

Upstream egglog PR
[#725](https://github.com/egraphs-good/egglog/pull/725) remains an open proof
refactor. Its CodSpeed report found three 5.48–7.31% regressions, but did not
isolate their cause. PR
[#837](https://github.com/egraphs-good/egglog/pull/837) later removed an older,
unused backend proof implementation in favor of the new proof encoding. They
are useful design archaeology, not a controlled validation of this recorder.

The campaign's scoped review did not identify a published system combining
grounded rule provenance, e-graph equality/rebuild history, replay-observable
removals, and source-level strict proof replay. That is a scoped search result,
not an exhaustive novelty claim.

## Code and validation accounting

At implementation snapshot `83c0444`, relative to merge base `6ef88f1`:

| Class | Files | Additions | Deletions | Net |
|---|---:|---:|---:|---:|
| Production-path classifier | 76 | 27,971 | 1,789 | +26,182 |
| Tests, fixtures, snapshots, corpus | 71 | 14,901 | 485 | +14,416 |
| Documentation | 4 | 682 | 7 | +675 |
| Manifests and lockfile | 5 | 47 | 0 | +47 |
| **Overall** | **156** | **43,601** | **2,281** | **+41,320** |

The “production” label is a path classifier, not a semantic audit: manifests,
Markdown, tests/test-named files, and `test-support` are separated; remaining
files fall into production. It also classifies eight deleted root
`output.*.log` files as production.

At original-report commit `06557b1`, the report raised the overall diff to 157
files, +44,007/−2,281. This revision changes only that report. Physical
subsystem sizes at `06557b1` are:

- `core-relations/src/provenance/*.rs`: 9,820 lines, including 641 test lines
  and 2,387 cold-explanation lines;
- slicing Rust: 5,273 lines, including 2,319 test lines and 2,954
  implementation lines; and
- the slicing design document: 573 lines.

Thus “9,820 lines of recording” is misleading: that directory also includes
tests, the borrowed view, data models, term projection, and cold explanation.

The clean CI run for original-report commit `06557b1` completed successfully
on August 6. It covered the Python and Rust jobs, benchmark smoke, and CodSpeed
checks. There were no submitted GitHub reviews. No equivalent validation has
run after integrating current `main`, because no such integration exists.

## Process retrospective

Three practices repeatedly improved the result:

- falsifying a design with the cheapest decisive probe before production work;
- preserving exact commands, SHAs, and hypothesis outcomes in ledgers; and
- reducing semantic surprises to small runnable counterexamples.

Two practices repeatedly hurt it:

- carrying old benchmark numbers forward as current architectural facts; and
- letting caveats disappear when evidence passed through several agent
  summaries instead of a durable ledger.

The raw agent-accounting numbers are not engineering-effort measures. Through
the campaign cutoff on August 5, top-level API counters across the six campaign
root logs sum to about 4.90 billion input tokens (98.3% cached) and 9.56 million
output tokens. There are 1,868 descendant session files through that cutoff;
summing each file's first-to-last timestamp gives 2,068.5 heavily overlapping
span-hours that include idle time. Four implementation/review logs contain 189
deduplicated user interventions. These figures describe the orchestration
record, not labor, compute, cost, or causal contribution. The original report's
model-by-model comparison and subjective attribution have therefore been
removed.

## Evidence index

### Durable branch and GitHub evidence

- PR [#42](https://github.com/saulshanabrook/egglog-encoding/pull/42): final
  description, benchmark tables, validation, closure reason, and live state.
- Implementation snapshot `83c0444`; original report commit `06557b1`; current
  `origin/main` `7600c192`.
- Branch-only [design guide](egglog/src/slicing/check_directed_replay.md).
- Branch-only [retained-data
  reference](egglog/core-relations/src/provenance/mod.rs).
- Retired records, recoverable with:

  ```bash
  git show fd4a4fd~1:.codex/causal-slice-v1/EXPERIMENTS.md
  git show fd4a4fd~1:.codex/causal-slice-logical-v1/EXPERIMENTS.md
  git show fd4a4fd~1:.codex/causal-slice-v1/RESEARCH-recorder-cost-2026-07-24.md
  git show fd4a4fd~1:.codex/causal-slice-v1/LITERATURE-REVIEW.md
  git show fd4a4fd~1:.codex/causal-slice-v1/REVIEW.md
  ```

### Machine-local evidence

- Final one-round diagnostic cache:
  `/Users/saul/p/wt/egglog-encoding/pr42-agent-causal-slice-logical-v1/.reports.jsonl`.
- Support-journal status and raw phase/floor data:
  `/Users/saul/p/wt/egglog-encoding/pr42-support-journal/.codex/support-journal/`.
- Historical benchmark caches in the arena-v0, receipts-v1,
  count-floor, and logical-v1 worktrees.
- Codex session logs under `/Users/saul/.codex/sessions/2026/` and their
  rollout summaries under `/Users/saul/.codex/memories/rollout_summaries/`.

These paths are workstation evidence, not branch contents. In particular, the
diagnostic patch that produced the witness-disabled binary was removed rather
than archived byte-for-byte.

### Reproduction checks for current status

```bash
git fetch origin --prune
git ls-remote origin refs/heads/main refs/heads/agent/causal-slice-logical-v1
gh pr view 42 --repo saulshanabrook/egglog-encoding \
  --json state,mergedAt,headRefOid,additions,deletions,changedFiles,reviews
git diff --shortstat 6ef88f1...83c0444
git diff --shortstat 6ef88f1...06557b1
git diff --shortstat 6ef88f1...HEAD
git rev-list --left-right --count 06557b1...origin/main
```
