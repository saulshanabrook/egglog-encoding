# Typed proof-encoding emission evidence

This file is the durable decision and measurement ledger for replacing generated
egglog source text with a portable typed generated IR.  Measurements are facts
only when the command, revision, and artifact are recorded here; estimates are
labelled as hypotheses.

## Mission and ownership

- **Aim:** remove the proof encoder's second parse, desugar, type-inference, and
  global-removal pipeline while preserving generated command order, proof output,
  database state, and error behavior.
- **Domain:** `egglog/src/proofs`, the generated-command driver in
  `egglog/src/lib.rs`, the shared call resolver and declaration-registration
  effects, focused tests, and benchmark evidence.
- **Authority:** implementation in the dedicated
  `codex/typed-emission-revival` worktree; no push, PR publication, or upstream
  mutation without a separate user request.
- **Coordinator:** root agent owns integration, acceptance decisions, history,
  and final gates.
- **Historical implementation roles:** the binder-spike circle owned the
  portable key model, shared resolver extraction, sequential outer-EGraph
  binder, and focused tests; accounting and conversion-census circles supplied
  read-only timing and coverage evidence.
- **Historical stop rule:** the first campaign stopped before encoder-wide
  conversion when its suite-wide binder residual remained above 150 ms after
  registration receipts. The revival below uses the subsequently approved
  outcome gate.

**Historical spike outcome:** the retained spike was **NO-GO**. Its optimistic production-like
corpus floor was 231.257 ms after registration receipts, 81.257 ms above the
precommitted 150 ms boundary.  Commit `57c1d53` preserves the complete
differential probe in branch history; `5cd61ca` removes the binder, dual path,
family sidecar, and migration oracle from that campaign's tree. At that
historical endpoint no generated emitter family had been converted. The later
revival reintroduced the typed architecture under a new gate and supersedes
that production-state conclusion.

## Revival campaign (2026-08-16)

The prior NO-GO remains valid against its pre-registered 150 ms boundary.  This
new campaign tests a different product gate: replace the generated frontend with
one typed production path, with no statistically detected regression in any
default `(file, mode)` cell and at least one independently confirmed proofs-mode
improvement.  There is no suite-level minimum; 20% remains a reported target.

- **Worktree:** `/Users/saul/p/wt/egglog-encoding/typed-emission-revival`
- **Branch/base:** `codex/typed-emission-revival` at `a54c798f980c795a2e22410da1aa3396121a7e30`
- **Historical probe:** `57c1d53`; command parity and universe rebinding passed.
  During the revival, a separately built executed twin extended state/output/
  proof/error evidence across the complete generated-command envelope before
  that twin and its alternate lane were deleted.
- **Final-state invariant — achieved in source:** the production diff contains
  only structured `GeneratedEntry`/`GeneratedBatch` emission and one generated
  resolver. The generated-text path, migration envelope, oracle, sidecar,
  instrumentation, family tags, selectors, and feature forwarding have been
  deleted rather than disabled.
- **Measurement separation:** intermediate correctness and attribution builds
  used separately hashed oracle/sidecar/verifier configurations. Those names in
  this ledger describe historical evidence only. The final source and Cargo
  manifests contain none of that machinery; final performance measurements use
  the ordinary optimized release build.
- **Origin boundary — achieved:** temporary family/origin tags from the
  intermediate harness are absent. Typed generated nodes retain only source
  spans required for diagnostics.
- **Verifier boundary — achieved:** generated builders remain private and
  typed, and every resolution-dependent or user-reachable check stays in the
  binder. The independent full-tree verifier was deleted after its historical
  ablation and differential evidence; no debug/test/release copy remains.

### Single-path cutover status (2026-08-17)

All generated families now lower directly to typed entries, including
declarations, actions, source rules, rebuild/subsumption maintenance, schedules,
checks, extraction, Input/Output, Push/Pop, and nested `Fail`. Generated errors
use a typed frontend-effects replay plus exact typed binding and never re-enter
the general source parser, desugarer, program typechecker, or globals
normalizer. Single-path regressions retain the valuable runtime, rollback,
role, receipt, Push-span, and error-span coverage after deletion of the
semantic/twin feature tests. Two test-only source-frontend comparisons remain
to pin diagnostic ordering and `SymbolGen` effects; they are not production
emission paths.

Publication requires a fresh post-merge `make check`, which owns the Python and
Rust workspace tests, clippy, rustdoc, formatting, and lockfile checks, plus a
fresh `make benchmark-smoke` for the public runner. The separate
`make proof-tests` subset need not be repeated after the superset workspace
test. The final single-path 30-cell performance protocol remains; no final
performance conclusion is recorded yet.

### Revival roles (historical)

These circles governed the intermediate dual-path measurements. They are not
runtime components and their instrumentation has been removed from the final
source.

| Circle | Domain | Aim | Stop condition |
| --- | --- | --- | --- |
| coordinator | integration, ledger, gates | preserve scope and accept only evidence-backed slices | final gates pass or a checkpoint stop rule fires |
| binder revival | generated binder and shared registration boundary | restore the probe and split correctness instrumentation from the production build | focused parity/tests pass with a clean uninstrumented build |
| rules census | proof encoder rule emitters | produce the exhaustive rules-first conversion map and ordering invariants | every rule-producing site is classified |
| instrumentation review | feature/build boundary | adversarially verify that gate binaries execute no oracle/tag/timer work | build contract is decision-complete or a blocker is proven |
| benchmark audit | 30-cell gate protocol | make the no-detected-regression and improvement-witness protocol reproducible | exact commands/artifacts/retest rules are specified |

### Revival checkpoints and disposition

1. **Completed:** restore and verify the historical binder without changing emitters.
2. **Completed:** measure a genuine verifier-off build and profile the remaining binder; do not
   credit cross-batch cache persistence again because `57c1d53` already has it.
3. **Completed:** convert the complete rules family and prove independent state/output/proof/
   error parity before performance testing.
4. **Completed for the rules checkpoint:** twelve observations per endpoint for the ten defaults in
   `off`, `term`, and `proofs`, balanced six baseline-first/six candidate-first.
   A cell whose 95% Fieller candidate/base interval has a lower bound above 1,
   or whose interval is undefined, is retested once with 36 fresh observations
   per endpoint, balanced eighteen/eighteen; the retest alone is final for that
   cell.  Every initially significant proofs improvement (`U < 1`) is also
   independently retested.  Final acceptance requires every one of the thirty
   cells to have a defined interval with `L <= 1`, and at least one identical
   proofs cell to have `U < 1` in both its initial run and its retest.  This is a
   no-statistically-detected-regression rule, not a claim of equivalence.
5. **Code cutover and Rust correctness completed; final performance pending:**
   every remaining family was converted, the intermediate parity evidence was
   preserved in artifacts/history, and both alternate pipelines plus their
   selection machinery were deleted. The single-path 30-cell release-binary
   gate remains to be run.

### Rules checkpoint result (2026-08-17)

The rules checkpoint **passed** on explicit locked feature-off release builds.
The clean baseline binary was
`3dcbcae084a858eb1d56ce0d4c7bbbc3fa797901106039a872bed8686c9bfaae`;
the typed candidate was
`e44b11f949456bd21e59491f62bc045805c23a20b94653c6803839797c739443`.
Cargo artifact metadata and binary-string scans contained no
`typed-emission-oracle`, shadow, verifier, family-tag, or migration-sidecar
markers, and poison sidecar variables produced no files.

The initial balanced run completed all 720 measured processes successfully.
Its suite candidate/baseline ratios were:

| Mode | Ratio (95% Fieller CI) |
| --- | ---: |
| off | 0.993874 (0.986991–1.000834) |
| term | 0.960683 (0.958267–0.963104) |
| proofs | 0.950867 (0.948651–0.953090) |

Exactly one cell triggered the regression retest rule: off-mode DialEgg at
1.024411 (1.008927–1.040038).  Its independent 36-observation-per-endpoint
retest was 1.004015 (0.991864–1.016294), so the retest-only final lower bound is
at most one.  Nine proofs cells initially had an upper bound below one.  A fresh
balanced 36-observation-per-endpoint proofs retest reconfirmed all nine; its
suite ratio was 0.953844 (0.952199–0.955494).  Thus every final cell has a
defined interval with `L <= 1`, and nine identical proofs cells have `U < 1` in
both the initial and independent retest.

The initial and replacement-proofs monitor logs had no unexpected
benchmark/build process; their maximum active sampling gaps were 212.819 ms and
209.814 ms.  The accepted off-mode DialEgg retest likewise had no overlapping
audit process.  An earlier proofs retest had three short read-only audit samples
overlap two rows; the entire pair was preserved under `rejected-audit-overlap-*`
and excluded before the clean replacement was collected.  Pre/post candidate
HEAD, status, tracked patch, untracked manifest, and complete source manifest
matched byte-for-byte around the accepted measurements.

The durable artifact is `/tmp/egglog-typed-rules-checkpoint.z6kExU`; its final
raw/analysis checksum manifest has SHA-256
`d3e4ceab0035e2b013cd78ddcac715fb5ed71887e70ca757cb6557ce871c5b45`.
At the time, this authorized conversion of the remaining families but not
shipping the intermediate mixed pipeline. That conversion and the required
single-path deletion have since completed; this checkpoint is not the final
single-path performance result.

## Frozen starting point

- Repository: `/Users/saul/p/wt/egglog-encoding/frontend-overhead-minimization`
- Branch: `codex/frontend-overhead-minimization`
- Revision: `ffb8ae435bd6421077b1c15826f32a6aeecf5b1b`
- Existing user file, excluded from this campaign's diff:
  `frontend-overhead-investigation.md`
- Default benchmark shape: `./bench.py --detail rulesets`, ten default files,
  six fresh rounds per endpoint, proofs versus off.
- Prior artifact command:
  `./bench.py --detail rulesets --report /tmp/egglog-frontend-overhead-ffb8ae4.jsonl --force-run`
- Prior aggregate wall time: off 3088.209 ms; proofs 6913.800 ms; delta
  3825.591 ms; proofs/off 2.23877x.
- Prior proof-specific frontend deltas: typecheck 782.395 ms; parse 181.341 ms;
  other frontend 335.905 ms; install 173.282 ms.  Typecheck plus frontend delta
  was 1472.922 ms.
- Clean MISAAL V4 profile: proof wall 145.719 ms; typecheck 64.488 ms; parse
  12.348 ms; other frontend 26.734 ms; install 23.015 ms.  Inclusive samples:
  `typecheck_program` 44.65%, `typecheck_rule` 37.38%, `Problem::solve` 15.66%,
  generated/source parsing 8.86% (92.3% under the proof encoder),
  `remove_globals` 5.41%, and generated desugaring 2.45%.
- Clean Luminal sampled-CPU attribution: generated proofs spent about 401.3 ms
  inclusively in standalone action blocks and 203.4 ms inclusively in rules out
  of 637.6 ms total typechecking per profiled iteration.  Off mode spent 15.2 ms
  and 18.3 ms respectively.  These are workload-local inclusive samples, not
  exclusive V4 leaves, confidence-bounded wall time, or suite totals.

The prior numbers are retained evidence from the investigation at the frozen
revision.  The implementation branch will record a new balanced baseline before
claiming a before/after result.

## Pre-registered savings budget

These are low-confidence priors registered before implementation, not measured
results.  They allocate an approximately 900 ms gross suite-wide removable
frontend pool using workload-local inclusive Luminal samples, the 17 generated
parser edges, and generated-form counts.  V4 has no frontend family split: its
typecheck, parse, and other-frontend leaves merge source and generated work, and
its action/ruleset leaves measure downstream execution. Five generated parser
edges (one schedule, two facts, and two expressions) also bypassed the timed
program parser and landed in `frontend_other`. The priors intentionally
do not book install or rule-planning savings.

| Generated family | Gross removable prior | Conditional net prior | Evidence basis | Provisional half-net checkpoint |
| --- | ---: | ---: | --- | ---: |
| Ground actions, source globals, and extraction setup | 400 ms | 350 ms | Actions were 64.18% of Luminal's proof-minus-off sampled typecheck; these forms also reparse and remove globals | 175 ms |
| Instrumented source rules, rebuild, and subsumption rules | 300 ms | 260 ms | Rules were 30.77% of Luminal's proof-minus-off sampled typecheck plus an unmeasured parse/desugar share | 130 ms |
| Headers, sorts, functions/views, proof declarations, and indexes | 160 ms | 130 ms | Static generated census and the remaining unclassified frontend pool | 65 ms |
| Checks, schedules, extraction command, and passthrough wrappers | 40 ms | 30 ms | Remaining parser edges and low-volume forms | 15 ms |
| **Total** | **900 ms** | **770 ms** | Conditional on a 130 ms total binder residual | **385 ms** |

For the historical migration measurement, family `k` used
`net_k = measured_legacy_generated_frontend_k - measured_bind_k`; the fixed net
numbers above are only the original priors under an assumed 130 ms aggregate
binder residual.  A 20% reduction of the frozen 3825.591 ms proofs-over-off
delta is 765.118 ms, so a 900 ms gross pool permits at most **134.882 ms** of
binder residual.  The 150 ms H1 boundary remains a broader architectural
kill-line, but would yield only 750 ms (19.605%) under that gross prior.

The revival selected its first converted family from fresh tagged attribution,
not this table's ordering. Before that attribution, actions-first was only the
qualitative Luminal prior. The resulting rules-first decision and checkpoint
are preserved above as historical governance evidence.

## Measured family attribution

The accepted post-fix run supersedes the qualitative ordering above.  It used
revision `69521b62334e86770279b0bed6008f05f5106208`, binary SHA-256
`ac9830a8732a1d721d7610fdb00a6aa70f6461b06e2abd8c5a85912264ce8630`,
ten files by six rounds, and a 250 ms process monitor.  All 60 sidecars closed
their timing/count identities, stderr was empty, no nested `fail` wrapper was
present, and the contamination log was empty.

| Generated family | Sum of file medians |
| --- | ---: |
| Instrumented source rules, rebuild, and subsumption rules | 554.621 ms |
| Ground actions, source globals, and extraction setup | 436.829 ms |
| Headers, declarations, and indexes | 47.762 ms |
| Checks, schedules, and wrappers | 2.082 ms |
| **Attributed generated frontend** | **1040.290 ms** |

The stage totals were 175.491 ms parse, 764.010 ms typecheck, 32.757 ms
desugar, and 69.077 ms global removal.  Encoder work outside nested parsing was
162.824 ms and is not booked into the conservative removable pool.  The
authoritative aggregate is
`/tmp/egglog-generated-family-fbc38a-dnFhYU/fixed/accepted-full/aggregate.json`
(SHA-256 `0f576c5fa0f4562dd609be6b98e2a6640eba8fc131e8391f62a1db8f895fd045`).

This fresh pool would permit a 275.172 ms binder residual for a literal 20%
reduction of the frozen proofs-over-off delta.  That does not retroactively
change the approved 150 ms architecture stop rule: the end-to-end typed emitter
still needed unmeasured IR construction time and confidence-bounded wall
validation. It established the rules-first order used by the revival and the
need to report both the 150 ms architecture threshold and the 275.172 ms
user-outcome budget.

## Architectural invariants

1. Generated IR is portable: it contains stable sort/function/primitive keys,
   local variable IDs and roles, literals, and source spans, never
   checker-universe `ArcSort`, `FuncType`, `ResolvedVar`, `ResolvedCall`,
   primitive IDs, backend IDs, or profiling-origin metadata.
2. One generated batch corresponds to one top-level source command.  The binder
   walks it lexically against the outer execution EGraph, commits declarations
   before dependent siblings bind, binds the whole batch before execution, and
   returns the one-shot resolved command vector consumed by the existing
   executor.
3. The batch is prefix-committing, not transactional.  Each declaration is
   prepare/commit atomic.  Existing runtime ordering, `Fail`, and push/pop
   behavior remain unchanged.
4. Primitive matching has one implementation.  The source constraint resolver
   and generated binder both call `ResolvedCall::from_resolution`.
5. A binder resolution cache is keyed by call kind, head, full signature,
   context, and that head's generation.  Registrations invalidate only affected
   names; the cache never outlives its execution-universe scope.
6. Extraction setup is represented as typed scratch entries. The binder expands
   each scratch to its hidden nullary function and set forms without invoking a
   general globals normalizer or registering scratch calls persistently.
7. The final production code has one typed emitter and one generated resolver.
   The generated source parser/formatter path, migration/oracle selectors,
   independent verifier/pretty-printer, desugar, program-inference, and
   global-removal fallbacks are absent from source and manifests.
8. PR #947 and proc-macro/quasiquote infrastructure are outside this campaign.
9. Typed generated nodes carry a stable enclosing source span: generated rules
   and maintenance schedules inherit their originating rule/command span, while
   command/action families use their enclosing command or action span and keep
   source child spans where available. `Push` retains its exact source span and
   `Span::Panic` is forbidden in emitted nodes. This improves diagnostics over
   offsets into ephemeral synthesized text; direct tests require the exact
   error class, generated head, call context, and originating source span.

## Hypotheses and decisive probes

| ID | Hypothesis | Probe | Acceptance boundary | Status |
| --- | --- | --- | --- | --- |
| H1 | Exact-key sequential binding is much cheaper than generated inference. | Bind a declaration plus dependent action and one rule in both seminaive context pairs; measure warmed and cold key resolution. | Extrapolated suite residual at most 150 ms after registration-receipt optimization. | **Failed:** 231.257 ms optimistic production-like floor after 10,873 receipt hits |
| H2 | Portable keys prevent checker/execution-universe leakage. | Bind equivalent batches against independently seeded checker and execution EGraphs; compare stable projections and reject copied handles. | Output and state projection identical to the historical generated-text lane; wrong-universe canary rejected. | **Passed before single-path deletion:** command parity covered 4,507 real proof-mode batches / 16,967 commands; the factory-built independent twin also matched frontend state, bound commands, database rows and subsumption bits, outputs and proof strings, scheduler progression, push/pop restoration, and normalized error payload/order across the generated envelope. Final direct-only tests retain the runtime and rollback canaries without preserving either comparison lane. |
| H3 | Per-name generations preserve overload ambiguity without cache thrashing. | Warm a unique primitive call, register a new same-signature overload, resolve again. | Second resolution reports the same ambiguity as uncached resolution; unrelated-head cache entries remain hits. | Focused probe passed |
| H4 | Atomic declaration registration can be shared without source-mode drift. | Invalid duplicate sort/function/index and invalid merge tests before/after refactor. | Successful behavior unchanged; failed declaration leaves no replacement/partial state. | **Passed and retained:** focused source and typed declaration tests pin prepare/commit atomicity, receipt timing, cache/generation rollback, reserved-name restoration, and prefix commit through `Fail` and Push/Pop. |
| H5 | Generated output needs no general globals-normalization pass. | Historical corpus projection plus direct structural/runtime tests. | No generated command re-enters `remove_globals`; global roles and extraction scratch expansion remain explicit. | **Passed for every family:** source-derived, path-compression, rebuild, subsumption/rekey, action, command, and extraction forms are typed. Production generated-emission files have no `remove_globals` call; role-aware binder tests and exact extraction effects cover the exceptional shapes. |
| H6 | The independent `LinearVerifier` is redundant after binder-local shape/schema checks and adds measurable residual cost. | Historical release oracle binary, six balanced verifier-on/off rounds over the ten defaults, with reverse file order and fast-ablation disabled. | Every command has differential parity; non-timing counts match; verifier-off records zero verifier time; paired suite residual decreases. | **Passed historically, then deleted:** mean reduction 41.989 ms, paired 95% interval 38.139–45.839 ms; all 4,507 batches / 16,967 commands retained exact differential parity. The final source contains only binder-local checks, not the independent verifier. |
| H7 | Repeated comparison of full portable call keys is a material part of the verifier-off binder remainder. | Profile verifier-off MISAAL and Luminal; then replace only the call-cache key lookup and repeat the same residual protocol. | Profile shows a distinct key-comparison hotspot; causal ablation preserves all parity/cache/context counts and lowers both binding and combined portableization-plus-binding. | **Failed overall:** compact signature IDs lowered binding by 9.880 ms, ratio 0.944921 (95% 0.925779–0.964458), but batch interning raised portableization by 22.214 ms and combined cost by 12.334 ms, ratio 1.038793 (95% 1.021556–1.056320). The slice was rejected. |
| H8 | Sharing immutable function signatures removes a measurable part of successful-call cloning without moving work into portableization. | Change only `TypeInfo` and `ResolvedCall::Func` ownership to `Arc<FuncType>` while preserving tuple outputs, primitive/values ownership, call keys, cache behavior, and the outer cached `Arc<ResolvedCall>`. Repeat the six-pair verifier-off/stats-off corpus protocol and source-typecheck controls. | Exact semantic/count parity; strictly positive paired 95% binder saving; combined portableization-plus-binding does not regress; source typecheck/end-to-end controls have no statistically detected regression under the campaign rule (ratio lower bound at most 1). | **Passed provisionally:** strict-cadence binder ratio 0.953418 (95% 0.932639–0.974660), saving 8.325 ms (95% 4.426–12.224); combined ratio 0.965380 (95% 0.949354–0.981677); process elapsed ratio 0.984627 (95% 0.972224–0.997189). Four-pair off/source controls were underpowered but every lower bound was below 1, so no regression was detected. Final acceptance remains subject to the 30-cell single-path gate. |

The historical family probe tagged each emitted command at its origin and
recorded exclusive generated parse (all five helpers), desugar, typecheck,
global-removal, bind, and registration-receipt time plus command/cache/node
counts. Final command shape was not a sufficient classifier because headers,
pending declarations, source-derived output, and maintenance output are
interleaved. That probe, its timing schema, and its sidecar were deleted after
they selected the rules-first order and supported the checkpoint above.

Suite binder residual is the sum, over the ten files, of each file's mean bind
nanoseconds divided by one million.  Do not divide by the file count or multiply
by the round count.  Before corpus integration, extrapolation must separately
measure batches, declaration receipts, cold misses, warm hits, and verifier
nodes in both `(Pure, Write)` and `(Read, Full)` context pairs and use the 95%
upper bound.

## Checkpoints

- **Historical Spike GO — failed under its original gate:** H1 recorded a
  231.257 ms optimistic residual, above the 150 ms boundary. H2-H4 evidence was
  retained for the separately governed revival.
- **First-family reassessment — passed:** the highest-attributed rules family
  converted, passed independent semantic and 30-cell checkpoint gates, and
  authorized the remaining conversion.
- **Completeness — passed in source and package tests:** every generated command
  and nested form has a typed path; the generated-text emitter, five generated
  parse helpers, migration envelopes, comparison lanes, selectors, and
  instrumentation are deleted.
- **Performance — final single-path gate pending:** the exact thirty-cell
  protocol above must pass. There is no
  suite-level minimum and no two-percent tolerance: overall reduction and the
  original 20% objective are reported outcomes, not acceptance conditions.
  Marginal 95% intervals are used as a pre-registered regression-detection
  policy rather than presented as simultaneous equivalence bounds.
- **Deadline — conversion met early:** every family reached the typed path on
  2026-08-17; the old 2026-10-19 conversion stop date no longer applies.
- **Final validation:** publication requires fresh post-merge `make check` and
  `make benchmark-smoke` gates. The balanced release benchmark is the only
  performance gate; the proof-test subset is covered by the workspace test in
  `make check` and need not be redundantly rerun.

The final performance run uses fresh, separate append-only reports and pinned
binary hashes.  For every mode, six observations per endpoint are collected in
baseline-first order and six in candidate-first order, yielding the initial
twelve observations per endpoint without pooling old cache rows.  A required
retest uses a new report and thirty-six fresh observations per endpoint in
balanced eighteen/eighteen order. Gate binaries are ordinary optimized builds:
the historical migration oracle, family sidecar, verifier, differential
harness, origin tags, timers, and selector are absent from source and manifests,
not merely compiled out.

The historical spike did not reach its 150 ms GO boundary. The revival uses the
separately approved outcome gate above; its single typed path and direct-only
Rust correctness gates are now complete, and its final single-path 30-cell
performance run is pending.

## Evidence log

Entries before the final cutover row describe the historical state and may name
temporary comparison lanes, features, sidecars, or verifiers that are no longer
present in source.

| Date | Revision | Evidence | Decision |
| --- | --- | --- | --- |
| 2026-08-14 | `ffb8ae435bd6` | Investigation baseline and clean MISAAL/Luminal profiles frozen above. | Begin retained binder spike; do not start macro or encoder-wide conversion first. |
| 2026-08-14 | `a2f6339` | V4 audit proved that family attribution is unavailable and five helper parser edges are charged to other-frontend. | Treat family budgets as low-confidence priors; add tagged migration attribution and use gross minus measured bind. |
| 2026-08-14 | `92af00a` | Shared call resolver and the temporary name-local generations passed overload invalidation; Function registration now rolls back its provisional type and SymbolGen on failure. Release resolver-only probe: cold median 3424 ns/max 12908; warm median 270 ns/max 585. | Retain the failed-declaration cleanup. The resolver extraction and generation map served only the rejected binder and are removed by `e88c353` and `0b93868`. |
| 2026-08-14 | `69521b6` | Replaced per-function full `SymbolGen` snapshots with owner-checked journaled checkpoints. A clean canary restored Luminal generated typecheck to 1.00093x of the frozen baseline; 10,000 no-merge declarations improved from about 1.28 s to 147.8 ms. | Retain the independently useful fix; it makes the failed-merge rollback introduced in `92af00a` cheap instead of cloning the growing symbol map. |
| 2026-08-14 | `57c1d53` | Exact differential probe covered 4,507 batches and 16,967 commands. Detailed residual was 249.621 ms; fast mode retained validation but removed diagnostic timing/counters and measured 231.257 ms. Receipts hit 10,873 times and reduced shared-resolver calls from 16,731 to 5,858. Artifact: `/tmp/egglog-generated-binder-receipt-paired.TIUfxB`; diff/source/binary SHA-256 prefixes `5eca9481` / `069dce73` / `b7c30203`. | **Spike NO-GO:** the optimistic floor still exceeded 150 ms by 81.257 ms. Do not begin the encoder-wide replacement. |
| 2026-08-14 | `5cd61ca` | Deleted the generated binder, shadow driver, family instrumentation, and temporary oracle from the working tree while preserving their commits in history. | Keep one production encoder path and retain only shared engine fixes plus this ledger. |
| 2026-08-14 | `e88c353` | Removed the now-unused call-generation map and narrowed binder-extracted registration APIs back to private source-typechecker helpers. | Do not carry probe-only state or public surface in the reduced production diff. |
| 2026-08-14 | `0b93868` | Restored the original call resolver, index registration, sort-command flow, and function metadata flow; kept a pre-backend duplicate-sort guard and local failed-merge rollback. `make check` passed the full Python, Rust, documentation, and proof fixture matrix; `make benchmark-smoke` completed 20/20 fresh runs. | Final production code contains no binder-facing registration layer or one-caller forwarding helpers. |
| 2026-08-16 | uncommitted revival checkpoint from `a54c798` | Restored the portable binder and shared registration boundary from `57c1d53`. Oracle mode passed 11 focused binder tests and a six-batch/53-command differential canary. A feature-off release binary (`7a15a4af…`) contained no oracle markers and ignored poison sidecar variables. Independent review found no shared-registration correctness regression. | Retain as an intermediate checkpoint only. The clean binary still executes the legacy frontend, all family labels are currently `misc`, and verifier-off binding is not safe to measure until binder-local shape/schema checks and feature-off tests replace verifier-only assumptions. |
| 2026-08-16 | uncommitted revival diff `7f0c4457…`, oracle binary `cb03ac38…` | Six balanced verifier-on/off corpus rounds, 120/120 sidecars, zero contamination. Verifier-on residual mean 227.255 ms; off 185.266 ms; paired reduction 41.989 ms (95% 38.139–45.839). Counts and differential parity matched for 4,507 batches / 16,967 commands. Artifact: `/tmp/egglog-verifier-ablation.qBcY3X`. | Remove the redundant standalone verifier from release after direct emission is complete; keep binder-local checks and the independent verifier in debug/tests. Profile the remaining binder before selecting allocation work. |
| 2026-08-16 | rejected call-key slice, binaries `cb03ac38…` / `cf63162b…` | Six accepted balanced baseline/candidate pairs plus three preserved contaminated rejects. Compact signature IDs and batch call interning reduced binder residual by 9.880 ms (95% 6.298–13.462), but added 22.214 ms (95% 19.966–24.461) to portableization. Combined portableization-plus-binding regressed 12.334 ms, ratio 1.038793 (95% 1.021556–1.056320), with exact parity across 4,507 batches / 16,967 commands. Artifact: `/tmp/egglog-callkey-causal.DXZIfc`. | Reject and revert the slice. Binder-only timing is not sufficient when an optimization moves structural work into direct-IR construction. Test the independent resolved-call clone cost next. |
| 2026-08-16 | H8 `Arc<FuncType>` slice, binaries `cb03ac38…` / `3d4d233b…` | Strict-cadence six-pair corpus: binder ratio 0.953418 (95% 0.932639–0.974660), combined portableization-plus-binding 0.965380 (95% 0.949354–0.981677), whole-process proof diagnostic 0.984627 (95% 0.972224–0.997189), with exact 4,507-batch / 16,967-command parity. Four-pair direct off/source controls on Luminal and MISAAL all straddled 1; no interval was wholly above 1. Observed monitor and quiescence gaps were at most 225.848/225.226 ms. The earlier favorable collection with cadence gaps above 250 ms is preserved but excluded. Artifact: `/tmp/egglog-h8-causal.XRKgjd/strict-cadence`. | Keep provisionally under the user-approved no-statistically-detected-regression rule, not as a proof of source-mode equivalence. Recheck all 30 cells on the final single-path binary. |
| 2026-08-17 | independent executed twin, uncommitted revival diff | Two factory-built EGraphs with distinct outer/source `ActionRegistry` Arcs independently run the legacy and direct lanes. Seven focused twin tests cover term, verified proofs, and proof extraction with seminaive off/on; execute source-derived globals/rules plus path-compression, ordinary rebuild, subsumption/rekey, push/pop, nested `Fail`, and a two-step choose-one scheduler; and compare frontend state, bound commands, tables/rows/subsumed bits, rulesets, outputs/proof strings, reports, proof state, cache restoration, and continuation names. Generated overload failures match class, payload, order, and state; two cases deliberately use the originating source span rather than offsets into deleted generated text. Feature-off library tests passed 160/160, oracle-feature library tests 204/204, proof fixtures 225/225, and the complete oracle-enabled workspace test including doctests exited successfully. Final pins include `twin_oracle.rs` `40411e73...`, `semantic_oracle.rs` `96eafa26...`, and `generated_binder.rs` `736f024f...`. | Semantic evidence is green for the **rules checkpoint**. Production direct-rule binding is verifier-free. Keep the independent legacy/oracle lane only through measurement, then delete it and rerun final single-path correctness gates. |
| 2026-08-16 | oracle binary `cb03ac38…`, verifier off | Samply profiles: MISAAL 19 iterations/175 binder samples; Luminal one 68.7-second iteration/97 samples. Allocation/copy/drop leaves were 48.8%/42.5%; call resolution 22.3%/35.1%; full-key hash/map/equality leaves 9.7%/19.4%; returned `ResolvedCall` cloning only 7.1%/3.2%. Artifact: `/tmp/egglog-binder-off-samply.E49SVb`. | Measure detailed-stat instrumentation tax, then test compact/precomputed call-key lookup before broader AST or shared-call refactors. Do not optimize spans or reimplement the already-persistent cross-batch cache. |
| 2026-08-16 | oracle binary `cb03ac38…`, verifier and detailed stats off | Six balanced detailed/suppressed corpus rounds. Detailed-stat tax was 5.247 ms mean, 5.175 ms median, paired 95% 1.688–8.806; all 120 sidecars retained exact differential parity and structure. Suppressed residual mean was 182.462 ms. Artifact: `/tmp/egglog-detailed-stat-tax.dMoOBo`. | Use suppressed statistics for subsequent causal binder comparisons. Treat the five milliseconds only as removal of oracle instrumentation, never as production/frontend savings. |
| 2026-08-17 | uncommitted single-path cutover from `a54c798` | All producers emit structured `GeneratedEntry`/`GeneratedBatch` values into one generated resolver. The generated-text parser/formatter path, migration envelopes, semantic/twin comparison modules, selector/feature forwarding, sidecars, family/origin tags, timers, standalone verifier/portableizer, and dual-path tests were deleted. Single-path regressions pin all-mode path compression; exact Extract/Input/Output effects and failures; panic and `Fail` prefix commit; Push and generated error spans; role/global separation; declaration receipts and rollback. Two test-only source-frontend comparisons retain exact diagnostic-order and `SymbolGen` parity without adding a production alternate path. | Rerun the root correctness and benchmark-smoke gates after merging main. Do not claim final performance until the coordinator runs the pre-registered single-path 30-cell protocol. |

The first generated-binder draft passed focused flat-batch parity but was
rejected because it omitted tuples, merges, sequential local lets, most
declarations, schedules, control/IO, `Fail`, and origin metadata.  The later
`57c1d53` checkpoint superseded that draft with the complete normalized command
envelope before the performance gate rejected production migration.

The intermediate differential harness and dual-path commits remain in local
branch history even though the final tree deletes them. The original spike
stopped before emitter conversion; the revival subsequently preserved its own
green differential/twin artifacts before completing the single-path cutover.
