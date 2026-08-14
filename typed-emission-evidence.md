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
- **Authority:** implementation and local checkpoint commits on
  `codex/frontend-overhead-minimization`; no push, PR publication, or upstream
  mutation without a separate user request.
- **Coordinator:** root agent owns integration, acceptance decisions, history,
  and final gates.
- **Implementation worker:** binder-spike circle owns the portable key model,
  shared resolver extraction, sequential outer-EGraph binder, and focused tests.
- **Research circles:** accounting owns read-only timing attribution; conversion
  census owns the exhaustive generated-form map.  Neither may edit production
  code.
- **Stop rule:** stop the campaign before encoder-wide conversion if the retained
  spike cannot establish semantic/state parity or if its suite-wide binder
  residual extrapolates above 150 ms after trying registration receipts.  Keep
  only independently useful resolver/atomic-registration work if that happens.

**Outcome:** the retained spike is **NO-GO**.  Its optimistic production-like
corpus floor was 231.257 ms after registration receipts, 81.257 ms above the
precommitted 150 ms boundary.  Commit `57c1d53` preserves the complete
differential probe in branch history; `5cd61ca` removes the binder, dual path,
family sidecar, and migration oracle from the final tree.  No generated emitter
family was converted and the legacy encoder remains the sole production path.

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
its action/ruleset leaves measure downstream execution.  Five generated parser
edges (one schedule, two facts, and two expressions) also bypass the timed
program parser and currently land in `frontend_other`.  The priors intentionally
do not book install or rule-planning savings.

| Generated family | Gross removable prior | Conditional net prior | Evidence basis | Provisional half-net checkpoint |
| --- | ---: | ---: | --- | ---: |
| Ground actions, source globals, and extraction setup | 400 ms | 350 ms | Actions were 64.18% of Luminal's proof-minus-off sampled typecheck; these forms also reparse and remove globals | 175 ms |
| Instrumented source rules, rebuild, and subsumption rules | 300 ms | 260 ms | Rules were 30.77% of Luminal's proof-minus-off sampled typecheck plus an unmeasured parse/desugar share | 130 ms |
| Headers, sorts, functions/views, proof declarations, and indexes | 160 ms | 130 ms | Static generated census and the remaining unclassified frontend pool | 65 ms |
| Checks, schedules, extraction command, and passthrough wrappers | 40 ms | 30 ms | Remaining parser edges and low-volume forms | 15 ms |
| **Total** | **900 ms** | **770 ms** | Conditional on a 130 ms total binder residual | **385 ms** |

For family `k`, the accountable result is
`net_k = measured_legacy_generated_frontend_k - measured_bind_k`; the fixed net
numbers above are only the original priors under an assumed 130 ms aggregate
binder residual.  A 20% reduction of the frozen 3825.591 ms proofs-over-off
delta is 765.118 ms, so a 900 ms gross pool permits at most **134.882 ms** of
binder residual.  The 150 ms H1 boundary remains a broader architectural
kill-line, but would yield only 750 ms (19.605%) under that gross prior.

The first converted family is selected by fresh tagged attribution, not by this
table's ordering.  Until that exists, actions-first is only the qualitative
Luminal prior.  After that family is oracle-green, stop and reassess if its
measured suite saving is below half of its remeasured net budget.  Reattribute
rather than silently moving missed milliseconds to later families.

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
would also need unmeasured IR construction time and confidence-bounded wall
validation.  It does establish that a future redesigned attempt should target
rules before actions, and should report both the 150 ms architecture threshold
and the 275.172 ms user-outcome budget.

## Architectural invariants

1. Generated IR is portable: it contains stable sort/function/primitive keys,
   local variable IDs, literals, and origin metadata, never checker-universe
   `ArcSort`, `FuncType`, `ResolvedVar`, `ResolvedCall`, primitive IDs, or backend
   IDs.
2. One generated batch corresponds to one top-level source command.  The binder
   walks it lexically against the outer execution EGraph, commits declarations
   before dependent siblings bind, binds the whole batch before execution, and
   returns a one-shot `BoundBatch<ResolvedNCommand>`.
3. The batch is prefix-committing, not transactional.  Each declaration is
   prepare/commit atomic.  Existing runtime ordering, `Fail`, and push/pop
   behavior remain unchanged.
4. Primitive matching has one implementation.  The generated binder and
   `ResolvedCall::from_resolution` delegate to the same extracted resolver.
5. A binder resolution cache is keyed by call kind, head, full signature,
   context, and that head's generation.  Registrations invalidate only affected
   names; the cache never outlives its execution-universe scope.
6. Extraction setup is emitted directly as its post-`remove_globals` internal-let
   function plus set form.  No handwritten general globals normalizer is added.
7. The migration oracle may live in intermediate commits only.  Final production
   code has one typed emitter, its verifier/pretty-printer, and no generated
   source parser, desugar, inference, or global-removal fallback.
8. PR #947 and proc-macro/quasiquote infrastructure are outside this campaign.

## Hypotheses and decisive probes

| ID | Hypothesis | Probe | Acceptance boundary | Status |
| --- | --- | --- | --- | --- |
| H1 | Exact-key sequential binding is much cheaper than generated inference. | Bind a declaration plus dependent action and one rule in both seminaive context pairs; measure warmed and cold key resolution. | Extrapolated suite residual at most 150 ms after registration-receipt optimization. | **Failed:** 231.257 ms optimistic production-like floor after 10,873 receipt hits |
| H2 | Portable keys prevent checker/execution-universe leakage. | Bind equivalent batches against independently seeded checker and execution EGraphs; compare stable projections and reject copied handles. | Output and state projection identical to legacy; wrong-universe canary rejected. | Command parity passed for 4,507 real proof-mode batches / 16,967 commands plus focused wrong-universe tests; independent state oracle was not reached |
| H3 | Per-name generations preserve overload ambiguity without cache thrashing. | Warm a unique primitive call, register a new same-signature overload, resolve again. | Second resolution reports the same ambiguity as uncached resolution; unrelated-head cache entries remain hits. | Focused probe passed |
| H4 | Atomic declaration registration can be shared without source-mode drift. | Invalid duplicate sort/function/index and invalid merge tests before/after refactor. | Successful behavior unchanged; failed declaration leaves no replacement/partial state. | Focused source registration tests passed; retained shared registration code remains subject to final full-suite validation |
| H5 | Generated output is a `remove_globals` fixed point except explicit extraction lowering. | Corpus-wide oracle projection and direct fixed-point test. | No generated top-level Let/LetBegin/global refs; cloned remove_globals is structurally identical. | Open |

The smallest honest family probe tags each emitted command at its origin and
records exclusive generated parse (all five helpers), desugar, typecheck,
global-removal, bind, and registration-receipt time plus command/cache/node
counts.  Final command shape is not a sufficient classifier because headers,
pending declarations, source-derived output, and maintenance output are
interleaved.  Any persisted version of that probe requires a timing-summary
schema bump; it may instead remain an opt-in migration sidecar and be deleted
with the oracle.

Suite binder residual is the sum, over the ten files, of each file's mean bind
nanoseconds divided by one million.  Do not divide by the file count or multiply
by the round count.  Before corpus integration, extrapolation must separately
measure batches, declaration receipts, cold misses, warm hits, and verifier
nodes in both `(Pure, Write)` and `(Read, Full)` context pairs and use the 95%
upper bound.

## Checkpoints

- **Spike GO:** H1-H4 pass, key count and cache behavior recorded, binder residual
  at most 150 ms, its target-specific position relative to 134.882 ms reported,
  and the legacy/typed state projection is green.
- **First-family reassessment:** the highest-attributed family is fully converted
  and oracle-green.  Descope/abort if it delivers less than half its registered
  net budget unless fresh attribution proves the budget belonged elsewhere.
- **Completeness:** every generated command and nested form has a typed path;
  generated frontend counters are zero; the legacy emitter and five generated
  parse helpers are deleted from the final tree.
- **Performance:** balanced/reversed endpoint order, aggregate default suite
  improves in both orders, at least one file has a significant improvement, and
  term/off have no meaningful regression.  Overall 20% is a target, not a
  correctness condition.
- **Deadline:** if every family is not oracle-green by 2026-10-19, stop treating
  the 2026-11-16 milestone as achievable and re-scope explicitly.
- **Final validation:** focused binder/verifier tests, `make proof-tests`,
  `make check`, `make benchmark-smoke`, and balanced 12-round
  `./bench.py --detail rulesets` evidence.

The final performance run uses one append-only report: six rounds baseline-first,
six rounds candidate-first, then a cache-only combined 12-round report.  Require
improvement in both six-round orientations and use the combined result for the
estimate; the JSONL observations are independent rather than paired.

The Spike GO checkpoint was not reached, so the later family, completeness, and
end-to-end performance checkpoints are intentionally not applicable to this
campaign run.

## Evidence log

| Date | Revision | Evidence | Decision |
| --- | --- | --- | --- |
| 2026-08-14 | `ffb8ae435bd6` | Investigation baseline and clean MISAAL/Luminal profiles frozen above. | Begin retained binder spike; do not start macro or encoder-wide conversion first. |
| 2026-08-14 | `a2f6339` | V4 audit proved that family attribution is unavailable and five helper parser edges are charged to other-frontend. | Treat family budgets as low-confidence priors; add tagged migration attribution and use gross minus measured bind. |
| 2026-08-14 | `92af00a` | Shared call resolver and name-local generations pass overload invalidation; Function registration now rolls back its provisional type and SymbolGen on failure. Release resolver-only probe: cold median 3424 ns/max 12908; warm median 270 ns/max 585. | Retain prerequisite, explicitly treating failed-declaration state cleanup as a source behavior fix. Do not claim Spike GO: the probe excludes batch/verification/registration, full H2 is absent, and Sort/Index atomicity remains. |
| 2026-08-14 | `69521b6` | Replaced per-function full `SymbolGen` snapshots with owner-checked journaled checkpoints. A clean canary restored Luminal generated typecheck to 1.00093x of the frozen baseline; 10,000 no-merge declarations improved from about 1.28 s to 147.8 ms. | Retain the independently useful fix; the temporary binder work had exposed a quadratic full-map clone. |
| 2026-08-14 | `57c1d53` | Exact differential probe covered 4,507 batches and 16,967 commands. Detailed residual was 249.621 ms; fast mode retained validation but removed diagnostic timing/counters and measured 231.257 ms. Receipts hit 10,873 times and reduced shared-resolver calls from 16,731 to 5,858. Artifact: `/tmp/egglog-generated-binder-receipt-paired.TIUfxB`; diff/source/binary SHA-256 prefixes `5eca9481` / `069dce73` / `b7c30203`. | **Spike NO-GO:** the optimistic floor still exceeded 150 ms by 81.257 ms. Do not begin the encoder-wide replacement. |
| 2026-08-14 | `5cd61ca` | Deleted the generated binder, shadow driver, family instrumentation, and temporary oracle from the working tree while preserving their commits in history. | Keep one production encoder path and retain only shared engine fixes plus this ledger. |

The first generated-binder draft passed focused flat-batch parity but was
rejected because it omitted tuples, merges, sequential local lets, most
declarations, schedules, control/IO, `Fail`, and origin metadata.  The later
`57c1d53` checkpoint superseded that draft with the complete normalized command
envelope before the performance gate rejected production migration.

The intermediate differential harness and dual-path commits remain in local
branch history even though the final tree deletes them.  No oracle-green tag was
created because the Spike GO boundary failed before emitter conversion.
