# Bounded consumer review of integrated plan

Disposition: **no material correctness, scope, attribution, or implementation-path blocker found** within the consumer domain. The plan is actionable as a reviewed discovery/execution process; it does not assert that any consumer is already eligible or impactful. No revision request is required from this review.

Reviewed on 2026-10-17:

- `plan.md`, SHA-256 `de50b73fc633567d3a17ee25be328ac1e25664c9785c85d630347173e3c268fc`.
- `planning/consumers.md`, SHA-256 `617f7662d65b7575725b3333f3a9dbdf153df1b522024cc10ba784b7796f403f`; source evidence at EggCC `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b` and the separately identified frozen prototype patch.

Scope was a single comparison of the integrated plan with the prior consumer note. No new broad source scan, compiler invocation, test, build, benchmark, or source/evidence modification occurred. Only this review file was written.

## Material boundaries checked

| Boundary | Review outcome |
| --- | --- |
| Remaining-child rule versus injectivity | Correctly separates reverse congruence on unmarked constructors from marked-only forward disequality and equal-parent cancellation. Parent disequality without equal siblings yields a disjunction, not a chosen-child fact. |
| Overflow leads | Correctly labels them untested, requires defined fixed-width inputs and a minimized unmodified-baseline failure, distinguishes wrong output/panic/timeout, and requires separate encoding relevance or an explicit ancillary label. The existing Const guard is not counted as new encoding detection. |
| Active alias replacement and attribution | Correctly includes the direct primitive demand control alongside query and materialized pairs. Shared analysis/closure and consumer rewrites must be separated; a demand-placement speedup cannot silently become an injectivity claim. |
| Real workload reachability | Correctly states that csrmv adjacent rowptr reads have no intervening write consumer, matrix loops cross roots, and existing dynamic call/loop forms are outside the current keys. Call/lifetime/bounds proofs and an actual hot consumer precede integration. |
| Tuple law | Correctly keeps arbitrary Concat unmarked and requires equal prefix lengths, not merely equal total arity. The linked consumer note's matching-context/type and initially finite-pure-tuple restrictions remain part of the law review before implementation; the seed-table shorthand does not waive them. |
| False-Eq propagation | Correctly requires a context-local, bottom-aware bridge. The general query extension does not authorize global assertions from unreachable branches or translate Expr disequality into pointwise runtime nonalias. |
| Mutable versus immutable data | Correctly excludes existing mutable interval/points-to annotation chains. Free metadata is only a candidate after a concrete missed check or removable cost is identified. |
| Full pipeline and stopping | Correctly preserves actual native extraction/reconstruction, non-null output checks, selected-test counts, transformation receipts, independent repeated measurements, and evidence-backed exhaustion rather than a fixed prototype quota. |

The remaining unknowns are experiment decisions already represented by the plan: whether the baseline arithmetic triggers actually occur, whether NoAlias work is material, whether direct primitive guards dominate, whether fixed-split cancellation is redundant with projections, and whether a scoped false-Eq model or hot loop-memory consumer is worth implementing. None is a reason to claim success or exhaustion during setup.

## Commands used

```sh
cat /Users/saul/p/egglog-encoding/goals/eggcc-encoding-impact/plan.md
cat /Users/saul/p/egglog-encoding/goals/eggcc-encoding-impact/planning/consumers.md
nl -ba /Users/saul/p/egglog-encoding/goals/eggcc-encoding-impact/plan.md | sed -n '95,165p'
```

Python `Path.read_bytes` plus `hashlib.sha256` recorded the two reviewed file identities above; `Path.write_text` created this review only. No implementation was authorized or started by this review.
