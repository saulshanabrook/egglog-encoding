# P1 Pack32 closure: portfolio supersession and a fail-closed probe

P1 is terminal for this bounded search because its generic reasoning roles and
exact false-`Eq` consumer are already represented by the retained Affine,
Route, and Parts32 results. A later actual-host probe also exists, but it does
not establish the proposed Pack32 chain: its source importer rejects every
recorded query, exports nothing, and produces the same positive endpoint in
every treatment.

These are two separate findings. The portfolio comparison closes P1's novelty
claim. The later probe records one conservative implementation attempt that
failed before admission; it does not prove the Pack32 law false or the importer
impossible.

## Intended law and consumer

For `B = 2^32` and `a,b` in `U32`, the staged design defines

```text
Pack32(a,b) = bits64(B*a+b)
Shift7(a)   = bits64(a+7)
```

Unsigned quotient and remainder by `B` recover `(a,b)`, so `Pack32` is jointly
injective on the stated bounded domain. The proposed source chain was:

```text
Pack32(a,b) = Pack32(c,d)  =>  a=c and b=d
Pack32(c,a) != Pack32(a,b) and c=a  =>  a!=b  =>  c!=d
Shift7(c) != Shift7(d)  =>  exact contextual Eq=false
```

The complete law, scope requirements, domain induction, causal controls, and
primitive-only null are specified in [design.md](design.md). The historical
[handoff.md](handoff.md) accurately describes the earlier source-only staging
point, when no compiler or native command had yet run. It should be read as a
chronological record, not as the final execution status.

## Why the portfolio already closed P1

The immutable hypothesis ledger first closed P1 by mechanism and consumer
supersession. Affine and Route execute marked multi-child cancellation, use a
new child equality in sibling-guarded reverse disequality, propagate the
result through a marked constructor, and apply an exact contextual false-`Eq`.
Route also retains genuine equality and disequality intermediate rescues.
Parts32 supplies the measured combined-mechanism instance of the same consumer
class.

This comparison does not say that Parts32 alone implements bounded packing, or
that P1 could have no runtime benefit. It says that P1's remaining distinct
work is its source-specific bounded-domain and loop-transport recognizer,
rather than a generic encoding operation or consumer absent from the retained
portfolio. See the retained [Affine](../affine-integration/report.md),
[Route](../route-integration/report.md), and
[Parts32](../parts32-integration/report.md) reports and the cycle-06
[source audit](../../../../goals/eggcc-nontrivial-encoding-payoff/cycles/06-codex-audit.md).

## What the later actual probe established

The later `probe-01` artifacts execute the staged candidate and preserve the
following reduction:

| Corpus | Result rows | Native output checks | Recorded queries | Accepted | Exported |
| --- | ---: | ---: | ---: | ---: | ---: |
| [Positive](probe-01/positive-results.json.gz) | 14 | 154 | 36 | 0 | 0 |
| [Semantic negatives](probe-01/negative-results.json.gz) | 54 | 54 | 72 | 0 | 0 |
| [Loop negatives](probe-01/loop-negative-results.json.gz) | 24 | 24 | 48 | 0 | 0 |
| [Absent-context negative](probe-01/context-negative-results.json) | 1 | 11 | 0 | 0 | 0 |
| **Total** | **93** | **243** | **156** | **0** | **0** |

Every recorded native output equals its expected output. The 36 positive
queries comprise three rejected source targets in each of the 12 queried
treatments; `u0` and `off` record no importer query. Every rejection reports
`exact packing, transport, target or bounded-domain mismatch`.

All 14 positive arms have the same emitted SHA-256,
`a82d913facc9cfeaf6156378daa06d85e6756c13f4248a842536291974075e16`,
and the same native process-main SHA-256,
`9f5cd78249d9a7237ace32c7fce2e2c5c5b090f42abc1f04fa2d4d548f9663c0`.
Thus Encoding, Manual, every causal control, and U0 reach the same retained
positive endpoint. There is no admitted Pack32 inference, causal code change,
or timing candidate in this probe.

The rejection reason deliberately combines several admission checks, so these
artifacts do not identify a semantic counterexample or one uniquely proven
matcher defect. They also do not show that a bounded revision could never
admit the source, and no revision-budget exhaustion is claimed. The terminal
status remains the earlier portfolio supersession, now accompanied by an
accurate record of the later fail-closed actual attempt.
