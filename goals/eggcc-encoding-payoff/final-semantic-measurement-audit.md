# Final semantic and measurement-claim audit

## Verdict

**PASS. No binding semantic or measurement finding remains in the reviewed
files.**

This was a read-only audit of the final claims in `report.md`, `reference.md`,
`reproduce.md`, `acceptance.md`, and `acceptance.json`. The only write was this
audit file. It ran no compiler, build, test, native workload, timing collector,
or network command. The reviewed file identities were:

| File | SHA-256 |
| --- | --- |
| `report.md` | `062cd52464fe7f3fc1d796063344bd87b9b8b384ffd29d9dbf69f0328427f5f9` |
| `reference.md` | `2c4a185ac4fc6a9cd44667df5d1ae1493deb5f9e1d1491999ad5f6a7e6c97728` |
| `reproduce.md` | `52dfef4eb6c0a00d9aaa2b60a48f1acc6968847adc01e574952e30204cd117eb` |
| `acceptance.md` | `ae662aca0e58ff61b0a84c5a310b1158912751e6795feedf476e4cf9cd709125` |
| `acceptance.json` | `f12672f5680ec8ff3cb3d5a93831d06d46d38dd80894eefdfe805d307d1e9f28` |

The primary comparison authorities were QR7's `final-r1/inspection.json`,
`actual-binary-inspection-r1.json`, and
`timing-r1/independent-verification.json`; Parts32's
`final-reviewed/inspection.json` and
`timing/independent-verification.json`; the retained QR7 and Parts32 reports;
and cycle 06's Fable output plus independent source validation. Same-mask,
Pack32, A1, and final-validation records were checked where the final prose
quotes their measurements or counts.

## Semantic claims

### QR7

- The stated law is sound over signed i64: for fixed divisor seven,
  `K7(v)=(trunc(v/7),v-7*trunc(v/7))` reconstructs `v`, and neither the
  multiplication nor subtraction leaves the signed range.
- The reported proof path matches the captured candidate: equal quotient and
  remainder children give equal `Pair` terms; the two representation identities
  give equal `K7` terms; cancellation of marked `K7` gives `x=y`; and ordinary
  same-base congruence gives equal addresses. Only `K7` is marked.
- The final documents correctly call QR7 **injectivity-only**. They make no
  disequality-contribution claim, and the evidence contains no disequality seed
  or witness query in this chain.
- The consumer is described accurately as an **added bounded
  `Qr7MustAlias` bridge** that performs the same value/state unions as ordinary
  store forwarding. The files expressly avoid claiming that untouched U0's
  same-address rule consumed the private equality.
- The knockout/rescue description agrees with the causal inspection. The mark,
  identity, query, bridge, and consumer boundaries return to baseline as
  stated; exact word/key rescues and Manual recover the winning endpoint.
  `consumer-off` retains the relation and loses the forwarding event.
- `transport-off` is consistently identified as an export-gate placebo. No
  file treats it as an ablation of transport computation.
- The baseline already has no executed i64 load. The supported causal statement
  is earlier EggCC forwarding exposing a different opportunity to the fixed
  backend, ending in a cyclic-versus-acyclic process entry. The final files do
  not name a specific LLVM pass or assert an exact LLVM pass order.

### Parts32

- The stated total signed-i64 partition is sound. With
  `low(x)=x & 0xffffffff`, `x-low(x)` remains representable and is exactly
  divisible by `2^32`; the two components reconstruct `x`.
- The combined path matches source and retained receipts:
  `x!=y` propagates through marked `Parts32`; representation equalities move
  that result to unequal unmarked `Pair` applications; equal low siblings let
  reverse congruence establish unequal high children; and only the exact
  contextual high-part `Eq=false` is applied to the host graph.
- The documents correctly distinguish the two generic roles. Marked forward
  disequality uses the injectivity promise for the full `Parts32` input, while
  the reverse `Pair` step follows from ordinary congruence and equal siblings;
  `Pair` is not claimed injective.
- The mark, representation, reverse, query, bridge, and exact target-application
  knockouts are described correctly, as is the exact high-child rescue. The
  prose does not repeat Fable's rejected claim that the separate false-`If`
  ablation disabled the interval rule. It states that the tested
  non-weakly-linear rule was nonessential and leaves the alternate downstream
  consumer unassigned.
- Primitive metadata cannot determine the dynamic equality-sort relations in
  either QR7 or Parts32. The primitive-only controls are therefore valid nulls,
  not disguised `true != false` or constant-conflict detectors.

### General encoding and causal limits

- The cancellation, marked-forward, and equal-sibling reverse implications in
  the explanation and reference agree with the retained engine implementation.
  Primitive mismatches are compared directly, primitive disequalities are not
  stored, and unsupported containers remain outside the encoding.
- The equal-sibling qualification is present. None of the final files infers an
  individual child disequality from a multi-child parent disequality alone.
- Manual computes a faithful finite closure and reaches the same emitted/native
  endpoints. All reviewed files therefore disclaim unique logical power for the
  generic implementation.
- The fresh private-graph and exact-export boundary is preserved. The final
  prose does not rely on Fable's rejected claim that `ContextOf` itself proves
  lifetime safety, and it does not claim an exhaustive equality-consumer census.
- Same-mask is accurately labeled a smaller, separately measured replication;
  its observations are not pooled with Parts32. Pack32 and A1 remain explicit
  fail-closed negative attempts and contribute no payoff measurement.

## Measurement claims

### QR7 arithmetic and design

The independent verifier records:

| Claim | Retained authority |
| --- | --- |
| Encoding/U0 | `0.550549423146935`, bootstrap 95% `[0.5471011571092694, 0.5575021727134777]` |
| Less elapsed time | `44.9450576853065%`, correctly rounded to 44.9% or 44.9451% |
| Neutral Encoding/U0 | `0.9892585012`, bootstrap 95% `[0.9836729081, 1.0003275615]`; no speed gate |
| Confirmation design | 14 arms, 112 cycles, eight complete 14-cycle blocks, two workloads |
| Measured rows | 3,136; ten serial fresh processes per row |
| Total invocations | 31,388 including 28 warmups |

All five reported primary hot comparisons and intervals match the verifier, and
their upper bounds are below the frozen `0.99` threshold. The report's two
instruction groups match the actual-binary inspection: ten baseline arms have
91 process-entry instructions and two internal backward branches; Encoding,
Manual, and the two rescues have 55 and zero. The same-code validity gate is
accurately described as a two-percent point-ratio bound; the report explicitly
does not require every interval to contain one.

The retained matrix count also reconciles: 14 positive cases with 154 native
checks, 18 premise/divisor negatives, four changed-pointer cases, and one
no-context case give 37 compiler cases and 177 native checks.

### Parts32 arithmetic and design

The six reported Encoding/U0 cells exactly match the independent verifier:

| Workload/session | Ratio | Bootstrap 95% |
| --- | ---: | ---: |
| equal-low-positive / 1 | 0.9242602893 | [0.9235351246, 0.9254912318] |
| signed-min-boundary / 1 | 0.9243145752 | [0.9222014328, 0.9246590230] |
| signed-max-crossing / 1 | 0.9250432355 | [0.9240444718, 0.9284290259] |
| equal-low-positive / 2 | 0.9195163357 | [0.9152623158, 0.9227153724] |
| signed-min-boundary / 2 | 0.9149248254 | [0.9124215628, 0.9172367136] |
| signed-max-crossing / 2 | 0.9139833514 | [0.9114336154, 0.9167011567] |

The stated 7.5% to 8.6% reduction is the correct one-decimal conversion of
those per-cell ratios. Each session has 90 balanced cycles, 1,350 measured
rows, 45 warmups, and eight process checks; each observation has 32 fresh
processes and one million loop iterations per process. The 18 required speed
comparisons are the three declared comparisons across three workloads and two
sessions, and every upper interval bound is below `0.99`.

The placebo wording matches the prospectively frozen rule: B1/U0,
SeedOnly/B1, and Encoding/Manual show no consistent greater-than-one-percent
directional shift across both sessions for a workload. The final files do not
replace that rule with a stronger confidence-interval equivalence claim.
Workloads and sessions remain separate throughout the report, reference, and
acceptance files.

The 200-check correctness count is also exact: 154 positive/causal, 25
semantic-negative, ten loop-negative, and 11 no-context native executions.

### Other quoted counts

- Same-mask's `0.98083849 [0.98041942,0.98164075]` Encoding/U0 result is
  correctly summarized as about 1.9% less elapsed time over 32 cycles. The
  files retain its uncontrolled native-layout caveat and do not pool it with
  Parts32.
- Pack32's retained reduction supports 14 positive rows and 154 positive
  native checks, 243 native checks overall, 156 rejected queries, zero accepted
  witnesses/exports, and identical positive emitted/process-main hashes. It is
  not promoted to causal or timing evidence.
- A1's summary supports 18 positive modes, 31 interpreter pairs, 233 passing
  native checks, zero exports, identical emitted/process-main code, and one
  load/two stores. The documents correctly decline timing and do not infer that
  the scoped law is false.

## Timing and acceptance boundaries

- QR7 measures generated-program fresh-process runtime for one fixed hot input
  and reports its zero-trip control separately. Parts32 reports all six
  workload/session cells. Neither accepted result includes compiler or lowering
  time.
- The separate Parts32 compiler-time ratio `0.99919 [0.99370,1.00697]` is
  consistently labeled descriptive and is never used as a speedup.
- QR7's screen and confirmation are not pooled. Parts32's sessions and
  workloads are not pooled. Rejected/aborted Parts32 sessions remain excluded
  under prospective process-admission rules rather than elapsed-value
  selection.
- Both accepted results are limited to constructed workloads on one Apple
  Silicon system and the retained backend. There is no suite-wide, production-
  frequency, compiler-time, proof-support, or generally transferable percentage
  claim.
- `acceptance.json` names the governing local `facts.md`, and its recorded
  SHA-256 matches that file. Its 13 pass plus one not-applicable statuses match
  all 14 facts. Treating the correctness fact as passed is supported under this
  local contract: the required root and selected-engine checks pass, the
  registered semantic/native coverage passes, and the two nonzero isolated-host
  commands are retained and freshly attributed. The prose repeatedly says the
  host is not green, accepts no snapshot, and makes no merge-readiness claim.
  It therefore does not use attribution to misreport a failed host command as a
  pass.

## Integrity checks

All local Markdown link targets in the five reviewed deliverables exist. Every
evidence path in `acceptance.json` exists. Its status counts recompute exactly,
and its `facts_source_sha256` matches the current governing fact file. The QR7,
Parts32, same-mask, and compiler-diagnostic SHA-256 values printed in the
reference and reproduction guide match the retained files.

No unsupported pass attribution, disequality contribution, unique-power claim,
pooled performance result, mismatched headline count, broken evidence link, or
unqualified causal assertion was found.
