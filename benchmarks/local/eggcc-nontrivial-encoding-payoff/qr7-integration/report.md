# QR7: lossless-key cancellation enables store forwarding

QR7 demonstrates a nonprimitive use of generic injectivity in an actual EggCC
memory consumer. Two quotient/remainder guards identify equal dynamic indices;
injective cancellation and address congruence establish an exact local
must-alias fact. Early store forwarding then enables a different native
optimization. On the constructed hot workload, Encoding uses **44.9% less
elapsed time** than untouched EggCC: ratio **0.55055**, complete-block bootstrap
95% **[0.54710, 0.55750]**. The [independent timing verification](timing-r1/independent-verification.json)
passes every prospectively declared hot comparison and same-code validity gate.

This is an injectivity-only result. [Parts32](../parts32-integration/report.md)
remains the measured example that requires injectivity and disequality
together. The [reproduction guide](reproduce.md) gives commands and immutable
identities; this report explains the connected argument.

## From source guards to equal addresses

The [valid Bril fixture](fixtures/source.bril) bounds `x,y` to `[0,64)` and `n`
to `[0,10000000]`. Inside two nested true branches it has this shape:

```text
qx = trunc(x / 7);  qy = trunc(y / 7);
if (qx == qy) {
    rx = x - 7*qx;  ry = y - 7*qy;
    if (rx == ry) {
        p = alloc(64); pi = p+x; pj = p+y;
        store(pj, -3);
        for (count = 0; count < n; count++) {
            store(pi, count);
            sum += load(pj);
        }
        free(p); print(sum);
    }
}
```

For every signed i64 `v`, let `Q7(v)=trunc(v/7)` and
`R7(v)=v-7*Q7(v)`. The product lies between `v` and zero, and the remainder is
in `[-6,6]`, so both are representable. Exact reconstruction
`v=7*Q7(v)+R7(v)` proves that `K7(v)=(Q7(v),R7(v))` is injective. The fixed
positive divisor avoids division by zero and the signed MIN/-1 exception.

The [sidecar](scoped_qr7.rs) imports only checked facts from the exact enclosing
branches into a fresh private graph. Its chain is:

```text
Q7(x)=Q7(y), R7(x)=R7(y)              dynamic branch seeds
  => Pair(Q7(x),R7(x))=Pair(Q7(y),R7(y))  ordinary congruence
  => K7(x)=K7(y)                    two representation identities
  => x=y                            generic marked K7 cancellation
  => Addr(region,x)=Addr(region,y)   ordinary same-region congruence
  => Qr7MustAlias(write_addr,load_addr)  exact local export
```

Only `K7` is marked. `Q7`, `R7`, `Pair`, and `Addr` are unmarked; no pointer
injectivity is assumed. All index and address equalities stay private. Typed
projection transport checks that the required pointer slots pass through the
loop unchanged in both arms of nested branches. The recognizer also checks the
same allocation, bounds, source contexts, and admitted lifetime/effect shape.
Missing guards, unsupported translation, contradiction, or an engine error
cannot authorize export.

## The compiler consumer and its controls

The [compiler patch](eggcc-candidate-r1.patch) adds a bounded `mem-simple`
bridge for `Qr7MustAlias`. Given an adjacent `Load(load_addr, Write(write_addr,
value,state))`, it unions the loaded value with `value` and the loaded state
with the write. These are the same value/state replacements as ordinary
same-address forwarding, but this is an **added bridge**, not execution of
untouched U0's same-address rule. The original rule remains unchanged.

The [captured inspection](final-r1/inspection.json) records the intermediate
equalities, exported relation, and `QR7 must-alias store forward` event.

| Fixed-input treatment | Result |
| --- | --- |
| U0, Off/B1, SeedOnly, PrimitiveOnly | baseline emitted code and native entry instructions |
| cancellation-off | equal keys remain; index/address equality and export disappear |
| identity-off | equal component pairs remain; key/index/address equality and export disappear |
| exact `x=y` or key-equality rescue | winning emitted/native code returns |
| query-off or bridge-off | no exported relation; baseline code |
| consumer-off | exported relation remains, forwarding event disappears; baseline code |
| Manual and Encoding | identical winning emitted code and native entry instructions |

The faithful Manual arm computes the same finite congruence/cancellation
closure; the result makes no claim of unique logical power. PrimitiveOnly
retains the same graph and dynamic seeds but performs no equality-sort
inference. `K7` has no primitive fields to compare; divisor/bounds metadata
cannot decide equality of the two dynamic words. No disequality inference or
`known-disequal?` query contributes to this result.

The label `transport-off` suppresses export at the same gate as `bridge-off`.
It is an export-gate placebo, not a direct transport-computation ablation.
Changed-pointer and absent-context controls separately reject export. Across
the four retained matrices, all **177 native outputs** are exact, including
the three initialized semantic negatives that must print `-24`, not `28`.
The [independent exact-integer oracle](../qr7-screen/oracle.py) supplies the
native expectations. [Six registered mechanism tests](revision-01/commands/mechanism-tests/stdout)
also have passing captured receipts; these checks do not replace final full
repository and host validation.

## What changed at the executed endpoint

Baseline LLVM already removes the memory load from executed C `main`; its
remaining computation is a cyclic vectorized reduction. Earlier EggCC
forwarding exposes the arithmetic recurrence soon enough for LLVM to produce
an acyclic closed sum. The [actual Mach-O instruction inspection](actual-binary-inspection-r1.json)
finds 91 entry instructions and two internal backward branches in every
baseline arm, versus 55 instructions and zero backward branches in Encoding,
Manual, and both rescues. Whole executable hashes differ; the stated identities
apply to emitted Bril and the inspected function instructions.

The measured improvement therefore concerns this phase-ordering change. It
cannot be attributed to removing an executed hot load or to instruction count
alone.

## Per-workload runtime evidence

The [frozen design](prospective-timing-design-r1.json) measures ten serial fresh
processes per observation, including startup, argument parsing, allocation,
computation, and printing. Compiler and lowering time are excluded. A 14-cycle
screen precedes an independent 112-cycle confirmation. Fourteen treatments use
complete Williams blocks to balance position and immediate predecessor; the
confirmation has eight blocks, 3,136 measured rows, and 31,388 invocations
including warmups. Every output is exact and all completed observations are
retained. Confidence intervals resample complete 14-cycle blocks.

| Confirmation workload/comparison | Paired median ratio | Bootstrap 95% |
| --- | ---: | ---: |
| hot `(12,12,10000000)`: Encoding/U0 | 0.55055 | [0.54710, 0.55750] |
| hot: Encoding/Off | 0.55028 | [0.54417, 0.55228] |
| hot: Encoding/SeedOnly | 0.55210 | [0.54940, 0.55442] |
| hot: Encoding/PrimitiveOnly | 0.55338 | [0.54958, 0.55707] |
| hot: Manual/U0 | 0.55741 | [0.55377, 0.55986] |
| zero-trip `(12,12,0)`: Encoding/U0 | 0.98926 | [0.98367, 1.00033] |

All five primary hot upper bounds are below the frozen `0.99` threshold.
The neutral workload has no required speedup. The independent verifier also
passes the declared same-code check: each confirmation hot median is within
2% of its instruction-identical group's reference. This does not require
intervals to contain one; Encoding/Manual is 0.98867 [0.97929, 0.99675].
The workloads and screen/confirmation are reported separately and never pooled.

This establishes generated-program fresh-process runtime for one constructed
QR7 workload on Apple Silicon, not an EggCC-suite estimate, compiler-speed
result, compiler bug, general alias analysis, or merge-ready feature. The
Encoding arm also executes an audit-only manual closure, while Manual
materializes the engine graph, so compiler-cost comparisons are excluded.
Memory pressure is descriptive and never blocks or discards observations;
the benchmark memory guard is unset. Raytracing, proof work, snapshot
acceptance, commits, pushes, and paper edits are outside this result. The
premeasurement inspection's `timing_collected:false` and
`performance_acceptance:false` remain historical facts; the newer
[timing verification](timing-r1/independent-verification.json) is the performance
authority.
