# Parts32 integration: combined encoding changes native code and runtime

This bounded integration derives and consumes a disequality over dynamic
equality-sort children through marked forward propagation, representation
equalities, and sibling-guarded reverse congruence. It passes the correctness,
native-code, and prospectively frozen generated-runtime gates. It is not a
pre-existing EggCC compiler bug.

The immutable evaluated compiler is `bin-reviewed-final/eggcc`; `final-source-identities.json` binds its source, dependencies, scripts, runtime and binary hashes. `final-source.tar`, `eggcc-final.patch` and `encoding-final.patch` retain the exact evaluated source. Earlier source archives and pilot binaries remain separate. The live isolated sources are `/private/tmp/eggcc-parts32-candidate` and `/private/tmp/encoding-parts32-candidate`. Neither the dirty root source nor previous screens were edited. No commits, pushes, proof integration or paper edits occurred.

The host starts from pinned U0 `a0bbec127f83249074a46af3fd6f6126c90fe0fb`. Its selected encoding source is `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5` plus the same retained E1 delta used in the same-mask study. `source-admission.json` records both archives and all retained-file identities. Compatible build output and the Python environment were cloned into the new isolated candidate, so later writes do not modify the earlier study.

## Exact mechanism

For any signed i64 word `x`, let `r=x & 0xffffffff`. The arithmetic partition is `Parts32(x)=(r,(x-r)/4294967296)`. The difference is representable and exactly divisible for every i64 word; the retained arithmetic screen contains the full argument and independent byte-string oracle.

The host recognizes only an exact target integer Eq nested under a true low-part Eq and a false original-word Eq. It follows each actual branch input to its typed `Get` bindings. It rejects sibling or unrelated contexts, non-integer fields, incompatible masks or divisors, changed operands, and loop constants whose slots change or move. A mask or divisor initialized through an enclosing If must resolve through its exact input to a literal, and the loop must preserve that same slot through both branches. Updated word values remain opaque lexical values; no cross-iteration word equality is assumed.

Each target gets a fresh graph with scoped opaque `x` and `y`. `Low(Word,i64)` and `High(Word,i64,i64)` retain primitive mask/divisor metadata and are unmarked. Unary `Parts32(Word)->Parts` is marked injective. Binary `Pair(Word,Word)->Parts` is unmarked. The host imports only the exact lossless representation identities and two dynamic path seeds:

```
x != y
Low(x,0xffffffff) = Low(y,0xffffffff)
Parts32(x) = Pair(Low(x),High(x))
Parts32(y) = Pair(Low(y),High(y))
```

The generic marked unary step proves the Parts32 outputs differ. Their representation identities make the Pair outputs differ. Generic binary reverse congruence, guarded by the equal low sibling, proves the high children differ. Only the exact contextual target predicate is exported as Eq=false. Local word equalities and branch assumptions never enter the main compiler graph.

The manual comparator computes the independent least fixed point of generic equality congruence, marked injectivity, marked forward disequality and sibling-guarded reverse congruence over the same finite rows and seeds. It does not directly recognize the Parts32 theorem or emit the final fact from primitive parameters. No unique logical expressiveness is claimed.

## What passed

`final-reviewed/inspection.json` contains executable assertions for all gates. There are 200 final native output checks: 154 across 14 positive/causal arms, 25 semantic-negative checks across U0/B1/SeedOnly/Manual/Encoding, ten changed-loop-slot checks, and 11 no-context checks. Every emitted program is also interpreted. All values match the independent retained oracle or the original interpretation for the explicit changed-slot controls.

U0, B1 and SeedOnly have byte-identical emitted Bril and native entry code. Encoding and Manual have byte-identical emitted Bril and native entry code. Both native main functions retain the scalar `99`/`7` target in U0/B1 and lose it in Encoding/Manual, where LLVM emits vector i64 operations. Compact LLVM/assembly functions and direct diffs are retained in each matrix arm.

| Fixed-input mode | Word != | Parts != | Pair != | High != | Native code |
| --- | --- | --- | --- | --- | --- |
| Encoding / Manual | yes | yes | yes | yes | optimized |
| SeedOnly: exact graph/seeds, no inference | seeded | not queried | not queried | not queried | U0 |
| Primitive-only null: exact graph/seeds | seeded | not queried | not queried | not queried | U0 |
| Forward mark removed | yes | no | no | no | U0 |
| Reverse edges removed | yes | yes | yes | no | U0 |
| Representation identities removed | yes | yes | no | no | U0 |
| Exact high-child rescue, forward/reverse disabled | yes | no | no | yes | optimized |
| Final high query removed | yes | yes | yes | not queried | U0 |
| Export bridge removed | yes | yes | yes | yes | U0 |
| Eq=false consumer removed | yes | yes | yes | yes | U0 |

SeedOnly stops immediately after populating the exact finite graph, identities and dynamic seeds: no saturation, contradiction probe, witness query, manual closure or export runs. The primitive-only null preserves that same graph and seeds, then finds no marked primitive fields to compare; it likewise runs no equality-sort inference. The first null had removed seeds and is retained as a rejected control in the earlier captures; the final acceptance map uses only the corrected treatment.

The consumer knockout preserves the internal high witness and export receipt but suppresses the target union. A separate knockout disables the named non-weakly-linear false-`If` rule after the union, yet still optimizes. The interval false-`If` rule remains enabled, and later extraction or the backend can also consume the constant predicate, so this ablation establishes only that the named rule is nonessential; it does not identify the alternate consumer. The contextual `Eq=false` application and resulting native code change are essential.

The semantic negatives remove word disequality, remove equal lows, narrow the mask without adjusting the divisor, widen the divisor, or use unequal divisors. All five compiler arms preserve the expected `99` result and generate matching code. Changed mask/divisor slots and absent context likewise export no fact. Five registered sidecar tests and all 18 registered selected-engine injectivity/disequality tests pass. Full engine `make check` and the complete dag test command passed. Root EggCC `make test` passed all 2,421 functional tests but exited nonzero for 13 pending snapshots, all byte-identical to the prior same-mask study. They were not accepted. Dag clippy retains two warnings in files byte-identical to pinned U0; the sidecar adds no warning. `validation.json` records the exact results and limitations.

## Generated-runtime result

The accepted timing campaign uses the immutable native programs already
produced by the correctness matrix. U0, B1, and SeedOnly are one byte-identical
baseline code group; Manual and Encoding are one byte-identical optimized code
group. Every observation runs 32 fresh native processes, and every process
executes one million loop iterations and produces the exact expected output.

Two independent sessions each contain 90 prospectively balanced cycles over
three workloads and five arms: 1,350 measured rows and 43,200 checked native
processes per session, plus 45 warmups. Process admission passed before each
session, at every complete 15-cycle block boundary, and after each session.
The independent verifier recomputed source and binary identities, declared
order, output hashes, paired ratios, complete-block bootstrap intervals, speed
gates, and placebo validity from the raw rows.

The frozen speed gate requires the upper 95% bound to be below `0.99` for
Encoding/U0, Manual/U0, and Encoding/B1 on every workload in each session.
All 18 required comparisons pass. The Encoding/U0 results are:

| Workload | Session | Ratio | Complete-block bootstrap 95% | Less elapsed time |
| --- | ---: | ---: | ---: | ---: |
| equal-low-positive | 1 | 0.92426 | [0.92354, 0.92549] | 7.57% |
| signed-min-boundary | 1 | 0.92431 | [0.92220, 0.92466] | 7.57% |
| signed-max-crossing | 1 | 0.92504 | [0.92404, 0.92843] | 7.50% |
| equal-low-positive | 2 | 0.91952 | [0.91526, 0.92272] | 8.05% |
| signed-min-boundary | 2 | 0.91492 | [0.91242, 0.91724] | 8.51% |
| signed-max-crossing | 2 | 0.91398 | [0.91143, 0.91670] | 8.60% |

No workloads or sessions are pooled into a headline estimate. Manual/U0 and
Encoding/B1 independently pass the same threshold in all six workload/session
cells. The B1/U0, SeedOnly/B1, and Encoding/Manual point estimates do not show
the same greater-than-one-percent directional shift in both sessions for any
workload, so the prospectively defined placebo validity check passes. The
complete authority is `timing/independent-verification.json`, SHA-256
`9b26a8c4a1176979d555ff0c054ee0c985c8a3faa0e7c4313f225a4cbaaae959`.

One earlier session was excluded whole after an unrelated build appeared at a
prospective block checkpoint. A later zero-sample attempt was excluded at its
session-start check when an unrelated Python test restarted. Rejected
preflights and both exclusions are retained separately; none of their elapsed
values enter the accepted result. The memory guard remained unset, and no
raytracing workload was run.

## Compiler-time diagnostic

The separate frozen optimize-time diagnostic runs ten balanced observations
per arm and is explicitly non-acceptance evidence. Its median times are 728.7
ms for U0, 692.4 ms for B1, 713.6 ms for SeedOnly, 719.2 ms for Manual, and
717.0 ms for Encoding. Encoding/Manual has a descriptive paired median ratio
of 0.99919 with interval [0.99370, 1.00697]. Differences against U0 mix the
dependency retarget and feature preparation, so this diagnostic is not a
compiler-speed claim. The frozen summary is
`compile-diagnostic-final/results/summary.json`, SHA-256
`283a6af7bb6a9d69d87510fab681042170f47ff70efa7a95719e37a8d36ad12e`.

## Failed pilot and limits

The first pilot preserved correct output but rejected all three potential queries. Its literal-only invariant support did not follow the mask/divisor's exact enclosing-If input. One bounded revision added that structural transport; the revised pilot admits the intended query. `failure-ledger.json`, `pilot.json` and `pilot-r1.json` retain the distinction.

This is an experimental source-initialization boundary integration, with
private immutable source expressions rather than a new general path analysis.
The law is specific to the exact arithmetic partition. The primitive-only null
cannot infer the dynamic relations from fixed parameters. The runtime result is
limited to three constructed one-machine workloads sharing one native code
pair; it is not an EggCC-suite estimate. The final source archive, binary
identities, raw rows, and independent verification bind the corrected controls
and complete replay; earlier captures remain separate.

`prospective-timing-design-frozen.json` binds the completed five-arm campaign,
90 cycles and six complete 15-cycle joint blocks per session, with session 2
reversing corresponding arm and workload rows. It uses per-workload log ratios
and whole-block bootstrap intervals. `timing-preflight.json` binds the source,
binaries, design, producer, verifier, and clean starting inventory. The
diagnostic is separately frozen by
`compile-diagnostic-final/prospective-design.json` and has no performance
acceptance threshold.

The EE differential initially failed on globals named `x`/`y`, which collide with inherited EE truth-support rule variables. The unmodified selected encoding CLI reproduces the error. Alpha-renaming only diagnostic bindings preserves the graph and makes the CLI and registered cross-mode diagnostic pass. This adjacent engine issue is not an EggCC payoff and no engine repair was added.
