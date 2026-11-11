# MISAAL exact pattern deduplication repair

Fresh public MISAAL family preparation explicitly publishes
`"pattern_deduplication": "exact-render-last-v1"` in every ready x86, ARM and
Hexagon request. Publication creates new request files and retains the target
preparers' original files and hashes. The family receipt records this policy;
its original and published request identities retain the derivation. Native
source/product hashes and cold/raw/abstract cache behavior are preserved.

A separately supplied complete-parent request can still opt in with that field;
without it, capture behavior is unchanged. Existing requests, source checkouts
and prior outcomes are not updated. Literal-width repair remains a separate
opt-in and is not enabled by this publication policy.

`scripts/reproduction_misaal_patterns.py` verifies the exact pinned MISAAL `44ff`
`PatternUtils.py` and `Pattern.py`, plus Hydride `beb` `Instructions.py` and
`Types.py`. It verifies loaded module paths and relevant function code against
those files before installing a scoped runtime replacement. The child receipt
records these four hashes and the replacement module's hash. New generated
imports see the replacement; all three wrapped functions are restored on exit.

The original quadratic deduplication discards an object if any later object
matches it. Equality compares full default expression strings in either
orientation; every non-Context endpoint renders as the literal `Reg`. It ignores
pattern metadata. The replacement renders each endpoint once, scans backward
using exact unordered string-pair keys, and reverses the survivors. It therefore
retains the same last object, orientation, metadata and original survivor order.
Keys are local to the call because later abstraction can mutate patterns.
The pinned renderers only read fields and construct strings.

The child `capture.json` gains `pattern_preparation` with a source/implementation
identity and ordered `phases`. Each `create_patterns`,
`prune_redundant_patterns`, and `deduplicate_patterns` call records its caller,
input count, start time, end time, elapsed time, result count and status. A start
receipt is persisted before work, so termination leaves a visible running phase.
Only deduplication changes; the other two wrappers call the original functions.

The cold/raw/abstract cache branches, pattern parsing and pruning, helper
validation subprocesses, optimizer schedule, selected outputs and native LLVM
feedback are unchanged. No cache is prepopulated or reused. A raw pickle cannot
silently replace a cold import: the original warm branch performs abstraction
and helper validation and may mutate the pattern list.

The original HVX blur3x3 child imports Halide patterns first. Static source
counts are 33,234 Halide records across 3 files and 4,668 HVX records across 20 files,
plus 1 handwritten HVX pattern. These are counts before pruning and deduplication,
not measured active-rule counts. The 900-second original attempt reached no
backend/helper invocation. Its empty cache does not identify whether parsing,
pruning or deduplication consumed the time. The repair's timing receipts are
intended to falsify the deduplication hypothesis in the next guarded canary.

Focused tests compile verbatim pinned equality, renderer, operand and dedup
declarations without importing any pattern population. They compare survivor
object identities/order against the original quadratic oracle, including
reversals, conflicting metadata, shared objects, non-Context endpoints,
type/name differences and unchanged inputs. Eight existing source-corpus
renderings are reconstructed using the pinned Context/operand behavior and
checked byte-for-byte before the same oracle comparison. This bounded fixture
does not execute the original full pattern parser or establish native success.

Next runtime gate: retain a new immutable flagged HVX blur3x3 request, run the
same guarded complete source pipeline, inspect phase receipts and unchanged
helper/backend accounting, then require native completion and ordinary replay.
Unit tests do not establish that this resolves the timeout.

Current native canaries have now completed for both x86 and ARM `blur3x3`,
including original compiler feedback and ordinary replay. Their cold serialized
pattern caches match the corresponding unmodified runs byte-for-byte. The
observed pattern counts are 5,994 → 5,823 for x86 and 4,641 → 4,165 for ARM.
For x86, backend input, selected output and standalone replay are also identical;
generated native artifacts agree after accounting for capture names and the
path-derived header guard. These are source-reproduction checks, not an isolated
timing comparison: the recorded runtime seals differ from the older controls.

Evidence is retained in
`benchmarks/local/reproduction/diagnostics/misaal-x86-dedup-equivalence-0001/`
and `benchmarks/local/reproduction/diagnostics/misaal-arm-dedup-canary-0001.json`.
The extra HVX `tensor_add` case also completed source optimization, LLVM feedback
and ordinary replay, in 246.890 seconds with a 2.24 GiB peak. Its snapshot is
`diagnostics/misaal-hvx-tensor-add-current-20260925.json`. It is an artifact extra,
not a required paper benchmark. The larger HVX `blur3x3` remains unresolved;
warm-cache abstraction and helper validation are not skipped or replaced.

## ARM blur7x7 unsigned-shift coverage gap

ARM `blur7x7` retains a source unsigned shift with 16-bit lanes, a 128-bit
vector and shift amount 2. The inspected emitted program has 11 unsigned-shift
patterns, all restricted to 32- or 64-bit lanes; none covers this operation.
The pinned target semantics includes `vshrq_n_u16`, but instruction availability
does not supply a verified rewrite. The [coverage audit](../local/reproduction/diagnostics/misaal-arm-blur7x7-pattern-coverage-0001.json)
records the actual query, selected result and active pattern files. This is a
source-reproduction blocker, with no demonstrated Egglog runtime or proof bug.

The original seed and pinned `EnumeratePattern`/DoubleGrammar path produced a
verified 32-bit control property, then returned `False` for the requested
16-bit contexts. The [diagnostic receipt](../local/reproduction/diagnostics/misaal-arm-shift-pattern-probe-0003/attempt-0001/result.json)
preserves that initially inconclusive failure. A separate guarded replay of the
[exact retained query](../local/reproduction/diagnostics/misaal-arm-shift-query-replay-0001/work/wwrha1in.rkt)
captured stderr without changing the original generator's output suppression.
It reported no runtime exception: verification found a counterexample, the next
synthesis iteration asserted a false lane constraint, and the original false
return path exited with no property. This establishes rejection by the attempted
bounded grammar, not general unsatisfiability of a 16-bit shift lowering.

The [source-backed diagnosis](../local/reproduction/diagnostics/misaal-arm-shift-query-diagnosis-0001.json)
identifies the width mismatch. Source register widths remain `[128, 32]`, so
the grammar's register-width checks admit only a 32-bit scalar broadcast beneath
the 16-bit shift. Adjacent lanes therefore use opposite halves of that scalar;
the verifier's scalar value 8 gives alternating shifts by 8 and 0, while the ARM
immediate shifts every lane by 8. Selecting 16-bit roots alone does not correct
the input domain.

No replacement seed, rewrite or pattern was invented or published. Recovery
requires a source-justified input-width correction or explicit conversion that
makes the 16-bit broadcast representable, followed by the original all-input
verification, canonical/property checks, complete native parent and ordinary
replay gates. A faster backend or longer timeout cannot add the missing rule to
the unchanged query. Retain this artifact gap while collecting the remaining
cases.
