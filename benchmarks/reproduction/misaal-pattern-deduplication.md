# MISAAL exact pattern deduplication repair

An immutable complete-parent request can opt in with
`"pattern_deduplication": "exact-render-last-v1"`. Without this field the
capture behavior is unchanged. No prepared request or source checkout is edited.

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
