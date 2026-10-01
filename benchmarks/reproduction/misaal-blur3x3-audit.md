# Independent MISAAL blur3x3 capture audit

**No concrete admission blocker found for this completed source/ordinary boundary.**
This read-only audit covers the fresh repaired x86 attempt `771795f…`, not the
historical capture whose legalizer returned undefined results. No native tools,
benchmarks or tests were rerun, and no implementation/source files were changed.
Machine-readable checks are in [MISAAL-BLUR3X3-AUDIT.json](/Users/saul/p/wt/egglog-encoding/reproduction-dialegg-speq/MISAAL-BLUR3X3-AUDIT.json).

## Parent completion and provenance

The [capture receipt](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/771795f755a25e4dff5dd7728ea12026978b47a50adfddb1879662a00540d99a/attempt-0001/capture-result.json) and
[process receipt](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/771795f755a25e4dff5dd7728ea12026978b47a50adfddb1879662a00540d99a/attempt-0001/capture/process.json) record an actual successful
parent: exit 0, **524.143 seconds**, peak process-group RSS **938,426,368 bytes**
(895 MiB). All five requested final files exist and their recorded hashes match:
`.a` 302,752 bytes; `.stmt` 113,091; `.h` 95,814; `.ll` 3,584,995; `.s` 1,877,981.
Final LLVM's retained `llvm-as` verification returned 0.

I independently rehashed **41 capture artifacts and three validation artifacts**;
all matched. The copied request's **19 source-file hashes** and the actual
backend, Python, generator, LLVM verifier, corrected legalizer and Halide library
hashes also matched. The request records MISAAL
`44ff893445d664cd87f52b08a138260ed2015ba8` and Hydride
`beb825327fc946d65032e96f7cde9acf3d24c13e`, with the approved inliner/SIMD repairs
already bound by the retained preparation/request evidence.

## Every source root and real feedback

Parsing the retained [generated Python](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/771795f755a25e4dff5dd7728ea12026978b47a50adfddb1879662a00540d99a/attempt-0001/capture/generation/children/child-0000/generated.py) as data found
**198 distinct named tests and exactly one distinct source expression**. These
198 names exactly match the legalization request and all 198 named outputs in
[test.out](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/771795f755a25e4dff5dd7728ea12026978b47a50adfddb1879662a00540d99a/attempt-0001/capture/generation/test.out). Their emitted Rosette bodies
are identical. The original `HydrideCompiler.compile_hydride` explicitly
compiles unique expressions, memoizes the result, then emits each named test;
its actual parent log reports `1 unique expressions to compile`. Thus one
backend invocation accounts for this parent; 198 is not a missing-call count.

The child directory, raw invocation set, materialized invocation list and parent
membership agree exactly: **one child, one optimizer invocation, one legalizer,
one standalone session**. The remaining temporary `.egg` has the same raw hash.
The scoped helper observer completed successfully with **zero helper calls**;
no helper was admitted as a workload.

The [child receipt](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/771795f755a25e4dff5dd7728ea12026978b47a50adfddb1879662a00540d99a/attempt-0001/capture/generation/children/child-0000/capture.json) and
[tool receipts](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/771795f755a25e4dff5dd7728ea12026978b47a50adfddb1879662a00540d99a/attempt-0001/capture/generation/children/child-0000/legalize-0000/tools.json) retain actual successful
`llvm-link`, `llvm-dis` and `opt` calls, using the corrected library
`a394c56f…9568b5`. The retained legalized LLVM hash is
`7afb532d2a90dc888da2d7fe6ab46998b48228aa7483b16c857079932245b3b9`.
It matches both the recorded feedback hash and the actual still-present `.ll`
read by the parent. The capture hook returns that verified native file through
the source compiler's original feedback path.

Independent scans of **all 198 required functions**, in both the returned
legalized LLVM and the final parent LLVM, found no missing function, no
`undef`/`poison` token anywhere in those bodies, and no residual `llvm.hydride.*`
call. The final 198 bodies are identical: bitcasts, two `<32 x i16>` additions,
and unsigned vector division by the literal 3. The legalizer's intermediate
bodies use the real add/broadcast wrappers and `udiv`; the final parent output
has inlined these wrappers. This establishes more than LLVM parseability for
the demonstrated undefined-result regression, while remaining short of a
universal semantic-equivalence claim.

## Standalone preservation and observed output

The [raw input](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/771795f755a25e4dff5dd7728ea12026978b47a50adfddb1879662a00540d99a/attempt-0001/capture/generation/children/child-0000/invocation-0000.egg) is 1,083,519 bytes, SHA-256
`53f11a3f3a17a1ee60389eaf3ccaa90d2f443d6c5e4ccd872d804929e41d2b72`.
Its 5,851 commands are one datatype, **20 rewrites, 5,824 birewrites**, four
source lets, **`(run 5)`**, and **`(extract srcexpr)`**. It has 209 explicit
`:cost` attributes and no dynamic cost actions.

I reconstructed the [standalone replay](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/771795f755a25e4dff5dd7728ea12026978b47a50adfddb1879662a00540d99a/attempt-0001/capture/generation/replays/invocation-0000.egg)
byte-for-byte from that raw input and the real native stdout. The only changes
are `$` prefixes for the four global names after the first let, and one appended
query immediately after the original extract. Every active rule, constructor
schema/cost, source term, schedule iteration and extraction request is retained;
no target term is seeded by a let, union, set or rule. The datatype/declaration
prefix is unchanged. Original and current default extraction use additive
constructor/child costs; no altered cost or removed operator was found here.

The equality asks whether the exact native selection is already equivalent to
`$srcexpr`. Its ordered command position and preceding-graph hash recompute to
the recorded contract. Current `EGraph::check_facts` implements a body-only
query with an empty action head and a match side channel; it does not construct
that selected expression in the graph.

The retained [ordinary validation](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/misaal-x86-blur3x3/validate/f5e151d1964f46b0bfa7920a70bc792b52a880b5bcc612b869cf61c1ad829999/attempt-0001/replay/validation.json) ran the
actual current engine, exit 0 in **0.559 seconds**, and passed the output contract.
Both native and ordinary output contain exactly one term and are **byte-identical**,
SHA-256 `f0c70494743d784f411f0b9cf75c641be7a6fc5ac284a59e0b2e9aecfade9c76`.
The replay SHA-256 is
`8a66eeb28625418f8fc7d5cf0ddfb72dc8471eb1f281b4d60d00108f900af570`.

## Limits

This supports complete original source optimization/host feedback, accounted
standalone export, native-result derivability, and ordinary replay agreement for
this one configuration. Strict proof validation is recorded **not run**. No
numerical target execution occurred, and this audit does not establish general
source-C/LLVM equivalence, global extraction optimality, or other MISAAL cases.
