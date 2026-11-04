# QR7 r2 matrix comparison

The complete r2 matrix passed all four phases and the retained semantic inspector:
14 positive modes, 18 negative rows, one context-negative row, and four
loop-negative rows. Across those 37 cases, all
177 native outputs are exact.
No timing or raytracing workload was run, and every receipt records the benchmark
memory guard as absent.

| Compared artifact | r1 versus r2 |
| --- | --- |
| Semantic result rows, queries, and counters | identical |
| Inspector JSON | byte-identical |
| E-graph and scoped evidence JSON | byte-identical |
| Emitted and saved optimized Bril | byte-identical |
| LLVM IR | identical after removing the one temporary `ModuleID` comment; raw hash differs |
| All disassembled function/instruction bodies | byte-identical |
| Native stdout | 177/177 byte-identical |
| Mach-O executable content | identical after UUID normalization |
| Complete Mach-O file | differs in all 37 cases |

The r2 actual-binary inspection reproduces the r1 instruction groups exactly.
The baseline group has 91 process-main instructions and
2 internal backward branches, with hash
`66d827e619ee132afed2d8ea3878a084cd184fee24b0b912a93519cdee24bcf0`. The winning group has
55 instructions and
0 backward branches, with hash
`8118a0fa625e0f98210d68a42f26122abe209a0a1ddf09425b0c26b006f17360`.

The complete generated Mach-O files are not byte-identical. Each pair differs in
117 to 120 bytes, and every changed byte is
inside the `LC_UUID` payload, local symbol/string metadata containing a temporary
object identity, or the ad-hoc code signature derived from those bytes. All Mach-O
sections and the payload after the load-command region and before `__LINKEDIT` are
byte-identical. The normalized LLVM difference is likewise only its temporary-file
`ModuleID`; the disassembly difference outside function bodies is only
llvm-objdump's input-path banner.

The strict exact-artifact answer is **no**: the retained r1 timing directly measures
the frozen r1 Mach-O files, while these regenerated r2 files have different hashes.
The execution-content answer is **yes**: semantic rows, optimized Bril, loadable
machine-code/data sections, complete instruction bodies, and outputs are identical.
Because the existing endpoint measures fresh-process runtime and excludes compiler
time, this establishes code-shape equivalence but does not relabel the old samples as
direct measurements of the r2 regenerated files. No new timing was collected.

Machine-readable details, including every case and byte-difference attribution, are
in [`r1-r2-comparison.json`](r1-r2-comparison.json). The r2 native inspection is
[`actual-binary-inspection-r2.json`](actual-binary-inspection-r2.json), and the
complete matrix receipts are under [`commands/`](commands/) and
[`top-level/`](top-level/).
