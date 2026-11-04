# EggCC encoding case study

An immutable address-key analysis enables a small load-elimination example in
EggCC. Query and manual modes produce the same checked program; query avoids
materialized nonalias pairs. The timings and peak RSS do not establish a query
advantage. The investigation found no new compiler bug or production-workload
improvement. This supports a compiler-integrated worked example for the paper,
with the semantic exclusions and strict retarget gate limits recorded below.

## Scope and provenance

The compiler baseline is the provided EggCC branch at
`15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`. The encoding baseline is PR119 at
`392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`. Current EggCC upstream was also
inspected at `a0bbec127f83249074a46af3fd6f6126c90fe0fb`; this study does not
claim an upstream bug. Both primary checkouts and the original feature checkout
were preserved before experiments. Experiments use isolated worktrees under
`/Users/saul/p/wt/`.

Raw evidence lives in
[benchmarks/local/eggcc-encoding-case-study](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study).
It is ignored by git and retained outside Cargo's build cache. The version and
host inventory, preservation snapshots, command receipts, source hashes and
patches belong to this evidence directory. The tracked inputs and collector
live in the isolated
[encoding study checkout](/Users/saul/p/wt/egglog-encoding/eggcc-study).
No paper files were edited. No new proof support or Lean work is part of this
study; the case uses ordinary execution.

## Candidate assessment

| Candidate | Assessment | Evidence and implication |
| --- | --- | --- |
| Arbitrary `Concat` injectivity | Rejected | Associativity and empty-tuple equalities identify applications with different fields. |
| Arbitrary `Bop` / `Top` injectivity | Rejected | Existing arithmetic and contextual equalities do not preserve all constructor arguments. |
| `Single` cancellation | Already supported | Existing `Get` left-inverse reasoning derives child equality. |
| Literal `Int` / `Bool` data | Sound narrow annotation; no new compiler benefit shown | Primitive payload disagreement is detectable, but the compiler already checks inconsistent top-level constants. |
| Global contextual `Const` injectivity | Rejected | Equality in unreachable contexts must not export equality between global literal payloads. |
| Injective optional points-to records | Rejected | Legitimate interval refinement `[1,2] → [1,1]` equates different resolved representations of one mutable analysis result. Cancellation would force `1 = 2`. |
| Unequal points-to intervals imply nonalias | Rejected | Unequal intervals can overlap; `[1,2]` and `[1,1]` share cell 1. The existing optional analysis instead reasons about empty intersection. |
| Immutable local address descriptors | Validated small compiler prototype | A same-state liveness invariant gives descriptor disequality a restricted runtime nonalias meaning. Native extraction and interpreter agreement pass; costs and broad-gate limits are recorded below. |

These assessments have executable positive, negative and expected-error controls
under both NEE and EE. All 16 expected outcomes at the first semantic checkpoint
passed. The
[semantic summary](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/semantic/summary.md)
and [fixture explanation](/Users/saul/p/wt/egglog-encoding/eggcc-study/benchmarks/eggcc-encoding/README.md)
give exact source ranges and mathematical laws. Seeded invalid unions are
controls, not discovered compiler bugs.

## Address-key hypothesis

The proposed immutable constructor is `LocalCell(function, ordinal, offset)`.
As data, equality of these descriptors determines all three primitive fields.
The analysis associates a pointer with such a key only within a restricted
allocation/store prefix rooted at the sole state argument of an `InFunc` body
whose `FunctionHasType` input is exactly a one-element state tuple.
Positive constant-sized integer allocations receive consecutive ordinals. Constant
integer stores preserve the prefix. Exact pointer additions require valid,
representable in-bounds offsets. Explicit `LiveAllocation` ancestry requires
both pointer origins to be live at the same consumer state.

For pointers satisfying this invariant in one applicable invocation,
`ordinal₁ ≠ ordinal₂ OR offset₁ ≠ offset₂` identifies distinct live cells.
The query arm asks `known-disequal?` about immutable keys; an equivalent manual
arm compares their primitive fields over the same analysis and liveness domain.
Equal keys make no claim of runtime aliasing. Function names and ordinals are
not global runtime allocation identities across calls or loop iterations.

This exercises structural disequality through an injective data constructor.
It does not demonstrate an optimization that requires nontrivial equality
cancellation between e-class children. The query does not need an asserted
disequality between every pair of primitive payloads.

There are no direct transfer rules for calls, frees, branches, loops or other
unsupported effects. Unresolved symbolic sizes/offsets, unknown pointers and
invalid offsets do not acquire usable keys. Existing source equalities can
expose eligible forms: a symbolic zero may fold to the same key as zero, and
load-state equality can recover a supported prefix. Audits run after these
equalities and before accepting consumers. Existing expression constructors
and refining analysis records are not marked injective. Distinct e-class IDs
alone never establish nonalias.

The source-derived Bril example stores 17 and 99 into two live fresh allocations
and then loads the first. Both the encoding replay and the complete compiler
forward 17 in query and manual modes. A/B baselines, prototype off and keys-only
retain the load. The query/manual extracted programs remove it and print the
constant 17, while preserving the allocations, stores and frees.

This is a small source-derived input, not a production workload discovered by
the study. EggCC's optional memory analysis already has reasoning for the
two-allocation sequence. The intended comparison extends the active default
memory rules and compares a query with an equivalent restricted manual-pair
analysis; it does not replace the general optional points-to analysis.

The [independent semantic review](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/harness/semantic-review.md)
supports a bounded opt-in prototype. Seeded key/rank/cyclic conflicts reject
before consumers; audits are interleaved with propagation to prevent unbounded
ordinal generation. The original 16 semantic outcomes and 14 added fail-fast
outcomes pass under NEE/EE. Conflict absence is a useful check, not a general
soundness proof.

## Complete compiler demonstration

The final opt-in modes are `off`, `keys`, `query` and `manual`; `off` remains the
default. Enabled modes require contexts and reject ablation, including at the
API boundary. They add the restricted rules after each complete existing source
schedule and enforce consistency before serialization. Native Tiger extraction,
fresh-graph reconstruction and all three passes are retained.

The final frozen checkpoint has 18 interpreted CLI runs and 18 emitted-Bril runs:
A/B plus all four prototype modes for three inputs. Every interpreted run has
non-null equal source/result output and every pass completes. A/B/off/keys Bril
is byte-identical per input, as is query/manual Bril. Independent review checked
all 54 diagnostic graph hashes and the final 14 source-file hashes. Six invalid
CLI combinations reject contexts/ablation with exit 2. Focused native/API tests
also pass; seeded corruption is not classified as a compiler bug.

| Input | Baseline/off/keys | Query/manual | Checked output |
| --- | --- | --- | --- |
| Two fresh allocations | Retains `load p` | Removes `load p`, prints constant | 17 |
| Both stores target `p` | Existing forwarding | Preserves the later store | 99 |
| Second pointer is `p + 0` | Existing forwarding | Preserves the later store | 99 |

The central transformation is `store(p,17); store(q,99); print(load(p))` to
`store(p,17); store(q,99); print(17)`, under the restricted prefix and co-liveness
premise described above. The
[final correctness checkpoint](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/retarget/prototype/final/correctness.json)
links the original inputs, emitted programs, exact commands, frozen compiler
and sibling Tiger, and per-pass graphs. The
[independent final review](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/harness/prototype-review.md)
records the accepted source and treatment boundaries.

Keys/query/manual share an extra mem-simple/type-analysis fixed point after
the original schedule. Thus off→keys includes that closure as well as key and
audit work; it is not a pure annotation-cost measurement. Query/manual share
the same guarded key/liveness domain. Their comparison concerns query-driven
versus materialized-pair consumption. Both retain a shared query-based conflict
audit. No asserted disequalities are needed here, so this workload does not
provide a meaningful NEE/EE assertion-storage comparison.

The diagnostic first-pass snapshot of the fresh-allocation case makes the
storage distinction concrete:

| Mode | Exact address rows | Liveness rows | Prefix rows | Manual pair rows | Total serialized nodes |
| --- | ---: | ---: | ---: | ---: | ---: |
| keys | 2 | 7 | 5 | 0 | 524 |
| query | 2 | 7 | 5 | 0 | 544 |
| manual | 2 | 7 | 5 | 6 | 550 |

Query and manual produce the same optimized program; query stores no manual
nonalias pairs. Both pay for address, liveness and prefix data. These are
serialized rows after closure, including subsumed rows, not peak memory,
asymptotic bounds or counts of rule firings. The
[per-pass diagnostic table](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/retarget/prototype/final/diagnostic-row-counts.md)
and its JSON retain all inputs and source graph hashes. Diagnostic runs are
excluded from timings.

## Engine-only control

Arms A and B preserve compiler behavior: A uses the original pinned engine;
B retargets both compiler manifests and lockfiles to the encoding checkout.
Both use Rust 1.91.0 release builds, contexts, all three default parallel passes,
one Rayon thread, ordinary execution and native Tiger greedy extraction.
The compatibility diff is four files; no API or schema adaptation was needed.

Arithmetic and memory canaries complete optimization, native extraction and
fresh-graph reconstruction in both arms. Explicit non-null interpreter receipts
agree, and A/B optimized Bril is byte-identical per case. Eleven focused tests
also passed with nonzero counts. The
[retarget checkpoint](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/retarget/summary.md)
records two setup failures separately: scratch Cargo workspace bookkeeping and
an initially missing native Tiger side effect in the shared build cache.

The engine-control capture contains 48 successful invocations: four correctness
runs, four warmups and forty timed observations (two cases × two arms × ten).
`verify` passed against the retained inputs, frozen binaries, native Tiger,
source/configuration snapshots, receipts and tests. This contrast measures the
engine upgrade and retarget, not an encoding benefit.

Timing excludes interpretation and includes CLI startup, optimization,
extraction, reconstruction and receipt writing. Memory is platform-normalized
`wait4` child `rusage.ru_maxrss`; it is not simultaneous process-group or host
peak memory. Generated-program runtime is not measured.

| Case | Arm | n | Wall seconds, median [min,max] | Wait4 peak MiB, median [min,max] |
| --- | --- | ---: | ---: | ---: |
| Constant folding | A | 10 | 0.1365 [0.1353,0.1387] | 40.41 [40.23,40.55] |
| Constant folding | B | 10 | 0.1340 [0.1330,0.1363] | 40.78 [40.73,40.86] |
| Existing store forwarding | A | 10 | 0.1425 [0.1413,0.1437] | 41.19 [40.61,41.50] |
| Existing store forwarding | B | 10 | 0.1411 [0.1405,0.1448] | 41.09 [40.88,41.30] |

The differences are small; no significance or encoding speedup is claimed.
[Per-case SVG/PDF figures, raw figure data and the table with sample SD](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/engine-control/figures)
show every measured observation. Spread is observational, not a confidence
interval. All seven generated artifacts matched an independent fresh export
byte for byte, and both PDF renders were inspected. The
[figure QA receipt](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/engine-control/figure-qa/receipt.json)
binds the commands and source hashes.

## Feature cost observations

The main feature cohort has one warmup and ten observations per case/mode after
all twelve source/result interpreter checks pass. All 144 invocations complete;
only the 120 timed observations enter the figures. All compiler builds and
other study sampling were stopped during collection. Each row below describes
one workload and mode; there is no pooled aggregate.

| Case | Arm | n | Compiler wall s: median [min, max]; SD | wait4 peak MiB: median [min, max]; SD |
| --- | --- | ---: | ---: | ---: |
| fresh-allocations | off | 10 | 0.1429 [0.1408, 0.1468]; 0.001641 | 41.27 [41.16, 41.41]; 0.08275 |
| fresh-allocations | keys | 10 | 0.1488 [0.1477, 0.1507]; 0.0007831 | 42.77 [42.23, 42.95]; 0.2144 |
| fresh-allocations | query | 10 | 0.149 [0.1477, 0.1498]; 0.0006074 | 42.9 [42.8, 42.97]; 0.05522 |
| fresh-allocations | manual | 10 | 0.1493 [0.1471, 0.168]; 0.006082 | 42.76 [42.55, 42.86]; 0.09722 |
| same-pointer | off | 10 | 0.1395 [0.1388, 0.1518]; 0.003878 | 41.04 [40.88, 41.3]; 0.111 |
| same-pointer | keys | 10 | 0.1456 [0.1444, 0.1476]; 0.001082 | 42.26 [41.97, 42.41]; 0.1199 |
| same-pointer | query | 10 | 0.1459 [0.1452, 0.1484]; 0.0009894 | 42.47 [42.39, 42.69]; 0.09242 |
| same-pointer | manual | 10 | 0.1459 [0.1446, 0.1473]; 0.0007376 | 42.47 [42.23, 42.72]; 0.121 |
| zero-offset | off | 10 | 0.142 [0.1411, 0.1456]; 0.001218 | 41.4 [41.23, 41.47]; 0.08908 |
| zero-offset | keys | 10 | 0.1481 [0.1472, 0.1489]; 0.0004529 | 42.68 [42.55, 42.88]; 0.1119 |
| zero-offset | query | 10 | 0.1486 [0.1469, 0.1519]; 0.001365 | 42.8 [42.5, 42.97]; 0.1266 |
| zero-offset | manual | 10 | 0.1485 [0.1473, 0.1523]; 0.001461 | 42.7 [42.3, 43.38]; 0.3033 |

RSS: wait4 child rusage.ru_maxrss; platform-normalized, not simultaneous process-group peak. Wall time is compiler process elapsed time, not generated-program performance.
Spread is observational, not a confidence interval. Warmups and interpreted checks are excluded.

Enabled modes have higher optimizer time and RSS than off in this small main
cohort. Off→keys includes analysis, audits and extra source/type closure.
Query/manual use the same guarded domain and produce the same program, but
these observations do not establish a time or peak-RSS advantage for query.
Avoiding six serialized pair rows is a logical storage result, not a measured
whole-process memory saving. Generated-program execution speed was not measured.

[Per-case SVG/PDF figures and raw figure data](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/feature-control/figures)
retain every observation. Their independent regeneration is byte-identical,
and all three PDF renders were inspected. The
[QA receipt](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/feature-control/figure-qa/receipt.json)
checks the summaries against all 120 raw measured rows.

### Fresh representative reproduction

A separate fresh artifact directory repeats the positive case in all four modes
with one warmup and ten observations, invoking the collector from `/tmp`.
All 48 invocations pass verification, including non-null interpreter output 17.
Four additional fresh emitted-program checks reproduce the earlier Bril bytes:
off/keys retain the load and query/manual remove it. The
[transformation receipt](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/reproduction/transformations/receipt.json)
links commands, source/input/binary hashes and the fresh interpreter receipts.

This second timing cohort has substantially wider wall-time variation. It is
retained separately and is not pooled with the main cohort:

| Case | Arm | n | Compiler wall s: median [min, max]; SD | wait4 peak MiB: median [min, max]; SD |
| --- | --- | ---: | ---: | ---: |
| fresh-allocations | off | 10 | 0.1726 [0.1423, 0.2193]; 0.03506 | 41.26 [41.19, 41.44]; 0.08184 |
| fresh-allocations | keys | 10 | 0.157 [0.1481, 0.2593]; 0.03917 | 42.59 [42.36, 42.91]; 0.1866 |
| fresh-allocations | query | 10 | 0.1738 [0.1482, 0.2786]; 0.04626 | 42.89 [42.64, 43.05]; 0.1146 |
| fresh-allocations | manual | 10 | 0.1831 [0.1477, 0.3184]; 0.05904 | 42.77 [42.66, 42.98]; 0.1093 |

RSS: wait4 child rusage.ru_maxrss; platform-normalized, not simultaneous process-group peak. Wall time is compiler process elapsed time, not generated-program performance.
Spread is observational, not a confidence interval. Warmups and interpreted checks are excluded.

The variation reinforces the limit on small timing differences. This study
makes no stable query/manual speedup claim. The
[fresh figures](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/reproduction/figures)
and [independent regeneration/QA](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/reproduction/figure-qa/receipt.json)
retain the full second cohort. Its PDF was inspected, and regenerated output
is byte-identical.

## Validation and preservation

The encoding checkout's complete `make check` passed: formatting, linting,
type/lock checks, documentation links, 256 Python tests and 1,797 Rust tests.
One optional Matplotlib test was skipped in the normal environment and passes
in the separately pinned 24-test collector suite. Six Rust tests are ignored by
the existing suite. The
[gate summary](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/encoding-validation/summary.json)
links the exact command and captured output.

The preservation verifier checked 8,365 pre-existing file states across both
primary checkouts and the original injectivity worktree: no file hashes,
branches, HEADs or unrelated status entries changed. The goal's own authorized
notes are excluded. Its
[receipt and rerunnable verifier](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/preservation/verification.json)
retain that boundary.

EggCC's runtime-resolved root execution passes 31 library tests, one CLI test,
two feature integration tests and 2,421 file trials. The separate exact DAG Make
command passes all 66 tests. The strict `make test` result remains exit 2 for
13 pending golden snapshots. All 13 bodies reproduce byte-identically in the
pre-feature engine-only B source and prototype off mode, across 26 exact-trial
comparisons. No snapshot was accepted. This limits a general drop-in retarget
claim; the measured three-case transformation is independently validated.

Strict `make nits` also remains exit 2. Rust 1.91 flags `unnecessary_unwrap` in
unchanged direct-jump code; the original A checkout reproduces it. Strict DAG
Clippy reports that lint and `cloned_ref_to_slice_refs` in two other unchanged
files. Root/DAG formatting and Prettier pass. Diagnostic Clippy passes when
allowing only the identified baseline lint names; those altered commands do
not make the strict gate green. No unrelated lint fix was included.

The first full test attempt had 757 missing-runtime failures. Preparing the
documented runtime outputs resolved all of them. On this macOS host the normal
installer emits LLVM18 bitcode before its final executable link fails; the
emitted bitcode passed LLVM18 verification, and the remaining documented copy/C
compile steps produced the required artifacts without source changes. Exact
commands, source identities, runtime hashes, strict failures and supplementary
checks are retained in the
[final gate dossier](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/retarget/prototype/final/summary.md)
and [machine-readable gate receipts](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/retarget/prototype/final/gates.json).

## Recommendation for the paper

Use immutable address keys as a compact worked example of structural disequality
through an injective constructor. The actual EggCC integration demonstrates a
semantically justified restricted consumer and avoids materializing a pair relation. Include the
failed mutable-record and contextual-constructor candidates to explain why the
representation contract matters.

Present this as a small source-derived compiler example. The investigated scope
found no new EggCC bug or production-workload improvement, and the measurements
do not support a speedup claim. The optional analysis already handles a similar
two-allocation sequence. A broader evaluation would need realistic workloads and
justified transfer across more effects and contexts; the current result does not
claim that no such use case exists.

The actual compiler case makes a separate standalone fallback unnecessary.
No new proof support, Lean work or paper edits were made. The
[prototype rules](/Users/saul/p/wt/eggcc/encoding-study-retarget/dag_in_context/src/optimizations/exact_local_addresses.egg),
[executable semantic explanation](/Users/saul/p/wt/egglog-encoding/eggcc-study/benchmarks/eggcc-encoding/README.md),
[rerun instructions](/Users/saul/p/egglog-encoding/goals/eggcc-encoding-case-study/rerun.md),
[compiler patch](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/retarget/prototype/final/full.patch)
and [encoding study patch](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/encoding-study/study.patch)
are retained for review.
All study changes remain local and uncommitted. The strict EggCC golden/lint
limitations above remain explicit rather than being silently accepted or fixed
outside the case.

The [completion audit](/Users/saul/p/egglog-encoding/goals/eggcc-encoding-case-study/completion-audit.json)
maps every accepted fact to evidence or a documented gate limitation. Final
[artifact/source/preservation verification](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/final-verification.json)
passes for all three measured datasets and the retained source boundaries.
