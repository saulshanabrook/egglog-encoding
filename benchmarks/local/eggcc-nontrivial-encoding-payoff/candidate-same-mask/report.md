# A scoped disequality chain removes a redundant comparison in EggCC

This experiment adds a conservative source-boundary analysis to EggCC and measures a generated-runtime improvement on one constructed Bril loop. The analysis uses the existing generic reverse-disequality query and an injective fixed-translation constructor together. It removes a comparison that the admitted EggCC and LLVM 18 pipeline retains. It finds no new compiler bug.

The measured Encoding/U0 cycle-paired median ratio is **0.98084**, with bootstrap 95% interval **[0.98042, 0.98164]**, about 1.9% less elapsed time for the generated program. This passes the prospective gate requiring the upper bound below 0.99. This is a microbenchmark result on this machine, not a benchmark-suite result. The candidate is not ready to merge: full EggCC validation retains known dependency-retarget snapshot failures and three baseline Clippy findings, plus a formatting delta in the added hook.

## The source fact and the two logical steps

The relevant source fragment, inside a loop, is:

```text
if ((x & m) == (y & m)) {
    delta = 3;
} else {
    if ((x + 7) == (y + 7)) delta = 99;
    else delta = 7;
}
```

All operations are EggCC's wrapping i64 operations. The inner comparison is false throughout the outer false branch:

1. `(x & m) ≠ (y & m)` implies `x ≠ y`. If `x = y`, ordinary congruence would imply `(x & m) = (y & m)`. Bitwise-and itself need not be injective; the common sibling `m` is essential.
2. `x ≠ y` implies `(x + 7) ≠ (y + 7)`. Addition of a fixed constant is a bijection modulo 2^64. This step uses injectivity.

Thus the compiler can replace the inner comparison with false and select `delta = 7` on that branch. When the masks differ, the first implication does not follow. When the two added constants differ, the second implication does not follow.

The [complete input](fixtures/hot.bril) updates `x = 3*x + 1` and `y = 5*y + 7` each iteration, accumulates the selected delta, and uses a dynamic common mask. These changing values keep the comparison in the hot loop. The [cold input](fixtures/cold.bril) demonstrates the same law without a loop. They are two instances of one optimization, not separate bug findings.

## What enters the encoding

The analysis runs on the contextualized source before insertion into EggCC's main egraph. For each eligible inner comparison it creates a fresh private NEE egraph. The [source](source/eggcc/dag_in_context/src/scoped_reasoning.rs) checks types, exact branch assumptions, and exact input-tuple projections before translating the operands.

The small [actual hot query program](hot-private-program.egg) uses these declarations:

```lisp
(datatype Scope (ThisScope))
(datatype Word)
(constructor Mask (Word Word) Word)
(constructor Leaf0 (Scope) Word)
(constructor Leaf1 (Scope) Word)
(constructor Leaf2 (Scope) Word)
(constructor Shift0 (Word) Word :injective)
```

`Leaf0`, `Leaf1`, and `Leaf2` are opaque equality-sort terms for the current `x`, `y`, and `m`. They have no primitive-valued fields. `ThisScope` belongs to this private graph and denotes exactly the parent context recorded in the query receipt. No equality or disequality about these terms enters another branch's graph.

`Mask(x,m)` represents the supported bitwise-and expression and is **unmarked**. `Shift0(x)` represents addition of exactly 7. A different constant gets a different unary constructor. Raw `Add`, `Bitand`, `Expr`, and context constructors are never marked injective.

The host commits the Mask and Shift terms and seeds only the outer branch fact:

```lisp
(disequal (Mask y m) (Mask x m))
(run-schedule (saturate injectivity))
```

It then queries the generic `known-disequal` machinery for the parent pair, the child pair, and the target pair. The retained engine's [reverse query implementation](source/engine/egglog-experimental/src/disequality.rs) uses an asserted parent disequality and equal sibling fields to establish `x ≠ y`. Its marked-constructor handling then recognizes the target Shift disequality. The positive receipts record `parent_known=true`, `child_known=true`, and `target_known=true`.

The final `target_known` query is the permission to export the exact child-context Boolean `Eq` as false. The [main-graph hook](source/eggcc/dag_in_context/src/lib.rs) adds only that Boolean equivalence to EggCC's initialization. The existing constant-If and interval consumers can then eliminate the unreachable arm. The branch assumption itself is never asserted globally. An inconsistent private graph, unsupported expression, failed translation, missing query witness, or analysis error prevents export. A missing witness means “not established,” not that the operands are equal.

This analysis intentionally recognizes a narrow Mask/Mask parent and Shift/Shift target. The two engine steps are causally necessary in this implementation, but a specialized contextual rewrite could encode this complete law directly. The experiment does not establish that the generic encoding is indispensable, nor that this integration already pays for itself across a compiler workload suite.

## Why the loop needed a checked constant proof

At the first hot attempt, source lowering represented the literal 7 as a loop input slot. The literal-only translator therefore found no eligible query. Those [attempt-0 artifacts](matrix/hot) are retained; they are a negative result, not positive evidence.

The selected version admits a loop slot as a fixed literal only when the exact initial projection is `Const k` in the enclosing context and the corresponding body output is structurally the same input slot. The proof flattens exact tuple construction and checks both branches of an intervening If. In a DoWhile body, output 0 is the loop predicate; input slot i is carried by output slot i+1. Types and contexts must agree. Arithmetic updates, forwarding from another index, and a runtime initial value fail this test.

On the exact hot input, the first eligible proof and export occur at source-boundary invocation 0. No later compiler pass is needed to expose `+7`. Receipts retain the admitted loop slots and the literal 7 proof.

The law would also hold for a common dynamic offset. This implementation supports fixed unary wrappers, so the structural constant proof is a deliberate restriction, not a mathematical requirement for cancellation.

## Causal controls on the actual compiler

Every control compiles the same source and uses the same native lowering. The [compact summary](causal-summary.json) points to full query receipts, and the selected [seven-mode matrix](matrix-invariants-results.json.gz) contains both cold and hot results.

| Arm | Parent known | Child known | Target known | Main-graph effect | Native entry code |
|---|---|---|---|---|---|
| U0 / B1 Off | analysis skipped | skipped | skipped | none | baseline |
| SeedOnly | not queried | not queried | not queried | none | baseline |
| Reverse step off | yes | no witness | no witness | none | baseline |
| Reverse off + exact child rescue | yes | yes | yes | apply target=false | winning |
| Injective annotation off | yes | yes | no witness | none | baseline |
| Annotation off + exact target rescue | yes | yes | yes | apply target=false | winning |
| Target query off | yes | yes | query withheld | none | baseline |
| Bridge off | yes | yes | yes | return no target | baseline |
| Application off | yes | yes | yes | returned target observed; union withheld | baseline |
| Primitive-only null | not queried | not queried | no primitive witness | none | baseline |
| Manual / Encoding | yes | yes | yes | apply target=false | winning |

The reverse knockout changes only the diagnostic engine's reverse-query eligibility. Its private input program, terms, and parent seed are byte-identical to normal. Adding exactly the missing `disequal x y` fact rescues the target query and winning code. Removing the Shift annotation preserves the child witness but loses the target; injecting exactly the target disequality rescues it. The [diagnostic evidence](causal-results.json.gz) preserves those separate treatment sources and binaries. They are not the compiler that was timed.

The primitive-only null arm retains the opaque equality-sort term grammar and parent seed. There are zero primitive fields in the Word constructors. It tests native primitive inequality even on the equal paired shift constants, finds no target witness, and retains baseline code. This is not a Bool true/false or constant-conflict detector.

The exact downstream [application knockout](causal-application-results.json.gz) proves all three private witnesses and records `export=true`, materializes the same false constant, and records `main_graph_union_applied=false`. Suppressing only that union restores byte-identical baseline entry assembly. This differs from BridgeOff, which withholds the returned target before the application site.

Two earlier consumer knockouts disabled constant-If rewrite families but still produced winning code: the proven Eq=false remained available to extraction and LLVM. These are retained as informative **failed knockouts**; they do not prove any one rewrite is the sole consumer. Their artifacts remain under `matrix-causal` and `consumer-knockout-dag`. The successful application knockout identifies the necessary producer/consumer boundary without claiming a unique downstream rewrite.

## Correctness, negatives, and native code

The selected correctness matrix checks 91 native outputs: four cold cases and nine hot cases across seven modes. Source interpretation, optimized interpretation at declared arguments, and direct native output all agree with independent expected values. Cases include zero and negative iteration counts, equal operands, zero masks, signed extrema, and wrapping updates. The [supplement](supplement-results.json) adds direct U0/B1 parity and seven actual-compiler negatives across Off, Manual, and Encoding: different masks, different shifts, true sibling branch, unsupported division, a runtime loop initial value, an updated slot, and a slot forwarded from another index. Every negative preserves behavior and exports no fact. No-context Off and Encoding emissions are byte-identical and produce no sidecar proof.

An early harness expectation for the updated/other-index slot controls incorrectly held delta=7 fixed. The original and optimized programs agreed on 67 and 34; an independent stateful oracle corrected the expectation. [adapter-notes.json](adapter-notes.json) and [loop-negative-oracle.json](loop-negative-oracle.json) retain this correction and the original receipts.

Untouched U0 and B1 Off have byte-identical emitted hot Bril and entry disassembly. Manual and Encoding also have byte-identical emitted Bril and entry disassembly. This is a comparison to the admitted upstream compiler, not merely a cross-mode change in the retargeted compiler.

The actual `_main` loop goes from 12 to 10 instructions. Baseline includes `cmp x20,x21` and a `csel` that retains the inner 99-versus-7 choice; the winning loop removes them. LLVM already simplifies equal fixed additions to operand comparison, but does not combine it with the mask-inequality branch fact. [Baseline assembly](matrix-supplement/hot-u0/off/native/main.asm) and [winning assembly](matrix-invariants/hot/encoding/native/main.asm) show this final endpoint. Code shape alone is not the performance evidence.

## Generated-runtime confirmation

The [design](confirmation-design.json) was frozen before sampling. Thirty-two complete four-arm balanced cycles provide 32 observations per arm, with three separate warmups per arm. Each measured program runs 200,000,000 iterations with arguments `200000000 0 1 6`, producing exactly `1200000000\n`. The independent finite-state oracle checks this expected value. Every measured and warmup execution succeeded and matched expected output; no sample is dropped.

The timer surrounds `subprocess.run` and excludes evidence-file persistence. It includes process startup. Ratios pair observations from the same cycle; the interval bootstraps complete cycle ratios with 10,000 draws and a fixed seed. [Raw rows](confirmation-samples.jsonl), [cycles](confirmation-cycles.json), and the [summary](confirmation-summary.json) are retained.

| Arm | Median elapsed | Paired arm/U0 median | Bootstrap 95% |
|---|---:|---:|---:|
| U0 | 170.162 ms | 1 | reference |
| B1 Off | 170.131 ms | 1.00034 | [0.99860, 1.00183] |
| Manual | 166.894 ms | 0.98087 | [0.98004, 0.98230] |
| Encoding | 166.843 ms | 0.98084 | [0.98042, 0.98164] |

Encoding/Manual is **0.99964**, interval **[0.99847, 1.00088]**, computed from the same existing batch; no new runtime samples were taken. This placebo is consistent with their equal entry code. Every order stratum shows the Encoding/U0 benefit.

There is no CPU isolation, and system activity is not controlled. The actual inlined loop starts at `0x10000570c` in U0/B1 and `0x1000056fc` in Manual/Encoding: both are 12 mod 16, but 12 versus 60 mod 64. The removed instructions alter layout. There is no alignment-matched or x86 confirmation, so the measured difference cannot be assigned exclusively to instruction count. This remains one synthetic workload on one Apple Silicon machine; it establishes neither suite-wide benefit nor production frequency of the pattern.

## Compiler-time diagnostic

A separate [frozen diagnostic design](compile-diagnostic-design.json) uses ten balanced five-arm cycles, one warmup per arm, and the exact same hot input/configuration. It includes all EggCC startup, parsing, contextualization, private graph construction and translation, schedule execution, extraction, and Bril emission. Rust builds, native lowering, and generated execution are excluded. Per-query evidence-file output is disabled equally; compiler run-data output remains inside the timed interval. All 50 measured emissions match the frozen expected Bril hashes exactly.

| Arm | Median optimize wall time | Paired arm/B1 median | Bootstrap 95% |
|---|---:|---:|---:|
| U0 | 650.0 ms | — | — |
| B1 Off | 629.1 ms | 1 | reference |
| SeedOnly | 636.8 ms | 1.01189 | [0.96902, 1.03206] |
| Manual | 644.5 ms | 1.02161 | [0.99400, 1.05278] |
| Encoding | 646.8 ms | 1.02094 | [0.95841, 1.03721] |

Encoding/U0 is 0.99782, interval [0.97691, 1.01500]. This diagnostic is too noisy to establish total overhead or a compiler-time improvement. Late-cycle drift and host load are retained, not filtered. It also does not isolate the marginal cost of each private graph. See [raw diagnostic rows](compile-diagnostic-samples.jsonl) and [summary](compile-diagnostic-summary.json).

## Validation and source identity

The [source admission](source-admission.json) binds EggCC `a0bbec127f83249074a46af3fd6f6126c90fe0fb`, encoding revision `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`, and five exact retained n-ary reverse-query files. The selected six-file EggCC delta is retained both as [source files](source/eggcc) and [invariants-source.tar](invariants-source.tar). Its selected compiler SHA-256 is `5343e3352f74e4e7ec80082a1e47912019d2f37bc641f2ed62891267e465fb87`; untouched U0 compiler SHA-256 is `d86869982413d4561cf713cc769c96eb1c9bfefe46fa459a2692c53a7aa93cf0`. Both use the admitted paired Tiger and runtime. Diagnostic control binaries have distinct identities and were not timed.

Full terminal [validation receipts](full-validation-results.json) show:

- Encoding engine `UV_PYTHON=3.12 make check`: **passes**, 233 Python and 1,804 Rust tests/doctests; six ignored. Earlier sandbox/cache, Python 3.15 dependency, and archive-without-git failures are preserved. Initializing local git metadata in the disposable source archive enabled the repository-root test; no source bytes or commit history changed.
- Selected EggCC `make test`: 31 library and 2,421 integration tests pass, but cargo-insta returns failure for 13 pending snapshots and Make stops before DAG tests. No snapshot is accepted. A separate exact official DAG command passes all 68 DAG tests and reports no snapshots to review.
- Each of the 13 pending snapshot files matches the prior dependency-only retarget control byte-for-byte in a [fresh comparison](snapshot-attribution-current.json). The known retarget-only no-context `branch_hoisting` regression remains an integration limitation, not a new bug found by this analysis.
- Root format passes. Strict root/DAG Clippy reports the same three unchanged-source findings already recorded for U0. DAG format additionally reports ordering/layout changes in this experiment's `lib.rs` hook. The selected timed source remains frozen, including that formatting issue.

These are not wholly green EggCC integration gates. The local runtime result does not waive them or establish that the E1 dependency retarget is generally safe.

## Reproduction boundaries

Every CLI receipt under [commands](commands) records exact argv, cwd, exit status, timeout, environment essentials, and output hashes. Compiler probes use finite 180-second limits, native correctness probes 30 seconds, `RAYON_NUM_THREADS=1`, LLVM 18, and no benchmark memory guard. Full build/test gates use their separately recorded larger finite limits. No memory-pressure stop or failed command is counted as successful behavior.

`matrix.py`, `supplement.py`, `causal.py`, and `causal-application.py` construct the correctness evidence. `confirmation.py` implements the already-completed runtime design and refuses to reuse its output directory. `compile-diagnostic.py` implements the separate completed compiler diagnostic. Reproduction should use fresh evidence directories and admitted binaries. The selected source/engine copies remain under `/private/tmp`; their original U0 and retained E1 sources are preserved. [files.json](files.json) indexes the retained evidence hashes.
