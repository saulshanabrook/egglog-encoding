# Compiler findings: first arithmetic screen

Status: **a valid-input silent baseline miscompile and two valid-input optimizer panics are reproduced**. This is the first frozen-binary screen, not a compiler fix, encoding benefit, speedup, upstream-current claim, or whole-goal completion. All work used the new compiler worktree and new raw evidence tree; no build, commit, push, old-source edit or timing cohort ran.

The evidence index is [receipt-index.json](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/arithmetic-screen/receipt-index.json>), with exact argv/cwd/complete explicit child environment, 60-second process-group timeouts, input/source/binary/Tiger hashes, statuses and output fields in its linked receipts. [verify-evidence.py](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/arithmetic-screen/verify-evidence.py>) independently checks the retained artifact/claim consistency; it does not assert that the compiler is correct or rerun compilation. [verification.json](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/arithmetic-screen/verification.json>) records the result.

## Reproduced behavior

All arms use previously frozen Rust 1.91 release compilers built from EggCC `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`, distinguished by artifact hash:

| Arm | Engine/feature role | Compiler SHA-256 |
| --- | --- | --- |
| A | Original historical-engine compiler | `e062c92bbcb9a8f05caed3cc10ec013c126a1d1f528e57f3b797bf6c3004912d` |
| B | Engine-only retarget, no local-address feature | `6c30c8cb28768f3c461666b0370ff5c249fe6ba1f8f58a1a1d6c78e2df3e638f` |
| P-off | Previous prototype, explicitly `--exact-local-addresses off` | `d44a89c2f752aff60b2691d9e055f23e54215fc9dfa74a0db8e956afc713162e` |

Each invokes its frozen sibling native Tiger, SHA-256 `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`. Pre/post verification confirms these binaries unchanged. Cwd is **new** `/Users/saul/p/wt/eggcc/encoding-impact`; outputs live only under `benchmarks/local/eggcc-encoding-impact/compiler/arithmetic-screen/`. Contexts are enabled, default parallel three-pass schedule and non_weakly_linear=true are preserved, native greedy extraction/reconstruction unchanged. RAYON_NUM_THREADS=1 and RUST_LOG=info are explicit. CLI timing fields/log timings are diagnostic byproducts, not observations for a performance claim.

First valid-input screen: 32 invocations (8 source-interpretation checks plus 24 optimizing runs). All eight source expectations were confirmed. Every arm gives the same result:

| Input | Source expectation | Optimizing outcome per arm |
| --- | --- | --- |
| `max-ge-max.bril` | true | Exit 101 in pass 0: `(+ la lb): call of primitive + failed` |
| `min-le-min.bril` | true | Exit 101 in pass 0: `(- la hb): call of primitive - failed` |
| `small-ge.bril`, `small-le.bril` | true | Exit 0, all three passes, non-null true == true |
| `mul-max.bril` with MAX | true | **Exit 0, all three passes, non-null original true != optimized false** |
| `mul-one.bril`, `mul-zero.bril`, `mul-negative.bril` | false | Exit 0, all three passes, non-null false == false |

These are deliberately new **source-derived valid Bril programs**, not production workloads, invalid annotations or seeded egraph equalities. No invocation timed out. Endpoint optimization failures produce no run-data JSON, so no null field is passed off as an equality check; separate parse-mode and DAG-round-trip interpretation establish their valid source behavior.

## Reduced silent miscompile

The stable reduced input is [mul-minimal-max.bril](</Users/saul/p/wt/eggcc/encoding-impact/tests/encoding_impact/arithmetic/mul-minimal-max.bril>); the passing control is [mul-minimal-one.bril](</Users/saul/p/wt/eggcc/encoding-impact/tests/encoding_impact/arithmetic/mul-minimal-one.bril>). Only the ARGS value differs. The earlier `mul-max` and first-screen input paths remain unchanged. The reduction removes the irrelevant else-branch print and join jumps; no global-minimality claim is made.

```bril
# ARGS: 9223372036854775807
@main(x: int) {
  zero: int = const 0;
  two: int = const 2;
  positive: bool = lt zero x;
  br positive .positive .done;
.positive:
  product: int = mul x two;
  answer: bool = lt product zero;
  print answer;
.done:
  ret;
}
```

This is total and terminating over i64 inputs: no division, shifts, memory operations or undefined pointer behavior. Signed wrapping multiplication is explicit in [interpreter.rs:245](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/interpreter.rs:245>); MAX*2 is -2 modulo 2^64, hence the source prints true. Original Bril interpretation and an optimization-free DAG round trip both actually print true. At x=1, the source/control correctly prints false.

All A/B/P-off optimizing runs on this reduced input complete passes 0/1/2 and reproduce true→false. Exact A evidence: [receipt](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/arithmetic-screen/localization/runs/mul-minimal-max/A-optimize/receipt.json>), [run data](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/arithmetic-screen/localization/runs/mul-minimal-max/A-optimize/run-data.json>), [emitted Bril](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/arithmetic-screen/localization/runs/mul-minimal-max/A-emit/optimized.bril>). B/P-off sibling directories have the same evidence shape. All three emitted programs replace the positive branch's multiplication/comparison with literal false.

The violated invariant is the signed interval lower bound, not arithmetic injectivity: [positive×positive](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/interval_analysis.egg:159>) and [nonnegative×nonnegative](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/interval_analysis.egg:192>) infer nonnegative products without an overflow precondition. [graph-witnesses.json](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/arithmetic-screen/graph-witnesses.json>) records each arm's pass-0 product lower bound 1 and the `product<0` expression in the same class as branch-context Bool false. The graph is diagnostic data, not mechanized proof provenance.

## Localization and failed hypotheses retained

[localization/results.json](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/arithmetic-screen/localization/results.json>) contains 23 additional compiler invocations: reduced repro/control, typed DAG round trips, CLI ablation attempts, and emitted Bril. The DAG round trips preserve all three bug inputs' source answers, narrowing the cause beyond basic frontend/tree reconstruction.

**CLI ablation was not a valid exclusion control.** Attempted `--ablate canon` still panics at the endpoints; `--ablate interval-analysis` still silently miscompiles. [Source lines 118–155](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/lib.rs:118>) move targeted rules to `never` and then replace the scheduled target by `never`; logs confirm actual `(run never)` execution. [ablation-provisional.json](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/arithmetic-screen/ablation-provisional.json>) retains commands and log counts. Treat this as a separate provisional source/log finding; it neither disproves the arithmetic diagnosis nor establishes effective ablation. No ablation implementation was fixed.

A separate **exported pass-0 replay**, not a full compiler treatment, cleanly changes source rules. Frozen B exports the complete prologue, initialization and first source schedule using `--run-mode egglog --stop-after-n-passes 1`. The frozen ordinary-mode CLI `semantic/bin/egglog-experimental-392b6d6b-debug` is verified at SHA `46f898796589e8585ecaf1499a9b9d7ee98d31fc45f64d2061c103795d62ecf2`. It executes original and filtered programs under the same schedule; raw `change.json` records exact removed text, one-occurrence assertions and hashes.

- Original multiplication export completes and checks the false equality. Removing **only** the strict-positive multiplication rule fails the attempted absence check: the nonnegative rule independently suffices. This failed single-rule hypothesis is retained as `pass0-replay/mul-minimal-max/filtered/`.
- Removing **exactly those two overlapping sign rules** leaves the product/comparison present, and the false equality absent. Both positive existence and negative equality checks pass: [filtered replay receipt](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/arithmetic-screen/pass0-replay/mul-minimal-max/filtered-two-sign-rules/receipt.json>). This narrows the cause without changing the rest of the exported schedule.
- Original endpoint exports reproduce the same primitive +/− errors. Removing only the corresponding GreaterEq or LessEq canonicalization rule makes each exported pass complete and checks that the original comparison still exists. These replays do not establish the final native result of a fixed compiler.

The main findings are full native-pipeline baseline failures. The filtering is explicitly reduced diagnostic evidence; no source-rule-removal compiler build or corrected full-pipeline treatment has run. Ten export/replay invocations are retained, including the failed one-rule absence check.

An initial empty `# ARGS:` marker caused a no-argument fixture to receive one empty argument; that setup failure is retained in `initial-attempt.json`, initial manifest/input copies and its receipt. The empty markers were removed before the valid screen. The initial obsolete input-path content is archived under `arithmetic-screen/inputs/`; the valid first-screen and reduced paths/hashes are stable. It is not counted as a compiler arithmetic bug. A raw script-generation quoting error also caused no compiler invocation; its corrected script is retained.

## Encoding role and next ranked mechanism

**No incremental encoding value is established.** These failures occur in original A, so neither the engine retarget nor local-address feature caused them. Endpoint panic diagnostics are primitive arithmetic failures, before the hypothesized existing Const guard. The silent mismatch is a branch-local wrong bound; it never unifies top-level true/false literals in the shown pipeline. Injective Int/Bool wrappers or global Const cancellation would not soundly repair this. Do not annotate mutable bounds or vacuous contextual values merely to obtain a detector.

A sound next correctness step, after review/build-slot release, is an actual narrowly filtered source-rule treatment: remove or overflow-guard the two sign inferences and guard endpoint canonicalization; rerun original failing/control inputs through the real pipeline. This would confirm/fix an ancillary arithmetic bug. Reproduce against a fresh current-upstream compiler before calling it upstream-current; no such build is authorized by this checkpoint. Encoding-specific localization would need a separately reviewed valid invariant or a consumer that supplies actual additional detection power; none is promised here.

**Proposed next encoding-led screen (C2), before any new key-domain implementation:**

1. Use frozen engine-only B with default full three passes/context/native extraction on existing `benchmarks/passing/bril/mem/csrmv.bril` and `mat-mul.bril`. For an inexpensive correctness diagnostic, archive copies with only first-line ARGS changed to small shape-valid parameters (proposed csrmv=8, mat-mul=4), retaining original source hashes and the one-line diff. Compiler inputs remain parameterized, but verify rather than assume an unchanged compile graph: compare original-header and small-header complete pass-0 exports (and normalized graph identities where feasible) before interpreting the small variants. Label diagnostic inputs rather than claiming original-size measurements.
2. Use one process group at a time, initially a 120-second whole-invocation timeout, the existing 10-GiB process-group ceiling, normal-pressure check and 2-GiB host reserve on this 16-GiB host. Reuse only the current selected-base `processes.py` plus `memory_guard.py` through a small isolated harness adapter; do not transplant the older runner or launch potentially large graphs unguarded. Wait for the encoding build/test slot to quiesce before a potentially large graph; stop and classify any memory/timeout failure before the next case. No timing cohort or unbounded/stress batch is proposed.
3. Retain original/optimized non-null output equality and all three serialized graphs. Count final serialized NoAlias rows per pass, present write→load demand pairs, their intersection, DidMemOptimization witnesses, graph nodes and context shapes. These are final-graph cardinalities, not cumulative derivations, all actual consumers over time, CPU cost or peak RSS. Include subsumption/canonicalization policy in the diagnostic.
4. Specifically check csrmv's adjacent rowptr/rid+1 read pairs: they may produce NoAlias with no immediate write/load commute demand. Matrix hot memory crosses array roots; do not claim same-root keys cover it. Record call/inlining/loop visibility and whether any eligible hot consumer is actually blocked.
5. Stop/reject the kernel for C2 if it has negligible pair work, a baseline failure, no reached guarded domain, or no plausible material cost. Do not implement a witness builder just to manufacture reachability. If a plausible case survives, submit a source/config/semantic proposal comparing original, shared-witness-only, query, materialized manual pairs and direct primitive demand guards with matched closure/audits. Query/manual gains caused solely by demand placement must be attributed accordingly.

This checkpoint requests review/routing of that untimed screen, not permission to conclude the whole goal. No new key domain, loop/call summary, runtime adapter or encoding axiom was implemented. Shared build slot remains with the encoding owner; all compiler experiment processes from this worker are stopped.


## Alternative next slice: pointwise observation consistency (proposal only)

This is a worthwhile, bounded **full-compiler diagnostic** alternative to C2, subject to semantic review. It can demonstrate a real use of injective literal data in catching the silent branch-local bug that the current top-level Const guard misses. It is dynamic translation validation for selected valid inputs, not a new optimization, a speedup, all-input verification, or unique power beyond a manual oracle. It does not exercise remaining-child disequality.

### Sound invariant and minimal scope

For one *actually feasible* contextual evaluation point p, deterministic evaluation of equivalent Expr values must agree. Introduce a new opaque ObservationPoint token per recorded point, an unmarked `EvalBoolAt(Expr, ObservationPoint) -> ObservedBool` constructor, and `ObservedBool(bool) :injective` in its own result sort. Seed **observations**, not Expr equalities:

```text
EvalBoolAt(original_test_expr, p) = ObservedBool(true)
EvalBoolAt(Const(Bool(false), matching_arg_type, matching_context), p) = ObservedBool(false)
```

An optimizer union of those Expr arguments makes the two EvalBoolAt results congruent. Injectivity then rejects the unequal primitive bools. **Do not mark EvalBoolAt or Expr injective.** No parent/child Expr disequality is asserted. No semantic nonalias inference is involved. The opaque point records its concrete root input, actual branch context and actual region input. Only points reached by the original pre-pass computation are seeded; an impossible branch has no point, and observations never move to an outer/other context.

Start with the minimized case's single function, no loops/calls/memory/floats, and a whitelist of total wrapping integer operations/comparisons and boolean values. The surrounding print/state plumbing is executed once as normal but is not observed as a value constructor. Do not treat generic ExprIsPure as totality. Reject unsupported validation configurations explicitly or record skipped coverage; do not suggest every compiled expression was checked. A general trace over calls, repeated loop visits, memory or divergence would be a separate proposal.

The observation includes the actual value at a concrete input, so TRUE at this one point does **not** union the original expression with Const(true) globally. Seeding Bool literal observations is sound in that same feasible context, including the matching argument type; avoid broad contextual Const cancellation. Separate observed-result sorts for future Int versus Bool avoid relying on unimplemented constructor-tag disjointness.

### Concrete existing API and integration path

The new compiler tree supports this without an external replay-only driver:

- [public interpreter::interpret_expr](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/interpreter.rs:154>) evaluates a call-free RcExpr under an explicit Value argument and returns BrilState.value; the program/VM helper documents the call-free restriction. It is suitable for the whitelisted pure arithmetic/boolean fragments here, not arbitrary detached effectful expressions.
- [children_same_scope](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/schema_helpers.rs:231>) distinguishes region boundaries. A small bounded observer can evaluate the parent If predicate/inputs, follow only the selected arm and record that arm's concrete input before walking its whitelisted value fragments. Preserve Rc sharing; [the interpreter explicitly relies on it](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/interpreter.rs:139>). An exact feasible trace is the meaningful new implementation, not a trivial accessor.
- [build_program](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/lib.rs:209>) already inlines then adds contexts before printing shared terms and initialization. Collect observations on **that same contextual pre-pass tree**, print their Expr references through the existing TreeToEgglog/cache, and seed observation unions in the existing initialization action. This keeps identity/context aligned with the actual optimizer input.
- [optimize's batch loop](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/lib.rs:943>) runs the actual schedule before serialization/Tiger. An opt-in observer must run its consistency audit there, before the first serialization/extraction of every observed pass; default Off leaves the current pipeline unchanged. The finite observation seeds add no generative saturation and require no early callback inside the source schedule for the shown silent bug. Endpoint primitive-overflow panics happen earlier and are outside this detector's first scope.
- The host has actual fixture arguments in Run::run/ProgWithArguments before calling optimize_bril. A narrow diagnostic flag/config can carry parsed root inputs into the DAG observer; the existing source argument parser is at src/lib.rs:58–96. Do not use the currently ignored trailing CLI argument field. First integration files would be DAG lib.rs/config + a focused observation module, interpreter hooks only if the bounded walk cannot reuse its public fragment API, src/util.rs and src/main.rs for explicit diagnostic plumbing, and focused valid Bril fixtures/tests.

This requires a compiler build after the encoding owner releases the shared slot; **no implementation has started**. Reconstruct the verified engine-only retarget in the new worktree, and do not import the old local-address feature merely to obtain an observation hook. A small separate Rust full-optimizer test could prove the mechanism first, but an actual CLI three-pass receipt is required before claiming full-host support.

### Fair control and decisive checks

Use Off, identical observation seeding plus a direct manual conflict oracle, and identical seeding plus injective ObservedBool. The manual control can store `(Expr, point, primitive_bool)` observations and reject two different booleans for the same committed Expr/point; run both audits at the same pre-serialization boundary. Both should reject the **same** invalid class merge. This makes the generic differential-assert nature explicit; the encoding's value is a reusable literal-consistency contract/localization, not an unsupported advantage over an equivalent ordinary guard.

Expected gates: default Off still reproduces true→false; both observers reject before Tiger accepts that pass; x=1 and unreached-branch x=0/-1 remain non-null correct; all impossible/dead contexts produce no false rejection; distinct point tokens cannot cross-contaminate; input/context/type records are retained; no global Expr unions/disequalities are added by the oracle; and no additional fail is attributed to the existing Const guard. A source-rule-corrected variant should make both observers pass and actual output true, independently confirming detector specificity. Report unsupported points and diagnostic graph growth/cost separately, with no performance claim.

Choose this alternative if the parent prioritizes connecting the confirmed bug to a sound annotation contract. Choose the guarded C2 screen if the priority remains compiler/analysis speedup discovery. Either route still leaves the broader candidate map and dossier obligations active.


## C2 approved screen: completed without a current consumer hit

The guarded, untimed two-case screen is complete: [C2 verdict and next proposal](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/c2-screen/README.md>), [pinned checkpoint](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/c2-screen/checkpoint.json>), [six-pass table](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/c2-screen/cardinalities.md>). Current runner/guard import smoke passed, then all six compiler invocations succeeded with no timeout/resource stop: original/small complete pass-0 exports are byte-identical for each kernel; csrmv=8 and mat-mul=4 non-null interpretation matches 963 and 2446272 respectively through passes 0/1/2. Their only source changes are labeled first-line argument variants. No build, timing cohort, optimization source change or new key domain ran.

C2 alias-pair storage is not a promising observed target here: csrmv final snapshots have 2/0/10 NoAlias ordered pairs among 35,976/71,796/629,463 total nodes; mat-mul has 0 in all three snapshots. Current commute demand intersects those pairs 0 times. CSR's only four final demand pairs are same-address, with one store-forward existence marker; matrix has no final demand pairs. These are final cardinalities and source-rule body joins, not cumulative rule matches/time/peak memory or proof that all retained pairs were historically useless.

The next exact C3 diagnostic would inspect a guarded emitted CSR program for a surviving inner-loop accumulator load/store before designing region certificates or scalar promotion. Final CSR still has 14 Call nodes; matrix has zero Call and five Alloc nodes but no established residual redundant-memory target. A new same-anchor key analysis cannot enable a distinct-address commute that is absent from these snapshots. Deprioritize C2 integration for these inputs; retain the broader candidate map and pointwise-observer alternative. No all-search negative or speedup claim follows.

An automated turn flag prompted authoritative state recovery. The existing session had already completed successfully and OS/artifact inspection found no live C2 process. No workload was restarted; state-recovery.json records the terminal receipts. All compiler processes are now quiescent for root review/routing.

## Restricted observation implementation: first debug checkpoint

The previously proposed observer is now implemented in the new compiler worktree only. [Review summary](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/observations/review-checkpoint/summary.md>) and [complete manifest](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/observations/review-checkpoint/manifest.json>) bind the source patch, frozen debug compiler/Tiger, complete authoritative five-file E1 source package,10 passing DAG tests,3 passing full-host tests and all37 expected CLI outcomes. No source optimization rule was changed and no old local-address feature imported.

The actual MAX common-seed control still finishes all three passes with source true / optimized false and no existing Const-guard failure. Manual and Injective reject the same actual feasible branch comparison/false-literal conflict before serialization/Tiger; Injective's named error comes from the immutable ObservedBool wrapper's unequal primitive argument. x=1/0/-1 and dead/contradictory controls finish all three native passes with matching non-null outputs. Selected Div is explicitly unsupported before seeding while unselected Div is skipped and compiles correctly. All32 applicable common/manual/injective logical seed/input and annotation-normalized initialization comparisons match. These results establish a bounded dynamic validation/localization mechanism with an equally strong manual oracle; they do not show unique detector coverage or speedup.

Actual E1 pre-pass diagnostic invocations and four separately labeled old/E1 initialization-only replays establish MAX known versus fresh x=1 unknown. A fresh otherwise witness-free different-point unknown-query control is prepared but not executed. The independent six-case oracle is covered by synthetic input/context/cache/effect tests plus the actual Bril controls; precise designated counts and actual frontend inputs are retained.

The first focused attempt's sort/constructor namespace failure is retained and resolved in the frozen green source. Current fresh-per-invocation evidence paths are a known cost-integration blocker for a collector repeating static arm args. The [bounded follow-up proposal](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/observations/review-checkpoint/next-slice-proposal.md>) proposes atomic persistent compiler invocation children with normal/abort locators and explicit output cost, then exact two-rule source-corrected specificity controls, guaranteed byte-for-byte restoration and full final gates on restored source. No follow-up source change, corrected-source build, broad compiler gate or timing cohort has run. All owned compiler subprocesses are quiescent; the parent/harness owns the shared build slot.

## Fresh evidence lifecycle: reviewed Rust delta and first repeated CLI checkpoint

[Fresh checkpoint](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/observations/fresh-evidence-checkpoint/summary.md>) and its source/manifest bind the independently reviewed six-Rust-file evidence-lifecycle delta, frozen debug compiler221d6477ed5f54faba9bd0bc4b33f5489df9914f5529ffee97b3c15c3957a762 and unchanged sibling Tiger. All54 corresponding observation manifests and initialization byte strings equal development-v2, confirming that only the evidence lifecycle changed. The old static-root collision limitation remains documented for that old binary.

DAG10/root5 tests and the full37-command CLI matrix pass. Five pairs of byte-identical actual CLI argv create10 unique persistent children across three successful enabled modes and both MAX rejecting modes. Atomic invocation indexes/normal optional locator/complete stderr abort locator are retained; Off omits the locator and allocates nothing. Fifteen Python post-capture checks pass with13 altered/missing/stale/swapped/wrong-root/duplicate/partial negatives; all23 terminal enabled matrix trees were revalidated/archived using the separately frozen Python package. That package requires its own independent review, beyond the Rust source consent.

Two frozen old/E1 CLI algebra negatives now explicitly confirm the otherwise witness-free different-point mismatch leaves the Expr query unknown while both audits accept. These are separately labeled replay/algebra diagnostics, not full-host feasible-point runs. The source-corrected control driver is prepared but unexecuted; exact original interval/two-rule snapshots are saved and no optimization rule was changed. Final full gates/release/cost work remains pending. Owned compiler subprocesses are terminal; no timing cohort or native adapter ran. Normal successful collector post-capture has a normal-receipt locator/internal PID association, while the diagnostic driver additionally retains full stderr and independent Popen PID; no recursive archival/locator validation is attributed to the unchanged collector.


### Python2 evidence repair checkpoint (2026-10-17)

Repaired only the four Python observation helpers. Frozen source and full/narrow patches: `benchmarks/local/eggcc-encoding-impact/compiler/observations/fresh-evidence-python-2-final/`. Source manifest SHA-256 `91ba80abe47dbc3b8c4b83243c879b88b967b2247d1ff6a2797e0a760629e89f`; complete patch `c555042adc0a63d8b7f391d5dfdc466a4d4f9d6ee724faf19e00573984d491ca`. All 29 non-Python compiler checkpoint files and binary/Tiger/collector hashes remain unchanged. Python1, intermediate Python2 packages and failing required-file probe are retained.

Current evidence: 59/59 protocol checks; ten fresh repeated CLI invocations with five identical-argv/distinct-child pairs and successful first-capture revalidation after second-repeat overwrite; fixed four-mode MAX oracle is valid original red (Off/Common full3pass true→false; Manual/Injective exact witnessed pre-Tiger rejection). One authorized diagnostic-only nine-call collector smoke completed, passed the actual frozen verifier and independent-reference cross-arm output check, then the frozen helper post-step archived nine distinct normal receipts and six unique complete enabled children. Six later outputs are null/null linked to exact same-arm correctness rows. Successful collector PID/full stderr remain unavailable; diagnostic aborts retain actual PID/full stderr. No timings admitted as study costs. Exact argv/cwd/environment/status/hashes are in the raw receipts indexed by final `results.json` and explained in `summary.md`.

Independent final Python2 review remains pending. All owned processes are terminal; no rule mutation, Rust/collector edit, build, release endpoint or performance cohort was started. Await root routing for the corrected-source control and subsequent official gates; compatible cache/runtime-copy authorization is prospective.

## Release specificity, restored-source gates and final endpoint (2026-10-17)

[Final compiler summary](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/observations/corrected-control-1/summary.md>) and [machine receipt index](</Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/observations/corrected-control-1/final-summary.json>) bind the terminal sequence. Strict original release red4 preceded exactly two interval-rule-block deletions. The same fixed driver/helper/valid-input bytes then passed all four corrected MAX assertions and24 nearby controls. Original interval bytes were restored, and all788 source identities verified. Common observations/seeds and source schedules match across the variants; initialization differs exactly by the two blocks. The corrected endpoint is a diagnostic specificity control, not a generally fixed compiler or a full-gate-ready production change.

Official `make test` exits2 with13 pending snapshot differences; Rust reports36 library and2421 integration passes, two ignored doctests. Fresh current-E1 engine-only controls each select one exact trial and reproduce all13 actual snapshot bodies, with matching input/harness/stored-expectation identities. Official `make nits` exits2 on unchanged root `unnecessary_unwrap`; strict DAG lint reports two unchanged warnings. Fresh root/DAG baseline lint reproduces all three with matching owning source bytes. These concrete controls classify the failures; neither official gate is relabeled passing and no snapshots were accepted. The complete standalone DAG release suite passes74/74.

A newly exposed owned warning was repaired with the accepted one-line cfg(test)-only `std::slice::from_ref(&input)` borrow. Frozen narrow/full patches preserve pre-fix receipts. DAG10, complete DAG74, formatting and exact-baseline-allowance diagnostic lint pass after the repair; official nits still fails at the baseline warning. Root's earlier16-minute suite outcome is retained rather than repeated for this test-only edit, as explicitly authorized. Production Rust/.egg/fixtures and all four FINAL Python helpers remain unchanged. The pre-repair corrected-source package is immutable and its test-only difference from the final package is disclosed.

Final frozen uncorrected release eggcc SHA256 is `5d980389feec6270146db9a2cfe4e1775974102ab6c50cdf7bad029471907af1`, sibling Tiger `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`, full source manifest `5cddb863fa1a242fd028051400fb9a58c54ff33c876fe74a678e29fee020c6a3`, patch `db5eec0373d8a77a06356d3d064a17b449e83208baed3f416e463ea0970b66e6`. Executable bytes are identical to the accepted original release; the corrected diagnostic endpoint stays `f44edb3cb9c4b9660524335a29bea536571fe2ddbd1bcc68ba589decbd9bcc15`. The final release independently completes37 expected CLI outcomes and ten fixed-argv repeats with ten distinct persistent children and historical-receipt revalidation. MAX Off/Common intentionally retain the baseline true→false bug; Manual/Injective reject before Tiger. These are untimed correctness diagnostics, not cost evidence or unique logical power over the matched manual oracle.

Compatible cache/runtime reuse is recorded without mutating old artifacts. Initial fresh-control missing-Tiger setup failure, historical runtime linker failure, all official gate failures and provisional/failed hypotheses remain retained. The source package binds the complete authoritative five-file E1 patch, not the incomplete development engine diff. All owned compiler processes are terminal; final quiescence found no compiler process. An earlier unrelated Cargo invocation is retained in the reporting diagnostic and had ended by the final check; parent must recheck host activity before a cost window. No cost cohort, unrelated fix, snapshot acceptance, commit or push ran.
