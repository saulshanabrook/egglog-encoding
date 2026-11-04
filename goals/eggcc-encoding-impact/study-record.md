# EggCC injectivity and disequality impact study

**Completed research dossier; all fourteen accepted facts independently reviewed.** A valid-input selected-baseline EggCC miscompile is independently reproduced and detected by a restricted injective observation checker. The remaining-child query extension is implemented and validated. The actual source-corrected specificity control, final source/endpoint admission and fresh representative reproduction have independent review, retaining official compiler-gate failures. Complete repeated cost observations and regenerable figures are available under a bounded descriptive scope with a disclosed host-protocol deviation. No speedup is claimed.

## Confirmed results

| Result | Evidence and boundary |
| --- | --- |
| General remaining-child disequality queries | Independent review, finite-fragment oracle and full `make check` pass. This closes a defined reasoning gap without materializing derived disequality pairs. |
| Baseline wrapping multiplication miscompile | A minimized Bril input prints true; baseline optimized output prints false. All three native extraction passes finish successfully. Independently reproduced with three compiler artifacts and a nearby passing control. |
| Injective observation checker | Debug and final release matrices pass 37 asserted expectations each. Both direct manual and injective audits reject the same committed wrong merge before extraction; the common-seed/no-audit mode still miscompiles. The actual corrected-source control passes; final endpoint admission retains attributed official compiler-gate failures. This is selected-input bug detection. |
| Additional endpoint failures | Valid MAX≥MAX and MIN≤MIN source programs panic during optimization. Retained separately from the silent mismatch. |
| Existing-kernel alias screen | Guarded CSR/matrix runs complete, but final graphs provide no promising distinct-address write/load commute demand for the current domain. This does not exclude other alias opportunities. |
| Compiler speedup / runtime speedup | None established. Diagnostic run durations and graph counts are not performance claims. |

The [candidate map](candidate-map.md) records the investigated scope and remaining leads. We are pursuing a positive bug-detection endpoint, not claiming search exhaustion or that no faster encoding use case exists.

## Remaining-child reasoning

For the same constructor and all positions except i,

```text
f(a₀, …, aₙ₋₁) ≠ f(b₀, …, bₙ₋₁)
and aⱼ = bⱼ for every j ≠ i
imply aᵢ ≠ bᵢ.
```

This is the contrapositive of congruence and needs no injectivity annotation. For example, `f(a,b) ≠ f(c,d)` and `a = c` imply `b ≠ d`. With neither child equality, the conclusion is only `a ≠ c OR b ≠ d`; choosing one would be unsound. The reverse direction, known child difference implying different parent values, still needs the injectivity annotation, as does cancellation of equal parent values.

The implementation queries existing committed scalar-constructor rows. Output and focused child must be unionable equality sorts; siblings may also be native primitives, whose equality is checked directly. It does not support container reasoning, arbitrary function tables, primitive query operands, or term/proof-mode queries. Unknown is undefined, not evidence of equality. No absent application, graph row, union, persistent pair cache or derived-pair relation is created.

A per-query transient parent index and typed visited-pair search handle the finite witness graph. This may scan all eligible rows and form expensive parent cross-products; no performance benefit is asserted. It also does not simplify every logical disjunction: unequal `T(a,k,a)` and `T(b,k,b)` alone still leave `a != b` unknown in this fragment. There is no unrestricted completeness claim.

Queries do not execute injectivity unions. Consumers use the required `:naive` context and rerun after committed sibling equalities or parent witnesses change. `check-contradiction` closes its private normalization, not an arbitrary joint fixed point with injectivity and consumers. The tests cover an explicit bounded schedule order. See [encoding findings](findings/encoding.md) and [independent review](findings/encoding-review.md).

## Baseline bug and its attribution

The selected compiler base is EggCC `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`. A new source-derived Bril fixture branches on `0 < x`, then prints `x * 2 < 0` in the positive branch. At `x = 9223372036854775807`, wrapping i64 multiplication yields -2, so source execution prints true. The official [Bril core-language reference](https://capra.cs.cornell.edu/bril/lang/core.html) defines signed 64-bit integers and two's-complement overflow, matching the pinned interpreters (checked 2026-10-17). The optimized compiler output prints false. At x=1, both print false. The source has no division, shifts, memory operations or deliberately seeded egraph facts.

This failure occurs in frozen original-engine A, engine-only B, and the old prototype with its feature explicitly off. Each exits successfully and completes passes 0/1/2 through native Tiger extraction/reconstruction. A separate checker reproduced all three failures and their passing controls with fresh receipts. This establishes a genuine bug in the selected baseline; it does not establish that current upstream still has the bug or that the engine retarget caused it.

Two interval rules infer positive/nonnegative multiplication signs without an overflow precondition. A reduced exported pass-0 replay still miscompiles if only one rule is removed, and avoids the false equality when both are removed. The later actual release control deletes exactly those two rule blocks: the same fixed MAX oracle passes all four modes with source/result true through all three native passes. Nearby controls give 21 successful full-pipeline output matches and three expected selected-unsupported rejections before seeding. Full source hashes verify byte restoration afterward. [Independent evidence review](findings/corrected-control-evidence-review.md) verifies all 32 control invocations, exact source deltas and restoration; [final compiler admission](findings/compiler-final-gates-review.md) records terminal gates and their attributed failures. This diagnostic deletion is not a general interval-analysis repair. The CLI's `--ablate` did not exclude the rules in this configuration and is not used as a valid exclusion control. Exact inputs, artifacts, receipts, failed hypotheses and scope are in [compiler findings](findings/compiler.md) and the [independent reproduction review](../../benchmarks/local/eggcc-encoding-impact/independent-bug-reproduction/review.md).

## Restricted observation experiment

The [reviewed observation slice](observation-slice.md) records supported Boolean values at actually feasible contextual points. Its unmarked `EvalBoolAt(Expr, i64)` uses a fresh native-i64 observation-point token and returns an immutable `ObservedBool(bool)` wrapper of sort ObservationValue. Marking only that wrapper injective detects inconsistent values after an invalid Expr merge. A direct manual checker uses the same feasible points and an equivalent consistency condition. Neither Expr nor EvalBoolAt is marked injective; observations do not assert global Expr equalities/disequalities or runtime nonaliasing. The checker stores observation rows; the disequality query avoids a derived disequality-pair relation.

Collection preserves actual root/region inputs, types, contexts, selected paths and Rc-sharing behavior. A limited grammar and explicit unsupported coverage prevent arbitrary detached evaluation of effects. Independent [oracle cases](findings/observation-oracle-cases.md) distinguish wrong but same-type region inputs, nested dead arms, shared expressions under different inputs, unsupported dependencies and state carriers. Ten focused DAG tests and five actual-host tests pass; [independent implementation review](findings/observation-implementation-review.md) found no semantic blocker for this restricted source checkpoint. This is selected-input validation, not an all-input proof.

The first real CLI capture uses one frozen debug binary and native Tiger. Seven parse-mode source oracles, seven cases under four modes, and two separately toggled query diagnostics account for 37 invocations. On MAX, Off and common-seed/no-audit both complete with source true/optimized false. Manual and Injective both exit 101 at the named pre-serialization audit, with the same retained true/false conflict and no serialization-entry marker. The injective error specifically reports unequal primitive argument 0 in ObservedBool. On x=1, 0, -1, a contradictory dead arm and a dead unsupported arm, all four modes complete the normal three-pass pipeline with expected non-null outputs. A reached unsupported Div is rejected before emitting observation seeds in each enabled mode. These rejection classes are retained separately from successful compilations. See [matrix results](../../benchmarks/local/eggcc-encoding-impact/compiler/observations/development-v2/results.json).

The actual narrow source-corrected release now passes all four modes on MAX; Off and common-seed independently return true/true, so correction does not depend on checking. The unchanged driver/helper/input hashes bind original red and corrected green. See `corrected-control-1/control-result.json` in the raw evidence and its [independent review](findings/corrected-control-evidence-review.md). The fresh-invocation mechanism is now implemented and independently reviewed: ten repeated CLI calls with five identical-argument pairs create ten distinct persistent children, and the complete matrix preserves its observations and results. [Independent fresh-evidence audit](findings/observation-fresh-evidence-review.md) also confirms configuration reuse and Off omission. The Python archive/control helpers now have [independent final source and empirical consent](findings/observation-python2-final-review.md): 59 focused checks, ten final-source repeats, a strict four-mode original red, and one real nine-call collector smoke pass. The smoke checks exact reference outputs, later null interpreter fields, per-row retained receipts and six complete enabled evidence trees. Its debug timings are excluded from performance results. The earlier [five repair findings](findings/observation-python-review.md) and stale intermediate review remain retained.

### What the new query adds

At the actual MAX point p, the initialized graph contains observations of the reached comparison e and its same-context false literal. Their native Boolean payloads differ:

```text
ObservedBool(true) ≠ ObservedBool(false)              [injective wrapper, native Bool difference]
EvalBoolAt(e,p) ≠ EvalBoolAt(false_literal,p)          [the seeded observation-result equalities]
e ≠ false_literal                                   [reverse congruence, equal point sibling p]
```

These are the mathematical witness steps followed by the read-only query; no Expr disequality assertion or derived-pair relation is inserted. On byte-identical exported initialization/query files, old unary-only queries are unknown for MAX and E1 succeeds. A fresh x=1 initialization is unknown on both. [Replay results](../../benchmarks/local/eggcc-encoding-impact/compiler/observations/initialized-replay/results.json) bind exact inputs and binaries, and the old MAX stderr specifically reports the known-disequal check failure after initialization. This is an initialization-only query contrast, complemented by the actual new-host pre-schedule diagnostic; there is no full old-query compiler endpoint here. An otherwise witness-free different-point algebra graph is unknown on both engines and accepted by both audits. Its negative assertions are fail-wrapped, so those complete fixtures exit 0; they are separate from the standalone check-failure replays.

The later injective consistency rejection uses the existing wrapper-cancellation feature; E1 adds this earlier Expr-inequivalence query. An observation at one feasible input can witness that two contextual expressions differ, but does not establish different runtime values at every input. A graph retaining the MAX counterexample may still witness Expr inequivalence even when another input agrees. Query probes are disabled in cost cohorts.

## Repeated descriptive cost observations

These are **absolute observations on two new minimized fixtures**, not a controlled-host performance experiment. Original `block-05` and corrected `block-03` each contain three interpreted correctness calls, three warmups and 36 measurements: 12 per Off/Manual/Injective arm in balanced rotating order. The complete source/result references are false/false and true/true respectively. Collector verification and frozen-helper archival pass for both; no prior row, warmup or correctness anchor is reused.

The user explicitly removed memory-pressure blocking. The **entire optional memory guard was uniformly disabled** using `/usr/bin/env -u EGGLOG_BENCH_MEMORY_GUARD`; the 300-second timeout, compiler wall boundary and normalized wait4 RSS measurement remain. This supersedes the historical guarded protocol, not compiler source or any mode's semantics.

Both windows have full before, two actual five-second during, and immediate after inventories. They retain normal desktop/UI activity and a coincident low-sampled-CPU `gh release create` artifact-upload process. Its disk/network I/O rate was not measured; low CPU does not establish inactivity or harmlessness. The original prelaunch attribution omitted that process, so **strict clean-host consent remains withheld**. The [host review](findings/cost-final-host-review.md) is not reversed. Before opening these distributions, [method review](findings/cost-descriptive-scope-review.md), [goal-scope review](findings/cost-descriptive-goal-review.md) and the [bound resolution](../../benchmarks/local/eggcc-encoding-impact/observations-cost/descriptive-observations-resolution.json) admitted only descriptive reporting with this protocol deviation. No build/test/collector waiver is inferred.

Use the following captions with both figures: interactive host with coincident artifact-upload process and unmeasured I/O; optional guard disabled; twelve observed total costs per arm. Open circles show every measurement, the black tick is the median, and the line is min–max. SD is sample standard deviation, not a confidence interval. RSS is wait4 child rusage, not simultaneous process-group or combined-live EggCC+Tiger peak. No generated-program runtime was measured. Do not pool the two source variants or infer causal feature/component cost, speedup, significance or production benefit from these values.

### Original rules, x=1

| Case | Arm | n | Compiler wall s: median [min, max]; SD | wait4 peak MiB: median [min, max]; SD |
| --- | --- | ---: | ---: | ---: |
| original-one | Off | 12 | 0.1537 [0.1526, 0.16]; 0.002668 | 42.48 [42.34, 43.34]; 0.2659 |
| original-one | Manual | 12 | 0.2912 [0.2837, 0.2945]; 0.002859 | 43.33 [43.06, 43.67]; 0.1814 |
| original-one | Injective | 12 | 0.2885 [0.2835, 0.3028]; 0.005375 | 43.38 [43.14, 44.23]; 0.3446 |

[SVG figure](../../benchmarks/local/eggcc-encoding-impact/observations-cost/original-one/block-05/figures/original-one.svg), [PDF figure](../../benchmarks/local/eggcc-encoding-impact/observations-cost/original-one/block-05/figures/original-one.pdf), [all raw values and statistics](../../benchmarks/local/eggcc-encoding-impact/observations-cost/original-one/block-05/figures/figure-data.json).

### Two-rule diagnostic control, MAX

| Case | Arm | n | Compiler wall s: median [min, max]; SD | wait4 peak MiB: median [min, max]; SD |
| --- | --- | ---: | ---: | ---: |
| corrected-max | Off | 12 | 0.1533 [0.1523, 0.1661]; 0.003939 | 42.52 [42.38, 42.88]; 0.1577 |
| corrected-max | Manual | 12 | 0.2889 [0.2849, 0.3061]; 0.007349 | 43.3 [43.12, 43.67]; 0.1755 |
| corrected-max | Injective | 12 | 0.2878 [0.2839, 0.2962]; 0.003576 | 43.38 [43.19, 43.86]; 0.2172 |

[SVG figure](../../benchmarks/local/eggcc-encoding-impact/observations-cost/corrected-max/block-03/figures/corrected-max.svg), [PDF figure](../../benchmarks/local/eggcc-encoding-impact/observations-cost/corrected-max/block-03/figures/corrected-max.pdf), [all raw values and statistics](../../benchmarks/local/eggcc-encoding-impact/observations-cost/corrected-max/block-03/figures/figure-data.json).

Primary and independently regenerated JSON, Markdown, SVG and PDF files match byte-for-byte for each case; their PDF renders match too. Both figures were visually inspected for readable labels, units, all observations and unclipped layout. [Regeneration/render evidence](../../benchmarks/local/eggcc-encoding-impact/observations-cost/figures-qa/regeneration-and-render.json) and [visual inspection](../../benchmarks/local/eggcc-encoding-impact/observations-cost/figures-qa/visual-inspection.json) retain the checks.

Earlier host-invalid cohorts stay excluded. The strict-pressure refusal and invalid-value-0 setup failure occurred before EggCC Popen and remain recorded. Original04/corrected02 succeeded technically but were excluded before statistics for unresolved work/tar interference; their [diagnostic-only statistics](findings/diagnostic-cost-observations.md) are separate and are never pooled here.

## Validation and limitations

The five-file E1 checkpoint passes 33 focused integration tests, seven file tests, both ordinary CLI encodings, and an independent least-fixed-point oracle over 64 fixed graphs and 16,192 pair queries. Its [full gate](../../benchmarks/local/eggcc-encoding-impact/encoding/full-check/final-summary.json) passed 233 Python tests/two snapshots and 1,804 Rust tests with zero failures and six ignored. An earlier actual disk-full attempt is retained; the successful retry used unchanged source.

The subsequent guarded harness port passes independent review, focused plotting/protocol tests, a [combined full gate and public smoke](../../benchmarks/local/eggcc-encoding-impact/harness-final-gate/final-summary.json). Combined `make check` passes 290 Python tests/two snapshots, one optional plotting skip, and the same 1,804 Rust tests with six ignored. The skipped plotting path passed separately in the pinned environment. Public smoke has four successful rows. An initial combined-gate fixture-timeout failure and its narrowly reviewed test-only repair are retained; production collector/guard/encoding code did not change. None of these smoke durations are study measurements.

The [final compiler checkpoint](../../benchmarks/local/eggcc-encoding-impact/compiler/observations/corrected-control-1/summary.md) preserves the official gate failures: `make test` exits 2 for 13 pending snapshot differences, with 36 library and 2,421 integration runtime assertions passing and two doctests ignored. A fresh engine-only control using the same current E1 dependencies reproduces every actual snapshot body with one selected trial each. Official `make nits` exits 2 at an unchanged root lint; strict standalone DAG lint finds two further unchanged warnings. Fresh source controls reproduce all three. These are attributed limitations, not passing official gates. No snapshot was accepted.

One new test-only clone lint was fixed with `std::slice::from_ref(&input)`. The affected complete DAG suite passes 74 tests after the repair, focused DAG10/root5 and formatting pass, and diagnostic lint commands pass with only the confirmed baseline lint names allowed. The full root suite was not repeated for this cfg(test)-only change; all production inputs and the rebuilt release binary are byte-identical. The corrected diagnostic endpoint retains its earlier source inventory, explicitly differing by the two rule deletions and this inactive test borrow. Its whole-suite readiness is not claimed. The final original release matrix has all 37 expected outcomes and ten same-argument repeats with distinct evidence children.

Independent [final compiler admission](findings/compiler-final-gates-review.md) and [concrete cost binding review](findings/cost-binding-review.md) consent to the frozen endpoints and declared controls. The historical block01 host failure, all refused/configuration attempts and subsequent interference exclusions remain retained. The final descriptive pair is bound by [replacement review](findings/cost-final-replacement-binding.md), the user memory amendment and the pre-numeric scope resolution above. Successful receipt checks are not substituted for strict clean-host consent.

The [fresh final representative reproduction](findings/fresh-final-reproduction-review.md) independently completes original x=1 and corrected MAX with Injective, producing exact source/result false/false and true/true. Both finish all three native passes with nonzero accepted observations, fresh PID-bound evidence trees and matching before/after endpoint/input/source hashes. These two calls are correctness evidence, excluded from costs.

The [independent numeric and figure review](findings/cost-final-numeric-review.md) verifies all 84 calls, twelve raw measurements per arm, exact references and evidence links, summary arithmetic, source bindings and byte-identical regeneration. The completed noncost evidence and rerun instructions retain [independent consent](findings/final-noncost-dossier-review.md). The [final independent fourteen-fact review](findings/final-dossier-review.md) consents to completion; [the audit](completion-audit.json) maps every accepted fact to its evidence. Expected detector aborts remain separate from successful compilations. No native runtime study is claimed.

Existing author changes, six prior checkouts and the previous study's 1,536 frozen artifacts are covered by the [initial preservation checkpoint](../../benchmarks/local/eggcc-encoding-impact/preservation/initial.json.gz). The after-cost [strict audit](../../benchmarks/local/eggcc-encoding-impact/preservation/verification-after-cost-strict.json) reports changes: eleven unattributed `.DS_Store` additions/changes in two old checkouts. The [classified audit](../../benchmarks/local/eggcc-encoding-impact/preservation/verification-after-cost-review.json) finds no unexpected substantive source/status, branch/HEAD or frozen-evidence drift. The strict failure is retained; no metadata was deleted, restored or adopted into the baseline. New implementation lives only in dedicated encoding/compiler worktrees. No paper edits, proof support, Lean work, commits or pushes are part of this execution.
