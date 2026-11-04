## Verdict and answers

**Verdict.** The report tells a true story but asks the reader to take its central link on faith. The bug section speaks in Bril names, the checker section speaks in `e`, `z`, `p`, and nothing in between shows that the checker's `false` literal is the very e-node the interval rule unions with. The chronology is also inverted in the reader's mind: the text reads as if the encoding found the bug, when the project's own record shows differential testing found it, manual graph inspection and replay filtering localized it, and the checker was built afterward to catch it. Fix those two things, demote the disequality query to a clearly separate coda, and move measurement and gate ledgers out of the explanation, and this becomes a usable half-page case study. It is not, and should not be presented as, an evaluation of the encoding's reasoning power.

Everything marked **Verified** below was read directly from the cited source. Everything else is my editorial judgment.

**Q1. Is the same program and Expr connected clearly?** No. The connection is asserted at report.md:5-13 and tabulated at report.md:90-93, but never shown. Three steps are missing for an egglog reader:

- **The EggCC representation of the branch.** Inside the taken branch, `x`, `two` and `zero` are projections of one region argument carrying the context `InIf true pred inputs`, and every constant carries a type and a context. The report never says this, so "same-context Boolean constant" at report.md:74 is opaque. **Verified:** the branch-bound rule sets bounds on `(Get ctx i)` where ctx is `(Arg ty (InIf true pred inputs))` at interval-original.egg:328-342, and the union rule produces `(Const (Bool false) ty ctx)` using `HasArgType` and `ContextOf` at interval-original.egg:78-85.
- **That `z` is constructed to be that exact e-node.** **Verified:** the collector builds `Const(Bool v, point.input_type, point.context)` at observations.rs:666-670. If the type or context differed, the optimizer's union would hit a different `Const` node and no congruence would reach the observations. This is the single fact that makes the harness work, and the report states it only as "constructs a Boolean-literal Expr in the same context" at report.md:88.
- **One concrete witness from the real run.** The retained conflict names the product-comparison seed and the branch's false literal at one point, with region input `[StateV, 0, MAX, 2]`. **Verified** in corrected-control-evidence-review.md:34. Quoting it once would anchor "same run".

**Q2. What is the contribution, and what is merely established?** Established, in order of weight:

1. A real silent miscompile in the selected baseline, found by differential testing of valid Bril inputs across three frozen compiler artifacts. **Verified** in compiler.md:19-27 and 51-55.
2. Localization to two multiplication sign rules, by graph witnesses plus pass-0 replay filtering, then confirmed by a release built with exactly those two blocks deleted. **Verified** in compiler.md:65-66 and corrected-control-evidence-review.md:7 and 22-28.
3. An opt-in harness that seeds concrete evaluations into the e-graph as facts and audits them after the schedule, detecting this merge in two logically equivalent forms. **Verified** at observations.rs:560-590 and lib.rs:1046-1057.
4. The remaining-child disequality query, implemented and tested, which finds a witness on the initialized MAX graph where the base engine's query does not. **Verified** at disequality.rs:304-312 and 384-408 and in initialized-replay/results.json exit codes.

Only a prototype or a trick: the observer grammar is `Mul`, `LessThan`, `And`, `Or`, `Not`, constants, argument projections and selected-arm `If`, on one function with no loops, calls or memory. **Verified** at observations.rs:438-534. The two-rule deletion is a diagnostic, not a repair. Measurements are descriptive only.

**On the ObservedBool case.** Its merit is that it is the minimal sound use of `:injective`: an immutable wrapper around a primitive, where the generated rule is exactly the conflict rule a developer would hand-write. **Verified:** the generated panic rule at injectivity.rs:264-275 and the hand-written rule at observations.rs:574-579 check the same join. Its limits are equally plain. All semantic work is done by the concrete evaluator and by congruence. The annotation exercises only the primitive-mismatch rule, never equality-sort cancellation, which is where injectivity is interesting. State it as: a case study showing the annotation serving as a reusable consistency contract that catches a real miscompile the compiler's own guard cannot see, with the caveat, stated first, that an equivalent two-line rule over the same observations detects the same conflict. The more general idea worth naming is the harness itself: ground-truth facts seeded into the graph that any later unsound union contradicts through congruence. Injectivity is one way to write the contract.

**Q3. What did the encoding actually do?** Detection only, after the fact, on one input.

- Discovery: differential testing, before any encoding work. **Verified** in compiler.md:19-27; the observer was proposed afterward as "proposal only" at compiler.md:90-92.
- Arithmetic semantics: supplied by the harness's restricted evaluator using `wrapping_mul`, cross-checked against the EggCC interpreter on the same pure fragment. **Verified** at observations.rs:456 and 539-547. Not by the encoding.
- Localization: manual graph inspection and replay filtering. **Verified** in compiler.md:55 and 65-66. Not by the encoding.
- Blocking the union: no. The audit runs after the full source schedule and aborts before serialization. **Verified** at lib.rs:1052-1060 and observations.rs:799-828.
- Fixing a rule: no. Both blocks were deleted with no replacement and no overflow guard. **Verified** at interval-corrected-expected.egg, where neither block appears, and reference.md:137.
- Overflow-safe repair: unimplemented. The report says so at report.md:185. Keep that sentence.

The report's own early assessment at compiler.md:75 says "No incremental encoding value is established" and warns against annotating merely to obtain a detector. The final report should be at least that candid about what injectivity contributed.

**Q4. Are both required? Which catches the bug?** Only one is required. Injective cancellation, or equivalently the manual relation rule, catches the bug after the schedule. The remaining-child query runs before the schedule, is disabled in cost arms, and is emitted only for a `LessThan` whose left child is a `Mul`. **Verified** at observations.rs:686-696 and 739-766. What it establishes on this graph is that the two expressions differ, which the collector already knew from evaluating them. Its value is that the query reaches that fact through an unmarked binary constructor on a real exported graph, where the base engine's unary-only query cannot. **Verified:** old-unary MAX exit 1, E1 MAX exit 0, both x=1 exit 1, in initialized-replay/results.json. That is an engine demonstration, not a bug-finding step. The section at report.md:148-179 is longer than the detection section and sits between detection and the control, splitting the story. Move it to the end, cut it to about ten lines, and drop "disequality" from the title.

**Q5. Did the baseline already detect conflicting constants?** Partly, and not here. Note the guard is not in `schema.egg`. **Verified:** the only baseline constant-conflict guard is at type_analysis.egg:41-45, which panics when two `Const` nodes with different values share a class and the first has context `(InFunc name)`. It is scheduled in the `error-checking` ruleset at schedule.rs:20-31. It misses this bug for two independent reasons. The merged class never contains a `Const (Bool true)` node, because the optimizer never derives `true` for the comparison. And the context is `InIf`, not `InFunc`. The Manual checker is new. **Verified:** `ObservationSeed`, `ObservationConflict`, the witness rule and the manual panic rule are all declared by the harness at observations.rs:571-579. What extends coverage is the observation seeding: it injects a truth the optimizer cannot derive and attaches it to the class through `EvalBoolAt`. That extension belongs to the harness, not to injectivity. Say exactly this in one paragraph at report.md:144.

**Q6. Are rules and before/after behavior explicit enough?** The literal rule blocks in reference.md:101-123 and the two configuration tables are good. **Verified:** the blocks match interval-original.egg:159-168 and 192-201, and the derivation chain at report.md:67-72 matches rules at lines 328-342, 159-168, 213-219 and 78-85, with `bool-< 1 0` and `bool-< 0 0` both false, so the nonnegative rule independently suffices. Gaps:

- What is seeded: the report shows two unions at report.md:116-117, but the harness also seeds a `true` literal at each point and the root-level observations, and emits `ObservationSeed` rows that the witness rule joins on. **Verified** at observations.rs:665-685. Say "among the seeds".
- Which union happens: show the actual union rule, since it is one line.
- Where the panic happens: correct at report.md:142. Add that all enabled modes first materialize conflict witness rows, then run the mode's audit. **Verified** at observations.rs:800-825.
- Why same context and same point matter: not explained where it is needed. The point-equality argument appears only at report.md:173, inside the disequality section.
- Multiple passes: the reader does not know EggCC runs three passes with fresh graphs, that the observer re-collects per pass, and that the MAX abort is in pass 0. **Verified** in corrected-control-evidence-review.md:25.

## Ranked revisions

1. **Opening paragraph, report.md:3 and :15.** Replace with the sample paragraph below. It must state that the bug was found by differential testing, that the checker was built afterward, that it detects and does not fix, and that a hand rule detects the same thing.
2. **Introduce `e` and `z` in the bug section, report.md:58-84.** After the derivation chain, add: "Call the comparison inside the branch e, and the branch's false constant z. The last rule is literally `(union e z)`." Then the checker section reuses names already defined. Add one sentence on EggCC's region-argument representation and that constants carry type and context.
3. **State why exact type, context and point are load-bearing, report.md:95-102 and :120.** Add: "The checker builds z with the branch's own argument type and context, so it is the same e-node the interval rule introduces. Both observations use the same point token, so the two `EvalBoolAt` nodes become congruent once e and z are merged. Observations at different points, or a literal in a different context, would never connect." Move the point-equality remark from report.md:173 here.
4. **Name the baseline guard and the Manual checker's origin, report.md:144.** Replace "The comparison includes a direct manual checker" with the paragraph from Q5: cite type_analysis.egg:41-45, give the two reasons it misses, and say Manual is a two-rule check added in the same harness.
5. **Demote the disequality query, report.md:1, :25, :148-179.** Retitle to something like "Detecting an EggCC miscompile with an injective observation wrapper". Move the section after the rule-removal section, cut to about ten lines, keep the three-step derivation and the replay result, and say plainly that it restates a fact the collector already knew. Put the general law and fragment limits in reference only.
6. **Collapse the measurement and gate ledgers, report.md:197-210 and :218.** Keep one sentence: wall time roughly doubled with the observer on these tiny programs, no speedup or component attribution is claimed. Move the caption, protocol deviation and gate counts to study-record.md, which already has them. Diataxis explanation should connect mechanism and why; protocol text is record material.
7. **Say the probe is selector-targeted, report.md:177.** Add "emitted only for the reached product comparison" with the citation to observations.rs:686-696.
8. **Add the pass structure, report.md:84 and :142.** One sentence: three passes, fresh graph each, observer re-collects per pass, MAX abort in pass 0.
9. **Trim explanation leaking into reference, reference.md:16 and :127-135.** Keep the line-number table and literal blocks. Drop "Remaining-child disequality is congruence's contrapositive" and the route narrative, which duplicate the report. Duplication across report, reference and study record is a likely cause of the "successive revisions" confusion: each restates the same caveats in slightly different words.
10. **Mention the interpreter cross-check, report.md:120.** One clause: the restricted evaluator supplies the value and the EggCC interpreter is run on the same pure fragment as an agreement check.
11. **Contribution section, report.md:214.** Replace "connects a real compiler mistake to a small valid injectivity contract" with the merit-and-limits sentence from Q2, manual equivalence first.

## Proposed outline, sample text, and open checks

**Outline for the explanation**, about one page:

1. What happened and how it was found. Program, input, wrong output, differential test, three artifacts.
2. Why the optimizer believes it. EggCC branch representation in two sentences, the four-rule chain, the two overflow-blind rules, the literal union rule, define `e` and `z`.
3. The harness. Evaluate on the real input, seed `EvalBoolAt` facts about an injective `ObservedBool` wrapper, same type, context and point as the optimizer's own nodes. One connected egglog example.
4. What the audit does and does not do. Congruence after the bad union, generated panic rule, abort before extraction, pass 0. Equivalent hand rule. Why the baseline guard misses.
5. Confirming the localization. Two-rule deletion, four modes, nearby controls, no repair.
6. Scope. One program, tiny grammar, no speedup, selected baseline only.
7. Coda. The remaining-child query on the same graph, ten lines.

**Sample opening paragraph:**

> EggCC's interval analysis at the selected baseline miscompiles a four-instruction Bril program. At the input `x = 2^63 − 1`, the taken branch computes `(x * 2) < 0` as `true` under Bril's wrapping arithmetic, but the optimizer rewrites it to the constant `false` and all three passes complete. We found the bug by differential testing of valid inputs, traced it to two multiplication sign rules that ignore signed overflow, and confirmed the localization by deleting exactly those rules. We then built an opt-in checker that evaluates a few branch expressions on the actual input and seeds the results into the optimizer's e-graph as facts about an immutable, injective `ObservedBool` wrapper. After the schedule, the optimizer's wrong union makes congruence equate the wrappers for `true` and `false`, and the rule generated from the annotation aborts compilation before extraction. The compiler's own constant-conflict guard cannot see this merge: it checks only top-level constants, and the optimizer never derives a conflicting constant here. A two-line hand-written rule over the same observations detects the same conflict, so the annotation's merit is that it states this contract declaratively, not that it detects more. A separate remaining-child disequality query is also exercised on this graph; it is not part of the detection.

**One connected example.** Schematic: names are shortened and the real terms are in the retained pass-00 `observations.json`. The region-input order comes from the control review.

```lisp
; Inside the taken branch, EggCC represents variables as projections of one region Arg.
; Region input at MAX: [StateV, 0, MAX, 2], so index 1 is zero, 2 is x, 3 is two.
(let ctx     (InIf true pred inputs))                 ; the positive branch
(let arg     (Arg ty ctx))
(let product (Bop (Mul) (Get arg 2) (Get arg 3)))     ; x * 2
(let e       (Bop (LessThan) product (Get arg 1)))    ; product < 0, assigned to `answer`
(let z       (Const (Bool false) ty ctx))             ; the branch's own false constant

; Harness, before the schedule: ground truth from executing the program at x = MAX.
; Token 1 identifies this branch at this input; it is an identity, not the value MAX.
(union (EvalBoolAt e 1) (ObservedBool true))
(union (EvalBoolAt z 1) (ObservedBool false))

; Optimizer, during the schedule (interval_analysis.egg 328-342, 159-168, 213-219, 78-85):
;   lo-bound (Get arg 2) = 1        because 0 < x held in this branch
;   lo-bound product     = 1        positive * positive, no overflow check: the unsound step
;   hi-bound e           = false    bool-< 1 0
;   (union e (Const (Bool false) ty ctx))     which is (union e z): same type, same context

; Rebuilding: e = z, so (EvalBoolAt e 1) = (EvalBoolAt z 1),
; so (ObservedBool true) = (ObservedBool false).

; Harness, after the schedule:
(run-schedule (saturate injectivity))
; Generated rule for the :injective ObservedBool panics with
; "injectivity violation in constructor `ObservedBool`: unequal primitive argument 0".
; Manual mode instead joins ObservationSeed rows on the merged e and panics on the conflict.
```

**Factual uncertainty for the parent to check:**

- I inferred from the seeding loop at observations.rs:657-685 that seed 2 is the false literal at the branch point and seed 5 is the product comparison, consistent with the retained row quoted in corrected-control-evidence-review.md:34. I did not open the pass-00 `observations.json`.
- I inferred that the root-level `0 < x` comparison is also observed at the root point from the grammar, not from evidence.
- The projection indices in the example follow the region-input order quoted in the control review. Confirm against the retained seed terms before publishing.
- The "unary-only" characterization of the base-commit binary comes from the project's own labels in the replay results and the disequality.rs doc; I did not inspect the base commit's query code.
- I did not read `rerun.md`, `candidate-map.md` or the Python review the report links at report.md:146.

**Sources consulted:** report.md, reference.md, study-record.md, findings/compiler.md, findings/observation-implementation-review.md, findings/corrected-control-evidence-review.md, findings/documentation-explanation-review.md, findings/report-semantic-claims-review.md, observations.rs and lib.rs in the EggCC worktree, interval-original.egg, interval-corrected-expected.egg, type_analysis.egg and schedule.rs in the frozen baseline source, mul-minimal-max.bril, the emitted optimized.bril, graph-witnesses.json, initialized-replay/results.json, injectivity.rs and disequality.rs in the encoding worktree, and the Diataxis explanation and reference pages.
