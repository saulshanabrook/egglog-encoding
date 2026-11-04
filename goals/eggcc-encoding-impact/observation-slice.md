# Restricted concrete-observation slice

Decision proposal following C1's independently reproduced baseline bug and C2's no-hit screen. The accepted goal/facts/plan remain unchanged. This is a bounded full-host diagnostic case study, with a separately labeled E1 query-coverage probe. It is not an optimizer speedup, an all-input verification claim, or unique logical power beyond a direct manual oracle.

## Aim and authority

Compiler owner: study_retarget, new `/Users/saul/p/wt/eggcc/encoding-impact` source only. Own DAG observation/config/build/audit integration, narrowly required CLI/argument plumbing and meaningful tests/fixtures. Root owns source selection, preservation, shared build slot, synthesis and final gates. Encoding owner has conditionally consented to the law and feasible-point boundary in [review](findings/observation-proposal-review.md). Measurement owner reviews the comparison contract before implementation.

Preserve the completed arithmetic/C2 raw checkpoints and the E1 five-file patch. Use new raw `compiler/observations/` and source patches for the next slice. Retarget **both** compiler Cargo graphs to the new E1 worktree using the existing engine-only adaptation; do not import the old local-address feature. Capture actual resolved metadata, source patches and new compiler/Tiger identities. No build begins until the current E1 make check releases the slot. Source implementation may proceed once the comparison review has no concrete blocker.

## Invariant and first implementation boundary

For one actually feasible contextual point p and supported Bool expression e, deterministic evaluation supplies `eval(e,p)`. Equal eligible Expr values must agree at that same point. Represent this with unmarked `EvalBoolAt(Expr, ObservationPoint) -> ObservedBool` and immutable `ObservedBool(bool)`, marked injective only for the encoding checker. Do not mark EvalBoolAt or Expr injective; do not assert Expr equality/disequality or infer runtime nonalias.

Begin with the minimized single-function multiplication example. A positive supported grammar may include its required constants, typed args/projections/tuples, wrapping multiplication, signed less-than, boolean values and selected If transitions. Exclude calls, loops, memory, floats, division/shifts and partial/unsupported operations. Generic ExprIsPure is insufficient. Establish the actual selected path, exact region input, type and context before detached pure evaluation; effects/state plumbing must not be replayed. Respect Rc sharing and scope transitions. Unsupported input/grammar/type/context must be rejected or explicitly counted as skipped coverage before facts are seeded.

Print observed Exprs and matching Bool literals through the same contextual pre-pass TreeToEgglog/cache as the optimizer. Tokens are opaque primitive/unionable scalars, distinct across actual inputs/regions/contexts/passes; archive their external identity/type/input record. Recreate observations for each actual pre-pass tree, never carry IDs from a prior reconstructed graph. Seed only observation result unions, not global semantic Expr facts. Audit committed state after each actual source schedule and before serialization/Tiger. Retain an explicit conflict witness and pre-audit receipt even when the command aborts without normal run-data output.

## Modes and controls

- **Off:** unchanged pipeline, no observation collection/seeding/checking; still reproduces the baseline wrong output.
- **Common seed/no audit:** identical supported observations/literals, no consistency audit; must show the same wrong merge and no earlier existing-Const-guard failure. This can be a correctness checkpoint rather than another timed arm.
- **Manual:** same observation collection, literal construction, initialization footprint and audit boundary; directly reject different primitive bools for the same committed Expr and exact point. Keep ObservedBool unmarked and do not schedule its cancellation. Archive the actual conflicting pair.
- **Injective:** same common observation contract, with the literal wrapper's annotation/audit supplying the consistency rejection. Explain any representation/metadata difference from Manual rather than calling unequal graph inputs identical.

The common seeded graph must be shown to preserve the original bug trigger. Added literal Expr nodes could affect optimization independently of checking. No claim of incremental detector coverage until the full-host common-seed receipt establishes that the existing top-level Const guard does not already catch it.

Add a read-only **pre-schedule** E1 probe using the same observation setup: a reached comparison and matching false literal at MAX have unequal observed results at a common point, so the new unmarked binary reverse query can witness their Expr inequivalence. Validate the identical seeded program with old unary-only and E1 query engines. An exported-initialization replay is acceptable for the old/new query contrast if clearly labeled; it is not a full old-query compiler endpoint. The real new-host probe still needs actual CLI/pass/path evidence. Fresh x=1-only and otherwise witness-free distinct-point graphs remain unknown. A MAX counterexample retained in the same graph can legitimately prove Expr inequivalence even when another input agrees; never describe this as per-input runtime inequality.

## Required decisive checks

1. Baseline Off remains source true / optimized false on MAX. Both valid checkers reject the same invalid branch-local class merge before Tiger. Source expectations come from the valid wrapping contract and independent oracle, not injected false axioms.
2. x=1 succeeds through all three passes with non-null matching output. x=0/-1 and a syntactically dead/contradictory arm record zero observations for the unreachable arm, then succeed; absence of a panic alone is insufficient.
3. Distinct points/inputs may give different observed values for the same Expr without rejection. Wrong type/region input/context/token records and unsupported grammar are rejected/skipped explicitly. Equal observed values cannot cancel to merge Exprs or point identities.
4. Inspect initialization for observation-only unions and no Expr disequality assertions. Retain point/type/context identities and supported/skipped counts per pass.
5. A narrowly source-corrected real compiler treatment (the diagnosed two sign rules removed or properly guarded) passes both checkers on MAX and produces true through the actual pipeline. A filtered replay alone is insufficient. Label this as a scoped correction, not a proof that all integer rules are sound.
6. Query-coverage positives/negatives obey the pre-pass order and point contract above; unknown is normal, not equality or an observer error. Ordinary-mode/naive restrictions remain explicit.
7. Run meaningful focused host/CLI tests and required final EggCC root/DAG gates; classify unchanged snapshot/lint limits with matched controls, without accepting unrelated snapshots or fixing unrelated code.

## Costs and stopping checkpoint

After correctness, measure successful controls/workloads with repeated matched release invocations. Compiler observation collection, added graph state, manual audit and injective audit are separate boundaries/ablations; retain total compilation time and defined RSS. Failing bug-detection runs may report separately labeled time-to-detection diagnostics, never a speedup over successful full compilation. Timed blocks have no concurrent builds/tests/collectors; keep all raw rows, variability and an independent confirmation only if an actual benefit is claimed. Native runtime measurement is not required for this diagnostic case and no native adapter is authorized here.

Stop the slice for independent review once the real-host positive/negative matrix, common-seed existing-guard control, source-corrected specificity control, pre-pass E1 contrast, source checkpoints and full gate outcomes are concrete. Reassess rather than broaden silently if feasibility requires a general execution tracer, user-supplied arbitrary semantic facts, invalid contextual cancellation, global Expr disequalities or unsupported state/call/loop semantics. Completing this slice still requires the overall dossier, reproducible results/figures, preservation and fact-by-fact completion audit before goal completion.

## Binding review conditions and implementation decision

The compiler owner, semantic owner and comparison reviewer conditionally consented. Their material conditions are accepted and bind implementation:

- Structural traversal may pass through Function/Print/state-value carriers to reach supported pure values; never detached-evaluate effects. Root input state must match host interpretation. Explicit type/context/region checks precede the interpreter helper.
- Separate initialization, source schedule and audit so a failing audit leaves complete pre-audit/conflict evidence. Shared witness-finding work is either common across modes or reported as a representation/cost difference.
- The E1 pre-pass probe requires injective literal metadata and runs in a **separate diagnostic invocation/toggle disabled in detector-cost cohorts**. Manual's unmarked wrapper need not produce that query witness. Match old/E1 initialized replay bytes and flags exactly; label replay versus real-host evidence.
- If common-seed/no-audit is untimed, Off-to-checker costs describe the whole package, not separately measured collection/audit components. Record logical seed identities and actual annotation/graph differences. Separate component claims require actual phase intervals or a timed common-seed arm.
- The source-corrected MAX control must also succeed with Off and common-seed/no-audit, proving the narrow correction works independently of observations. Use a real source correction, never the ineffective CLI ablation.
- Successful cost rows require exit0, non-null matching outputs, full passes/extraction/reconstruction. Expected detector aborts remain a separate evidence class with named observer stage, exact feasible point, true/false payloads and no later Tiger entry. An earlier guard failure or malformed/unsupported observation is not a successful detector.
- Declare timed arms before sampling and balance them: if Off/Manual/Injective only, use complete three-arm rotations (for example12 observations each), not an inherited ten-round default. No claimed speedup means no independent speedup-confirmation cohort is required; raw variability and repeated costs still are.

Coordinator decision: authorize the compiler owner to implement this bounded slice after its consent response, with all above conditions. Preserve source patches/checkpoints before source-corrected variants. The encoding full-check currently owns the build slot; compiler source edits are allowed, compiler builds wait for an explicit handoff. No native adapter, new address-key law, global Expr disequality, general tracer or proof support is authorized by this decision.
