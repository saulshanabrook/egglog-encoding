# Compiler consumers and ordered payoff probes

Setup-only discovery, 2026-10-18. This note proposes experiments; it contains no new compiler result. No build, test, compiler execution, benchmark, worktree, source edit, fetch, commit or goal activation was performed. Only this planning note was written. The fourteen accepted facts and interview interpretation govern success: a genuine new EggCC bug found using an encoding, or a reproducible measured end-to-end compiler/generated-program speedup. An integration, an unmeasured optimization and an unsuccessful search do not close the goal.

## Source authority and boundaries

The frozen previous integration is `/Users/saul/p/wt/eggcc/combined-encoding`. Its authoritative final manifest is `benchmarks/local/eggcc-combined-encoding/consumer/oracle-final/source.json`, SHA-256 `8165c4521d16ea4f5d1cffe66a08092962b55b8976f37c2b6a2553bfc5352738`. The manifest identifies its root, full source inventory, preserved baseline and test-only final delta. Its production closure is unchanged from its previous snapshot. Fresh `git status --short` confirmed existing modified manifests/entrypoints and untracked observation/type implementations, fixtures and pending snapshots; these were preserved. The primary `/Users/saul/p/eggcc` checkout was not changed.

The harness owner supplied the freshly checked current-main commit `a0bbec127f83249074a46af3fd6f6126c90fe0fb` and recommends it as the execution baseline. I read only the relevant objects with `git show <commit>:<path>` in the existing compiler worktree. Current-main source, rather than the historical result, grounds the first hypotheses below. The execution plan must preserve three distinct roles:

1. **U0:** pinned current main with its declared `08771...` engine dependencies and normal native path.
2. **B1:** the same current-main source, narrowly retargeted to E1 with necessary compatibility/observer plumbing, all experimental checks off.
3. **Candidate:** B1 with the selected encoding/check enabled. Manual and shared-seed controls use this same source/input domain.

A bug must exist on U0, or an actual reached unsound baseline union/invariant must independently be established there. A failure appearing only after engine retargeting or new observation integration is insufficient. Old binaries are historical controls, not substitutes for a current-main compiler/native-backend pair. Harness owns dependency, baseline, build, binary and backend admission; this note does not independently certify those roles.

Current-main Git blob identities read during setup:

| Path under `dag_in_context/src/` | Git blob at `a0bbec12` |
| --- | --- |
| `interval_analysis.egg` | `899d032e65e3f9e06c04110c062849dc542393d1` |
| `interpreter.rs` | `0560ee649a1a602213d55185bab2e4666e4a5177` |
| `optimizations/hackers_delight.egg` | `0c18baa58185f2f0fe54d5cde2988199856030c3` |
| `schedule.rs` | `55826239feaa062acb7e6a583a4d52c8290a4ea7` |
| `optimizations/mem_simple.egg` | `9cba1ecf302f14fde28e6639dd7ec4059bb665ad` |
| `utility/util.egg` | `47052eb8d0ba0f4a7fad689310e26285a925dffc` |

Numbered current-main references below mean these `git show` objects, not an assumed clean checkout at that revision. Legacy references name the frozen worktree explicitly. The current-main Bound representation changed from `Maybe/Either` to `IntB`/`BoolB`/`Dead`; copying an old analysis patch wholesale is inappropriate.

## Prior dispositions: what cannot count again

Read `eggcc-encoding-impact/{candidate-map.md,report.md,findings/compiler.md,planning/consumers.md,observation-slice.md}` and `eggcc-combined-encoding/{report.md,planning/consumers.md}`. Their relevant constraints are:

- The completed positive-times-positive and nonnegative-times-nonnegative multiplication interval bug is excluded. Its exact legacy rules are `interval_analysis.egg:159–168` and `192–201`; current-main counterparts are `188–197` and `221–230`. Changing its input or putting the same faulty product in another wrapper is repetition.
- `MAX >= MAX` and `MIN <= MIN` were also already reproduced as native optimization panics in the earlier arithmetic screen. Their unguarded canonicalization is not a fresh discovery. Retain as historical regression controls if needed, never as new payoff.
- The completed structural type checker rejected the same malformed internal types as the old checker. Replacing normalized raw-ID comparisons with structural disequality is not a new source bug or measured speedup.
- C2's existing CSR/matrix NoAlias producer/storage/consumer screen had no useful distinct-address commute demand. Recounting its final pairs is not new impact. That negative does not rule out a different fresh/live producer and actual consumer.
- C4 fixed-split tuple cancellation has a conditional law, but existing projection closure is strong redundancy evidence. C5 has a real conditional-elimination endpoint but no approved pointwise/bottom-safe bridge. C3 has no certified live-allocation producer for the old kernels. These are open leads, not exhausted or successful cases.

The old discovery explicitly mentioned Add/Sub as nearby hypotheses. The retained first arithmetic screen and final candidate map establish no Add/Sub experiment or localization. Thus the proposed transfer-rule probes are new executions of a previously untested hypothesis, not a claim that this source suspicion was first conceived here. An exact evidence-index check belongs in execution admission before calling a result new.

## Ranking and first decision

| Order | Probe and actual endpoint | Proceed only when | Early falsifier |
| --- | --- | --- | --- |
| 1 | One-sided Add/Sub interval transfer; encoding-based feasible-observation audit detects a bad compiler union before native extraction | Narrow observer adaptation has independent checks; actual U0 baseline still reaches the candidate | Correct baseline result with no violated invariant, unsupported observer domain, only port failure, or only old Mul/canonicalization cause |
| 2 | Low-bit loop normalization at signed MIN; inspect the odd-part output of `hacker` data rewrite | Actual source loop matches the rule and both data outputs survive; a bounded observation bridge is justified | No native/reached union mismatch, no actual match, or failure attributable only to the observation extension |
| 3 | Scoped false-Eq reverse congruence, preferably through noninjective Bitand; existing If elimination | A scope-isolated, bottom-safe pointwise model and a blocked real consumer exist | Global/scope leakage, infeasible-path rejection, existing optimization already supplies result, or native backend erases all benefit |
| 4 | Fixed-split tuple cancellation aimed at compiler time | Real same-result/same-split pairs remain costly after current projection closure | All useful equalities already present, or adding constructors does not remove work |
| 5 | Distinct live allocations feeding write/load commute and forwarding | A closed valid call/loop has fresh live regions and a blocked hot demand | Static-site identity only, aliasing/unknown calls/frees, no reached consumer, or same native code |

Do the first small vertical probe before implementing a broad new domain. A bug on a valid source input can satisfy the strict endpoint without a performance claim, provided the encoding actually discovers the violated compiler equivalence and the independent U0/localization evidence is complete. No unique logical power beyond the fair manual checker is promised. If it fails, record the reason and advance; do not redefine failure or integration coverage as success.

## 1. First vertical probe: one-sided Add/Sub ranges under wrapping integers

### Current source chain

Current-main `interpreter.rs:239–244` defines explicit wrapping-i64 Add/Sub. In `interval_analysis.egg:120–133`, Add independently derives a lower bound by adding lower endpoints and an upper bound by adding upper endpoints, with no no-overflow obligation. Sub does the analogous endpoint subtraction at `136–149`. A one-sided signed bound is not preserved across wrapping addition/subtraction merely because the arithmetic performed on that bound itself is representable.

The reached consumer is concrete. A true `0 < x` branch gives its scoped x lower bound 1 through current-main `interval_analysis.egg:357–371`. The Add lower rule can therefore derive `lo(x+1)=2`. The `LessThan` upper rule at `242–248` derives false for `(x+1)<0`, and `107–114` unions that test with the context-matching Bool false. The mirror uses x<0's upper bound -1 (`325–340`), the Sub upper rule (`143–149`) to derive `hi(x-1)=-2`, and the same LessThan/Bool-folding consumers for `0<(x-1)`. Helpers run canonicalization, interval analysis and mem-simple in the normal schedule (`schedule.rs:93–96`).

These are hypotheses about actual reached input shapes, not observed firings or results. They must be checked on the fresh baseline; the source premises alone do not prove that extraction changes the program.

### Exact proposed valid input shapes and independent expectations

First input, with MAX supplied as a runtime argument rather than embedded as an arithmetic operand:

```bril
# ARGS: 9223372036854775807
@main(x: int) {
  zero: int = const 0;
  one: int = const 1;
  positive: bool = lt zero x;
  br positive .positive .done;
.positive:
  shifted: int = add x one;
  answer: bool = lt shifted zero;
  print answer;
.done:
  ret;
}
```

Mathematical fixed-width expectation: MAX+1 = MIN modulo 2^64, so the reached print is `true`. At MAX-1, 1 and 2 it is `false`; at 0 and -1 the branch is not executed and output is empty. Replace only the argument to obtain these nearby controls. Do not claim an empty-output run agrees by treating missing/null output as a value.

Mirror input: branch on `lt x zero`; in that branch compute `sub x one` and print `lt zero shifted`. At MIN the expected result is `true` because MIN-1 wraps to MAX; at MIN+1 and -1 it is `false`; at 0 and 1 output is empty. This checks the distinct Sub upper transfer rather than just commutativity or syntactic reassociation of Add.

Both source forms terminate, have only total integer Add/Sub and signed comparisons, and contain no Mul, GreaterEq, LessEq, memory, shifts or division. The proposed abstract arithmetic computes only `1+1` or `-1-1`, so the target is not the prior primitive-overflow panic on a constant endpoint. Check expectations with a standalone modulo-2^64 oracle and source interpretation/optimization-free translation; the new observer's local evaluator is not its own oracle.

### Encoding contribution and chronological evidence

Reuse the existing bounded feasible-observation design, not Expr injectivity. Frozen `observations.rs:438–476` currently permits Mul/LessThan/And/Or/Not but rejects Add/Sub. A narrow positive-grammar extension for total wrapping Add/Sub, with independent boundary tests, is necessary before either new input is eligible. Port only the required module/hooks to current main; do not transplant the full old compiler patch or old Bound representation.

The sound invariant is: for an actually reached contextual evaluation point p, equivalent expressions must have the same Boolean observation. An unmarked `EvalBoolAt(Expr,p)` maps both the original true predicate observation and a matching-context Bool false to separate `ObservedBool` values; only the immutable `ObservedBool(bool)` constructor is injective. If the compiler actually unions those Exprs, congruence merges their observed wrappers and injectivity requires the incompatible primitive Booleans to agree. The audit rejects before serialization/native extraction. Effects, Exprs, contexts and mutable bounds are not marked injective. Frozen source locations are `observations.rs:560–588`, `665–685`, and `799–838`.

Run the encoding-led detector on the admitted hypotheses and retain its first conflict receipt; then independently confirm wrong baseline semantics/localize the union. Keep source suspicion, observation generation, first actual detection, independent output check and localization times separate. Do not rename a mismatch already independently observed by another route as encoding discovery. If it was found first by that route, describe the encoding's actual later contribution honestly and reassess whether it meets the accepted fact.

E1's disequality query may give a pre-pass witness that the observed test differs from Bool false by reverse congruence through unmarked EvalBoolAt with a common p. That remains a separate diagnostic unless an actual compiler check consumes it. The fixed-input injective audit alone is an eligible encoding contribution under the accepted either-encoding choice; a second encoding should not be forced into the claim through a decorative query.

### Controls, localization and pass/fail boundaries

The same input and observation domain must run under U0 and the B1 family. On B1 compare Off, CommonSeed, equivalent Manual audit and Injective audit. With identical observation seeds, removing only the literal annotation/audit must remove that new detector; it must not change source execution or silently accept an unsupported observation domain. The Manual audit is a fair hand-written comparison over the same points/seeds, not an existing baseline mechanism.

For a positive candidate retain an actual reached graph witness: branch bound, Add/Sub result bound and `answer = Const(false,matching type/context)`, bound to source/binary/pass/input identities. Independently check that U0 either emits/runs the wrong output or really reaches that unsound equivalence on the valid concrete input. A hypothesis about a rule that could fire is not enough.

Localize by exact source-rule treatments, not the previously ineffective `--ablate` route:

1. Disable the two already completed Mul sign rules while keeping the new input fixed; the candidate must remain. The source contains no Mul, but this control records causal exclusion in the actual compiler. If related historical builds use the existing corrected-control patch, record its exact identity rather than assuming it matches current main.
2. For Add, remove/replace only the lower Add transfer (`120–126`), then inspect whether another valid reassociation/transfer still supplies the same bound. For Sub, do the same with the upper Sub transfer (`143–149`). Keep unsuccessful single-rule hypotheses as evidence. A whole-ruleset exclusion is too coarse for final localization.
3. Use a conservative correctness control that declines this inference when a no-wrap range cannot be proved; do not merely guard `1+1` or `-1-1` for overflow, since those endpoint operations are safe while the represented concrete value wraps. A proper interval repair needs both operand ranges and signed-wrap handling, or omits the inference.
4. Rebuild/run the actual corrected native compiler through the full pipeline on failing and nearby controls, with shared observer seeds and checks. An exported pass replay can help localize, but cannot substitute for corrected native coverage.

Reject as the strict result if U0 is correct and no real unsound invariant is established; if only a newly retargeted compiler fails; if the observer remains unsupported; if observations evaluate an unselected path; if only an old excluded rule causes the result; or if malformed internal assertions are required. Do not infer a speedup from early rejection, fewer passes or failed-versus-successful runs. Successful bug evidence requires registered nonzero tests, an independent oracle, actual native/compiler coverage and review of the localized root cause.

## 2. New reserve: low-bit loop normalization at signed MIN

Current-main `optimizations/hackers_delight.egg` is still the same source-shaped pattern: parity detection at `10–15`, `NTZIterations` recognition at `20–41`, divergence-preserving state rewrite at `51–83`, and data rewrite at `85–101`. Its data rule unions both the doubling-factor output with `n & -n` and the repeatedly-halved n output with `n/(n & -n)` without a signed-MIN guard. `hacker` participates in cheap optimizations unless explicitly disabled (`schedule.rs:116–126`). The existing benchmark source at frozen `benchmarks/passing/fenwick/fenwick_tree.rs:30–37` supplies the repeated-halving loop shape, though it only returns the factor.

Concrete proposed Bril shape: set `factor=1`; while `n == (n/2)*2`, assign `n=n/2` and `factor=factor*2`; after the loop print whether n<0 and also use/print factor so both outputs remain live. Start n as a runtime argument. At signed MIN, the source loop takes 63 halving steps and ends with n=-1 and factor=MIN under wrapping multiplication. A wrapped lowbit is MIN, making the replacement quotient MIN/MIN=+1. Thus the proposed sign observation differs. At -8, -6, -1, 1, 6 and 8, the conventional identity has the expected negative/positive odd part; n=0 diverges and must stay a separate timeout/divergence control, never a successful finite output.

This is a source-derived arithmetic hypothesis, not a reproduced bug. The exact NTZ pattern must first be present in the native source-derived graph; an internal fixture that manually asserts `NTZIterations` cannot qualify. Distinguish factor equality from odd-part equality and preserve the state/divergence rule. The original source can avoid unary Neg; the candidate rewrite introduces it. `interpreter.rs:248–250` uses wrapping division, while unary Neg at `340` uses ordinary Rust unary minus. Therefore debug overflow behavior and native/release semantics require explicit independent checks; do not silently assume a uniform Neg contract. An optimizer-introduced debug panic, if actually reproduced on valid source U0, is different evidence from a native wrong quotient.

The existing observer excludes DoWhile, Div, Eq, Bitand and Neg. A bounded loop-output observation or restricted terminating replay needs a separate semantic design and independent oracle. Do not make all loops admissible or observe infeasible iterations merely to reach this case. First falsifier: actual original graph lacks the recognized loop/both data outputs, or the default compiler never reaches the bad quotient equivalence. If it survives, compare exact data-rule removal/appropriate signed-domain guard with state-rule preservation; disable the prior two Mul sign rules in an additional control because parity/factor computations contain Mul. A full corrected native comparison must confirm the cause. This is larger adaptation than Add/Sub, hence second.

## 3. C5: scoped false-Eq congruence into conditional elimination

The actual missing producer remains visible in current-main `interval_analysis.egg:408–431`: Eq's true branch transfers integer bounds; no corresponding false-Eq disequality flow exists. A known-false inner predicate has existing consumers: Bool false folding at `107–114` and If elimination at `283–290`.

Prefer an additional noninjective test to merely replaying the old fixed-shift proposal. Current source supports integer Bitand (`schema.egg:92`; interpreter `238`; Rust Bril bridges `src/rvsdg/to_dag.rs:230` and `from_dag.rs:150`). Source-shaped case:

```text
if ((a & b) == (a & c)) {
    ...
} else {
    if (b == c) { expensive_valid_work } else { fast_valid_work }
}
```

On a feasible else path, unequal Bitand results and the same a imply b!=c by reverse congruence. Bitand is not injective: b!=c alone cannot imply different results. Both the equality and disequality are pointwise facts in that branch, not global inequalities of Expr functions. The proposed bridge supplies only that scoped inner Eq=false, then existing If elimination removes the impossible expensive arm. A larger valid loop can make the avoided operation hot only after the small source case is confirmed; labels must distinguish that variant from the small mechanism case.

Before integration, semantics must provide isolated pointwise values and bottom handling. A scope field on an injective wrapper is insufficient if cancellation can still union unscoped children or globally collapse incompatible facts in impossible paths. Do not assert current global EE/NE facts for every syntactic branch and hope a later guard contains them. Unknown remains unknown; dead branches are bottom, not global contradictions. Pure total integer Bitand/Eq avoids Div and divergence in the initial logical fragment, but the removed arm must also preserve source effects and program termination as required by ordinary conditional semantics.

First checks: feasible witness a=1,b=1,c=0; infeasible false branch with b=c; equal Bitand results with b!=c (a=0,b=1,c=2); different a operands (no sibling equality); reversed inner equality, nested/wrong scopes, unknown inputs, and impossible outer branches. Compare a direct scoped hand-written congruence/NotEqual analysis with encoding query, query off, common-sibling premise off and consumer off. The encoding must materially supply the fact consumed by the actual compiler.

This is only a performance lead if native output and timing show benefit. Inspect the same native backend's original/candidate final code before collecting measurements: it may already remove the inner condition/arm. If code and runtime are unchanged, an additional egraph equality is not payoff. End-to-end compile speed is separately eligible but must include the scoped-analysis cost and use the same valid workload/configuration. A correct reasoning integration alone does not satisfy this goal.

## 4. C4: tuple cancellation has a real redundancy gate

Frozen `utility/canonicalize.egg:41–51` equates associative/empty Concat forms; its interpreter appends flat tuples at `400–410`. Global Concat injectivity is false. A fixed prefix length gives a conditional cancellation law only for matching finite pure tuple/context/type semantics. Existing `utility/util.egg:58–105` generates leading projections and propagates them across Concat; canonicalization `98–107` reconstructs subtuples. `passthrough.egg:5–14,41–50` consumes projected equalities. The current-main util object was identified above; no new runtime graph was inspected here.

First future probe must identify an actual same-result/same-split pair with a downstream equality still missing or expensive after current helper closure. Keep unequal-split associative, empty, mismatched type/context and effect/divergence controls. Compare a guarded direct cancellation rule with the same fixed-split law represented using encoding constructors. If all useful equalities are already present, close the candidate. If compiler time is the target, show which existing work is actually avoided: leading-Expr helpers currently create all leading Gets, so merely adding a new constructor does not eliminate that work. A separate demand/schedule change needs a demand-matched manual control; do not attribute that change's gain to injectivity. Any retained optimization still needs measured end-to-end benefit.

## 5. C3: live-region producer must precede memory optimization

Frozen `mem_simple.egg:20–58` derives NoAlias from bounded nonzero same-base offsets; `71–81` commutes a write followed by a proven-disjoint load, and `106–113` forwards a same-address store/load. Its current-main object is identified above. The interpreter allocates from runtime `next_addr` and ignores Alloc's static id (`interpreter.rs:390–398`). Therefore different static allocation sites/formal parameters are not live provenance certificates.

A new small eligible source proposal would allocate two nonempty arrays once in one closed caller, then in a loop store p[i], load q[i], and reload p[i], with bounds and state order explicit. A common-state live-region certificate could establish the cross-array NoAlias needed to commute the first store/load and expose forwarding of the final p load. This differs from repeating C2's old zero-demand kernels. It is a proposal, not a certified producer: verify actual pass/inlining shapes, no free/unknown call/escape, disjoint live allocation events, in-bounds nonwrapping offsets, and a reached blocked demand before implementing keys. In-loop allocations or aliased generic callers require their own stronger model.

Compare the encoding producer to a direct fresh-pair/NoAlias guard over the same certificate and a hand-written key consumer. Same-pointer, aliasing caller, repeated call/site, unknown/freeing call, zero/negative allocation, wrapping/out-of-bounds offset and wrong-context controls are required. Inspect native code early: the backend may already infer fresh-allocation disjointness and remove the final load. No eliminated egraph load or NoAlias witness alone establishes runtime benefit. A scalar-promotion redesign is not silently included; propose a new loop-memory consumer separately if the existing commute/forward path is insufficient.

## Setup checks and next-stage admission

Performed only: accepted-fact/status/prior-report reads; narrow `rg` searches of compiler producers/consumers and old arithmetic dispositions; numbered source reads; existing-worktree `git status --short`; selected `shasum -a 256`; current-main `git show` and `git rev-parse <commit>:<path>` reads after the harness supplied the object. A lightweight memory-registry search had no useful task-specific result. Two attempted source reads reported absent `hackers_delight.rs`/`dag_in_context/src/tests.rs`; they yielded no evidence and were replaced with the actual `.egg`/existing source references. No engine/harness source scan or independent upstream/ref search was done.

Legacy principal file SHA-256 values checked against the final manifest: interval analysis `ff363e2c10c57c2f3f79005d1f883f98091b3a32d023f43265b2ccbb89ce2647`; interpreter `dd991459c2baa77f52ba03a0533147c4b134a2da0ed343f105cb049e415f0491`; observations `02075844820baf66b4021aaf5ba480c9be00a1b6ff0d467a3ea06a924d8dc3d5`; hacker rules `9353b929df18fbe5c25da85a0c65a9990ad0df5bf5b75f6bc28e824080aacdd3`; canonicalization `aa7b40cba93c9d51133df7e94fa15f5a4fa3ec1f897c4eb4780f632a4e582c52`; schedule `9fbdab5fb1b738e7e93cad0cc2924a2a440d725903354c5c81a62ccfb8ec10e0`.

Next-stage gates owned elsewhere remain explicit: semantic review of observation extension and scoped alternatives; U0/B1/current native-backend/dependency admission and exact preservation identities; isolated implementation authority; registered nonzero tests, independent oracles and full required gates; per-workload timing protocol only for a correctness-passing performance lead. All predictions here remain unknown until those experiments. If all pursued probes fail, retain their exact falsifiers and report the strict goal unmet, then reassess with the user; do not mark an unsuccessful search complete.
