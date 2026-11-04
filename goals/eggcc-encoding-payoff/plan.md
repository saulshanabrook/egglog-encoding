# Find a demonstrated EggCC payoff from injectivity or disequality

## Outcome and present evidence

The goal succeeds only with **a genuine new EggCC compiler bug found using the encodings, or a reproducible measured speedup** in generated-program execution or end-to-end compilation. Prefer using injectivity and disequality together; either can qualify if its contribution is demonstrated. A correct integration, an optimization without measured benefit, and an unsuccessful search leave the goal **unmet**. There is no third success option.

This is an execution plan, not a claim of a new result. Setup inspected source and prior evidence; it ran no compiler, test, model or benchmark. The [accepted facts](facts.md) and [interview interpretation](interview-interpretation.json) control acceptance.

The completed studies established a multiplication-overflow bug and an equivalent structural type-checking integration. Neither is a new result for this goal. Earlier `MAX >= MAX` and `MIN <= MIN` optimization panics are also known. Their exact exclusions and discovery chronology are recorded in [prior results](planning/prior-results.md) and [compiler discovery](planning/consumers.md#prior-dispositions-what-cannot-count-again).

## Approach

Start with the smallest new vertical experiment: extend the bounded observation audit to wrapping Add/Sub, then use it on valid Bril inputs that may expose overflow-unsound interval transfers. If this fails, investigate a signed-MIN loop identity, followed by a scoped conditional optimization that can combine both encodings. Reject leads early when their semantic contract, actual compiler consumer or potential payoff fails. Keep further tuple and allocation leads behind those checks rather than implementing broad machinery in advance.

Detailed source discovery is split into [compiler consumers](planning/consumers.md), [encoding semantics](planning/semantics.md), [verification and measurement](planning/verification.md), and [prior results](planning/prior-results.md). Source references in those notes distinguish historical worktrees from objects at the new baseline.

## 1. Admit an isolated current baseline and comparisons

Use EggCC commit `a0bbec127f83249074a46af3fd6f6126c90fe0fb`, the current main revision checked during setup, as the primary target. The historical study used `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`; it is not an ancestor of this main revision. Do not silently reuse that source, its binaries or its native backend as current-main evidence.

Preserve the dirty primary checkouts, both completed-study worktrees, their controls, and frozen evidence. On execution, create new isolated source/evidence locations and establish three distinct roles:

| Role | Source and purpose |
| --- | --- |
| U0 | Untouched pinned EggCC main with its declared `08771f9…` engine dependencies. Establishes pre-existing bugs and the existing compiler's performance. |
| B1 | The same main revision narrowly retargeted to the selected E1 encoding source, with required API compatibility and experimental checks off. Separates integration overhead from the new mechanism. |
| Candidate and controls | B1 plus the selected use; the same inputs, preparation, backend and semantic domain across encoding, manual and feature-removal comparisons. |

Pin the full E1 source identity, including the retained encoding delta, rather than referring to a branch name or historical commit alone. Inspect current remote identity at execution admission and record any drift; changing the pinned target requires a recorded reason and fresh admission. No fetch, worktree creation or build was performed during setup.

Current main changes `Bound` to `IntB`/`BoolB`/`Dead`, changes export APIs, and changes Tiger's sources and timeout interface. Port only the necessary observer/module hooks. Rebuild a compatible current-main Tiger; the old study's backend is not automatically compatible. Resolve locked dependency metadata and release builds for U0/B1 before accepting any actual compiler result. An E1-only failure is an integration issue until independently reproduced in U0.

**Verification:** use the exact admission commands and source-manifest schema in [verification](planning/verification.md). Record source revision and patch, dependency closure, generated prologue, binary/backend hashes, inputs and arguments, configuration, commands and machine-readable results. Confirm that checks-off B1 preserves U0 behavior on the small passing controls. Run no experiments in the old study trees.

## 2. Register independent oracles and the narrow detector before probing

The retained `dag_in_context/src/observations.rs` supports Mul/LessThan/And/Or/Not but rejects Add/Sub. Extend only its total, typed integer grammar to `wrapping_add` and `wrapping_sub`, with the original reached-region, input transport, type/context and point/pass identity checks. Keep loops, calls, memory and other unsupported operators explicit. Admitting an operator name without a faithful evaluator does not establish coverage.

Use an independent exact-integer modulo-2^64 oracle for expected values; it must not call the new observation walker or interval rules. Check it against actual source interpretation and optimization-free native lowering. Register nonzero tests before relying on the detector: ordinary and wrapping endpoints, wrong types/contexts, unselected arms, missing producers, unsupported forms and matching-context literals. An empty output from a skipped arm is a valid explicit value; null or missing interpreter output is not agreement.

Only `ObservedBool(bool)` is marked injective. `Expr` and `EvalBoolAt(Expr, point)` remain unmarked. At a reached point, seed independently checked Boolean observations for the real predicate and its same-context false literal. If the compiler wrongly unions those Exprs, congruence equates their observations, and injectivity rejects incompatible primitive Boolean fields. This is a concrete counterexample to a claimed expression equality, not a globally asserted runtime-value disequality or a proof for all inputs.

Use the actual compiler graph at the actual pass boundary. Keep Off, CommonSeed, direct Manual audit and Injective audit controls over identical inputs and seeds. Check that seeds alone do not repair the behavior, and removing the annotation/audit removes the new detection. A pre-pass disequality query is optional diagnostic evidence unless an actual consumer needs it; it is not required for the Boolean audit.

**Verification:** register the new observer/oracle tests in the current-main test discovery, list them, assert a nonzero selected count and run them. Run the existing encoding integration suite plus the actual compiler host/CLI modes described in [verification](planning/verification.md). Record unsupported, missing, infeasible and error outcomes separately. Historical tests or initialized graph replays cannot substitute for current native compiler coverage.

## 3. First vertical probe: addition and subtraction interval transfers

These are source-derived hypotheses, not reproduced bugs. Current-main `dag_in_context/src/interpreter.rs:239–244` wraps integer Add/Sub. In `interval_analysis.egg`, Add at 120–133 and Sub at 136–149 propagate signed endpoints without a no-wrap obligation. LessThan at 242–248 and Boolean folding at 107–114 provide an actual possible consumer.

For `MAX=2^63−1`, `MIN=−2^63`, use these valid source shapes with a runtime argument:

| Hypothesis | Independent expectation | Suspected invalid inference |
| --- | --- | --- |
| In `0 < x`, print `x+1 < 0` | At MAX, wrapping gives MIN, so print true. At MAX−1 and 1, false; at 0 and −1, skip the print. | Branch lower bound `x≥1` becomes `x+1≥2`, then the comparison folds false. |
| In `x < 0`, print `0 < x−1` | At MIN, wrapping gives MAX, so print true. At MIN+1 and −1, false; at 0 and 1, skip the print. | Branch upper bound `x≤−1` becomes `x−1≤−2`, then the comparison folds false. |

The [consumer note](planning/consumers.md#exact-proposed-valid-input-shapes-and-independent-expectations) gives the proposed Bril. Use no Mul, GreaterEq or LessEq in these inputs, so they do not just repackage the old findings. Check the prior evidence index before calling the result new.

Run the admitted encoding detector prospectively and retain its first conflict, pass, observation domain and implicated equality. Then independently reproduce U0's wrong result or actual violated semantic invariant on the same valid input. Preserve the chronology of source suspicion, first encoding detection, independent confirmation and localization. Do not relabel an independently discovered mismatch as encoding-led discovery.

If the hypothesis survives, minimize it and localize with exact source-rule controls. Disable the old Mul-sign rules in an additional control; remove or conservatively repair only the relevant Add lower/Sub upper transfer and inspect alternate derivations. Merely checking whether `1+1` or `−1−1` overflows is insufficient: those endpoint operations are safe while the represented concrete value wraps. A repair must prove the necessary no-wrap range or decline the inference. Preserve other arithmetic behavior and run the corrected compiler through the full native pipeline on failing and nearby passing cases.

**Accept as a bug only if:** the valid minimized U0 case exhibits independently established wrong semantics or a reached unsound equivalence; the encoding materially detects it on the actual compiler graph; the cause and conservative correction are localized; registered tests, independent oracle and nearby controls pass. A hypothetical rule firing, parser failure, retargeting defect, malformed internal fixture or old finding is insufficient.

**Reject/advance if:** current main already avoids the inference, Dead handling safely contains it, lowering does not produce it, no real invalid union/result occurs, the observer cannot soundly support the case, or only the new integration fails. Preserve the precise falsifier rather than generalizing to all Add/Sub bugs.

## 4. Follow the next live hypothesis if necessary

### Signed-MIN loop identity

Current `dag_in_context/src/optimizations/hackers_delight.egg:85–101` proposes the odd-part result `n/(n & -n)` for a recognized repeated-halving loop. At signed MIN, the source-derived prediction is odd part −1 versus replacement +1. It is untested. Require an actual valid source loop, actual recognition, both live loop outputs and the real native schedule; manually asserted internal recognition cannot qualify.

This route needs a separate bounded semantic design for loop observations, Div, Bitand and Neg. Current Neg's debug/release behavior is unresolved; do not assume it wraps. Preserve the state/divergence rule, treat zero's divergence separately, disable the old Mul faults in controls, and compare exact data-rule removal or a justified signed-domain guard. Reject immediately if the real pattern/consumer is absent. Do not broadly admit loops merely to obtain a counterexample. See the [reserve probe](planning/consumers.md#2-new-reserve-low-bit-loop-normalization-at-signed-min).

### Scoped conditional optimization using both encodings

Investigate a real remaining conditional whose path establishes either of these chains:

```text
Shift_1(x) = Shift_1(y), x ≠ z
  ⇒ x = y                    injective cancellation
  ⇒ y ≠ z                    equality transports disequality
  ⇒ Shift_2(y) ≠ Shift_2(z)   injective forward disequality
```

```text
And(x,m) ≠ And(y,m)
  ⇒ x ≠ y                    reverse congruence, common sibling m
  ⇒ Shift_k(x) ≠ Shift_k(y)   injective forward disequality
```

Here `Shift_k(v)=v+k mod 2^64` for a fixed k is a bijection. Bitand is **unmarked and not injective**. Its unequal outputs imply unequal corresponding inputs only when the other sibling is equal. Different masks provide a required negative case. Different constructor names and different source symbols do not imply disequality.

Use a fresh private NEE egraph per exact path scope, via the existing `new_experimental_egraph_with_options(true, DisequalityEncoding::Nee)` API. Symbols remain unmarked. A Scope field alone does not isolate unions or contradiction state. Do not assert every branch's conditions in a global Expr graph. Retranslate nested assumptions through a checked binding map; do not reuse graph-local IDs across graphs.

Before implementing a host bridge, identify the exact typed/contextual normalizer and Bool/If consumer in current main (`interval_analysis.egg:107–114,283–290`). Establish correct root-to-region inputs, total-operation eligibility and no scope leakage. Restrict the initial grammar to total pure integer operations; `ExprIsPure` alone does not prove totality. This host bridge is proposed work, not an existing solver feature.

Commit finite terms/assumptions, run injectivity cancellation, normalize/check contradiction, then query using a `:naive` consumer only for non-Bottom graphs. A known local contradiction is Bottom and must not abort a valid compiler for an impossible branch. No contradiction is not a satisfiability proof. Errors, unsupported forms and timeouts are not Bottom. If a producer adds terms/facts/equalities, use an explicit finite progress measure and repeat the joint schedule with audits before promotion.

Promote only a valid consequence into that same branch/type/context. Do not export local value equality as global Expr equality. Include feasible witnesses, impossible paths, equal distinct symbols, wraparound, zero/different masks, missing facts, late equalities, wrong contexts and sibling-scope isolation. Compare the direct manual scoped rules and fixed-input cancellation/annotation/query/consumer ablations; observe each intermediate witness and the actual eliminated conditional.

Screen current EggCC and downstream native code early: an already removed conditional or unchanged executable can reject the runtime lead. A correct new equality alone cannot close the goal. Compiler-time improvement remains eligible only after including the local graph and translation overhead. See [semantic design and limits](planning/semantics.md#isolation-bottom-and-promotion).

### Later source leads

Only if the earlier probes fail, screen fixed-split tuple cancellation for work not already supplied by projection closure, or live-allocation NoAlias feeding an actually blocked commute/forward demand. Generic Concat injectivity and distinct static allocation sites are unsound shortcuts. Require the missing producer, consumer and payoff opportunity before implementation; the [consumer note](planning/consumers.md#ranking-and-first-decision) gives the boundary cases. These leads have not been ruled out, and this list is not exhaustive.

## 5. Admit timing only after correctness and actual consumer checks

A bug can satisfy the goal without a speedup. For a performance candidate, first show correct outputs and an actual native/compiler change on identical valid workloads. Compare U0, checks-off B1, candidate and the fair manual/common-preparation controls. A gain only over overhead introduced by the new integration is insufficient as an improvement to existing EggCC.

Predeclare per-workload warmups, repetitions, interleaved order, timeout, timing boundary, retained outliers/errors and confirmation method. Record machine/toolchain/backend identities. Keep unrelated builds/tests outside controlled measurements. Use fresh evidence and an independent confirmation batch beyond observed variability. Retain neutral and regressive workloads; report each workload rather than an aggregate headline.

The proposed protocol is U0/B1/Manual/Candidate, one warmup and 12 observations per arm for screening, followed by a fresh one-warmup/32-observation confirmation in balanced rotating order. Freeze a useful improvement threshold and paired analysis before confirmation; retain raw samples and uncertainty. An inconclusive confirmation is not success. The [verification note](planning/verification.md#measurements-only-after-a-promising-correctness-screen) specifies the proposed paired-cycle analysis and controls against drift and selective reruns.

Distinguish whole `--run-mode optimize` time from complete executable compilation through `--run-mode llvm --optimize-egglog true --optimize-bril-llvm O3_O3`. Report generated-program runtime separately, with the actual platform clock unit and output checks for every sample. Include scoped-analysis overhead in compiler timing. Do not use `infra/profile.py` unchanged: its parallel preparation, unchecked sample output, missing timeouts and blocked treatment order need a bounded adapter. Exact supported commands and admission checks are in [verification](planning/verification.md).

**Accept as speedup only if:** paired workloads/configurations and backend match; both arms finish correctly; repeated measurements and independent confirmation establish a benefit beyond variability; fixed-input controls explain the encoding's actual role. Rule-only timing, fewer egraph nodes, an unmeasured optimization, diagnostic retries and failed-versus-successful runs are not speedups.

Keep memory-pressure blocking disabled. Leave the benchmark memory-guard variable **unset**, rather than setting it to `0`. Use useful smaller workloads and explicit timeouts/errors when needed; memory pressure alone does not stop the search.

## 6. Validate, explain and apply the strict final gate

Run registered focused tests while iterating, then the required complete suites once the source is stable. Use fresh U0 comparisons for baseline failures; the old study's thirteen snapshots and three lint sites are not automatic waivers on new main. Keep failed official commands explicit. Verify actual compiler host and native CLI coverage; do not report zero selected tests or a successful interpreter call without comparing its outputs.

Deliver `report.md` as a collaborator-readable explanation of the **successful** case: valid source example, exact before/after rules, the connected encoding-to-consumer mechanism, what the old/manual version did, the bug's consequences or per-workload speedup, and limits. Put concise laws/API/schedule reference in `reference.md` and exact commands/identities/results in `reproduce.md`. Keep failed candidates in findings with their falsifiers; separate them from the successful narrative. No new proof support, Lean work, paper edits, commits or pushes are included.

At final review, require machine-readable evidence for every automated fact below plus semantic/novelty/claim review. Mark the goal complete **only** if the new bug or measured speedup criteria are actually met. If explored leads produce only failures or equivalent integrations, report progress and the unmet condition, reassess the next search with the user, and do not mark complete. Two no-progress cycles on one hypothesis trigger reassessment rather than identical retries. Do not infer an exhaustive negative result from this finite search.

## Accepted-fact verification map

| Fact | Execution check / review |
| --- | --- |
| `strict-success` (automated) | Final result record admits only a complete new-bug or measured-speedup evidence bundle; no integration/negative-result success. Human review confirms semantics and contribution. |
| `encoding-choice` | Prefer the combined chain; document which feature materially contributes. No decorative second-feature claim. |
| `bug-evidence` (automated) | U0 replay, minimized valid input, independent oracle/invariant witness, localized source treatment and nearby passing controls. |
| `new-result` | Compare exact prior findings and discovery chronology; exclude planted/internal-only/new-integration/tooling faults. |
| `speedup-evidence` (automated) | Matched successful sample rows, repeated observations, explicit boundary, noise and independent confirmation checks. |
| `causal-comparison` (automated) | Fixed-input Off/CommonSeed/manual/encoding and essential-law/consumer ablations on the actual compiler graph. |
| `soundness` | Review laws, types, contextual bridge, feasible paths, totality, Bottom and no scope leakage. Independent boundary oracles support the review. |
| `adaptation` | Review bounded write set and scope; no wholesale redesign, proof/paper work, commits or pushes. |
| `correctness` (automated) | Nonzero test discovery, focused/full suites, independent oracle, actual native host/CLI, explicit unsupported/missing/infeasible/error rows and compared outputs. |
| `preservation` (automated) | Before/after source manifests and immutable prior evidence hashes; exact source/dependency/patch/binary/backend/input/configuration/command identities. |
| `measurement-honesty` (automated) | Per-workload report from validated samples, compiler/runtime unit separation, neutral/regressive cases and failed trials retained. |
| `search-discipline` | Hypothesis/falsifier ledger; no-progress reassessment; exhausted leads leave the strict goal unmet. |
| `resources` | Confirm guard is unset; use smaller useful cases/timeouts, never pressure-only blocking. |
| `explanation` | Collaborator review of the connected case, before/after rules, manual comparison, results, reference and separate reproduction guide. |

Concrete existing commands, proposed new verifier boundaries and remaining compatibility gates are catalogued in [verification](planning/verification.md). New test/driver names must be registered and shown nonzero before they can provide acceptance evidence; this plan does not claim they already exist.

### Concrete command entrypoints after goal launch

Use role-private targets, pinned tools and timeouts as specified in the verification note. Variables below refer to admitted new locations; these are not commands to run during setup.

```bash
# U0 and, after intentional lock regeneration, B1/candidate compiler roots:
cargo metadata --locked --format-version 1
cargo metadata --locked --manifest-path dag_in_context/Cargo.toml --format-version 1
cargo build --locked --release --bin eggcc

# Isolated encoding root, after reconstructing the documented E1 source:
cargo test --locked -p egglog-experimental --test injectivity_disequality
cargo test --locked -p egglog-experimental --test files 'injectivity/injectivity-disequality.egg'

# Actual compiler correctness; independently compare both JSON outputs to the oracle:
"$BIN" --with-context --run-mode parse --interp --run-data-out "$FRESH/source.json" "$INPUT"
"$BIN" --with-context --run-mode optimize --interp --run-data-out "$FRESH/correctness.json" "$INPUT"

# Compiler roots: run both required full targets and retain failures.
make test
make nits
# Encoding root if engine or harness source changes:
UV_PYTHON=3.13 make check
```

The retained compiler-time collector has existing `collect`, `verify` and `figures` commands, listed verbatim in the verification note. Its schema must bind the independently checked reference and all role identities; its verifier alone does not prove cross-arm semantics. A new native-cost adapter or case acceptance checker is proposed only if needed. Review its schema and registered negative tests before relying on it; do not invent an existing CLI. The observer currently requires optimize mode, so full executable compilation must use a matched optimize→lower pipeline in every arm or a reviewed mode adaptation.

## Risks and open gates

- Current-main E1/Tiger/API compatibility is not yet built or tested. Preserve U0 and classify integration failures before interpreting a compiler result.
- Add/Sub and low-bit examples are predictions. Actual lowering, Dead handling or schedule behavior may reject them.
- A source hypothesis can precede a detector; the actual discovery chronology must stay visible.
- The scoped solver's factory exists, but source-to-local translation, Bottom classification and conditional promotion still need implementation and semantic review. The finite fragment is not a complete disequality/SAT algorithm.
- Existing manual rules or LLVM may already eliminate the proposed work. Measure the real endpoint before extending the mechanism.
- No positive result is guaranteed. The accepted goal has a strict positive completion condition; a failed search requires reassessment, not a weakened gate.
