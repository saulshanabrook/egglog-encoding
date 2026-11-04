# Semantic paths to a qualifying EggCC payoff

Read-only setup discovery, 2026-10-18. This note proposes bounded experiments after plan approval; it reports no executed experiment, new bug, optimization, speedup or exhaustive search. The [fourteen accepted facts](../facts.md) control acceptance. Only a genuine new baseline EggCC bug or a reproducibly measured end-to-end compiler/generated-program speedup can close this goal. Equivalent integration, a correct but unmeasured optimization, and exhausted leads leave the goal **unmet**.

## Source authority and existing capabilities

The engine API reads use `/Users/saul/p/wt/egglog-encoding/eggcc-combined-encoding`, branch `codex/eggcc-combined-encoding`, HEAD `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5` plus the retained E1 `disequality.rs` delta. This is the actual available E1 implementation, not a claim that this historical base is current upstream. The verification owner separately screens fresh baselines. No source was edited and no build/test/compiler/model run was performed.

| Available behavior | Exact source | Consequence for a new bridge |
| --- | --- | --- |
| Fresh independent graph with selected NEE/EE; encoding fixed for that graph | `egglog-experimental/src/lib.rs:160–169`; `disequality.rs:167–200` | `new_experimental_egraph_with_options(true, DisequalityEncoding::Nee)` is enough to construct a private local solver. No new engine constructor API is needed. |
| Marked constructor cancellation | `injectivity.rs:222–288` | Equal marked outputs union equality-sort children; unequal primitive fields generate a panic action when `injectivity` runs. Containers/nonunionable equality children are rejected. The annotation is an obligation, not a discovered mathematical fact. |
| Partial read-only `known-disequal?` | `disequality.rs:203–255, 298–405` | Same unionable equality sort only; `Unit` means a finite witness, undefined means no witness. Marked forward propagation and unmarked remaining-child reverse congruence are already implemented. Direct primitive queries, containers, ordinary function tables and term/proof query modes remain outside this fragment. |
| Assert DQ at top level or in rule actions | `disequality.rs:450–471, 661–688` | `(disequal a b)` is supported; rule-produced seeds need no new materialization API. Assertions are graph-global, not scoped constraints. |
| Explicit contradiction normalization | `disequality.rs:475–515` | `(check-contradiction)` saturates only private `@disequality` and succeeds if a contradiction is present. It does not compute cancellation/consumer joint closure, and failure to find contradiction is not a satisfiability result. |
| Existing host boundary | `egglog/src/lib.rs:1671–1715, 3006–3012`; `exec_state.rs:64–81` | Parse/run returns `Result`; host-owned status function rows can be read without extracting keys. Query rule bodies require `:naive`. Missing witness, unsupported domain and API failure must remain distinguishable host outcomes. |

`known-disequal?` builds transient indexes and searches existing committed rows; it stores no derived pair and performs no union. It currently logs internal query errors and returns undefined (`disequality.rs:248–254`), so a bridge must not interpret undefined as proof of equality, successful coverage or satisfiability. There is no built-in scoped query, satisfiability solver, arbitrary conditional-equality facility, or automatic producer/cancellation/query fixed-point manager. Existing manual comparison is therefore both fair and necessary.

The laws must remain separate:

- Marked cancellation: `F(a)=F(b) ⇒ a=b`, only for justified injective `F`.
- Marked forward DQ: `a≠b ⇒ F(a)≠F(b)`, under that same contract.
- Remaining-child reverse congruence: `F(a,s)≠F(b,s) ⇒ a≠b`; no injectivity requirement. For n-ary constructors all other corresponding children must be canonically equal. Two unresolved unequal siblings do not identify a particular unequal child.

Different constructor names are not automatically disjoint. Different source symbols do not denote different runtime values. Equality-sort `!=` only observes current identities; absence of equality does not prove mathematical disequality. These rules do not justify global Expr injectivity, generic Concat cancellation, mutable-record injectivity, or pointer nonalias from expression inequivalence. [Prior constraints](../../eggcc-combined-encoding/planning/prior-constraints.md) and [the previous source-grounded API note](../../eggcc-combined-encoding/planning/encoding.md) remain relevant, without making the old search exhaustive.

## First route: prospectively detect a new Add/Sub invariant violation

The consumer owner routed a concrete family distinct from the completed Mul-sign result. A targeted read of current-origin-main object `a0bbec127f83249074a46af3fd6f6126c90fe0fb` shows the following in `dag_in_context/src/interval_analysis.egg`:

- Add lower/upper endpoints at lines 120–133 and Sub endpoints at 136–149 have no overflow/monotonicity guard.
- LessThan upper bound uses the left lower and right upper endpoints at 242–248.
- A false Boolean upper bound unions the expression with a same-type/context false Const at 107–114; the existing false-If consumer is at 283–290.
- Current main now has `IntB`, `BoolB`, `Dead` and explicit contradictory-bound handling at 4–32. Historical Maybe/Either snippets are not its current representation. A rule-level suspicion does not establish that its actual normalization, Dead handling and full native schedule produce a wrong result.

For the intended signed wrapping-i64 domain, let `MAX=2^63−1`, `MIN=−2^63`. These are independent mathematical predictions, **not run results**:

| Valid source-shaped hypothesis | Endpoint prediction | Nearby and boundary controls |
| --- | --- | --- |
| Inside `0 < x`, evaluate/print `x+1 < 0` | At `x=MAX`, modular addition yields `MIN`, so the result is true. The branch-derived lower bound `x≥1` would give claimed lower bound `x+1≥2`, which is false at MAX, and can incorrectly support a false comparison bound. | `MAX−1`, `1`: false; `0`: branch skipped. Check exact branch input transport rather than substituting a root argument inside a region. |
| Inside `x < 0`, evaluate/print `0 < x−1` | At `x=MIN`, modular subtraction yields `MAX`, so the result is true. A claimed upper bound `x≤−1` would give `x−1≤−2`, which is false at MIN, and can support a false comparison bound. | `MIN+1`, `−1`: false; `0`: branch skipped. |

The compiler owner must verify current source arithmetic semantics and construct valid actual Bril/native examples; this note does not treat predicted graph firing as observed. Oracle arithmetic should use exact integer modular reduction, independently of the interval implementation and the new walker, then compare the baseline interpreter/native results and minimized semantic invariant. Neither the old Mul finding nor previously reproduced MAX/MIN inequality-guard panics can qualify as the new result.

The previously reviewed concrete observer offers a bounded detector bridge. In the retained compiler module `dag_in_context/src/observations.rs`, lines 438–476 support Mul/LessThan/And/Or/Not, **not Add/Sub**. A future Add/Sub extension needs typed `wrapping_add`/`wrapping_sub`, independent agreement with the real interpreter, and the same reached-region, argument transport, context/type, point/input/pass identity and per-region memo checks. Merely admitting the operator name is insufficient. No loops, calls, memory or detached effect evaluation are implied by this extension.

The existing declarations at 560–588 mark only `ObservedBool(bool)` in Injective mode. `Expr` and `EvalBoolAt(Expr, point)` remain unmarked. Seed a reached comparison and its same-context false literal with independently checked true/false observations at the **same** point. If a real optimizer pass wrongly unions those expressions, ordinary congruence equates their observation outputs; the marked primitive payload conflict then rejects the graph before native extraction (`audit`, lines 799–828). This is one feasible-input counterexample to an asserted expression equality. It is not an all-input guarantee of unequal values, an optimization enabled by injectivity, or a pointer fact.

The detector must contribute prospectively on a new candidate: retain the first encoding witness, implicated source schedule/union and its chronology, then independently reproduce the wrong baseline result or semantic invariant, minimize, localize and retain nearby controls. A bug independently found by other means must not be relabeled encoding discovery. Graph invalidity may qualify as the accepted semantic-invariant route only with an independent interpretation witness; a parser, unsupported form, missing producer or new walker error does not.

Fixed-input controls: default Off; identical shared seed without audit; direct Manual seed-conflict audit; Injective with only the valid wrapper flag; and the corresponding flag/audit removal. Shared seed must not itself repair or change the baseline behavior. Manual can detect the same inconsistency; no unique detector power is claimed. Both modes must operate on the actual compiler graph after the same pass, not only an initialized replay. An optional pre-pass DQ query may exercise more encoding but is not necessary for this detector's panic and must not be represented as necessary.

Earliest falsifiers: fresh baseline fixed the bounds; intended region/producer absent after normal lowering; no actual erroneous union/output under the real schedule; current Dead handling safely contains the case; only unsupported source triggers; old independent guard already rejects for another reason; or independent wrapping/reference semantics disagree with the proposed oracle. Preserve each outcome; move to a new hypothesis rather than retrofit the old Mul witness.

## Second route: genuinely private scoped value reasoning

The prior C5 global-constraint attempt is not proof that conditional reasoning is impossible. A viable bounded design is **one fresh solver graph per exact path scope**, with a host bridge that returns conditional facts and never copies engine Values/e-class IDs into EggCC. Fresh construction using the existing public factory is the first approach; do not add a core API or persistent index before demonstrating a concrete need.

### Domain and sound laws

Start with a finite straight-line, total, pure wrapping-i64 value grammar: branch variables, selected exact literals if needed, and unary `Shift_c(v)=v+c mod 2^64` for a finite set of literal displacements actually present in the program. Build only the finitely many source applications. Each fixed `Shift_c` is a bijection and may be marked injective. Its cancellation is valid even across signed wraparound. Generic two-child Add is not jointly injective: `Add(0,1)=Add(1,0)` despite different children. No generic Bop/Expr annotation follows.

Use an **unmarked** `Symbol(id)` leaf. Its identifier records which scoped source value it represents, not a runtime disequality; different variables may be equal. Do not mark Symbol and derive DQ from different native IDs. A literal wrapper can be injective for exact literal identity, but marking it is unnecessary for the minimal chain. For a first Bottom-aware profile, unmarked literal wrappers plus explicitly justified distinct-literal DQ avoid treating an engine primitive-mismatch abort as the normal local infeasibility API. No disjointness between Symbol, Literal and Shift constructors is assumed.

The proposed real source chain is: in the true branch of `(x+1)==(y+1)`, then the false branch of `x==z`, examine `(y+2)==(z+2)`. The local graph receives only path-valid assumptions:

```text
Shift_1(x) = Shift_1(y)          path equality
x ≠ z                           path disequality
x = y                           scheduled Shift_1 cancellation
y ≠ z                           existing equality transport of the DQ witness
Shift_2(y) ≠ Shift_2(z)          marked forward DQ query
the final Eq is false           proposed conditional compiler bridge
```

All local relations mean pointwise statements for **every assignment satisfying this exact path**, rather than global inequivalence of Expr functions or a fact from one observed input. The simple path has feasible witnesses, e.g. `x=y=0,z=1`; use such a witness so a proposed payoff is not merely unreachable-code reasoning. Full source lowering, actual remaining conditional and the useful existing consumer are still compiler-owner obligations, not demonstrated outcomes.

A second, potentially richer finite chain uses the false branch of `(x & m)==(y & m)`. Represent bitwise And as an **unmarked** binary constructor on local Values. Seed only the path-valid `And(x,m)≠And(y,m)`; existing remaining-child reverse congruence can witness `x≠y`, and marked forward reasoning for a fixed wrapping-add `Shift_k` can then witness `Shift_k(x)≠Shift_k(y)`. Thus `(x+k)==(y+k)` is false in that path. This is supported by the current scalar query (`disequality.rs:384–405` followed through its marked-forward goals at 361–378), without an And injectivity annotation or any disjointness between And and Shift. It exercises reverse congruence and marked forward DQ, **not equal-output cancellation**. All required applications must already exist in committed local rows.

Use a feasible witness such as `x=0,y=1,m=1`; a zero mask makes the false-Eq branch impossible and must not count as useful optimization. With different masks, unequal And results do **not** imply unequal x/y: `x=y=1,m=0,n=1` is a counterexample. Require the same canonical mask sibling and test this negative explicitly. Removing the Shift mark should lose the final composite witness; removing n-ary unmarked reverse inference should lose the root witness despite the asserted unequal And results. Compare the equivalent direct scoped rule and the actual baseline/native result. Whether the real compiler or downstream native backend already removes the redundant condition is unexecuted and can reject this lead. Bitand expands the local optimization grammar, not the initially proposed Add/Sub observer whitelist.

### Isolation, Bottom and promotion

NEE-only is a defensible initial **explicitly bounded profile** because the factory already selects it. It avoids EE-specific private-Truth maintenance but does not make branch assumptions globally safe. NEE self-DQ can still mark the whole graph contradictory; conditional unions still act globally within their graph. EE additionally has lift/double-negation rules that can union user-sort values (`disequality.rs:886–944`). Test EE only if it becomes a claimed supported local profile; do not silently imply parity from the earlier engine tests.

Adding a Scope field to a constructor is not isolation. Equal marked outputs still cancel and union any unscoped Expr children; private Truth values/assertions are shared within one EGraph. A later feasibility guard cannot undo those unions. Per-scope graphs instead have distinct mutable stores, equality partitions, DQ tables and Truth values. When entering a nested scope, retranslate the parent's assumptions into the new graph with a checked binding map; do not transport raw local IDs. A custom scoped constraint relation would require its own equality/congruence/cancellation/query semantics and a reviewed bridge. Current `known-disequal?` does not read arbitrary `(scope,a,b)` relations. That is a possible later extension, not a currently available solution.

After finite supported producer/cancellation/DQ normalization, inspect contradiction **before** consuming local results. A known contradiction means local `Bottom`: discard that graph's ordinary consequences, retain a diagnostic and do not abort a valid compiler for an impossible branch. No contradiction means only “not proved Bottom”; this engine is not a SAT solver. For example, impossible modular constraints outside the bounded theory need not be recognized. Distinguish local contradiction from unsupported domain, timeout, parse/type/backend error and missing evidence; those errors cannot be promoted to unreachable-code proofs.

Sound conditional consequences do not require a complete SAT decision: every actually reached execution satisfies the recorded path assumptions. Promotion is safe only into the exact same typed/contextual branch, with exact root-to-region input transport, total-operation eligibility and no fact escaping its assumptions. If the host wants to eliminate an outer branch because it is Bottom, that is a separate reviewed consumer contract. The first slice should not do it. No inferred local equality of values becomes a global Expr equality between unrelated contexts.

The host mapping, conditional bridge and eligibility checks are **proposed compiler work**; only the solver factory, annotation, DQ actions and query exist today. Require the compiler owner to identify an actual bound/Bool/If API that preserves these conditional semantics under subsequent normalization before authorization to implement the bridge. `ExprIsPure` alone is not a totality proof: exclude calls, loops, memory, division and unsupported operators in the first grammar. Excluded forms remain explicit unknown/unsupported, including selected forms that would be evaluated; skipping an actually dead arm is distinct.

### Schedule and finite closure

Queries read committed state and cannot trigger cancellation. For the minimal fixed-input profile: declare finite source nodes and assumptions; commit; saturate `injectivity` (equality-only Shift cancellation); normalize/check DQ contradiction; only for non-Bottom run the `:naive` query consumer; read host-owned statuses. `check-contradiction` succeeds on Bottom and returns a CheckError when no contradiction is known; an explicit host classifier must distinguish that specific expected check from other failures.

If a producer or consumer introduces new equalities/DQ/terms, this one-shot sequence is insufficient: iterate committed producer → cancellation → contradiction audit → query consumer with an explicit finite progress measure and bounded failure outcome. Keep audits before any promotion. Do not saturate a generative producer indefinitely and audit afterward. Do not claim completeness beyond the finite chosen grammar, existing applications and explicitly scheduled closure. Existing `naive_consumers_observe_late_equalities_and_parent_assertions_under_both_schedulers` (`tests/injectivity_disequality.rs:143–183`) demonstrates why late equalities/assertions require rescheduling; it does not validate this new host bridge.

### Contributions, independent oracle and early rejection

Use identical source/domain/path assumptions across baseline, direct/manual scoped algebra and the new local solver. To demonstrate **both** mechanisms on the proposed chain, removing Shift_1 cancellation must leave the root equality unavailable; removing Shift_2 injectivity must leave the final composite DQ unavailable; suppressing the DQ-consuming bridge must leave the actual conditional unchanged even if an internal generic query still knows a witness. Assert each intermediate result and actual compiler outcome. Preserve the manual direct equivalent; the engine has no unique logical power over those rules.

Independent validation must compute fixed-width semantics without calling the solver: enumerate a small finite assignment set plus signed endpoints for original and transformed conditions, and independently test the modulo-2^64 shift inverse law. Include equal distinct symbols, wraparound, different displacements, absent path DQ, inconsistent path, late cancellation, missing producer, parent/child context mismatch and sibling-scope isolation. A small bounded enumeration is a test oracle, not a proof for all i64 inputs; the mathematical bijection argument supplies that law. Fixed-input ablations should yield unknown where their essential law is absent rather than silently falling back to a separate raw-identity guard.

Reject this optimization candidate early if default/manual rules already remove the conditional, the real lowering produces no eligible chain, root/region transport cannot be enforced, the useful branch is infeasible, generated native code already removes the cost, or the bridge cannot remain scoped. If correct transformation survives, only matched full compilation time or generated-runtime measurements can qualify. Count the local-graph creation/translation/analysis overhead in compiler time. A branch removed in a replay, reduced rule time, or new correct IR alone is not payoff. Neutral/regressive outcomes remain visible.

## Ordered gates and stop terms

1. **Before integration:** pin a fresh baseline and valid source hypothesis; identify the actual native consumer; write independent expected outcomes, laws, whitelist, fixed-input controls and novelty exclusions. Start with Add/Sub because it needs the smaller observation extension. Do not broaden to loops/Div/bit arithmetic merely to obtain a counterexample.
2. **Smallest falsifier:** after execution is authorized, validate the oracle/eligible grammar and detector/scoped-model negatives first. Preserve predicted versus actual outcomes. Two no-progress cycles trigger hypothesis reassessment, not repeated identical runs.
3. **Actual host:** default Off unchanged; missing/unsupported inputs fail explicitly; retain source-to-graph context identity, intermediate witness and pass boundary. Require registered nonzero tests plus independent oracle and valid native compiler coverage. For a bug, reproduce the new baseline violation independently, minimize/localize and retain passing controls. For an optimization, establish actual baseline/new/manual output and native code behavior first.
4. **Contribution review:** bind source/input/binary/dependency/configuration and fixed-input feature ablations. Separate new integration defects from the preexisting compiler behavior. Initialized replay may supplement, never substitute for, actual-host evidence.
5. **Payoff admission:** only a new qualifying bug or repeated independently confirmed end-to-end speedup closes the goal. If only equivalent checking/unmeasured optimization/negative results remain, mark the explored candidate disposition and keep the goal unmet; reassess the next search with the user. No exhaustive-search claim follows from these two families.

Future existing engine validation entrypoints, **not executed during setup**:

```bash
# cwd: the authorized isolated encoding implementation checkout
CARGO_BUILD_JOBS=4 cargo test -p egglog-experimental --test injectivity_disequality
CARGO_BUILD_JOBS=4 cargo test -p egglog-experimental --test injectivity_disequality naive_consumers_observe_late_equalities_and_parent_assertions_under_both_schedulers
# Final coordinated full source gate after implementation/review:
make check
```

New local-model/observer/host tests must be registered by their implementation owner, not represented as existing tests by these commands. Fresh compiler entrypoints, current-baseline interpreter semantics, native coverage and timing admission belong to the consumer/verification plans. Memory pressure alone is not a stop condition; preserve timeouts/errors, reduce to useful small workloads and continue within authorized scope.

## Read record and identities

Commands were read-only `git rev-parse`, targeted `git status`, `rg`, `nl`/`sed`, `shasum`, and `git show a0bbec127f83249074a46af3fd6f6126c90fe0fb:dag_in_context/src/interval_analysis.egg`. Cwds were the repository root, the E1 engine tree above, and `/Users/saul/p/wt/eggcc/combined-encoding`. Compiler reads were restricted to root-routed interval and observer bridges, not a broad frontier scan. A lightweight memory-registry check oriented the old explicit-schedule contract; substantive current API statements were verified in source. No imports, builds, tests, models, workloads or measurements ran. Only this planning file was authored.

| File/object | SHA-256 |
| --- | --- |
| Accepted `facts.md` | `cabf4e7ec192658a1d7932c901cb380aab1af3a9f9ea8ebc98a14f95d3257092` |
| Prior `eggcc-combined-encoding/planning/encoding.md` | `9526dbb9fee45c36f8114a93f883e857178e45259bb63f794d4b60fb445bc9a5` |
| E1 `egglog-experimental/src/injectivity.rs` | `3eccb019378d11155f8dce27dbd7a6780efe7a4a24233536a9cafc9607cfa281` |
| E1 `egglog-experimental/src/disequality.rs` | `8d56d53d87d0c21595b765f3aa6a9f7e3bc4752b4f87dfbcc651c108fe11bb3c` |
| E1 `egglog-experimental/src/lib.rs` | `29cc7459d737e6289a68dff6d518ce8c7e82cb70e09c6762952e99f4816a4f07` |
| E1 `egglog/src/lib.rs` | `5128c934dfb4f8ec8a2116eb8e79da607820fff74086f83ad324e3b73cdcc8e9` |
| E1 `egglog/src/exec_state.rs` | `5edfc70985b6a862c55effe4b75016b3a9cc0433bac4c46204927aaf04af456e` |
| E1 `tests/injectivity_disequality.rs` | `3da93594215cf562380d0dd9c2391dcf5e184ff3214e60dac80b8c303816251c` |
| Current-main object interval source | `b18729ef499e2d5257e80f091468cf3d7f80686280a5c4d65e93766511a888dd` |
| Retained compiler observer source at HEAD `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b` plus prior delta | `02075844820baf66b4021aaf5ba480c9be00a1b6ff0d467a3ea06a924d8dc3d5` |

The old observer is reusable integration evidence, not a claim that fresh upstream already has that module. Fresh port/current native behavior and the actual new payoff remain unverified.
