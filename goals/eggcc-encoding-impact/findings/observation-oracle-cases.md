# Small independent oracle matrix for concrete observations

These are six expectation designs, not new executed tests. No builds, source edits, compiler runs or broad source scans were performed. They reuse the API/semantic evidence in [observation-proposal-review.md](observation-proposal-review.md): If passes its evaluated **input** into only the selected region; region entry resets memoization; the detached helper starts a new VM; Const/Arg evaluation itself does not validate stored context/type. The compiler circle owns implementation and actual test receipts.

Counts below name **designated original boolean probes** and distinct feasible region invocations. They do not count their synthetic literal counterparts, other boolean subexpressions the observer may choose to cover, or raw egglog rows. A passing implementation may record additional supported probes, but must match each named probe's value/count and actual region argument. Each root invocation counts as one region invocation. Points for separate root inputs/invocations remain distinct even when the contextual RcExpr is identical.

For the synthetic DAG notation, `If(pred, input, then, else)` evaluates `pred` and `input` in the current region, then invokes only the selected arm with the new `input`. `arg[0]` is an explicitly typed, in-bounds tuple projection; constants carry that region's matching argument type/context. All listed integer arithmetic is i64 wrapping arithmetic. The small values below do not overflow.

| Case | Kind | Designated probe observations | Feasible region invocations |
| --- | --- | --- | --- |
| 1. Same-type changed region input | Synthetic typed DAG | one `false` | root + selected arm = 2 |
| 2. Nested selected path | Synthetic typed DAG | selected inner-else one `false`; both dead probes zero | root + outer-then + inner-else = 3 |
| 3. Shared Rc, different inputs | Synthetic collector-session fixture | same Rc probe: `true`, then `false`, once each | two root invocations = 2 |
| 4. Confirmed branch-overflow source | Existing actual Bril case, input variants | answer once for MAX/1; zero for 0/-1 | assert designated counts, not an assumed frontend region layout |
| 5. Unsupported selected/dead dependency | New Bril-shaped fixture proposal | supported arm one `true` for x=1; selected unsupported probe emits zero observations for x=-2 | one reached designated probe per run; eligibility differs |
| 6. Typed state carrier with one print | Synthetic typed DAG, Bril-shaped effect flow | one `false`, no state observation | root + selected arm = 2; one Print event |

## 1. Root and region arguments have the same type but different values

Root argument type is `(Int)` and value is `[7]`:

```text
If(true,
   [2 * root_arg[0]],
   then(region_arg): probe1 = region_arg[0] < 10,
   else(region_arg): false)
```

The selected arm's actual argument is **`[14]`**, still type `(Int)`. `probe1` is **false**, with exactly one feasible observation. There are two feasible region invocations, and no else-arm invocation. Its false literal counterpart must use the arm's context and `(Int)` argument type at the same point.

This catches a silent error that a type-only check misses: evaluating the arm with the root argument `[7]` produces true. Evaluating it with a missing/scalar argument is also wrong, but is a weaker falsifier because it merely panics. Require the observed argument value `[14]` as well as the false boolean. This is a synthetic unit fixture; no claim is made that a particular Bril lowering chooses these tuple slots.

## 2. Nested If transports the selected input twice and never visits dead arms

Root argument is `[3]`, type `(Int)`. All region inputs keep that same type:

```text
If(0 < root_arg[0],
   [2 * root_arg[0]],
   then(outer_arg):
       If(outer_arg[0] < 5,
          [2 * outer_arg[0]],
          then(inner_arg): dead_inner_probe = 0 < inner_arg[0],
          else(inner_arg): selected_probe = inner_arg[0] < 10),
   else(outer_arg): dead_outer_probe = outer_arg[0] < 100)
```

The outer predicate is true; the outer-then argument is `[6]`. The inner predicate is **false** (`6 < 5`); its evaluated input is `[12]`. Only inner-else runs, and `selected_probe` is **false** (`12 < 10`), once. `dead_inner_probe` and `dead_outer_probe` each have **zero** feasible observations. Feasible invocations are precisely root, outer-then and inner-else: **three**. No boolean observation is assigned to either dead probe, even if a detached evaluator could calculate a value under a fabricated argument.

A root-argument walker tests `3 < 5` and chooses the wrong inner arm. A parent-argument walker can choose the correct arm but then evaluate `6 < 10` as true. An all-children walker records dead probes. The value, selected-path and zero-count assertions distinguish all three failures. This is a synthetic nested-region fixture.

## 3. Reuse the exact same contextual RcExpr under two inputs

Construct the contextual probe object `shared = (arg[0] < 10)` **once**, with argument type `(Int)` and the same function context. Reuse that exact RcExpr in one collector-session test, first under root input `[3]`, then under `[20]`; do not reconstruct two lookalike expressions.

Expected records, in order:

```text
(shared, p3,  root=[3],  region=[3],  Bool(true))
(shared, p20, root=[20], region=[20], Bool(false))
```

There are **two** feasible root invocations and **two** designated observations, one at each distinct point. Both the manual consistency audit and injective ObservedBool audit must accept the combined graph. Sharing the exact Expr/Rc and context is intentional; differing concrete inputs must prevent point conflation. A session-global `Rc -> value` memo would incorrectly return true on the second input, so checking only “no panic” is insufficient: assert the actual true/false payloads.

For the optional E1 probe against the same-context false literal, the combined observations establish Expr inequivalence using `p3`. In a fresh `[20]`-only graph these observations supply no such witness. Do not expect the combined graph's query to become unknown merely because the expression agrees with false at `[20]`.

This is a synthetic shared-object/session test. Separate CLI invocations of a Bril program do not establish that this memoization lifetime has been tested. No loop or Call is required or authorized by this fixture.

## 4. Actual branch-local overflow case with live/dead input variants

Use the existing `tests/encoding_impact/arithmetic/mul-minimal-max.bril` shape, preserving the normal compiler pipeline:

```bril
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

| x | `positive` | `product` when reached | `answer` / designated feasible points | Source print log |
| --- | --- | --- | --- | --- |
| `9223372036854775807` | true | -2 | true / **1** | `["true"]` |
| 1 | true | 2 | false / **1** | `["false"]` |
| 0 | false | not evaluated | no observation / **0** | `[]` |
| -1 | false | not evaluated | no observation / **0** | `[]` |

The MAX source expectation and baseline true→false failure already have real compiler/interpreter receipts in `findings/compiler.md`; the new observer's behavior remains unexecuted. MAX should supply the positive pre-pass E1 witness against false, and later cause the manual/injective conflict audit to reject the real wrong merge. The fresh x=1 graph should supply no witness from these observations and should complete correctly. For 0/-1, the unreached `answer` must have zero points and cannot manufacture a conflict. If the observer also covers `positive`, it has exactly one source evaluation for each input, with the values shown above.

This is the actual Bril-pipeline case. Do not assume its lowered argument tuple ordering or total region count from the Bril text: retain the actual contextual region input/reference produced by the shared tree/cache. Such frontend identity evidence is precisely what the synthetic cases do not establish.

## 5. Unsupported selected dependency versus an unselected unsupported arm

Proposed new Bril-shaped input; no compiler receipt exists yet:

```bril
@main(x: int) {
  zero: int = const 0;
  two: int = const 2;
  positive: bool = lt zero x;
  br positive .supported .unsupported;
.supported:
  good: bool = lt x two;
  print good;
  jmp .done;
.unsupported:
  q: int = div x two;
  bad: bool = lt q zero;
  print bad;
.done:
  ret;
}
```

Choose Div as a deliberately **non-whitelisted dependency**, despite division by two being well-defined for these inputs. This avoids turning an undefined source operation into a purported observer/compiler bug.

- x=1 reaches `good=true` once; `bad` and its Div dependency are unreached. For a selected-point collector, expected emitted designated observations are **1**, selected-unsupported probes **0**, and dead-arm observations **0**. Source log is `["true"]`.
- x=-2 reaches `q=-1`, `bad=true` once in source execution. Its dependency is outside the observer grammar: expected emitted designated observations are **0**, with **1 selected unsupported probe**. The observer must report unsupported coverage or reject the diagnostic configuration; it must not silently label this a fully validated run or call the generic interpreter to bypass the whitelist. Source log is `["true"]`.

This separates feasibility from eligibility. A walker that inspects both arms unnecessarily rejects x=1 or seeds the dead `bad` probe. A shallow whitelist that checks only `LessThan` but ignores its Div child wrongly accepts x=-2. A dead branch must not be evaluated to discover that it is dead.

A deliberately conservative **whole-program** grammar check may reject both configurations before collecting points. That is sound but narrower than selected-point coverage; record the configuration as unsupported rather than reporting the x=1 observation case passed. This oracle does not demand expansion of an approved whole-program restriction. Exact feasible/eligible probe counts above remain the expectation if the selected-point collector is claimed. Calls, loops or memory stay outside scope; accepting dead Div does not authorize them.

## 6. Typed state carrier: one normal print, pure observation after region entry

Synthetic typed DAG with root argument `(Int, State)` equal to `[7, StateV]`. `Print(value,state)` appends that integer to the execution log and returns State; it is executed only as normal program plumbing:

```text
If(true,
   [2 * root_arg[0], Print(root_arg[0], root_arg[1])],
   then(region_arg): [probe6 = region_arg[0] < 10, region_arg[1]],
   else(region_arg): [false, region_arg[1]])
```

The selected region input is **`[14, StateV]`**, type `(Int, State)`. `probe6` is **false**, exactly once. The whole expression returns `[Bool(false), StateV]`; its normal execution log is exactly **`["7"]`**, with **one Print event**. There are two feasible region invocations. The state slot is carried with its correct type, never observed as Bool or interpreted as address/point identity. The matching false literal retains argument type `(Int, State)` rather than erasing the state carrier to `(Int)`.

A correct trace can obtain this concrete input from the one normal evaluation, then observe the pure branch projection/comparison. Independently evaluating the If input tuple (even to extract only its integer slot) re-evaluates Print under the existing eager tuple/projection interpreter and is not a pure detached observation. A root-input substitution again returns true instead of false. A collector that rejects every tuple containing State would unnecessarily lose this explicitly approved carrier case; if the current slice intentionally excludes it, report unsupported coverage instead of claiming this test passed.

Assert the observer's complete evaluation trace/effect accounting as well as the final program log: duplicate effect evaluation in a disposable VM can be hidden if its private log is discarded, so unchanged external output alone does not prove that collection avoided detached effects. No memory allocation, load/store or effectful expression is an observed value. This is a synthetic state/trace fixture; a Bril counterpart and actual lowered state-carrier receipt would be separate full-pipeline evidence.

## Acceptance boundary

Cases 1–3 and 6 isolate semantic path/input/cache invariants with deliberately constructed typed DAGs. Case 4 connects them to the already reproduced real compiler bug. Case 5 is a new source-shaped coverage-control proposal. None is a production workload or performance result. Correct values without the corresponding zero/nonzero point and eligibility counts are insufficient. A manually seeded egglog algebra example cannot substitute for actual feasible-path collection, and a detector abort is not a successful source/optimized output comparison. The compiler worker should keep those result kinds separate in its receipts.
