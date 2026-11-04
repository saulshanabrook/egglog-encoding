# Cycle 04 Codex source refresh

**No genuinely new eligible family was found in this pass. K2 routing and K3 tagged sorting remain eligible existing leads and merit bounded actual integrations. Their retained evidence does not support closing them.** K2 is the cheaper next integration; K3 follows it. This is a finite continuation of the admitted ledger, not a proposal to keep inventing reversible keys indefinitely.

This pass read the accepted facts, plan, current ledger, source findings, retained Parts32 integration, the available affine integration receipts, and the lossless-key backend screens. It then reread the relevant scalar, conditional, type, memory, and translation source in pinned U0 at `/private/tmp/eggcc-nontrivial-encoding-payoff-u0`. `git rev-parse HEAD` still reports `a0bbec127f83249074a46af3fd6f6126c90fe0fb`. It did not build, execute a compiler, collect timings, edit source, or change the ledger. Its only write is this report. Existing evidence is being assessed, rather than reproduced here.

## What the newer evidence changes

The [Parts32 actual integration report](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/report.md) establishes more than another manual opportunity. On its retained fixed input it reaches `word != -> Parts != -> Pair != -> High !=`, exports only the exact target predicate, and changes native code. The final report records 200 native checks, exact U0/B1/SeedOnly parity, exact Manual/Encoding parity, and forward/reverse/identity/query/bridge/consumer knockouts plus rescue. It explicitly contains no timing samples. Its full-validation limitations remain visible; this pass does not waive them.

The affine integration was still being packaged while this report was prepared. The available [inspection.json](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/affine-integration/inspection.json) says `status=passed`, zero semantic revisions, 140 positive native runs, 25 semantic-negative native runs, and 20 no-context native runs. It reports exact U0/B1 and Manual/Encoding emitted/native parity. Its causal receipts retain `a=c`, `b=d`, `z!=w`, and the final target disequality; cancellation, representation identity, reverse, forward, query, bridge, and application knockouts block the appropriate step. This is an **artifact snapshot**, not an independent acceptance audit, final immutable-source claim, timing result, or substitute for its eventual report.

Together these receipts weaken the implementation-risk objection to K2/K3: the required engine closure and exact false-predicate consumer have now run in closely related actual-host integrations. They do not establish K2/K3 expression import, scope transport, causal controls, native correctness, or speedup.

The [three-key backend report](../findings/lossless-key-backend-screens.md) already retains decisive nonclosure evidence for both:

| Lead | U0 native application instructions | Exact manual fold through U0 | What survives only in U0 |
| --- | ---: | ---: | --- |
| K2 route pair | 22 | 19 | Dynamic target compare and `99` selection |
| K3 tagged sort | 29 | 25 | Dynamic target compare and `99` selection |

The successful `execution-02` used the same U0/LLVM 18 pipeline for both arms. Across all three keys, 205 native and 205 interpreter output checks pass, including field omissions, selector/tag mistakes, true Add branches, even multipliers, ties, and wrapping extremes. Command elapsed values are diagnostics. The acyclic native difference is an opportunity, not a measured endpoint payoff or proof that a future hot driver retains it.

## Remaining ranked integrations

The common selected chain is:

```text
Key(a,b) = Key(c,d)
  => a=c, b=d                       marked key cancellation
Add(c,z) != Add(a,w), a=c
  => z!=w                           unmarked Add reverse congruence
  => Mul3(z) != Mul3(w)              marked forward disequality
  => exact contextual Eq=false      consumer export/application
```

All dynamic words, selector values, products, and key arguments are equality-sort children. Binary Add stays unmarked: its reverse step is congruence contraposition after the other child becomes canonically equal. `Mul3` is the total bijection `x -> 3*x mod 2^64`. Wrapping Add/Mul are defined at [interpreter.rs:239](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interpreter.rs:239). No numerical bounds, sampled values, memory certificate, division, or shift are needed.

The existing compiler consumer is the exact contextual Boolean predicate. The false-If rewrite at [interval_analysis.egg:284](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interval_analysis.egg:284) is one available consumer, but Parts32 demonstrates that extraction/LLVM can also consume a constant predicate when that particular rule is disabled. Therefore retain an **application knockout suppressing the exact target union**; do not claim that the named false-If rule is essential unless its own knockout actually restores baseline native work. Current true-Eq handling only transfers bounds at [interval_analysis.egg:408](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interval_analysis.egg:408), so it is not already a general symbolic key-cancellation mechanism.

### 1. K2: common-selector paired routing

**Exact sound law.** For a Boolean value `p` and total i64 payloads, define

```text
Route(p,a,b) = Triple(p, Select(p,a,b), Select(p,b,a)).
```

This map is jointly injective: the first output determines `p`; when `p=true` the remaining outputs are `(a,b)`, and when `p=false` they are `(b,a)`. Equivalently, with the same dynamic `p` on both sides, equality of both routed outputs implies `a=c,b=d`. Do not mark the untagged ternary map jointly injective: changing `p` and swapping payloads preserves its two outputs. Do not mark ordinary Select injective.

**Actual producer.** The retained [routing source](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/lossless-key-screens/20261019-three-total-keys/execution-02/routing/source.bril) already contains `p=lt(q,r)`, four direct Select expressions, and two nested true integer-Eq guards over the routed outputs. It then contains the false Add guard and the odd-multiplier target above. This is an existing constructed input, not a newly invented trigger or a demonstrated corpus application. The source operators are admitted directly at [to_dag.rs:281](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/rvsdg/to_dag.rs:281) and emitted at [from_dag.rs:292](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/rvsdg/from_dag.rs:292). The optimizer also creates real Selects from pure small If outputs at [select.egg:5](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/select.egg:5), and from exact input projections at [switch_rewrites.egg:36](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/switch_rewrites.egg:36). Neither producer is evidence of a full paired-key guard in the current benchmark corpus.

**Existing consumer and primitive-only null.** Use the common dynamic Add/Mul3 consumer. Preserve both routed-output equality seeds, the Add-result disequality, all terms, the selector identity, and literal metadata in the null. No primitive field comparison determines `a=c` or `z!=w`: either selector outcome admits arbitrary payloads. A direct primitive `true/false` conflict is absent. A faithful dynamic manual closure over those same rows is a required comparator and may prove the same result; generic reasoning has no claimed unique logical power.

**Cheapest remaining decisive falsifier.** Run one smallest actual-host import on the retained acyclic source, with both selector outcomes. If the importer cannot identify the shared dynamic selector and exact branch-local payloads without general path reasoning, the bounded candidate fails. If it can, compare the actual Encoding/Manual emitted and native code with U0/B1; close if the target survives or a causal knockout does not restore it. The prior manual screen need not be rerun merely to rediscover the same native difference. Before a timing campaign, screen a hot driver with fresh dynamic tuples; close the runtime lead if the matched baseline/manual native entries are identical or if all removable work is hoisted out of execution.

**Bounded implementation.** Reuse the proven private finite Word closure, scalar Add/Mul3 importer, exact source-context transport, and consumer application boundary. Add only an importer for the two complementary Selects under one localized Boolean term, plus a semantic Route constructor and its tagged representation identities. The selector is an opaque equality-sort Boolean value; no enumeration of its outcomes or Boolean-value observation is needed. Restrict Select payloads to total pure scalar words. The interpreter is lazy at [interpreter.rs:221](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interpreter.rs:221), whereas output conversion visits both payloads, so effects and partial payloads are outside this probe.

Retain fixed-input cancellation/reverse/forward/identity knockouts, exact intermediate rescue, query/bridge/application knockouts, Manual, SeedOnly, and the same-graph primitive null. Preserve negatives for one routed output only, different unresolved selectors, wrong branch/context, an even-multiplier target, and both outcomes of the common selector. One import/scope revision is allowed only for a concrete failed witness; do not grow a general Select path analysis.

**Disposition: retain for bounded actual integration.** Neither “LLVM already solves it” nor “the law is only a primitive conflict” matches the retained evidence. Sharing the affine tail makes it less independent as a consumer demonstration, but does not invalidate its distinct reversible-control producer.

### 2. K3: signed sorting with retained orientation

**Exact sound law.** Over all signed i64 values, define

```text
tag(a,b) = Select(a<b, 1, 0)
OrderKey(a,b) = Triple(Smin(a,b), Smax(a,b), tag(a,b)).
```

This map is injective. When tag is 1 the original pair is `(min,max)`; otherwise it is `(max,min)`. Equal inputs fall in the latter case and reconstruct correctly. MIN/MAX require no subtraction, absolute value, or overflow assumption. Signed min/max and comparison behavior is explicit at [interpreter.rs:251](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interpreter.rs:251). Min or max alone, or their pair without the orientation, is not injective. Float sorting is outside this law.

**Actual producer.** The retained [sorting source](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/lossless-key-screens/20261019-three-total-keys/execution-02/sorting/source.bril) has direct signed min/max, two integer-valued Select tags, and nested true Eq guards for all three key fields before the common tail. Smin/Smax are accepted at [to_dag.rs:236](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/rvsdg/to_dag.rs:236), emitted at [from_dag.rs:160](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/rvsdg/from_dag.rs:160), and typed at [type_analysis.egg:289](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/type_analysis.egg:289). Existing conditional-swap rules create min/max at [switch_rewrites.egg:4](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/switch_rewrites.egg:4). The actual bubblesort conditional swap is only a near match: it does not preserve an equal-key orientation guard and does not establish the proposed payoff.

**Existing consumer and primitive-only null.** Use the same Add/Mul3 target and exact union application. The 0/1 tag literals alone cannot determine `a=c`; they identify only an orientation once the two *dynamic* extremum outputs are known equal. Keep all three field-equality seeds and the symbolic tag nodes in the null. Do not replace the dynamic tag by an observed primitive bit or use a primitive tag mismatch as the endpoint. The retained no-tag, omitted-min, and omitted-max counterexamples each reach `99` and show why complete dynamic key evidence is necessary.

**Cheapest remaining decisive falsifier.** One actual-host probe on the existing acyclic source, covering ascending, descending, equal, and MIN/MAX payloads. Close if exact localization of the two tags and all three guarded fields requires general predicate reasoning; otherwise demand the same native/causal gate as K2. Before timing, use a matched fresh-tuple hot-driver native screen. The three fewer or four fewer application instructions in an acyclic entry alone are insufficient to justify a timing claim.

**Bounded implementation.** Add a binary marked OrderKey constructor and representation identities to an unmarked three-field equality-sort product. Import only exact signed Smin/Smax over the same payload pair and a literal `Select(LessThan(a,b),1,0)` orientation expression, following exact branch input substitutions. Do not derive arbitrary order predicates, normalize floating comparisons, reconstruct full sorting networks, or annotate min/max individually. Reuse the existing private closure and exact consumer application. Add no-tag, omitted-min, omitted-max, reversed/changed tag, different context, wrong Add branch, and even-multiplier negatives. One concrete scope/import revision is the maximum.

**Disposition: retain after K2.** It is a distinct information-recovery law with one extra field/guard to localize. Current evidence supports actual integration, not closure and not a promised speedup.

## Fresh directions rejected before admission

The reread covered the operators available in [schema.egg:84](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/schema.egg:84), their actual interpreter semantics, Select/min/max/If generation, type admission, and existing memory consumers. It did not claim an exhaustive search of all possible EggCC programs. No closed lead is reopened.

| Direction considered in this refresh | Why no new eligible hypothesis was admitted |
| --- | --- |
| Other odd coefficients, nonlinear triangular reversible word pairs, wider affine networks | Their algebra may be sound, but no new actual corpus guard or blocked consumer was identified. Replacing the key function while reusing the exact same constructed tail is not a reason for an unbounded sequence of new leads. K1 already tests total simultaneous dynamic cancellation. |
| Dynamic-selector routing networks and longer compare/swap networks | Bounded compositional controls for K2/K3, rather than separate families. Start with the existing complete trigger; only add one composition control after import works. |
| Unary Neg/Abs/Not wrappers and float sign transformations | No new source-derived equality/DQ producer and blocked consumer was identified. Integer Neg/Abs additionally use ordinary Rust negation/abs at [interpreter.rs:337](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interpreter.rs:337), so a total MIN law cannot be assumed across configurations. Float payload equality needs its own NaN/zero semantics. These do not justify another unsupported annotation or a broad semantic redesign. |
| Distinct fresh-allocation regions | U0 already models pointees with primitive allocation IDs and offset intervals at [memory.egg:25](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/memory.egg:25); allocation IDs are produced at [to_dag.rs:272](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/rvsdg/to_dag.rs:272). For the ordinary distinct-ID route, one specialized primitive ID check can emit the final NoAlias fact, so it fails the accepted null. Repeated executions of one site need a new lifetime/instance producer, which this pass did not find. A2 has no demonstrated nonprimitive producer or exact blocked consumer and should be closed at this source/eligibility gate unless new concrete evidence is supplied. This does not close the already distinct dynamic same-live-region A1 lead. |
| Structural state/write cancellation or symbolic output-order audit | General Write is not injective in the previous heap: it overwrites information. A complete heap reconstruction needs a different semantic model. The retained print-trace lead still names no actual bad equality between interpretable ordered traces. No newly identified compiler equality or independently suspicious producer appeared here. Do not build a general effect interpreter merely to search for one. |

Changing the endpoint to memory does not automatically create a fresh family: exact same-address forwarding already exists at [mem_simple.egg:107](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/mem_simple.egg:107), and commute uses an exact NoAlias pair at [mem_simple.egg:70](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/mem_simple.egg:70). A new memory proposal still needs an actual key/branch producer and exact pointer transport. The currently retained A1 and Q1 entries already cover the concrete source-backed opportunities found for those consumers; this pass adds none.

## Finite stop boundary

**An eligible lead remains: K2, then K3.** Other existing admitted opportunities, including A1/Q1/P1, must keep their explicit dispositions. This report cannot support an overall exhaustion stop while those rows remain unresolved. Conversely, it admits no cycle-04 new family and gives no reason to open another arbitrary reversible-key construction.

For K2 and K3 separately: use the retained input and seeds; allow one smallest actual-host/native probe and at most one revision justified by a concrete importer/scope falsifier. Two no-progress cycles close that lead. A passed acyclic integration proceeds only to a bounded fresh-tuple native screen, and a retained executed code difference may proceed to a prospectively frozen matched endpoint measurement. A failed or identical hot endpoint closes the runtime claim without a larger workload search. No general path reasoning, heap model, new executable IR, sorting optimizer, or wholesale alias redesign belongs in this budget.

After the finite admitted set is resolved, run the required fresh Codex and read-only Fable passes against the new evidence. Stop discovery when both produce no new source-backed eligible law/producer/consumer chain, or every remaining proposal needs a substantial redesign. Report the proved speedup and its limits if final acceptance passes; otherwise report the goal's actual failed gates. Do not infer global impossibility, promote the current unmeasured integrations to speedups, or treat a fresh model's alternate coefficients as a mandate to continue indefinitely.
