# Wrapping Add/Sub interval repair contract

2026-10-18. **Initial mathematical/source guidance; no concrete repair diff is approved yet.** I reuse the independent [U0 baseline finding](baseline.md): Add/MAX and Sub/MIN are successful true-to-false wrong-output cases, with ten nearby/skipped controls. I have not rerun or independently re-audited that 96-command evidence here. This slice derives the laws and safe implementation conditions; it performs no compiler/native/engine run, test or source edit.

Read authority: B1 `/Users/saul/p/wt/eggcc/encoding-payoff`, baseline `a0bbec127f83249074a46af3fd6f6126c90fe0fb`; current `dag_in_context/src/interval_analysis.egg:4–58,119–149` SHA-256 `b18729ef499e2d5257e80f091468cf3d7f80686280a5c4d65e93766511a888dd`, with no interval source diff at this read. The prior observer source map is `compiler/sources/add-sub-evaluator/source.json` SHA-256 `8500e992563ee9835c115c36957951f8a1e9ef6f1bf7e9b535d508ac8acd447c`; its observer hash remains `89c7c2d9f78546c4cdd0e11cc73d69f4eba480c00505afe6e71b1dc1c8ae1aa5`. Observation-domain review is in [oracle.md](oracle.md#2026-10-18-bounded-static-portreference-review); no broader detector conclusion is added by this note.

## Meaning of the bounds

Write `N=2^64`, `m=MIN=−2^63`, `M=MAX=2^63−1`, and `w(s)` for signed decoding of `s mod N`. Assume sound, same-context input bounds for actual signed values:

```text
m ≤ la ≤ a ≤ ha ≤ M
m ≤ lb ≤ b ≤ hb ≤ M.
```

`IntB` carries an ordinary signed lower or upper bound, not a modular interval. `bound-max` strengthens lower bounds, `bound-min` strengthens upper bounds, and `Dead` absorbs either merge. Missing or unnormalized opposite bounds do not imply `Dead`. Known `lo>hi` indicates an empty domain only when the premises were sound. Wrapping overflow does not mean dead code: both endpoint witnesses are feasible. An invalid bound may already have caused an invalid Expr union before a later Dead update; Dead cannot justify that earlier transfer.

Bounds need not describe independent program variables. The rectangle below is an overapproximation even for correlated operands; requiring a condition for the entire rectangle is conservative and sound. Necessity claims below concern this interval-only rectangle, not all possible richer relational analyses.

## Exact extrema and the four ordinary transfers

In **unbounded mathematical integers**, all possible exact sums/differences in the rectangle lie in:

| Operation | Minimum L | Maximum U | Original lower / upper candidates |
| --- | --- | --- | --- |
| Add | `la+lb` | `ha+hb` | `w(L)` / `w(U)` |
| Sub | `la−hb` | `ha−lb` | `w(L)` / `w(U)` |

If `m≤L` and `U≤M`, wrapping is the identity throughout `[L,U]`. Therefore both original lower and upper transfers are sound, and their primitive endpoint operations are in range. This proves all four directions with a common operation-specific **whole-range no-wrap** guard. Checking just the endpoint used by one direction is insufficient.

For completeness about “minimal”: no-wrap is a simple sufficient profile, not a necessary condition for every sound wrapped endpoint. On these exact-sum ranges, signed wrapping is increasing except at cuts `t=m` and `t=M+1`. If no cut satisfies `L<t≤U`, both wrapped endpoint candidates give the exact output hull. If a cut is crossed, the hull includes both m and M; the original lower candidate is sound only if `w(L)=m`, and the upper only if `w(U)=M`. Uniformly wrapping a whole range can consequently be sound. Supporting these extra cases would need an explicit modular-range design; it is unnecessary for the first conservative repair.

With **only** the two endpoints used by an old rule and no other information, fill missing endpoints conceptually with the type bounds m/M. The ordinary no-wrap proof generally fails. The exact interval-only exceptions for the old wrapped candidates are:

- Lower Add or Sub: `L=m` gives a trivial lower bound, or `L≥M+1` makes the entire possible range wrap uniformly above MAX.
- Upper Add or Sub: `U=M` gives a trivial upper bound, or `U<m` makes the entire possible range wrap uniformly below MIN.

These are mathematical exceptions, not recommendations to add more rule cases now. If opposite bounds are partly available, the same whole-range test can use available endpoints plus type extrema. For example an exact zero operand allows a no-wrap identity even when the other operand has only one known bound. A simpler first implementation can instead require all four explicit `IntB` bounds and decline when any is absent.

## Safe guards with existing scalar primitives

The current representation has separate lo/hi tables for both operands, so it can require all four `IntB` endpoints plus `la≤ha` and `lb≤hb`. Constants provide both endpoints. The problematic positive/negative branch values provide only one useful endpoint; their missing opposite endpoints are exactly why the original transfer was unjustified. Requiring all four endpoints is conservative; it is not a representation extension.

Do **not** test a potentially overflowing `la+lb` in a rule body and assume failure means nonmatch. That evaluation behavior has not been established here, and textual condition order is not a guarantee against rule planning/reordering. The following guards use only globally safe threshold operations, including at MIN/MAX:

| Operation | Guard proving `L≥m` | Guard proving `U≤M` |
| --- | --- | --- |
| Add | `la ≥ m − min(lb,0)` | `ha ≤ M − max(hb,0)` |
| Sub | `la ≥ m + max(hb,0)` | `ha ≤ M + min(lb,0)` |

All threshold arithmetic is safe for **every** signed operand, regardless of evaluation order:

```text
m − min(lb,0) ∈ [m,0]       M − max(hb,0) ∈ [0,M]
m + max(hb,0) ∈ [m,−1]      M + min(lb,0) ∈ [−1,M].
```

Proof sketch: for Add's lower check, if `lb≥0`, underflow is impossible and the threshold is m; otherwise `la+lb≥m` is exactly `la≥m−lb`. For its upper check, if `hb≤0`, positive overflow is impossible and the threshold is M; otherwise `ha+hb≤M` is exactly `ha≤M−hb`. Sub follows by the same sign split: positive hb is the only underflow risk in `la−hb`; negative lb is the only overflow risk in `ha−lb`. With nonempty input ranges, `L≤U`, so these two checks also rule out the other endpoint's out-of-range direction. Only after both checks pass should the original endpoint action execute.

The source already uses total i64 `min`/`max` (`interval_analysis.egg:35–40`). The guards need no new engine primitive and avoid duplicating four sign cases. A shared eligibility relation can be justified if it owns this whole-range invariant and is used by both directions; a trivial forwarding helper is unnecessary. Actual syntax, scheduler behavior and tests still need concrete-diff review.

## Positive and negative boundary cases

These are mathematical test expectations, **not additional compiler executions**. “Reject” means decline the ordinary no-wrap transfer, never mark the source dead.

| Input interval rectangle | Candidate / actual counterexample or safe result | No-wrap guard |
| --- | --- | --- |
| Add `[1,M]+[1,1]` | Lower candidate 2; `M+1` wraps to m, below 2 | Reject; U=M+1 |
| Add `[m,−1]+[−1,−1]` | Upper candidate −2; `m+(−1)` wraps to M, above −2 | Reject; L=m−1 |
| Sub `[1,M]−[−1,−1]` | Lower candidate 2; `M−(−1)` wraps to m | Reject; U=M+1 |
| Sub `[m,−1]−[1,1]` | Upper candidate −2; `m−1` wraps to M | Reject; L=m−1 |
| Add `[0,M−1]+[1,1]` | Correct result interval `[1,M]` | Accept at upper boundary |
| Sub `[m+1,0]−[1,1]` | Correct result interval `[m,−1]` | Accept at lower boundary |
| Add `[m,M]+[0,0]` | Correct identity interval `[m,M]` | Accept both extrema |
| Sub `[m,M]−[0,0]` | Correct identity interval `[m,M]` | Accept both extrema |
| Add `[M,M]+[1,1]` | Exact wrapped result m; no-wrap profile declines a valid uniform-wrap result | Reject conservatively |
| Add `[m,m]+[−1,−1]` | Exact wrapped result M | Reject conservatively |
| Positive a with no hi, plus exact 1 | a=M remains possible; no ordinary lower bound 2 | Decline if missing, or reject with default hi=M |
| Negative a with no lo, minus exact 1 | a=m remains possible; no ordinary upper bound −2 | Decline if missing, or reject with default lo=m |
| Missing/symbolic opposite endpoint | Not a complete ordinary-range proof | Decline; preserve unknown |
| Sound proven-empty/Dead context | No reached value to approximate | No reachable-value conclusion or new global equality |

The first four rows refute all four naive rules even though the particular endpoint arithmetic `1+1`, `−1+(−1)`, `1−(−1)` or `−1−1` is itself safe. Merely guarding that one primitive operation does not repair the interval inference.

## Conservative choices and next review

1. **Smallest diagnostic localization:** delete only Add-lower or only Sub-upper in separate frozen controls, establish the corresponding case flips, restore exact bytes. This establishes necessity for those examples; it is not a soundness repair for the other two directions.
2. **Simple conservative family repair:** delete all four unguarded general transfers, allowing other valid constant/semantic mechanisms to operate. No overflow result should become Dead. Precision loss is explicit; no performance claim follows.
3. **Precision-preserving no-wrap profile:** guard both directions of both operations with the complete nonempty-range eligibility above. Keep the action only after the range proof. Ordinary safe ranges should retain bounds; one-sided/unknown or wrapping ranges should decline. This is the preferred bounded guard proposal if the concrete tests confirm the expected operation/schedule behavior.

For either repaired-source control, require the fixed oracle's two true endpoints and ten controls through the actual native pipeline, both Manual/Injective audits, and checks-off comparisons. Add meaningful transfer-level tests for all four unsafe directions, safe extrema, missing opposite bounds and Dead/unknown distinctions. Verify the threshold calculations themselves do not panic at any signed edge. An independent small-width exhaustive interval oracle can check the algebra if implemented; it must be distinct from the rule predicates and cannot replace the i64/native regressions. Preserve test-before-fix and exact original/restored source identities.

This contract assumes input bounds are sound; it does not repair other pre-existing arithmetic families or prove the entire current compiler correct. The U0 result, encoding-first conflict, one-rule causal controls, concrete guarded diff and final native regression remain separate evidence links. I stop here pending the owner's proposed repair diff; no compiler source or operational experiment was changed by this review.

## 2026-10-18: concrete guarded-diff consent

**Consent to the mathematical/source hunk; no binding correction.** Reviewed [guarded-interval-repair.patch](../../../benchmarks/local/eggcc-encoding-payoff/compiler/localization/guarded-interval-repair.patch), SHA-256 `819ece07070d55edef942c1d8e14af02770d3a29ad98a5f72ca0d6ff4b838e74`. It replaces the four independent one-sided rules with one full-range Add rule and one full-range Sub rule. Each matches all four endpoints, checks both input ranges nonempty, uses the two proven clamp guards, and sets both result bounds from that same witness tuple. It introduces no cached relation or new API.

The request described restored unfixed B1; my first read instead found the proposed guarded source already present, SHA-256 `ba4180adf9c460c061d4207124ed808810f4dcb91cc0dcccd021c46d2ab1c3a7`. The targeted live diff matches the supplied semantic hunk against the original `b18729ef499e2d5257e80f091468cf3d7f80686280a5c4d65e93766511a888dd`. The guarded hash was stable on the final source read. I did not apply or change the patch/source. This provenance observation does not weaken the patch review or claim I executed a corrected compiler.

The current B1 manifests point to `/Users/saul/p/wt/egglog-encoding/eggcc-encoding-payoff/egglog-experimental`. Targeted read of that engine's `egglog/src/sort/i64.rs` (base HEAD `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`) confirms:

- Lines 29–30 register `+`/`−` through `checked_add`/`checked_sub`.
- Lines 48–49 register `<=`/`>=` as predicates that succeed exactly when the comparison is true.
- Lines 57–58 register total ordinary i64 `min`/`max`.
- Full file SHA-256: `8857ed9088b8274455554a70c829c33d04b33c2683c1821e631132958d9fcb94`.

Consequently every clamp/threshold expression in the body has a defined in-range result, including before any nonempty/comparison filter is evaluated. On a matching row, the proof above puts both action endpoints inside `[m,M]`, so checked arithmetic succeeds. There is no dependence on whether an overflowing primitive in another rule body would be a nonmatch, and no dependence on textual primitive evaluation order. Signed MIN is used as an i64 literal in binary expressions, not negated through an unsafe unary arithmetic call. Static syntax and declared primitive names/arities agree; actual parser/type/schedule tests remain execution evidence owned by the compiler worker.

The Add hunk computes lower `la+lb` and upper `ha+hb`; the Sub hunk computes lower `la−hb` and upper `ha−lb`. Both nonempty checks are present. Both assignments share one complete eligible input tuple, so neither is an independent one-sided inference. No atomic transaction property beyond ordinary successful rule execution is required: each produced bound is separately sound and its arithmetic is defined. Backend failures remain errors, not successful partial semantic evidence.

**Alternative rows and normalization:** any matched numeric witness tuple is safe if each participating IntB is a sound bound. Multiple canonical IntB alternatives can cause extra matches; each match independently satisfies the same proof, so min/max bound merging preserves validity. Rules cannot manufacture a missing endpoint. Purely missing, symbolic/unresolved or exclusively Dead table values do not match the four IntB patterns. If a genuinely Dead class also retains numeric alternatives, a match concerns an infeasible context; this repair does not turn that into a new reachable-value fact or require constructor disjointness. It creates no Dead assertion. It cannot sanitize an unsound bound produced by another pre-existing rule; that limitation is unchanged.

**Conservatism:** requiring four explicit endpoints loses valid one-sided, identity-with-implicit-type-extrema and uniformly wrapping transfers. It can delay inference until bound normalization produces the required IntB rows. That is an intentional precision loss, not a new semantic failure. The comment's “requires ... no wrap” describes this chosen conservative profile; mathematically, the uniform-wrap exceptions above remain possible and are not claimed impossible. No broader modular analysis or global compiler correctness claim follows.

Read commands were limited to the supplied patch and earlier review note, targeted interval-source reads/diff/hash, the two manifest dependency-path entries, and the i64 primitive implementation. No builds, tests, imports, compiler/native calls or source edits ran. Remaining acceptance evidence is the guarded transfer tests and exact two-endpoint/ten-control native matrix, actual observer/manual controls, localization/source restoration records and final validation gates. This consent approves the proposed source semantics, not those pending empirical results.
