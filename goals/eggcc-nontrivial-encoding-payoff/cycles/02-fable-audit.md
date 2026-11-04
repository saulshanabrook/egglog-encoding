**Bottom line.** The live same-mask candidate is sound as written, and its hot-loop export now reproduces the manual fold byte-for-byte in entry code. But the ablations do not show that generic disequality plus injectivity is *materially* needed: the host pre-filters the exact Mask/Mask and Shift/Shift shape, so the private graph only confirms a fixed two-step pattern that a single contextual rewrite rule would also produce. No timing has been taken, the confirmation design has gaps, and the benchmark corpus contains no trigger for the law. Below, "confirmed" means I read it in source or receipts; "proposal" means untested.

## 1–3. Audit of the live candidate

**Soundness (confirmed facts).**

- Translation is context-exact. Parent operands translate in the parent scope; child operands go through `project(input, index)` only when the Get's Arg context equals the recorded child context (`scoped_reasoning.rs:264-285`). Branch contexts are built the same way the compiler builds them (`add_context.rs:273-274`).
- Leaves are opaque. Distinct constants, slots and proven constants become `Leaf_i(ThisScope)` with no asserted equalities. Mask is unmarked; only `Shift_k` is `:injective` (lines 417-431). The private graph never receives main-graph unions.
- The loop induction (lines 113-158) admits a slot only from a literal initial projection in the initial tuple's own context plus exact same-index passthrough through both If arms. Arithmetic, including `slot+0`, is Unknown; nested loops abort. The four unit tests, including the two induction negatives, passed in the `focused-invariants` receipt. The earlier `focused-scoped` receipt shows two failures; treat it as the red run, not as evidence.
- Export unions the exact child-context `Eq` term with a child-context `Const false` (`lib.rs:262-276`). The consumer is the existing false-If rule at `interval_analysis.egg:284-290`. Substitution rules rewrite `Const` leaves into new contexts (`subst.egg:68-73`), so the fact migrates with any substituted copy of the branch. That is sound for this law because the fact is schema-valid for every instantiation of the same parent predicate. It would *not* be automatically sound for a law whose truth depends on a slot's value, which is exactly what pack32's bounded domain would need. Flag this before any value-dependent law is exported.
- Bottom blocks export; errors are swallowed into receipts and block export (lines 444-447, 542-547). Conservative.

**Two soundness-adjacent observations.** First, the induction is mathematically unnecessary for the live law: `x+k = y+k ⇒ x = y` holds for any `k`, literal or not. It exists only because the engine's forward rule is whole-constructor injectivity and binary `Add` is not jointly injective. The induction therefore adds attack surface to obtain a fact the law never needed. Second, the `ChildKnown` query (lines 460-466) ignores whether the masks match; it is diagnostic only, but a reader of the receipts could mistake it for the guarded inference.

**Causal audit.** The matrices are internally consistent:

| Family | Off, SeedOnly, AnnotationOff, QueryOff, BridgeOff | Manual, Encoding | U0 |
|---|---|---|---|
| cold entry asm | `423e…` | `2962…` | not in matrix |
| hot entry asm | `51ae…` | `bea1…` | `51ae…` (untouched binary) |

The hot Encoding entry code is instruction-for-instruction identical to the pilot's manual fold. However:

- SeedOnly, QueryOff and BridgeOff are no-ops *by construction* (lines 450, 468, 473). They test plumbing, not logic. AnnotationOff is the only law ablation, and it correctly shows child disequality without the target.
- The host gates at lines 528 and 537 accept only a Mask/Mask parent and a Shift/Shift target. After that gate, the engine's remaining work is: check the two mask leaves coincide and the two shift indices coincide. The Rust `manual` closure reproduces this in about thirty lines, and a ten-line contextual `.egg` rule would too. So the evidence establishes the derivation path, not material necessity. This fails the goal's "not a single constructor-specific rule" bar as the facts are written.
- Missing control: a hand-written `.egg` rule arm inside EggCC (the fair "existing or manual comparison" the plan asks for) rather than a Rust closure. Missing positive cases: any input where the chain needs more than one reverse step or consumes a main-graph equality.

**Measurement audit.** The frozen design (`confirmation-design.json`) is reasonable: 32 cycles, four rotating order rows, warmups, paired median ratio with a seeded bootstrap, output checks per sample, no re-creation of the output directory. Gaps that could invalidate a claim:

1. Encoding and Manual binaries differ in SHA although entry code matches. Assert that `optimized.bril` is byte-identical between Encoding and Manual, and between B1 and U0, or the ratio can reflect layout rather than the fold. Likewise require the Encoding/Manual interval to contain 1 as a placebo check.
2. The removed `cmp`/`csel` shifts the loop start address (`0x5668` vs `0x566c`). A two-instruction, off-critical-path delta of about 2% is plausible, but alignment is an uncontrolled confound. Record loop alignment, or confirm on x86.
3. Compile time is excluded (`compile_time_included: false`). The analysis builds three fresh egraphs per compile. The accepted facts require compile-time reporting even when runtime is the claim.
4. Single synthetic workload. `bitand` appears in no file under `benchmarks/passing`; the only use in the tree is `tests/passing/small/lowbit_br.bril`. Run the full suite under Encoding and show identical emissions as the neutral-result control.
5. Confirm the `--with-context` flag matches the production benchmark configuration. The supplement shows the candidate is inert without context, so a no-context default would make the baseline comparison non-representative.
6. The negative-fixture supplement (`supplement.py`) has no retained receipts or results file. Its seven real-compiler negatives have not been shown to pass.

## 4. Remaining hypotheses

The corpus is barren for equality-sort disequality: no `bitand`, and quotient/remainder shapes (`mod_inv`, `euclid`, `sum-divisors`, `digital-root`, `adler32`) never compare two key pairs. Everything below is therefore synthetic-triggered unless noted.

**H1. Cancellative binary Add replaces the induction (new, engine law).** Producer: same host; law: `x≠y ∧ k=k′ ⇒ x+k ≠ y+k′`, a sibling-guarded *forward* rule for unmarked binary `Add`/`Sub`. Consumer: unchanged false-If. Trigger: the `nonliteral-loop-initial` fixture in `supplement.py`, where `7` is a runtime argument and the current candidate must not fold. Cheapest falsifier: U0 versus one-line manual fold native diff on that fixture. Why not a single rule: the same critique as S2 applies; its value is removing the induction surface, not a new payoff.

**H2. Pack32 bounded binary cancellation (retained P1).** Law: `P(a,b)=P(c,d) ⇒ a=c ∧ b=d` on `[0,2^32)`, then equal-sibling reverse, then marked forward. This is the only remaining chain where a dynamic sibling is *produced* by an earlier cancellation, which congruence closure alone cannot do. Falsifier already run (native retains `cmp`/`csel`). Gap: `interval_analysis.egg` has no `Bitand` or `Shl` transfer, so the domain premises the law needs cannot currently be established by the host.

**H3. Live-cell NoAlias chain (retained A1).** Three generic steps feed the existing commute rule at `mem_simple.egg:71`. Gap: a new guarded loop-transport rule and a host-proved `Cell` wrapper. Strongest manual endpoint among the retained families.

**Non-qualifying bug probes worth one run each.**

- `rec_to_loop.egg:142` hard-codes `Const 0` for the accumulator when zero recursive steps occur, but `Accum-Bop (Mul) 1 (Mul)` needs 1. Commutativity (`canonicalize.egg:5`) and `swap-if` make `fact.bril` and `recfact.bril` plausible matches. Falsifier: run `fact.bril` with argument 0 and `recfact.bril` with 1 through U0 optimize and interp. Expected 1; a match would print 0.
- `hackers_delight.egg:100` returns `n/(n&-n)`, which is 1 at signed MIN while the loop yields −1. Falsifier: the lowbit loop fixture at `-9223372036854775808`.
- `select.egg` converts pure branches to `Select`, and `purity_analysis.egg:10` marks `Div` pure, so a zero-guarded division becomes an unconditional `sdiv`. The interpreter evaluates Select lazily, so only the native run can expose it. Whether the maintainers treat division by zero as undefined decides if this counts.

## 5. Challenges and rejections

- **QR7 (retained Q1): reject as encoding-qualifying.** With `R(x)=x−7Q(x)`, the peephole `a+(b−a)=b` gives `x=7Q(x)+R(x)`, and congruence then yields `x=y` from equal quotients and remainders. The marked `K7` is decorative. Keep it only as a phase-ordering optimization lead.
- **H1 challenge:** identical endpoint to S2; a per-argument injectivity annotation is engine work, not an EggCC result.
- **H2 challenge:** LLVM already cancels the `+7`; without host bounds the law is unavailable; the "equal sibling from cancellation" step is the sole non-trivial part.
- **H3 challenge:** the loop transport is a single new rule, and the wrapper's in-bounds and liveness premises come from the host, not the encoding.
- **Rejected weak variants:** odd-multiplier cancellation (LLVM folds it), S1 and any equality-transports-disequality chain (LLVM byte-identical), collatz parity and fizz-buzz divisibility (ring or CRT reasoning, not equality-sort), Switch or literal-Eq disequality (primitive), distinct-allocation NoAlias (primitive), Parts32 (unsupported `Shr`), print-trace audit (no producer), loop-invariant hoisting of guarded `Div` (closed: `body_contains.rs:13-14` treats If arms as captured bodies, so they are never loop-body subexpressions), and context-constructor injectivity audits (no producer).

The three bug probes above are the cheapest next actions, but none would satisfy the encoding requirement as the facts stand. For the live candidate, the decisive next step is to remove the shape gates and add a fair `.egg` rule arm before spending the 32-cycle confirmation.
