Audit complete. Everything below was checked read-only against the listed evidence files and the pinned U0 tree. Tags: **RF** = retained fact read from evidence, **SV** = conclusion I validated against source, **P** = proposal.

## 1. Current-result audit

**QR7 passes the mechanism and measured gates as written, but two framing points are overstated and its validation gate is not green.**

- **Chain (SV, `qr7-integration/scoped_qr7.rs:540-669`).** Seeds are the two branch guards on unmarked `Q7`/`R7`, which carry primitive 7. Representation identities tie marked `K7` to unmarked `Pair`. Congruence gives equal keys, the single generic step is `K7` cancellation to `x = y`, and congruence on unmarked `Addr` gives equal addresses. No `disequal` or `known-disequal` is used. The injectivity-only label is accurate.
- **Consumer (SV, `eggcc-candidate-r1.patch:544-554`).** The consumer is an added `mem-simple` rule gated by `Qr7ForwardEnabled`. Its actions copy the right-hand side of U0's store-forward rule at `mem_simple.egg:107-113`, but that pre-existing rule never fires. Ledger row 12 still names "existing same-address mem-simple store forwarding"; row 42 correctly says "added bounded bridge". Use the row 42 wording everywhere.
- **Controls (SV).** `PrimitiveOnly` and `SeedOnly` share one code path at line 543, so the primitive null is argued from `K7` having no primitive fields rather than executed. `TransportOff` only gates export at lines 650-651. The report and the timing verification both disclose this.
- **Phase ordering is the whole payoff (SV, `final-r1/matrix/positive/u0/native/program.asm:5364-5433` vs `encoding/.../program.asm:5349-5381`).** Baseline `process_main` has no load or store in either loop. It contains `cmp x19, x20` at 0x1000057d4 guarding the remainder exit, which means LLVM itself reduced the remainder guard to `x == y`, knew the pointers alias, and forwarded the load. The winning binary computes the closed form of the sum. Consequences: LLVM did not lack the K7 law; the win is LLVM's exit-value rewriting seeing the recurrence before GVN would have exposed it; the complexity drops from linear to constant, so the percentage is a function of the iteration count against process startup. Any summary saying QR7 "removed a hot load" or that LLVM needed injectivity is wrong. Robustness to other LLVM pipelines is untested.

| QR7 cell | Ratio | Bootstrap 95% |
| --- | ---: | ---: |
| hot n=10M, Encoding/U0 | 0.55055 | [0.54710, 0.55750] |
| neutral n=0, Encoding/U0 | 0.98926 | [0.98367, 1.00033] |

- **Validation (RF, `validation-r1/independent-attribution.md`).** Status is `attributed_without_waiving_failed_validation`: root release run exits 1 with 13 unaccepted snapshots, `make nits` exits 2 on an inherited Clippy diagnostic, the DAG run passes 70 tests including the six QR7 tests.

**Parts32 passes all three mechanism criteria and the measured gate; its validation state matches QR7's.**

- **Chain (SV, `parts32-integration/eggcc-final.patch:1024-1035,1082`).** `Low` and `High` are unmarked and carry the primitive mask and divisor, `Parts32` is marked, `Pair` is unmarked. Seeds are `(disequal x y)` and `(union lx ly)`. Marked forward disequality, representation identities, then sibling-guarded reverse congruence through `known-disequal?` yield the high-child disequality. Export is the single union at patch line 561 on the exact contextual `Eq`.
- **Consumer (RF, `validation.json`).** The false-If rule at `interval_analysis.egg:284-290` was gated and shown non-essential; extraction and LLVM consume the constant predicate. The causal endpoint is the exact union, as the report says.
- **Measured (RF, `timing/independent-verification.json`).** `all_session_speedup_gates_passed`, `all_sessions_passed`, and `placebo_validity_passed` are all true. The six Encoding/U0 cells span 0.91398 to 0.92504. The win is LLVM vectorization after the impossible arm disappears, and the screen shows LLVM had kept the `(x xor y) < 2^32` test, so here the law genuinely exceeded the backend. Nothing in the report is overstated; the compile-time diagnostic is correctly non-acceptance.
- **Validation (RF, `validation.json`).** Root `make test` exits 2 with 13 pending snapshots byte-identical to the retarget control, including `files__branch_hoisting-optimize-no-ctx.snap.new`; Clippy exits 101 on two U0-inherited lints with zero new sidecar warnings.

**Cross-cutting gap (SV plus RF).** No qualifying row has a green facts.md line 18 gate. Every integration attributes 13 emitted-program changes to the egglog dependency retarget, with a dependency-only control that byte-matches. The attribution is sound, but the retarget changes compiler output and carries a known no-context `branch_hoisting` regression. The acceptance map needs an explicit recorded decision: either classify these as integration-introduced defects under line 13 and mark the gate "unmet, attributed", or repair the retarget before calling any row qualifying. Same-mask, Affine, Route, and Sort are consistent with the ledger; Affine additionally has 17 new sidecar Clippy diagnostics.

## 2. P1 and A1 lifecycle

**P1 Pack32: an evidence-backed terminal supersession is justified.**

| P1 element (pack32-screen) | Covered by completed integration |
| --- | --- |
| Law: `(a<<32)+b` injective only for `0<=a,b<2^32`; needs a loop range invariant through the `bitand mask` updates at `pack32-screen/source.bril:73-80` | Affine, Route, Sort are total binary keys with marked cancellation (rows 33, 37, 38). Parts32 is the inverse 32-bit decomposition, total and measured (row 41) |
| Step 1: binary cancellation gives `a=c`, `b=d` | Affine, Route, Sort step 1 |
| Step 2: reverse congruence on the packed key with equal sibling gives `a!=b` | Affine, Route, Sort on unmarked `Add`; Parts32 on unmarked `Pair`. The reverse law never uses the mark, so firing it on the marked key is wiring, not a new law |
| Step 3: marked fixed translation by 7 | Same-mask `Shift7` (row 29, measured); Affine `OddMul3` |
| Consumer: exact `Eq=false`, then false-If or extraction | All five integrations; measured twice (same-mask, Parts32) |

The only residue is that P1 would time a binary-cancellation hot loop and would need a new bounded-domain invariance analysis. That is extra cost with no new mechanism. Recommend terminal row `closed_superseded_by_completed_mechanisms` citing rows 29, 33, 37, 38, 41 and retaining the screen as a native opportunity.

**A1: one bounded probe remains eligible, sound, materially distinct, and cheaper than the ledger records.**

- **U0 memory rules (SV).** `NoAlias` is declared at `mem_simple.egg:8`, pushed into If at 11-18, produced only by interval rules at 20-58, symmetrized at 60-62, consumed by commute at 71-81, followed by store-forward at 107-113. There is no loop rule. `mem-simple` saturates in every `helpers()` at `schedule.rs:96`, and the first pass runs before loop inversion, which subsumes the original loop at `ivt.egg:184`.
- **Soundness backbone (SV).** `utility/context_of.egg:15-21` panics if one e-class has two contexts. A fact asserted on branch-local terms therefore cannot migrate to parent-context terms by merging. This underwrites both the QR7 export and an A1 export.
- **Retained graph (RF, `alias-screen/reachability/transport.json`).** Seed pair 232/236, both-invariant loop args 272/274, If args 289/291, consumer load 297 over writes 296 and 295, replacement value 293. The receipt records that neither the engine nor compiler rules were executed.
- **Cost reduction (SV).** The QR7 sidecar already performs the loop and If transport on the host: `transport` at `scoped_qr7.rs:128-192`, `resolve_slot` at 222-238, `address` at 385-423, with export on load-site local terms (`translated_offsets: "Slot(4),Slot(3)"`). A1 can export `(NoAlias write_local load_local)` on the 291/289 classes the same way. The two recorded missing premises, the guarded loop transport rule and the one-shot lifetime, collapse to the already-accepted QR7 design. No U0 rule changes, and the consumer is untouched U0 rather than an added bridge.
- **Distinctness.** It is the only lead that consumes a disequality in a memory consumer, it needs reverse congruence on unmarked `Mask` plus marked forward steps on `Shift` and `Cell`, and the baseline native loop still executes store, store, load, so its payoff is not purely the indvars ordering effect that QR7 depends on.
- **No falsifying source fact.** The main risk is extraction choosing a substituted loop copy; unions made in the first helpers pass propagate through `Subst` congruence exactly as in QR7. The literal mask 1 is acceptable because the sibling equality is still congruence over the equality-sort parent.

Cheapest decisive probe (P): clone `scoped_qr7.rs` to a new sidecar. Recognizer: a `Load` whose state is a `Write` to the other pointer, an ancestor `InIf(false, Eq(Bitand(a,m), Bitand(b,m)))` with `a`, `b` root slots and one `m`, addresses resolving to `PtrAdd(Get(Alloc,0), Add(slot,k))` with equal `k` and one allocation, bounds guard, live fragment. Private NEE graph: `(disequal (Mask a m) (Mask b m))`, marked `Shift_k`, marked `Cell`, saturate, query `known-disequal?` on the cell pair. Export `(NoAlias write_local load_local)` into the initial program. Controls: SeedOnly, PrimitiveOnly, Manual, reverse-off with exact `a != b` rescue, shift-mark-off and cell-mark-off with exact rescues, query-off, bridge-off, consumer-off via a shadow relation, plus different-mask, different-shift, equal-mask-branch, two-allocation, in-loop free, and changed-slot negatives. Falsifier: the Encoding emission still contains the load, or no `commute write then load` and `store forward` events appear, or native code matches U0. Only after a native difference, run a frozen timing design shaped like QR7's.

## 3. Fresh source-backed hypotheses and stop boundary

**No new eligible lead.** The search was a census of every rule in the running schedule that consumes a semantic relation between equality-sort terms (SV).

- Disequality consumers: only the `NoAlias` commute rule. Every `(!= ...)` in U0 rule bodies is a type, context, or index check, an error-checking panic, CICM's e-class non-identity at `conditional_invariant_code_motion.egg:17`, or the disabled `memory.egg:344`.
- Equality consumers: the four must-alias rules at `mem_simple.egg:98-127`, `Sub x x` at `peepholes.egg:24-30`, `Select p x x` at `peepholes.egg:47`, and Boolean-constant predicates for If and loops. QR7 covers must-alias; the other three must-alias rules need the same producer; LLVM's equality propagation already covers the two peepholes; Boolean endpoints are the measured `Eq=false` family.

| Direction examined | Reason rejected |
| --- | --- |
| Interval refinement in the false branch of `Eq(x, const)` | Decided by comparing primitive bounds and the constant; fails the primitive null |
| Direct `Eq(i,j)=false` to `NoAlias(p+i, p+j)` | One-step contextual rewrite; A1's Mask and Shift chain is the qualifying form of this idea |
| Duplicate-load, shadowed-write, Select-arm merge | Same QR7 producer; weaker or LLVM-covered consumer |
| `hackers_delight.egg` lowbit, loop strength reduction, IVT, unroll, push-in, CICM | Structural or constant-driven; no equality-sort relation is consumed |
| Switch branch pruning | No Bril producer of multi-way `Switch` |
| Compile-time speedup | No measured bottleneck in source; brainstorming only |

**Confirmed nonqualifying defect (SV).** `Shl` and `Shr` are accepted at `src/rvsdg/to_dag.rs:238-239`, interpreted at `interpreter.rs:261-262`, typed in Rust at `schema_helpers.rs:839-840`, but absent from `bop-of-type` at `type_analysis.egg:283-296`, so the egglog type analysis never gives them `HasType`. No U0 test or benchmark uses either op. This is the gate that stopped the direct-shift Parts32 attempt in row 18. It is visible without the encoding, so facts.md line 14 excludes it; report it upstream separately.

**What remains before the finite search can close.** First, run the single A1 probe above and record its outcome. Second, add the P1 terminal row. Third, record an explicit full-validation decision for every qualifying row. Fourth, fix the QR7 wording about the added bridge, the LLVM-derived equality, and the size-dependent percentage. Nothing here supports a claim of global impossibility.
