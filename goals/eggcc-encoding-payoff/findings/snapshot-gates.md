# B1 snapshot-gate attribution

The final B1 `make test` retained 13 pending root snapshots after 36 root-library tests and 2,421 integration trials completed; the snapshot failure stopped Make before the standalone DAG suite. No accepted snapshot changed. The retained pending files and hashes are indexed by [`adapter-failure-and-snapshots.json`](../../../benchmarks/local/eggcc-encoding-payoff/compiler/final-gates/commands/make-test/adapter-failure-and-snapshots.json).

## Exact-current causal control

All 13 differences belong to the E1 retarget/lock package, rather than the observer plumbing or the guarded Add/Sub repair.

The finite control reconstructed EggCC `a0bbec127f83249074a46af3fd6f6126c90fe0fb` and applied only the four-file B1 handoff patch. Its 771-file source authority has SHA-256 `b44148750755ecf1fd9bd43975496b333ca222c005a753afbd209525805c72af`; it binds handoff patch `b92c8f39273702f466da4217fad80904b91350d352857cfd5a3cf9cd013b8747`, handoff source authority `bb1bd4c546fae2413f2f5a51dd634b3b7b303ae3f6069af84d87939364315f1c`, and the same 969-file E1 authority `97618f533dfb36f038432cab4517cff78a855eb23caf1ea100f3e27e35f44fe2`. It contains neither observer plumbing nor the interval repair.

Each exact-name command selected one trial and exited 101 solely on its snapshot assertion. All 13 complete `.snap.new` files equal the corrected live B1 files byte for byte. [`results.json`](../../../benchmarks/local/eggcc-encoding-payoff/compiler/final-gates/handoff-control/results.json), SHA-256 `40c4a7ec6b2bf5c12e3774e6cef5efd6d62fe8ab30d24dc7dedc8fed0c183de5`, binds the inputs, accepted goldens, actual files, per-command receipts, and equality checks. This exact-current result supersedes the older `15ee...` controls for causal attribution. It does not isolate a particular E1 implementation change from the rest of the retargeted dependency package.

Untouched-main U0 is the complementary baseline: its fresh `make test` passed 31 root-library, 2,421 integration, and 64 DAG tests with no pending or unreferenced snapshots. That result and its unchanged 771-file source boundary are recorded in [`admission.md`](admission.md#subsequent-final-u0-gates).

## Semantic review of the 13 bodies

The `assertion_line: 36` addition is snapshot metadata. The table classifies the changed Bril bodies separately. “Runtime checked” means `tests/files.rs:23-31` compared original and optimized interpreter output for the fixture's declared arguments before reaching the snapshot assertion.

| Family and configurations | Source argument | Runtime checked by this gate |
|---|---|---|
| `branch_duplicate_work`: optimize, sequential | Equivalent for all inputs: the new body hoists the same wrapping `x + x` computed in both branches. | Optimize at `x=1`; sequential not checked. |
| `branch_hoisting`: no-context | **Confirmed separate regression.** The new body removes the `n == 0` choice and always advances the output recurrence by 2. It agrees for the declared `n=0`, but at `n=1` source/accepted execution prints `3 * 499 = 1497`, while optimized exact-emitted execution prints `2 * 499 = 998`. | Independently checked at `n=0` and `n=1` by interpretation and native execution; see [branch-retarget.md](branch-retarget.md). |
| `if_invariant_do_pull_out`: optimize, sequential | Equivalent under wrapping i64 arithmetic. On `x>0`, `abs(x)=x`; on `x<=0`, `2*abs(x)-x=3*abs(x)` modulo 2^64. The sequential result also reuses an already computed `abs`. | Optimize at `x=20`; sequential not checked. |
| `if_invariant_dont_pull_out`: sequential | Equivalent. The positive numerator changes from `2*abs(x)` to `3*abs(x)-x`, equal when `x>0`; the other branch reassociates `x+abs(x)+2*abs(x)`. Divisors, including division-by-zero behavior, are unchanged. | Not checked. |
| `loop_strength_reduction`: optimize | Equivalent for this input-free program: the accepted body emits four consecutive multiples for 75 iterations; the new recurrence emits one for 300 iterations. Both print `0, 5, ..., 1495`. | Checked. |
| `loop_with_mul_by_inv`: optimize | Equivalent by the loop invariant `g = 5*i (mod 2^64)`; accumulator, condition, and iteration count agree. | Checked at `n=4`. |
| `pull_out_small`: optimize, sequential | Equivalent for all inputs: both branches print 20 and then wrapping `5*x`; the new body hoists that multiplication. | Optimize at `x=20`; sequential not checked. |
| `strong_loop`: optimize, sequential, no-context | Equivalent by the recurrence invariant `y = 7*i (mod 2^64)`, initialized by `i=3`, `y=21`; condition, prints, and accumulator agree. | Optimize at `n=3`; sequential and no-context not checked. |

The arithmetic arguments use the pinned Bril interpreter contract: `brilirs/src/interp.rs:345-366` implements wrapping Add, Mul, Sub, and Div and rejects a zero divisor. All affected conditional bodies evaluate the same initial `abs`, so their behavior at `i64::MIN` is shared.

## Harness gap and completed follow-up

`Run::new` initializes `interp` to `None` (`src/util.rs:367-379`). Ordinary Optimize configurations replace it with `Interp` (`src/util.rs:501-527`), while sequential and no-context configurations retain `None` (`src/util.rs:529-539`). Consequently, six ordinary Optimize mismatches received a declared-input interpreter comparison, while all five sequential and both no-context mismatches did not.

The follow-up executed disposable `branch_hoisting` fixtures at `n=0` and `n=1` in the exact handoff-only retarget. At `n=1`, source interpretation and source native execution print `1497`, while no-context optimized interpretation and exact emitted native execution print `998`; at `n=0`, both sides print `998`. All twelve commands exit 0 and the optimizer completes passes 0/1/2. The retained result SHA-256 is `3287f42a9947db73b9f1be97c9e294913450706bd262b7bbfb4c49af603e582d`. This confirms a separate E1-retarget regression; it does not pre-exist in U0 and does not count toward the qualifying Add/Sub result. The other 12 classifications rest on the explicit algebraic and loop invariants above; snapshot acceptance remains a separate owner decision.
