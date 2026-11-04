# Acceptance review: EggCC injectivity and disequality payoff

Overall status: **passed**. The authoritative 14 accepted facts are in
[`facts.md`](facts.md); the machine-readable authority is
[`acceptance.json`](acceptance.json). Thirteen facts pass and the compiler-bug
route is not applicable because the qualifying results are measured
generated-program speedups.

QR7 is the strongest substantive-consumer, injectivity-only result. Parts32 is
the strongest result that requires injectivity and disequality together. Both
qualify independently; Parts32 also satisfies the stated preference for a
combined case. Neither result claims a compiler bug or unique logical power
over its faithful multi-rule Manual comparator.

## Qualifying results

### QR7: injectivity reaches a memory consumer

For signed i64 values, the fixed-divisor key

```text
K7(v) = (trunc(v/7), v - 7*trunc(v/7))
```

is lossless. Equal quotient and remainder guards therefore give equal keys;
generic cancellation of marked `K7` gives `x=y`; and ordinary same-region
address congruence gives the exact local address equality. Only a
`Qr7MustAlias` relation escapes the private graph. An **added bounded bridge**
then performs store forwarding. This is not execution of U0's untouched
same-address rule, and no disequality contributes.

All causal knockouts return to baseline code, both exact intermediate rescues
recover the winning code, and Manual and Encoding have identical winning
instructions. The retained matrix has 37 compiler cases and 177 exact native
checks. The actual process entry changes from 91 instructions with two internal
backward branches to 55 with none. Baseline LLVM already removes the executed
load, so the supported explanation is earlier forwarding followed by loop
elimination in the fixed backend. The evidence does not identify a particular
LLVM pass order.

The independently confirmed hot Encoding/U0 ratio is `0.5505494231`, with
complete-block bootstrap 95% `[0.5471011571, 0.5575021727]`: 44.9451% less
fresh-process elapsed time for the fixed constructed workload. The zero-trip
control is `0.9892585012 [0.9836729081, 1.0003275615]` and has no speedup
requirement. See the [QR7 report](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/report.md)
and [independent timing verification](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/timing-r1/independent-verification.json).
The retained samples directly measure the frozen r1 Mach-O files. The later r2
validation cleanup has identical executed content but different complete file
hashes, and carries no separate timing claim.

### Parts32: the combined encoding

Parts32 decomposes a signed i64 word without information loss:

```text
low(x)  = x & 0xffffffff
high(x) = (x - low(x)) / 2^32
Parts32(x) = Pair(low(x), high(x)).
```

For one exact nested branch, the host supplies `x!=y`, `low(x)=low(y)`, and
the two representation identities. The private graph derives:

```text
x != y
  => Parts32(x) != Parts32(y)                 marked forward propagation
  => Pair(low(x),high(x)) != Pair(low(y),high(y))

low(x) = low(y)
  => high(x) != high(y)                       sibling-guarded reverse congruence
  => Eq(high(x),high(y)) = false              exact contextual export
```

The primitive-only arm preserves the graph and seeds but finds no dynamic
equality-sort witness. Removing the mark, identities, reverse step, query,
bridge, or final application restores baseline code; the exact high-child
rescue and faithful Manual arm restore the optimized code. All 200 retained
native checks and their interpreter/oracle comparisons pass.

Across three workloads and two independent sessions, Encoding/U0 ranges from
`0.91398` to `0.92504`, or 7.5% to 8.6% less elapsed time. All 18 frozen speed
comparisons have an upper 95% bound below `0.99`, every output is exact, and
the prospectively defined placebo checks pass. Workloads and sessions remain
separate. See the [Parts32 report](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/report.md)
and [independent timing verification](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/timing/independent-verification.json).

## Search and lead closure

The bounded lead and search lifecycle is closed. The append-only
[ledger](../eggcc-nontrivial-encoding-payoff/hypotheses.jsonl) records the
qualifying QR7 and Parts32 results, supporting examples, and terminal lead
dispositions. The final fresh [Codex audit](../eggcc-nontrivial-encoding-payoff/cycles/06-codex-audit.md)
and authenticated read-only [Claude Fable audit](../eggcc-nontrivial-encoding-payoff/cycles/06-fable-audit.md)
produce no new bounded eligible family after independent
[source validation](../eggcc-nontrivial-encoding-payoff/cycles/06-fable-validation.md).
The source validation corrects unsupported exact LLVM-pass, lifetime-proof,
and exhaustive-census claims; none of those claims is used for acceptance.

P1 Pack32 remains terminal by portfolio supersession. Its later actual-host
probe is also retained: 14 positive arms and 154 positive native checks pass,
but all 36 positive boundary queries reject, zero witnesses export, and every
positive arm has identical emitted and native process-main hashes. Across all
positive and negative rows, 243 native outputs match and all 156 recorded
queries reject. This is a fail-closed attempt, not a refutation or a payoff.
See the [Pack32 report](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/report.md).

A1 same-region `NoAlias` is terminal under its initial attempt plus one
evidence-driven revision budget. The revision still rejects admitted auxiliary
rows before a positive certificate. The complete host library result is 67
passes and three new A1 failures; 31 interpreter pairs and 233 native checks
pass only because all actual modes fail closed. All 18 positive arms emit the
same code, retain one load and two stores, and justify no timing claim. This
does not refute the scoped law or prove another implementation impossible. See
the [A1 report](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-integration/actual-r0/report.md).

## Validation boundary

The repository-required root `make check` passes: 1,979 Python tests and 1,502
Rust tests/doctests pass, with two Python snapshots and six ignored Rust tests.
The isolated selected engine's complete check passes 233 Python tests and 1,804
Rust tests/doctests, with two Python snapshots and six ignored Rust tests. The
isolated EggCC DAG suite passes all 70 tests, including six QR7 tests.

The first final-validation pass exposed QR7-local formatting and two DAG Clippy
findings. A four-hunk r2 cleanup changes only `scoped_qr7.rs`; root and DAG
formatting now pass, and strict DAG Clippy has zero QR7 diagnostics. The one
remaining root Clippy diagnostic and two remaining DAG Clippy diagnostics all
reproduce at the same sites in byte-identical pinned-U0 source. The isolated
EggCC host therefore remains **not green**, while no candidate-specific
formatting or lint defect remains in r2.

The cleaned r2 host root command passes 31 unit and 2,420 file-test bodies, then
exits 1 on the same 13 unaccepted snapshots; all 13 are byte-identical to r1 and
the dependency-retarget control. No snapshot was accepted. The r2 matrix also
reproduces all 37 cases and 177 native outputs, with equal semantic records,
optimized Bril, instruction bodies, and loadable Mach-O sections. Whole-file
Mach-O hashes differ only in non-executed UUID, temporary linker metadata, and
the derived signature.

This satisfies the accepted correctness fact because the repository-required
suite and selected engine suite pass, registered mechanism/native checks pass,
and every host failure is retained and independently attributed rather than
accepted or silently waived. It is not a merge-readiness claim. The exact
receipts, stream hashes, counts, and attribution are in the
[r2 validation summary](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/final-summary.json).

The benchmark memory guard was absent from every reviewed receipt. The heavy
`raytracewithscreen` test was filtered as requested, while the ordinary
`raytrace-test-benchmark` fixture ran and passed; ordinary work continued under
host memory pressure. No snapshot was accepted, and no commit, push, pull
request, proof work, paper edit, or destructive cleanup occurred.
