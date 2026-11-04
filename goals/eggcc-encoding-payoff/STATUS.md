# EggCC encoding payoff

Phase: **complete**.

The [explanation](report.md), [reference](reference.md),
[reproduction guide](reproduce.md), and machine-readable
[acceptance map](acceptance.json) establish two qualifying generated-runtime
results and retain the bounded negative outcomes.

QR7 is the strongest substantive-consumer injectivity-only result. Equal
quotient/remainder guards lead through marked `K7` cancellation and address
congruence to an exact local must-alias relation. An added bounded forwarding
bridge changes the fixed workload's process entry from 91 instructions and two
internal backward branches to 55 and zero. Baseline LLVM already removes the
executed load, so the supported account is earlier forwarding followed by loop
elimination, without a claim about a particular LLVM pass order. Hot
Encoding/U0 is `0.5505494231`, bootstrap 95%
`[0.5471011571,0.5575021727]`; the separate zero-trip control is
`0.9892585012 [0.9836729081,1.0003275615]`.

Parts32 is the strongest combined injectivity-and-disequality result. Marked
forward disequality, two lossless representation identities, and
sibling-guarded reverse congruence derive the exact high-child disequality and
apply only its contextual `Eq=false` fact. Across three workloads and two
independent sessions, Encoding uses 7.5% to 8.6% less elapsed time than U0; all
18 frozen speed gates, exact-output checks, and placebo-validity checks pass.
Workloads and sessions are not pooled.

The bounded search continued after the first payoff. P1 Pack32 is terminal by
portfolio supersession and retains a later fail-closed actual-host probe: 243
native outputs match, all 156 recorded queries reject, and no endpoint changes.
A1 same-region `NoAlias` is terminal after its permitted revision: its actual
import still fails conservatively, all 18 positive arms emit identical code,
and no timing is claimed. Fresh cycle-06 Codex and authenticated read-only
Claude Fable audits, followed by independent source validation, identify no new
bounded eligible family. This is a finite stop boundary, not a global
impossibility result.

The repository-root `make check`, isolated selected-engine check, and EggCC DAG
suite pass. Direct checks on r1 exposed QR7-local formatting and two DAG Clippy
findings; the four-hunk r2 cleanup fixes them. Root and DAG formatting now pass,
and the remaining one root plus two DAG Clippy diagnostics reproduce in
byte-identical U0 source. The isolated EggCC host remains explicitly non-green:
its root tests reject the same 13 unaccepted dependency-retarget snapshots after
all test bodies pass. The r2 matrix reproduces all 37 cases and 177 outputs with
identical executed content; the timed r1 files remain the sole QR7 performance
authority. Only `raytracewithscreen` was filtered, the ordinary raytrace fixture
passed, the benchmark memory guard remained unset, and no snapshot was accepted.

No commit, push, pull request, proof work, paper edit, or destructive cleanup
was performed. Dirty author work and all prior and frozen evidence remain
preserved.
