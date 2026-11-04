# QR7 nits cleanup validation r2

This validation copied the retained QR7 r1 host source from
`/private/tmp/eggcc-qr7-candidate` to
`/private/tmp/eggcc-qr7-candidate-nits-r2`, excluding build output under
`target/` and the 13 generated `*.snap.new` files. The
[`source-manifest-before.json`](source-manifest-before.json) manifest records all
774 copied entries. The cleanup changed only
`dag_in_context/src/scoped_qr7.rs`; the complete four-hunk delta is
[`nits-r2.patch`](nits-r2.patch), and
[`source-manifest-after.json`](source-manifest-after.json) records the resulting
774 entries.

The four edits are nonsemantic at the Rust source level: two are the exact
changes requested by `rustfmt`, one introduces a function-local `ManualRow` type
alias for the Clippy-flagged tuple, and the test-only expression `5 % 7` becomes
`5`. The source manifest still matched byte for byte after the nits, DAG test,
and build commands, and that validation phase generated no `*.snap.new` files.

| Check | Result |
| --- | --- |
| Root `cargo fmt --check` | pass |
| DAG `cargo fmt --check` | pass |
| DAG `cargo clippy --tests -- -D warnings` | exit 101 on two inherited U0 diagnostics; zero diagnostics in `scoped_qr7.rs` |
| Focused release tests matching `qr7_` | 6 passed, 0 failed |
| Full DAG `cargo insta test --release --unreferenced=reject -- --skip raytracewithscreen` | 70 passed, 0 failed; no snapshots to review |
| Full root suite with the same skip | 31 unit and 2,420 file tests passed; 1 filtered; exit 1 on 13 inherited snapshots |
| Exact offline locked release `eggcc` build | pass |

The two remaining DAG Clippy diagnostics are `unnecessary_unwrap` in
`extractiongymfastergreedydag.rs` and `cloned_ref_to_slice_refs` in
`fastercbcextractor.rs`. The independent fresh-U0 control under
[`u0-nits/`](u0-nits/report.md) reproduces both diagnostics exactly and verifies
that both flagged files are byte-identical. The raw r2 output is retained at
[`commands/dag-clippy/stderr`](commands/dag-clippy/stderr).

The rebuilt compiler does **not** have the frozen r1 SHA-256:

| Binary | Bytes | SHA-256 |
| --- | ---: | --- |
| frozen r1 | 61,915,472 | `ab1185cd3e24d1ed1698bc004ed3cc70f16c89202e3cc36a910b8308221df251` |
| rebuilt r2 | 61,915,472 | `046efff7fcc7ea3a1e31ff8e35ccad32001967b75f97e4f2c1efaef0413b6333` |

This triggered the initial delegated stop gate. After that result was reported,
the parent authorized a complete r2 matrix without timing. The first matrix
attempt failed closed because the fresh target lacked the retained `tiger`
helper; that setup attempt is preserved under
[`matrix-r2-attempt-01-missing-tiger/`](matrix-r2-attempt-01-missing-tiger/).
The final run provisioned the byte-identical frozen Tiger helper beside r2
`eggcc`, then passed all four phases and the retained inspector.

The final comparison covers 37 matrix cases and 177 native outputs. Every
semantic row, query/counter result, evidence file, emitted Bril program,
loadable Mach-O section, disassembled function body, and native output matches
r1. Raw LLVM differs only in its temporary `ModuleID`; raw disassembly differs
only in the displayed input path. The complete regenerated Mach-O files have
different hashes: all 117–120 changed bytes per pair are confined to UUID,
temporary-object symbol/string metadata, and the derived ad-hoc signature.
Thus execution content is identical, while strict exact timed-file identity is
not. The retained timing directly measures the frozen r1 Mach-O files.

The final root release suite passed all functional test bodies: 31 unit tests
and 2,420 file-test arms, with `raytracewithscreen` as the one explicit filter
and two ignored doctests. Its 13 rejected snapshots are byte-identical to r1
and to the dependency-retarget-only control; the checked-in snapshots remain
byte-identical to U0, whose unfiltered run passed 2,421 file-test arms and
generated no pending snapshots. No snapshot was accepted. The first root
attempt failed on one unit test and 1,012 file-test arms because the fresh
external target did not expose Tiger; after the retained Tiger binary was
placed beside the test executables, the corrected run produced the results
above. The generated `.snap.new` files are retained under
[`host-tests/pending-snapshots/`](host-tests/pending-snapshots/) and were removed
from the isolated source after capture.

[`matrix-r2/report.md`](matrix-r2/report.md) explains the comparison, and
[`matrix-r2/r1-r2-comparison.json`](matrix-r2/r1-r2-comparison.json) contains
the per-case byte attribution. [`host-tests/report.md`](host-tests/report.md)
explains the root validation. [`final-summary.json`](final-summary.json) binds
the build, matrix, and host evidence. Every captured command removed
`EGGLOG_BENCH_MEMORY_GUARD`; no timing samples were collected, and both full
suites explicitly skipped `raytracewithscreen`. The ordinary
`raytrace-test-benchmark` fixture still ran and passed in the root suite.
