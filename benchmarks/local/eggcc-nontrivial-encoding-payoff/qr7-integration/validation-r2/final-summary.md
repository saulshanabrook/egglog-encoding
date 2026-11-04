# QR7 validation r2 final summary

The four-hunk cleanup changes only `dag_in_context/src/scoped_qr7.rs` and is
nonsemantic at the Rust source level. Root and DAG formatting pass, six focused
QR7 tests pass, and all 70 DAG tests pass. DAG Clippy now reports only two
warnings that the fresh U0 control reproduces byte for byte in unchanged files.

The r2 compiler is not byte-identical to frozen r1, so the complete 37-case
matrix was rerun without timing. All semantic rows, queries, counters, evidence,
emitted Bril, loadable Mach-O sections, disassembled function bodies, and 177
native outputs match r1. The Mach-O file differences are confined to UUID,
temporary-object symbol/string metadata, and the derived ad-hoc signature. The
retained timing therefore continues to measure the frozen r1 files; no r2
performance samples were taken.

The corrected root suite passed 31 unit tests and 2,420 file-test arms, with
`raytracewithscreen` as its one explicit filter and two ignored doctests. Its
exit code 1 comes from 13 rejected snapshots. All 13 equal r1 and the
independent dependency-retarget-only control byte for byte, while the checked-in
snapshots equal U0. U0's unfiltered total was 2,421 file-test arms, exactly
`2,420 + 1 filtered`. No QR7 r2-specific root difference was found, and no
snapshot was accepted.

The first root attempt is retained as a harness failure: one unit test and 1,012
file-test arms failed because Tiger was not visible from the fresh external
target. After the retained Tiger binary was placed beside the test executables,
the corrected run produced the results above. The 13 `.snap.new` files were
retained as evidence and removed from the isolated source. All 774 source entries
and 270 checked-in snapshots remain unchanged.

Every captured command removed `EGGLOG_BENCH_MEMORY_GUARD`. Both full suites
explicitly skipped `raytracewithscreen`; the ordinary
`raytrace-test-benchmark` fixture still ran and passed. No timing samples or
heavy raytracing workload were requested.

| Evidence | Result |
| --- | --- |
| [Source, nits, DAG, and build](report.md) | cleanup and scoped validation |
| [Fresh U0 nits control](u0-nits/report.md) | inherited diagnostics reproduced |
| [Complete r2 matrix](matrix-r2/report.md) | semantic and execution content equal r1 |
| [Root host suite](host-tests/report.md) | functional pass; inherited snapshot rejection |
| [Machine-readable final summary](final-summary.json) | SHA-256 `051e8a3951265779bba1ddd3b5b0eee79fc8c73dc06c7657d9d4db20f1214d9a` |

The frozen digest is also recorded in [`final-summary.sha256`](final-summary.sha256).
