# QR7 r2 root host validation

The corrected root release run executed `['cargo', 'insta', 'test', '--release', '--unreferenced=reject', '--', '--skip', 'raytracewithscreen']` in
`/private/tmp/eggcc-qr7-candidate-nits-r2` with Rust 1.91.0, four Cargo jobs,
`EGGLOG_BENCH_MEMORY_GUARD` absent, and `raytracewithscreen` explicitly skipped.
It completed in 496.5 diagnostic seconds.

All test bodies passed: 31 root unit tests and 2,420 file-test arms, with the one
requested filter, plus two ignored doctests. This exactly matches r1. U0 passed 31
unit tests and 2,421 file-test arms without a filter; `2,420 + 1 filtered = 2,421`,
so the count difference is solely the explicit skip.

The command exited 1 because Insta generated 13 rejected snapshots. Every r2
snapshot is byte-identical to its r1 counterpart and to the dependency-retarget-only
control recorded by the independent r1 attribution. All 13 checked-in r2 snapshots
remain byte-identical to U0. U0 itself generated no pending snapshots. Therefore all
observed root snapshot differences are inherited dependency-retargeting differences;
this run found no QR7 r2-specific root difference.

The first captured attempt failed before this comparison because the fresh external
target did not expose Tiger to `find_tiger_binary`; 1,012 file-test arms reported the
same missing-Tiger harness error, as did one unit test. No snapshots were generated,
and source remained unchanged. The retained Tiger binary (`130eaba8bb575e196b8e18898826356269efe6e28a56b9d3690ef42647d3b201`) was then copied beside the
test executables in the external target, matching the lookup contract. That setup is
recorded in [`tiger-provision.json`](tiger-provision.json), and the preliminary
receipt remains under [`attempt-01-missing-tiger/`](attempt-01-missing-tiger/).

The final run did not modify any of the 774 source entries or 270 checked-in
snapshots. Its 13 `.snap.new` files were copied to
[`pending-snapshots/`](pending-snapshots/) and then removed from the isolated source;
[`snapshot-cleanup.json`](snapshot-cleanup.json) records their exact hashes. No
snapshot was accepted. The narrower `raytracewithscreen` selector was skipped; the
ordinary `raytrace-test-benchmark` fixture still ran and passed.

[`comparison.json`](comparison.json) contains every snapshot hash, parsed test result,
source comparison, and verified receipt hash. The final full streams and receipt are
under [`command/`](command/).
