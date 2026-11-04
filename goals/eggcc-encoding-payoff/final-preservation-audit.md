# Final preservation and scope audit

**Verdict: PASS. Binding findings: none.**

This audit checked the current checkout, retained manifests, archives, binaries,
receipts, validation streams, pending snapshots, hypothesis ledger, and the
files written during cycle 06 and final documentation. It ran no build, test,
compiler, native program, timing campaign, or network command. This audit file
is its only write.

## Repository and authorization boundary

The repository remains on `refs/heads/main` at
`fdd4eac12c1318c578badbf5d1299e0e3eb4e6c0`. `HEAD`, the index, local branch
logs, and remote-tracking logs show no final-phase commit, checkout, staging,
push, or fetched PR state. No file under `.git/refs` or `.git/logs/refs` is
newer than the goal branch setup on October 18 at 13:54 local time.

A scan of all 7,176 retained command receipts found exactly two Git commands:
the recorded `git init -q` calls that supplied repository metadata to two
disposable extracted engine trees. It found no `git commit`, `git push`,
`gh pr create`, `gh pr merge`, or `cargo insta accept` command. This audit did
not query GitHub, so the PR conclusion is based on the complete retained
command record and unchanged local/remote-tracking refs rather than a new
network observation.

The root checkout is substantially dirty, but that is pre-existing author
work. Every extant tracked modified file has a modification time no later than
September 29; the directory containing the one tracked deleted proof snapshot
was last changed September 24; and the Git index was last changed October 17.
The proof and paper paths currently shown by `git diff` likewise date from
September 24--29. Recent untracked files outside `goals/` and this goal's
`benchmarks/local/` evidence are only two `.DS_Store` files and `screenlog.0`,
not compiler, proof, or paper source.

Cycle 06 intentionally changed isolated experimental candidates for the P1
and A1 probes, as allowed by the goal. Those changes are retained in ignored
evidence and `/private/tmp`; they did not alter root compiler source. After
evidence collection, the finalization write set is confined to the P1 report,
the appended ledger row, cycle-review and validation records, and the goal's
`STATUS.md`, acceptance map, explanation, reference, reproduction guide, and
audits. No proof support or paper file was written in this phase.

## Snapshot, memory, and workload policy

The QR7 host still has all 13 rejected `.snap.new` files. For every row, the
pending file matches its recorded SHA-256, while the corresponding checked-in
candidate snapshot still matches pinned U0. Thus no pending snapshot was
accepted. The older snapshot changes visible in the dirty root predate this
goal and are unrelated author work.

All ten receipts reviewed by the final validation summary contain
`EGGLOG_BENCH_MEMORY_GUARD` in `absent_environment`; every retained stdout and
stderr stream still matches its receipt hash. Both isolated EggCC host test
commands include `--skip raytracewithscreen`. The ordinary
`raytrace-test-benchmark` fixture did run in the root host suite, so the exact
claim is that the heavy `raytracewithscreen` test was excluded, rather than
that every test with `raytrace` in its name was excluded.

## Frozen evidence integrity

An independent byte check produced the following results:

| Evidence | Current SHA-256 | Result |
| --- | --- | --- |
| QR7 source identity manifest | `22c37674b4f8617b90cceadddb2daa0992b501b9f627029ebc48dbda6515723c` | matches published reference |
| QR7 corrected source archive | `17d40620cb9c621ff493cb4edfd5099a487ce0f68ee054184b75381386a7e30e` | matches manifest |
| QR7 frozen compiler | `ab1185cd3e24d1ed1698bc004ed3cc70f16c89202e3cc36a910b8308221df251` | matches manifest |
| QR7 independent timing verification | `d23cda45901736c2c02721f7c456bf591526fc72e262f84de1a0c27c68276b56` | matches ledger and reference |
| Parts32 source identity manifest | `932ca349f56070c4810edde24f1d23e97481322f1ddbf2af743f083b2cf2007b` | matches timing authority |
| Parts32 final source archive | `ba2f65df7091573a594b7c51ec68a8b3665b5c85f279fe4415ca0f6e08565873` | matches manifest and timing authority |
| Parts32 frozen compiler | `d712e8347bf6eea231de829174a9436f411a3cedfd210daf8e7c4614c2371d2f` | matches manifest and timing authority |
| Parts32 independent timing verification | `9b26a8c4a1176979d555ff0c054ee0c985c8a3faa0e7c4313f225a4cbaaae959` | matches ledger and report |
| Parts32 compiler-time diagnostic | `283a6af7bb6a9d69d87510fab681042170f47ff70efa7a95719e37a8d36ad12e` | matches report |

The QR7 manifest replay matched all 38 live path entries and all 31 members of
the corrected source archive. The Parts32 replay matched all 17 live path and
archive entries. The timing designs, collectors/producers, independent
verifiers, and preflight records also match the hashes embedded in both timing
authorities. As an additional preservation check, all 1,740 entries in A1's
`final-source-r1.tar` match its manifest.

P1's early `implementation-manifest.json` and
`staged-source-identities.json` describe mutable source-only staging paths that
were later advanced for the actual probe; they are historical records, not
current-tree manifests. The retained P1 report states that chronology
explicitly. The original staged delta remains bound by the unchanged
`pack32-versus-parts32.patch`, while the later raw probe rows remain bound to
the retained baseline and candidate compiler hashes. This distinction does not
affect either qualifying frozen result.

## Append-only ledger

`hypotheses.jsonl` contains 46 valid JSON rows. Its first 45 rows currently
hash to `8a23b625a7c6da73c3215af1c62b0c5eb67b763c488b270326fdd9c312a5a6de`;
the complete ledger hashes to
`d527d7a2d08531ebd46284be685d08d7e075e6336e6719962943906f2e1288c1`.
The cycle-06 Codex audit records that it read all 45 prior rows and explicitly
identifies the existing P1 supersession at row 43. The later P1 actual-probe
disposition is row 46. Earlier P1 rows 13, 15, and 43 remain intact, so the
new evidence was appended rather than substituted for P1's prior history.

The current state therefore preserves the dirty checkout, prior studies,
frozen QR7 and Parts32 authorities, failed-probe evidence, and ledger history
within the authorized scope.
