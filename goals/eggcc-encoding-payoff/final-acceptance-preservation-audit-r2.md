# Final acceptance, requirements, and preservation audit r2

## Verdict

**PASS. Binding findings: none.**

The governing 14-fact contract is satisfied through the generated-runtime
speedup route. The acceptance map is internally consistent, the r2 cleanup has
no remaining QR7-specific validation defect, and the preserved evidence
supports the stated validation limits. The isolated EggCC host is still not
green: strict Clippy retains inherited U0 diagnostics and the root test command
still rejects 13 dependency-retarget snapshots. The deliverables state both
failures explicitly, accept no snapshot, and make no merge-readiness claim.

This was a read-only audit except for this file. It ran no compiler, build,
test, native workload, timing collector, snapshot update, Git mutation, or
network command. The reviewed deliverable identities were:

| File | SHA-256 |
| --- | --- |
| `report.md` | `b59444a988c50675d942bd369c398c9160f75adfe003ebfe88bc5cdb078d3392` |
| `reference.md` | `de9c040ed36b457620b18d79056eb75f6f0a31e129e5b9e3b98d4948cdca20dd` |
| `reproduce.md` | `36b3a022c904a3954dc52df64979b795d82080036648c8478bb401664638a3d8` |
| `acceptance.md` | `f936bb5254471c93ac5d4a7c2a84d2d40ad8a6a542c4eea72bad98ce3b117514` |
| `acceptance.json` | `25b869e48f1a1347311ed2cc547a409433590b86145602a003c80eff0b28e459` |
| `STATUS.md` | `8e26e8862cdf03f94330851f101d0275550cec23c9df78da268e7b9db07b0d6c` |
| `facts.md` | `cabf4e7ec192658a1d7932c901cb380aab1af3a9f9ea8ebc98a14f95d3257092` |

## Acceptance authority and complete fact crosswalk

`acceptance.json` names the local `goals/eggcc-encoding-payoff/facts.md` as
its authority, and its recorded SHA-256 exactly matches the current file. Its
14 entries map once each, in order, to fact lines 3 through 16. The recomputed
status counts are 13 `pass`, zero `pending`, zero `fail`, and one
`not_applicable`, exactly as declared. Every `remaining_gate` is null, every
`completion_blocker` is false, and every cited evidence path exists.

| Fact line / acceptance ID | Audit result | Evidence-backed finding |
| --- | --- | --- |
| 3 `strict-payoff` | **PASS** | QR7 independently confirms Encoding/U0 `0.5505494231`, bootstrap 95% `[0.5471011571,0.5575021727]`. Parts32 independently passes all 18 speed gates over six separate workload/session cells, with Encoding/U0 `0.91398` to `0.92504`. Either result meets the strict measured-speedup route. |
| 4 `encoding-choice` | **PASS** | QR7 materially uses marked `K7` cancellation to reach a bounded memory consumer. Parts32 materially uses marked forward disequality plus equal-sibling reverse congruence, satisfying the preference for both encodings. |
| 5 `bug-evidence` | **NOT APPLICABLE** | Acceptance claims no compiler bug and uses only the generated-runtime route. |
| 6 `prior-result-exclusions` | **PASS** | The reports exclude the old ObservedBool arithmetic conflicts, structural integration, retarget snapshots, lints, planted faults, and integration defects. P1 and A1 remain failed leads and are not credited as payoffs. |
| 7 `speedup-evidence` | **PASS** | Both campaigns retain exact native outputs, balanced repeated observations, explicit fresh-process runtime boundaries, frozen designs, independent verification, and U0/B1/Manual controls. Compiler and lowering time are excluded. QR7's r1 timing remains tied only to the frozen r1 Mach-O files. |
| 8 `causal-comparison` | **PASS** | Fixed-input knockouts restore baseline endpoints, exact rescues and faithful Manual recover the winning endpoints, and actual compiler consumers change. QR7's r2 replay preserves all 37 semantic cases, 177 native outputs, and both process-entry instruction groups. |
| 9 `semantic-scope` | **PASS** | The total signed-i64 reconstruction laws, equality-sort fields, private graph scope, checked branch/loop transport, exact exports, and unsupported cases are explicit. The files do not assume generic `Expr` or `Concat` injectivity, mutable global analysis, or allocation-site disequality. |
| 10 `implementation-scope` | **PASS** | The implementations are bounded sidecars and exact consumer bridges. A1 stops at its authorized revision budget. No wholesale IR redesign, proof support, Lean work, paper edit, commit, or push is part of the result. |
| 11 `correctness` | **PASS** | Registered mechanism tests, independent oracles, positive/negative boundaries, interpretation checks, and native checks pass for the qualifying cases. Root `make check`, selected-engine `make check`, and the r2 DAG suite pass. The nonzero host exits are retained and freshly attributed, not described as green. |
| 12 `preservation` | **PASS** | Source, dependency, patch, binary, input, command, configuration, timing, failed-attempt, and result identities remain retained. The r2 cleanup is a separate manifest-bound patch and does not rewrite r1 timing evidence or unrelated author work. |
| 13 `measurement-honesty` | **PASS** | QR7 reports hot and zero-trip workloads separately; Parts32 reports all workloads and sessions separately. Both use matched native backends and exact output checks. Diagnostic compiler time, rejected sessions, failed attempts, and rule-only time are excluded from speedup claims. |
| 14 `search-discipline` | **PASS** | The 46-row append-only ledger retains early falsifiers, revisions, successes, P1/A1 failures, and the later probes. The cycle-06 Codex/Fable passes and independent source validation close the bounded search without claiming global impossibility. |
| 15 `resources` | **PASS** | Memory pressure did not block or discard work. The guard is absent from reviewed receipts. Commands retain timeouts/error records. The heavy `raytracewithscreen` test is filtered; the ordinary `raytrace-test-benchmark` fixture ran and passed. |
| 16 `deliverables` | **PASS** | The explanation connects laws, rules, compiler consumers, controls, measurements, failures, and limits. The compact reference and operational reproduction guide are separate. All 59 local Markdown targets in the five final deliverables resolve. |

The two qualifying measurement authorities remain byte-identical to their
published identities: QR7's independent verifier is
`d23cda45901736c2c02721f7c456bf591526fc72e262f84de1a0c27c68276b56`,
and Parts32's is
`9b26a8c4a1176979d555ff0c054ee0c985c8a3faa0e7c4313f225a4cbaaae959`.
QR7's verifier status is `passed` and every declared gate is true. Parts32's
session, speed-gate, code-identity, output-admission, and placebo-validity
booleans are all true.

## r2 source and direct-check audit

The retained r2 patch has SHA-256
`b0802da11e40e6d7fba3eefc8a3639a81153bee445cd90a71000e967d4211e00`.
It is exactly the live diff from r1 to r2 and has four hunks in only
`dag_in_context/src/scoped_qr7.rs`: two rustfmt changes, a function-local tuple
type alias, and a test-only constant simplification. The before and after
manifests each contain the same 774 paths; this is their only changed entry.
All 774 live r1 source entries match the before manifest, and all 774 live r2
entries match the after manifest.

The direct checks support the final classification:

- root and DAG `cargo fmt --check` exit zero;
- six focused QR7 tests pass;
- all 70 DAG tests pass with no pending snapshots;
- the release `eggcc` build passes; and
- strict DAG Clippy has zero QR7 diagnostic and only the two diagnostics
  reproduced by fresh U0 in byte-identical pre-existing files.

The fresh U0 archive is commit
`a0bbec127f83249074a46af3fd6f6126c90fe0fb`, SHA-256
`7a886debd758e78d0e859a05bbac75084e7da9c4f4bd0d73321dcf6f5ad25c2a`.
All 771 Git blobs were verified, and its before/after manifests are identical.
U0 passes root and DAG formatting. Its root Clippy run reproduces the one
pre-existing root diagnostic, and its DAG Clippy run reproduces the same two
candidate diagnostics. The candidate DAG Clippy stream contains no reference
to `scoped_qr7.rs`.

The r2 compiler is the same size as r1 but correctly recorded as a different
file:

| Compiler | SHA-256 |
| --- | --- |
| frozen timed r1 | `ab1185cd3e24d1ed1698bc004ed3cc70f16c89202e3cc36a910b8308221df251` |
| validation-only r2 | `046efff7fcc7ea3a1e31ff8e35ccad32001967b75f97e4f2c1efaef0413b6333` |

That difference triggered the complete r2 replay. All 331 final matrix
receipts exit zero with no timeout; 177 are native executions. The comparison
contains 37 cases and establishes equal semantic rows, queries, counters,
e-graph/evidence files, emitted Bril, optimized Bril, native stdout, loadable
Mach-O sections, and disassembled function bodies. The regenerated complete
Mach-O files are not byte-identical; their differences are confined to UUID,
temporary-object metadata, and the derived signature. Thus the r1 samples
remain direct measurements of r1 only, while r2 establishes semantic and
executed-content equivalence without making a new timing claim.

## Complete validation receipts

The final repository `make check` receipt has SHA-256
`4e419fe4e240069a782f8ea3a01dd1fc0e3a396c8f5f6934cb1c203dfec574f2`.
It records `make check`, exit zero, no timeout, and the memory guard absent.
Its raw output reports 1,979 Python tests and two Python snapshots passing.
Summing all Rust result groups gives 1,502 passes and six ignores.

The isolated selected-engine `make check` receipt exits zero with 233 Python
tests, two Python snapshots, 1,804 Rust tests/doctests, and six ignores. The
current hashes of all 724 stdout/stderr streams named by r2 and selected-engine
receipts match their recorded stream hashes.

The corrected r2 host root run passes all 31 unit and 2,420 file-test bodies,
with one explicit `raytracewithscreen` filter and two ignored doctests. Its exit
one is the Insta rejection of 13 pending snapshots. Every pending snapshot is
byte-identical to r1 and the dependency-only control; all 270 checked-in
snapshots remain byte-identical to U0. The before/after checked-in-snapshot and
source manifests are byte-identical, the isolated r2 source contains zero
`*.snap.new` files, and all 13 pending files are retained separately as
evidence. No snapshot was accepted. The first missing-Tiger run remains
separately classified as a harness setup failure and is not substituted for
the corrected result.

The r2 final summary has SHA-256
`051e8a3951265779bba1ddd3b5b0eee79fc8c73dc06c7657d9d4db20f1214d9a`;
its sidecar digest agrees. All 16 path/size/SHA triples embedded in that summary
match the current files, including the finalized host comparison
`12bf6cbaef77011ba8f029537559eb1cf51c4898ea016355cb8e4aeb3cf2edab`.

## Preservation and authorization boundary

The frozen result authorities remain unchanged:

| Evidence | SHA-256 |
| --- | --- |
| QR7 source identity | `22c37674b4f8617b90cceadddb2daa0992b501b9f627029ebc48dbda6515723c` |
| QR7 corrected source archive | `17d40620cb9c621ff493cb4edfd5099a487ce0f68ee054184b75381386a7e30e` |
| QR7 frozen compiler | `ab1185cd3e24d1ed1698bc004ed3cc70f16c89202e3cc36a910b8308221df251` |
| QR7 timing verification | `d23cda45901736c2c02721f7c456bf591526fc72e262f84de1a0c27c68276b56` |
| Parts32 source identity | `932ca349f56070c4810edde24f1d23e97481322f1ddbf2af743f083b2cf2007b` |
| Parts32 final source archive | `ba2f65df7091573a594b7c51ec68a8b3665b5c85f279fe4415ca0f6e08565873` |
| Parts32 frozen compiler | `d712e8347bf6eea231de829174a9436f411a3cedfd210daf8e7c4614c2371d2f` |
| Parts32 timing verification | `9b26a8c4a1176979d555ff0c054ee0c985c8a3faa0e7c4313f225a4cbaaae959` |
| Parts32 compiler-time diagnostic | `283a6af7bb6a9d69d87510fab681042170f47ff70efa7a95719e37a8d36ad12e` |

The hypothesis ledger still contains 46 valid JSON rows. Its first 45 rows
hash to `8a23b625a7c6da73c3215af1c62b0c5eb67b763c488b270326fdd9c312a5a6de`
and the complete file hashes to
`d527d7a2d08531ebd46284be685d08d7e075e6336e6719962943906f2e1288c1`,
matching the preceding preservation audit. Row 46 remains the appended P1
actual-probe disposition; the earlier P1 rows remain present.

Since the preceding preservation audit, all new benchmark evidence is confined
to the nine r1 direct-check receipt/stream files and the new
`qr7-integration/validation-r2/` tree. No earlier Parts32, QR7 timing, failed
lead, cycle-audit, or ledger authority has a newer write. This is consistent
with addition of validation evidence rather than replacement of prior results.

The root repository remains on `refs/heads/main` at
`fdd4eac12c1318c578badbf5d1299e0e3eb4e6c0`; `origin/main` remains
`03e533714524c1b21be77edff46fb694120b8b81`. The Git index was last modified
October 17 and the newest goal branch ref/log update is the October 18 setup.
A scan of all 7,539 retained command receipts finds only two Git commands,
both `git init -q` for disposable extracted engine trees. It finds no commit,
push, PR creation/merge, snapshot acceptance, or destructive Git command.

The dirty root source is preserved. The 41 extant dirty proof/paper-related
paths date from September 21 through 29, before this goal; the one tracked
deleted proof snapshot was already deleted before the goal, and its directory
last changed September 24. No tracked dirty source path is newer than the
preceding preservation audit. No proof or paper source change belongs to this
work.

The later root `.venv` refresh is environment state, not a source change:
`/.venv/` is explicitly ignored, its `pyvenv.cfg` records the Python 3.14 uv
environment, and 4,671 files under it are newer than the preceding audit.
`uv.lock` remains unchanged with its July timestamp. The dirty
`pyproject.toml` change dates from September and predates this goal. The final
root check also refreshed eight ignored `egglog/output*.log` test artifacts.
Neither generated set enters Git status or any frozen source manifest.

All 361 receipts under validation r2 declare
`EGGLOG_BENCH_MEMORY_GUARD` absent, and none records it in the effective
environment. No r2 performance samples were taken. The only receipt commands
whose arguments mention raytracing are the three explicit
`--skip raytracewithscreen` suite commands. The corrected host output confirms
that the ordinary `raytrace-test-benchmark` fixture ran and passed. This
matches the stated resource boundary: memory pressure did not block ordinary
work, and the heavy raytracing workload was not run.

The current state therefore passes the final acceptance and preservation gate.
No requirement remains pending under the governing local fact sheet.
