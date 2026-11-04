# Final semantic and documentation audit after QR7 r2

Verdict: **PASS**.

## Binding findings

None.

## Scope and authority

This was an independent, read-only audit of the current bytes of `report.md`,
`reference.md`, `reproduce.md`, `acceptance.md`, `acceptance.json`, and
`STATUS.md`. The audit checked their semantic, measurement, validation, and
Diátaxis claims against these primary authorities:

- QR7 r2 final summary, SHA-256
  `051e8a3951265779bba1ddd3b5b0eee79fc8c73dc06c7657d9d4db20f1214d9a`;
- QR7 r1/r2 matrix comparison, SHA-256
  `0b29b24ccfe9b5b7de9d2b5a1a2cd82f095810384fa542aeb935d042dee125f4`;
- QR7 r2 host comparison, SHA-256
  `12bf6cbaef77011ba8f029537559eb1cf51c4898ea016355cb8e4aeb3cf2edab`;
- fresh pinned-U0 nits comparison, SHA-256
  `92a5f5a568bed5d6ee6db381a8de576cf6b473bc7a713d364bde80a9a21dd374`;
- final repository `make check` receipt, SHA-256
  `4e419fe4e240069a782f8ea3a01dd1fc0e3a396c8f5f6934cb1c203dfec574f2`;
- QR7 r1 independent timing verification, SHA-256
  `d23cda45901736c2c02721f7c456bf591526fc72e262f84de1a0c27c68276b56`;
  and
- Parts32 independent timing verification, SHA-256
  `9b26a8c4a1176979d555ff0c054ee0c985c8a3faa0e7c4313f225a4cbaaae959`.

The audited document identities were:

| Document | SHA-256 |
| --- | --- |
| `report.md` | `b59444a988c50675d942bd369c398c9160f75adfe003ebfe88bc5cdb078d3392` |
| `reference.md` | `de9c040ed36b457620b18d79056eb75f6f0a31e129e5b9e3b98d4948cdca20dd` |
| `reproduce.md` | `36b3a022c904a3954dc52df64979b795d82080036648c8478bb401664638a3d8` |
| `acceptance.md` | `f936bb5254471c93ac5d4a7c2a84d2d40ad8a6a542c4eea72bad98ce3b117514` |
| `acceptance.json` | `25b869e48f1a1347311ed2cc547a409433590b86145602a003c80eff0b28e459` |
| `STATUS.md` | `8e26e8862cdf03f94330851f101d0275550cec23c9df78da268e7b9db07b0d6c` |

## Semantic and measurement findings

The documents preserve the necessary r1/r2 boundary. The retained QR7 timing
directly measures the frozen r1 compiler and Mach-O files. The r2 compiler has a
different hash, and every regenerated native executable has a different whole
file hash. The r2 comparison establishes equality of all 37 semantic cases,
177 native outputs, 1,739 disassembled function instruction bodies, and every
loadable Mach-O section; it confines the remaining file differences to UUID,
temporary-object symbol/string metadata, and the derived ad-hoc signature. The
documents consistently call this execution-content equivalence and make no r2
timing claim.

The QR7 measurements match the retained r1 authority: Encoding/U0 is
`0.550549423146935` with complete-block bootstrap 95%
`[0.5471011571092694, 0.5575021727134777]`, while the separately reported
zero-trip control is `0.9892585012313899` with interval
`[0.9836729080819114, 1.0003275615417164]`. The actual process-entry groups are
91 instructions and two internal backward branches for baseline versus 55 and
zero for the winning group. All frozen QR7 gates are true.

The Parts32 per-session values and limits also match their independent timing
authority. Its six Encoding/U0 point estimates range from
`0.9139833514013909` to `0.9250432354587043`; all session speed gates and the
placebo-validity gate pass, no failed or partial session enters the result, and
the documents keep workloads and sessions separate. The prose does not turn
the compiler-time diagnostic, same-mask replication, supporting integrations,
or failed leads into the accepted Parts32 or QR7 performance claims.

## Validation findings

The four-hunk r2 cleanup changes only `dag_in_context/src/scoped_qr7.rs` and
removes the QR7-local formatting and two strict-Clippy findings. Root and DAG
format checks pass. The one remaining root diagnostic and two remaining DAG
diagnostics reproduce at the same sites in byte-identical pinned-U0 files; the
documents correctly keep the host nits gate non-green.

The cleaned r2 host run passes 31 unit and 2,420 file-test bodies before exiting
on 13 unaccepted snapshots. All 13 match r1 and the dependency-retarget control,
checked-in snapshots remain unchanged, and no snapshot was accepted. The final
repository `make check` exits zero with 1,979 Python tests, two Python snapshots,
1,502 Rust tests/doctests, and six ignored Rust tests. The selected-engine and
70-test DAG claims match their retained receipts. The documents also state the
raytrace boundary precisely: `raytracewithscreen` was filtered, while
`raytrace-test-benchmark` ran and passed. They do not claim that every
raytrace-named fixture was skipped or that raytracing contributed timing data.

## Diátaxis and integrity findings

The document set has a clear division of reader tasks:

- `report.md` is the connected explanation: it introduces the rules, follows
  each encoding-to-consumer chain, relates controls to the causal claims, and
  explains the measured results and limits.
- `reference.md` is the lookup surface for terms, rules, host contracts,
  treatments, exact fields, identities, and result tables.
- `reproduce.md` is operational guidance. It separates read-only review,
  correctness replay, performance collection, supporting-case review, and
  failure interpretation; write-producing replays use fresh temporary roots.
- `acceptance.md`, `acceptance.json`, and `STATUS.md` state the evidence gate and
  current disposition without presenting the non-green EggCC host as merge
  ready.

The small mathematical and result tables in the explanation support its
argument; they do not replace the compact reference or mix retained timing with
reproduction commands. The reproduction guide repeatedly preserves the r1
timing/r2 validation distinction.

Mechanical integrity checks found:

- 88 local Markdown links, with no missing targets or invalid local anchors;
- 48 literal repository paths in the reviewed prose, with no missing targets;
- all 29 unique printed SHA-256 values valid: 26 match their files directly,
  and the r2 compiler plus two process-entry instruction hashes match their
  bound machine records;
- all 65 `acceptance.json` evidence references present, its facts-source hash
  correct, and its status totals recomputing to 13 pass, zero pending, zero
  fail, and one not applicable;
- every path/hash pair embedded in the r2 final summary valid and the root-r4
  stdout/stderr hashes matching its receipt; and
- 26 targeted semantic assertions over the QR7 and Parts32 timing records, r2
  matrix, host comparison, U0 diagnostic attribution, and root validation all
  passing.

No audited deliverable or retained evidence file was changed by this audit.
