# Final requirement-by-requirement completion audit r2

## Verdict

**PASS. No binding blocker or required work remains.**

The goal's strict done condition is satisfied through reproducible,
correctness-preserving generated-program runtime speedups. Parts32 is the
preferred combined injectivity-and-disequality result; QR7 independently
provides the larger injectivity-only result through a substantive compiler
consumer. Neither result relies on the excluded primitive-Boolean bug route.

The goal may be marked complete. The non-green isolated EggCC host commands
remain reported limits: they are not described as green, waived, or evidence
of merge readiness.

This was an independent, read-only completion audit except for this file. It
ran no build, compiler, test, native workload, timing collector, Git mutation,
snapshot update, or network command. It changed no acceptance, documentation,
source, or evidence file.

## Governing contract and frozen state

The governing acceptance authority is the adjacent [`facts.md`](facts.md), as
specified by [`goal.md`](goal.md) and [`plan.md`](plan.md):

| Authority | SHA-256 |
| --- | --- |
| `goal.md` | `20084eb0eab534b65c7b50316ca9c9144f5cf30fb8c12819bd7fea4fa7b557ec` |
| `plan.md` | `2b407991c3f70ed9d8e278c681ab6a8e4d80ae5c55c966ce8e5bd1ea4c91592d` |
| local `facts.md` | `cabf4e7ec192658a1d7932c901cb380aab1af3a9f9ea8ebc98a14f95d3257092` |

`acceptance.json` names
`goals/eggcc-encoding-payoff/facts.md` and records that exact facts SHA. The
neighboring `goals/eggcc-nontrivial-encoding-payoff/facts.md`, SHA-256
`bcccd6016850ca12340079a33cf6e3daa8f6e48bf1f29f0dfe6923f51539c70f`,
is a separate, stronger follow-on fact sheet and is **not** the completion
contract for this audit.

The audited final deliverables were frozen at these identities:

| File | SHA-256 |
| --- | --- |
| `STATUS.md` | `8e26e8862cdf03f94330851f101d0275550cec23c9df78da268e7b9db07b0d6c` |
| `report.md` | `b59444a988c50675d942bd369c398c9160f75adfe003ebfe88bc5cdb078d3392` |
| `reference.md` | `de9c040ed36b457620b18d79056eb75f6f0a31e129e5b9e3b98d4948cdca20dd` |
| `reproduce.md` | `36b3a022c904a3954dc52df64979b795d82080036648c8478bb401664638a3d8` |
| `acceptance.md` | `f936bb5254471c93ac5d4a7c2a84d2d40ad8a6a542c4eea72bad98ce3b117514` |
| `acceptance.json` | `25b869e48f1a1347311ed2cc547a409433590b86145602a003c80eff0b28e459` |

The machine-readable map contains exactly 14 entries, one for each fact line
3 through 16 and in the same order. Its recomputed totals are 13 `pass`, zero
`pending`, zero `fail`, and one `not_applicable`. Every `remaining_gate` is
null, every `completion_blocker` is false, and all 65 cited evidence paths
exist.

## Complete local-fact audit

| Fact line / acceptance ID | Result | Concrete evidence and conclusion |
| --- | --- | --- |
| 3 `strict-payoff` | **PASS** | QR7's independent verifier, `qr7-integration/timing-r1/independent-verification.json` (SHA-256 `d23cda45901736c2c02721f7c456bf591526fc72e262f84de1a0c27c68276b56`), reports hot Encoding/U0 `0.5505494231`, bootstrap 95% `[0.5471011571,0.5575021727]`. Parts32's verifier, `parts32-integration/timing/independent-verification.json` (SHA-256 `9b26a8c4a1176979d555ff0c054ee0c985c8a3faa0e7c4313f225a4cbaaae959`), passes all 18 speed gates; its six Encoding/U0 cells range from `0.9139833514` to `0.9250432355`. Either result independently satisfies the positive speedup route. |
| 4 `encoding-choice` | **PASS** | Parts32 materially uses both encodings: marked forward disequality, lossless representation equalities, and equal-sibling reverse congruence derive the exact high-child disequality consumed as contextual `Eq=false`. QR7 separately uses marked `K7` cancellation and makes no disequality claim. |
| 5 `bug-evidence` | **NOT APPLICABLE** | No compiler bug is claimed. Acceptance uses the generated-runtime route, so the alternative bug bundle is not required. |
| 6 `prior-result-exclusions` | **PASS** | The explanation and ledger exclude the prior ObservedBool arithmetic conflicts, structural integration, inherited snapshots/lints, planted or malformed cases, and integration-introduced defects. P1 and A1 remain unsuccessful probes rather than qualifying results. |
| 7 `speedup-evidence` | **PASS** | Both campaigns retain matched valid workloads, exact native outputs, fresh-process runtime boundaries, balanced repeated observations, complete-block bootstrap intervals, frozen designs, fair U0/B1/Manual controls, and independent confirmation. Compiler/lowering time, rejected sessions, and diagnostic retries are excluded. QR7 timing directly measures only the frozen r1 Mach-O files. |
| 8 `causal-comparison` | **PASS** | The actual compiler consumers change under fixed inputs. Essential feature knockouts return to baseline, exact intermediate rescues and faithful Manual recover the winning endpoint, and primitive-only controls remain null. QR7 changes the added bounded must-alias bridge; Parts32 changes only the exact contextual false-equality application. |
| 9 `semantic-scope` | **PASS** | The reports and reference justify the signed-i64 reconstruction laws, equality-sort children, private graph scope, checked branch/loop transport, feasible paths, exact exports, Bottom/unknown handling, and relevant lifetime/effect limits. They do not assume global `Expr`, generic `Concat`, mutable-analysis, or allocation-site injectivity/disequality. |
| 10 `implementation-scope` | **PASS** | The successful implementations are bounded sidecars plus exact consumer bridges. A1 stops after its authorized initial attempt and one revision. No wholesale IR redesign, proof support, Lean work, paper edit, commit, push, or pull request is part of the result. |
| 11 `correctness` | **PASS** | Registered mechanism tests are nonzero and cover independent oracles, positive/negative boundaries, interpretation, emitted code, and native execution. QR7 has 37 semantic cases and 177 native outputs; Parts32 has 200 native checks. Repository-root and selected-engine `make check` pass, and the cleaned r2 DAG suite passes. The remaining host failures are freshly attributed and retained exactly, as detailed below. |
| 12 `preservation` | **PASS** | Source/dependency manifests, patches, archives, binaries, commands, inputs, configurations, raw timing rows, failed attempts, and result identities remain retained. The r2 cleanup is a separate four-hunk patch; r1 timing evidence was not rewritten. Dirty author work and checked-in snapshots remain unchanged. |
| 13 `measurement-honesty` | **PASS** | QR7 reports the hot and zero-trip workloads separately; Parts32 reports every workload and session separately. Both use the same backend within matched comparisons and exact output checks. Rule-only time, the descriptive compiler-time diagnostic, failed attempts, and rejected sessions do not enter a speedup claim. |
| 14 `search-discipline` | **PASS** | The 46-row append-only ledger retains early falsifiers, revisions, successes, and terminal failures. P1 is terminal by portfolio supersession and has a retained later fail-closed actual probe. A1 is terminal after its permitted revision. Cycle 06 closes the bounded search without claiming global impossibility. |
| 15 `resources` | **PASS** | Memory pressure did not block or discard work; reviewed receipts record `EGGLOG_BENCH_MEMORY_GUARD` absent and retain finite timeouts/errors. Only the heavy `raytracewithscreen` host test was filtered. The ordinary `raytrace-test-benchmark` fixture ran and passed. |
| 16 `deliverables` | **PASS** | `report.md` is the connected explanation, `reference.md` is the compact lookup surface, and `reproduce.md` is the operational guide. Together they show the rules, before/after behavior, encoding-to-consumer paths, Manual comparisons, measurements, negative probes, and limits. The acceptance map and lead ledger are machine-readable. |

## Strict payoff and causal evidence

QR7 uses equality of quotient/remainder guards, representation identities, and
injective cancellation of marked `K7` to derive the exact local equality that
feeds address congruence and an added bounded store-forwarding bridge. Its
winning process entry changes from 91 instructions with two internal backward
branches to 55 instructions with none. Baseline LLVM already removes the
executed load, so the supported mechanism is earlier forwarding exposing loop
elimination; no particular LLVM pass order is claimed. The 112-cycle
confirmation contains 3,136 measured rows with ten serial fresh processes per
row. The separate zero-trip Encoding/U0 control is `0.9892585012`, bootstrap
95% `[0.9836729081,1.0003275615]`, and carries no speed gate.

Parts32 transports `x != y` through marked `Parts32`, uses exact lossless
representation identities to expose unequal unmarked `Pair` terms, and uses an
equal low sibling to derive `high(x) != high(y)`. The host consumes only that
exact contextual false-equality fact. Its 200 native checks, mechanism
knockouts, exact rescue, Manual parity, semantic negatives, and no-context
cases pass. Two independent 90-cycle sessions cover three workloads; all 18
predeclared speed comparisons and the placebo-validity gate pass, with no
pooled workload or session estimate.

## Terminal leads and cycle-06 stop boundary

The ledger remains valid JSON with 46 rows. The first 45 rows hash to
`8a23b625a7c6da73c3215af1c62b0c5eb67b763c488b270326fdd9c312a5a6de`;
the full ledger hashes to
`d527d7a2d08531ebd46284be685d08d7e075e6336e6719962943906f2e1288c1`.
Row 46 appends the P1 actual-probe disposition without replacing its earlier
history.

- P1 remains terminal by portfolio supersession. Its later actual-host probe
  retains 93 rows, 243 exact native outputs, 156 rejected queries, zero
  exports, and no endpoint difference.
- A1 remains terminal after its initial implementation plus one permitted
  functional revision. All 31 interpreter pairs and 233 native checks agree;
  all 18 positive endpoints are identical, no fact is exported, and no timing
  is claimed.
- The fresh cycle-06 Codex audit finds no new bounded eligible family. The
  Claude Fable subprocess receipt has SHA-256
  `7a0a177aeb276d68b6e57348b855c0c63410000e4e6d5f8d5b5d0f70abdcaa19`,
  exits zero, is marked read-only, and allows only `Read`, `Grep`, and `Glob`.
  Its recorded stdout hash equals the retained Fable audit hash
  `53f9fd25680fc09982515daeb4870550fb358667b97339e152a658d34c2bb307`.
  Independent source validation rejects the unsupported exact LLVM-pass,
  exhaustive-consumer-census, `ContextOf` lifetime-proof, and false-`If`
  claims while preserving the supported conclusion that no new source-backed
  eligible lead emerged.

This is the finite stop condition required by the plan. It is not an
exhaustive claim about all future EggCC programs or representations.

## Validation and r1/r2 boundary

The final validation boundary is complete and explicit:

| Scope | Retained result | Completion interpretation |
| --- | --- | --- |
| Repository root | Final `make check` receipt SHA-256 `4e419fe4e240069a782f8ea3a01dd1fc0e3a396c8f5f6934cb1c203dfec574f2`; exit zero; 1,979 Python tests plus two Python snapshots, 1,502 Rust tests/doctests, six ignored | **Pass** |
| Selected encoding engine | Isolated `make check` exits zero; 233 Python tests plus two snapshots, 1,804 Rust tests/doctests, six ignored | **Pass** |
| EggCC DAG | Six focused QR7 tests and all 70 DAG tests pass; no pending snapshots | **Pass** |
| Direct format/lint checks | Root and DAG formatting pass after r2. Strict root Clippy retains one diagnostic and strict DAG Clippy retains two diagnostics; all reproduce in byte-identical pinned-U0 files, and DAG Clippy reports zero QR7 diagnostic | **Attributed non-green host nits; no QR7-specific defect remains** |
| EggCC host root | Corrected r2 run passes 31 unit and 2,420 file-test bodies, then exits one on 13 unaccepted dependency-retarget snapshots. All 13 match r1 and the dependency-only control; checked-in snapshots match U0 | **Retained non-green host result; no snapshot accepted** |
| Resource boundary | Memory guard absent; `raytracewithscreen` skipped; ordinary `raytrace-test-benchmark` ran and passed | **Matches user and plan constraints** |

The first r2 host attempt that lacked Tiger remains separately classified as a
harness setup failure. The corrected command uses the retained hash-verified
Tiger and is the functional authority.

Direct r1 checks exposed QR7-local formatting plus `type_complexity` and
test-only `identity_op` findings. The isolated r2 patch, SHA-256
`b0802da11e40e6d7fba3eefc8a3639a81153bee445cd90a71000e967d4211e00`,
contains four nonsemantic hunks in only `dag_in_context/src/scoped_qr7.rs`:
rustfmt changes, a local tuple type alias, and a test assertion
simplification.

The r2 compiler hash
`046efff7fcc7ea3a1e31ff8e35ccad32001967b75f97e4f2c1efaef0413b6333`
differs from the frozen timed r1 compiler hash
`ab1185cd3e24d1ed1698bc004ed3cc70f16c89202e3cc36a910b8308221df251`.
The resulting stop gate was honored by running a complete r2 matrix. Its 37
semantic cases, 177 native outputs, queries/counters, e-graph evidence,
emitted and optimized Bril, all 1,739 disassembled function bodies, and every
loadable Mach-O section match r1. The whole Mach-O files differ in UUID,
temporary-object symbol/string metadata, and derived ad-hoc signatures.
Consequently, the retained timing is a direct measurement of frozen r1 only;
r2 establishes semantic and executed-content equivalence and makes no timing
claim. The r2 final summary has SHA-256
`051e8a3951265779bba1ddd3b5b0eee79fc8c73dc06c7657d9d4db20f1214d9a`;
all 16 embedded path/size/hash records match current files.

## Plan section 6 and final-gate crosswalk

| Explicit plan §6 obligation | Result and evidence |
| --- | --- |
| Run registered focused tests, then complete suites on stable source | **PASS.** Six QR7 focused tests, 70 DAG tests, repository-root `make check`, and selected-engine `make check` have retained receipts. Parts32's registered mechanism and selected-engine tests also pass. |
| Use fresh U0 controls for baseline failures; do not inherit old waivers | **PASS.** Fresh pinned-U0 format/Clippy controls reproduce the one root and two DAG diagnostics in byte-identical files. Snapshot bodies are compared to U0 and dependency-only controls. |
| Keep failed official commands explicit | **PASS.** Host root and nits remain non-green in the acceptance boundary; 13 snapshots remain unaccepted; the missing-Tiger setup attempt is retained separately. No failure is relabeled green. |
| Verify actual compiler host/native CLI coverage, nonzero discovery, and interpreted outputs | **PASS.** Selected counts are nonzero. QR7 and Parts32 retain source/result interpretation, exact independent-oracle comparisons, emitted code, actual native exit/output, and negative/unsupported cases. |
| Deliver the connected successful explanation with exact rules, old/manual behavior, results, and limits | **PASS.** `report.md` covers both causal chains and separates failed leads. `reference.md` owns laws, APIs, schedules, identities, and result tables. `reproduce.md` owns commands and failure interpretation. |
| Preserve failed candidates with their falsifiers | **PASS.** The ledger and P1/A1 reports retain terminal reasons, controls, failures, and nonclaims. |
| Exclude proof support, Lean, paper edits, commits, and pushes | **PASS.** The preservation audit found none; no PR or snapshot-acceptance action occurred. |
| Provide machine-readable evidence for every automated fact plus semantic, novelty, and claim review | **PASS.** `acceptance.json` covers all 14 facts and all seven plan-marked automated gates. Independent timing verifiers cover empirical gates; cycle-06 source validation covers novelty; the two final r2 audits cover semantic, measurement, documentation, acceptance, and preservation claims. |
| Apply the strict positive final gate | **PASS.** QR7 and Parts32 are measured, correct, causally consumed speedups. This is neither equivalent integration, unmeasured optimization, repeated old finding, nor unsuccessful search. |
| Reassess no-progress leads and avoid global impossibility claims | **PASS.** P1/A1 have explicit terminal dispositions, cycle 06 supplies the fresh independent hypothesis pass, and the final prose states only a bounded search stop. |

The operational guide's corrected commands also pass final static review. It
uses unique `mktemp` roots and copies for write-producing Parts32, same-mask,
U0, and diagnostic replays; preserves the shared measurement-exclusion lock;
separates immutable review from optional replay; lists the r2 review hashes;
and gives `unset EGGLOG_BENCH_MEMORY_GUARD; make check` for a fresh repository
check. It explains that the retained root receipt is authoritative and that a
fresh dirty-checkout run can differ. The final semantic/docs audit found 88
local Markdown links, 48 literal repository paths, and 29 printed SHA-256
values with no invalid target or identity.

## Closing audits and resolution of earlier findings

The two audits over the current frozen bytes both pass with no binding
finding:

| Audit | SHA-256 | Result |
| --- | --- | --- |
| [`final-semantic-docs-audit-r2.md`](final-semantic-docs-audit-r2.md) | `2c036133d9fafa562a410c521715e4b57731ca86ee53f58841bcf39166efefa4` | **PASS**, zero findings; semantic, measurement, validation, Diátaxis, link/path/hash, and reproduction-command review |
| [`final-acceptance-preservation-audit-r2.md`](final-acceptance-preservation-audit-r2.md) | `afffbe184aaba2591538335da33f6990e00b021759cb6daa36cb8570a9d3c27f` | **PASS**, zero findings; all 14 facts, r2/U0 attribution, root/engine/host boundary, preservation, resources, and authorization review |

The earlier `final-semantic-measurement-audit.md`, `final-docs-audit.md`, and
`final-preservation-audit.md` also passed for their then-current state. The two
r2 audits supersede them for the current file identities and recheck those
same areas after the validation cleanup.

The earlier `final-requirements-audit.md` is historical and correctly blocked
completion at that time. Each of its four tasks is now resolved:

1. `acceptance.json` now binds the local 14-fact contract and exact facts SHA;
2. the local-plan host boundary is explicit, freshly attributed, and not
   described as green or merge-ready;
3. `STATUS.md`, `acceptance.md`, and `acceptance.json` include the terminal
   P1/A1 ledger, authenticated cycle-06 work, r2 validation, and final counts;
   and
4. current-byte semantic/docs and acceptance/preservation audits both pass.

The additional direct-nits issue found during the final audit was addressed by
the r2 cleanup, followed by fresh U0 attribution, full QR7 matrix replay, host
replay, root check, and both closing audits. No earlier binding finding remains
open.

## Completion transition

The exact post-audit administrative change below is anticipated and does not
invalidate this substantive verdict:

```diff
-Phase: **acceptance passed; ready for the final goal-completion audit**.
+Phase: **complete**.
```

Applied as that one-line replacement in `STATUS.md`, its predicted SHA-256 is
`d62d6a8919b4f2699916963b4c28f462566853237eb233d77b1a201cdae422c2`.
It records the decision authorized by this audit and changes no requirement,
claim, result, evidence, or validation boundary. Any other substantive change
to a frozen deliverable or evidence authority requires a refreshed audit.

There is therefore no pending fact, final-review finding, validation action,
measurement action, documentation repair, or lead-search obligation under the
governing goal package.
