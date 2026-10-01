# Expanded proof-performance benchmark report

The current [collection census](local/coverage-review-20260924/BENCHMARK-STATUS.md)
separates prepared replays, missing artifact inputs, historical measurements,
and observations for the current binaries. Restored original extractions,
disabled native Egg proof minimization, and the expanded five-minute timeout
require fresh measurements under their cache identities. Selection now depends
only on normal-mode time, with per-family fast/slow exclusions reported separately
from failures and incomplete baselines.

The [family follow-up](local/family-followup-20260923/REPORT.md), its
[figure gallery](../figures/review/family-followup-20260923/index.html), and all
checkpoints below are historical evidence. Their successful validations and
timings do not establish results for the current binaries or restored workloads.

This campaign inventories complete source populations before selecting usable
measurements. Only Math has a paired Egg/Egglog implementation. The other seven
families measure Egglog's proof recording and extraction overhead. Herbie and
pointer analysis are excluded from this expansion; the original ten-workload
default is unchanged. Paired Math-analysis and Lambda examples remain
excluded because their analyses or
binding rules require semantic reconciliation beyond mechanical modernization
and scheduling changes. This campaign does not repair those discrepancies.

The machine-readable source inventory is [catalog.json](catalog.json). The
generated [coverage report](local/coverage.md) includes
every expected case, its capture outcome, current pilot admission, and measured
row counts. Its [JSON companion](local/coverage.json)
retains hashes and links to process evidence. These generated files require
the local acquisition and pilot steps in [README.md](README.md).

The original 131 prepared replay inputs were recovered after the user deleted
Cargo's `target/` directory to free disk space. Durable inputs and evidence now
live under `benchmarks/local/`. The [recovery record](local/recovery-20260922/README.md)
distinguishes restored bytes, recovered metadata, and newly executed checks
from unavailable original logs. The rebuilt Egglog binary has a different
hash because its embedded build date changed; old measurements and admissions
have not been relabeled as results for the new binary.

Before the shared-cache preparation continuation, the current binaries completed 30 selected attempts per condition for
Math's eleven cutoffs, four SpEQ cases, eight DialEgg inputs, and Churchroad's
simple multiplier: 2,100 attempts, of which 2,099 succeeded. The remaining
native Egg proof run at Math-11 was stopped by host memory pressure and stays
in the sample. Math, SpEQ, and DialEgg exports passed independent visual and
numerical review at 180 mm.

The Egglog-only portion contains 1,440 successful observations: 24 workloads
with 30 normal and 30 proof-extraction executions each. These observations are
retained. Screening now uses the same append-only cache; strict-validation
evidence remains separate. The previous Luminal host-pressure interruption is
retained as a resource outcome, not evidence of an intrinsic workload limit.

Source preparation added 35 HardBoiled replays, bringing the prepared population
to 166. All preserve the original 20-iteration schedule. Only an unexecuted
`keep-best` rule is omitted, after checking its reachability. Each replay checks
the first newly established equality in original extraction-root order. All
35 positive controls and 35 initialization-only negative controls passed;
strict proof validation remains a separate gate. Five source configurations
still have partial generator captures. See the
[source validation](local/cache-campaign-source/query-validation.json).

## Current collection checkpoint — 2026-09-23

The overnight invocation completed preparation of every captured replay and
filled all 59 ready workloads to 30 proofs-off and 30 proof-extraction
observations each: 3,540 successful observations for the admitted comparisons.
No captured workloads remain pending. The full cache contains 6,373 rows,
including historical observations and retained failures.

Since the preceding 4,291-row checkpoint, 2,082 observations were appended:
26 remaining Eggcc normal-mode successes, 25 Eggcc proof-extraction timeouts,
one Eggcc proof-extraction panic (Nussinov), and 2,030 successful observations
that completed the 35 previously partial comparisons. The errors and
resource deferrals printed in the final report also include earlier saved
outcomes; their appearance does not mean the entire overnight job failed.

Of 166 captured replays, 59 are ready and fully measured, 66 resource limited,
38 proof errors, and three historically safety-deferred. An ambient
host-pressure stop remains distinct from exceeding the 6-GiB process limit.

| Family | Replays | Ready and measured (30/condition) | Resource limited | Proof errors | Safety deferred |
| --- | ---: | ---: | ---: | ---: | ---: |
| Math | 11 | 11 | 0 | 0 | 0 |
| Eggcc | 96 | 30 | 63 | 2 | 1 |
| Luminal | 7 | 5 | 2 | 0 | 0 |
| HardBoiled | 35 | 0 | 0 | 35 | 0 |
| MISAAL | 1 | 0 | 0 | 1 | 0 |
| Churchroad | 2 | 1 | 1 | 0 | 0 |
| DialEgg | 10 | 8 | 0 | 0 | 2 |
| SpEQ | 4 | 4 | 0 | 0 | 0 |

Source blockers remain separate: 100 MISAAL configurations await generator
capture and x86 `mul` has a source-generation failure; four preserved SpEQ cases failed reference-query preparation and
two paper inputs are unavailable. Math cutoffs 12–100 remain deferred. None of
these source cases is counted as a successfully screened replay.

### Interpreting the reported errors

- **HardBoiled:** All 35 normal-mode observations succeeded; all 35 original
  proof-extraction attempts exited with code 1 before strict validation. A
  guarded diagnostic reproduction of `matmul_flat_1x1` recovered the omitted
  headline: `primitive operation lacks a validator function`. The offending
  `remove-aligned-bc-impl` rule uses `unstable-app`, which is registered without
  a validator. This is a proof-encoding compatibility limitation, not a time
  or memory limit. The benchmark report kept only the final 1,000 characters
  of stderr, dropping the useful headline. The complete reproduced error is
  in [the diagnostic log](local/diagnostics-20260923/hardboiled-matmul-flat-1x1.log).
  This diagnostic run was not appended as a performance measurement.
- **MISAAL:** The earlier exact-identity pilot completed ordinary execution and
  extraction, but strict proof checking rejected a substituted equality before
  simplification. This is a proof correctness failure, not evidence that the
  underlying vector identity is false. It remains excluded from performance
  conclusions. A fresh guarded run reproduced the same panic. Renaming only
  the three top-level `reg_0`/`reg_1`/`reg_2` globals (six identifier edits) made
  both ordinary execution and strict proof checking pass, while all 5,844 rules,
  the schedule and final check remained byte-identical. This confirms that the
  global/rule-local name collision triggers this failure. Proof materialization
  drops recorded local substitutions merely because a global has the same name;
  the checker then substitutes that global's value. See the
  [controlled diagnostic](local/diagnostics-20260923/misaal-global-rename/README.md).
  The original replay and its failure classification remain unchanged. Neither
  the earlier pilot times nor these diagnostic runs were imported into the cache.
- **DialEgg NMM80/NMM160:** These inputs were not run overnight. Historical
  peaks of about 6.2/6.1 GiB exceeded the current 6-GiB guard, so their current
  binary remains unvalidated. The final report preserves that explicit deferral.
- **Churchroad wide multiplier:** The saved normal-mode run exceeded the
  120-second timeout. Proof extraction was therefore not attempted for this
  screening outcome; it is not a proof-specific failure.
- **Eggcc:** The 26 newly screened cases all succeeded normally. Twenty-five
  timed out during proof extraction and Nussinov panicked. None of these cases
  was silently topped up to a success-only sample. The 30 ready Eggcc cases
  completed all requested observations.

[Coverage](local/coverage.md) includes every source case and current outcome.
The [overnight instructions](README.md#overnight-collection-on-this-mac) remain
valid, but rerunning the same collector now reuses these complete samples and
known failures; it does not automatically retry failed cases.

## What each family measures

| Family | Predeclared source population | Benchmark boundary and query |
| --- | --- | --- |
| [Math](https://github.com/pldi23-eqlog-ae/micro-benchmarks/tree/5360490242ec846d3323f3a8e83e3df78cb81f2f) | Cutoffs 1–11; 12–100 deferred | Seven original seeds and 24 rules; one equality first established at that cutoff |
| [Eggcc](https://github.com/egraphs-good/eggcc/tree/16be0063133ef0b8ba21cd75ee377002dc3ecbed) | All 96 passing programs: 64 Bril, 30 PolyBench, Fenwick tree, ray tracer | Pass one; the main function body acquires its declared output type |
| [Luminal](https://github.com/saulshanabrook/egglog_repro/tree/7fb0194812b5b11e41a286d8b55e48e3b0bfcd66) | Seven model exports | Complete original schedules; an Iota expression equals its derived KernelIota lowering |
| [HardBoiled](https://github.com/yihozhang/cgo2026-hardboiled-artifact/tree/b99cf0c6400e954a278f697bf3a0596ac3fa4f25) | 16 Conv1D sizes, six other convolution/resampling cells, four ML cells, four case studies, five instruction-selection programs | All reached sidecar calls retained; 30 complete and five partial captures; original schedule and one derived output equality per invocation |
| [MISAAL](https://github.com/RafaeNoor/MISAAL/tree/c098f0f289d03f0c58db1ef85d9b4ff7eef9dec4) | 102 target/program pairs: 31 ARM, 39 HVX, 32 x86 | Central rewriting/swizzle invocation boundary; frontend and pinned-engine dependencies currently prevent complete capture |
| [Churchroad](https://github.com/gussmith23/churchroad/tree/9f82ca23b273a5a500cc6a1ca60b30d3c33c5721) | Both integration circuits | Original saturating mapping phase; a selected multiplication fragment matches the derived DSP interface |
| [DialEgg](https://github.com/AzizZayed/dialegg-cgo-artifact/tree/4d0d522e98c15becdc5e7d711348cb0891ff0d44) | Five applications and NMM sizes 10, 20, 40, 80, 160 | Every exported block retained; replay queries require a newly derived equality |
| [SpEQ](https://github.com/avery-laird/lleq/tree/00bd6254b3832d94558b7c38a394ea03d01a2763) | Ten paper applications, including eight preserved FIR inputs | Independent reference-kernel matching, with the source's transformation schedules |

These are source-case counts. One input can yield several invocations, a raw
invocation can lack a usable proof query, and identical replay/fact hashes share
one measured workload while retaining their source aliases. Calls into one
persistent Churchroad engine form one replay, not several independent engines.

## Math comparability

The [pinned PLDI 2023 application](https://github.com/pldi23-eqlog-ae/micro-benchmarks/tree/5360490242ec846d3323f3a8e83e3df78cb81f2f)
supplies the same language, rules, and seven starting expressions to both
engines. The current experiment uses simple/seminaive schedules without
backoff or internal node limits. It adds proof queries and uses current local
engines, so it is not a reproduction of the Egg rebuilding or Small Proofs
evaluation.

The eleven [frozen witnesses](math/witnesses.json) are part of the hashed input.
The first uses integration over addition; cutoffs 2–10 follow successive
integration-by-parts consequences; cutoff 11 retains the derivative-of-sines
equality. The claim is: **this equality is first established by these schedules
at iteration N**. It makes no claim about mathematical truth before N or
minimum proof depth.

Each witness is checked at N−1 and N with proofs off and extraction enabled in
both engines. A negative result must be an unestablished equality, not a parser
error, unsupported operation, timeout, or memory stop. Both engines also pass
strict proof validation at N. Native Egg looks up terms before explaining
them; neither query inserts missing targets.

The pilot compares all 13 shared logical constructor counts and the Math
class count, before and after checking/extraction and across engines/modes.
Proof tables and permanent-term bookkeeping are excluded. Matching counts
support comparability but do not establish graph isomorphism. The full
boundary and count evidence is retained in the pilot records and process logs.

All eleven boundary/parity checks pass again on the rebuilt executables. The
[current validation records](local/evidence/math-parity-current-20260922.json)
contain each constructor count, the before/after checks, and the exact binary
identities. The [recovered prior records](local/recovery-20260922/math-parity.json)
are retained separately. Both validations produce the following counts:

| Iterations | Logical nodes, both engines | Classes, both engines |
| ---: | ---: | ---: |
| 1 | 69 | 50 |
| 2 | 118 | 71 |
| 3 | 208 | 116 |
| 4 | 389 | 197 |
| 5 | 784 | 361 |
| 6 | 1,576 | 666 |
| 7 | 3,160 | 1,347 |
| 8 | 8,113 | 3,576 |
| 9 | 28,303 | 12,445 |
| 10 | 136,446 | 58,464 |
| 11 | 1,047,896 | 443,832 |

The timing boundary is a fresh process, including library initialization.
Egg 0.11 uses [Quanta 0.12.6](https://docs.rs/crate/quanta/0.12.6/source/src/lib.rs): its first clock read initializes a hardware-counter
calibration loop with a 200-ms deadline and an early-convergence condition on
this macOS/ARM host. The approximately 0.203-second floor observed at small
cutoffs is consistent with that calibration cost; its exact contribution has
not been isolated. This startup cost can dominate small cross-engine
comparisons and pull Egg's proof-on/off ratio toward one. These are not
steady-state e-graph-operation timings. No startup cost has been subtracted
and neither engine's clock implementation was changed.

## Capture findings and limits

**Eggcc.** All 96 pass-one exports were captured. A query for
`FunctionHasType` would only recheck initialization, so each replay instead
checks `(Function "main" in out body) (HasType body out)`. All 96 checks fail
with the initialization phase alone and pass with the original schedule.
Proof extraction and strict validation remain separate admission gates;
successful export and ordinary execution do not imply a valid timed case.
On the prior executable, the `is-decreasing` and `nussinov` pilots pass ordinary checking but panic
during extraction (exit 101), before strict validation is reached. The
`raytrace` extraction process exits on signal 9; the sampled memory peak alone
does not establish why it was killed. Its
[recovered pilot metadata](local/recovery-20260922/current-expanded-pilots.json)
retains exact input/binary hashes and recorded failure messages; the original
process logs were deleted. This is distinct from a timeout,
and the log does not establish a deeper root cause.

**Luminal.** All seven exported programs retain their original schedules.
The added query concerns an actual lowering result, not an asserted input.
The large Gemma4 MoE export failed the prior executable's 120-second extraction
pilot; its input and failure remain visible alongside the smaller exports.
The rebuilt executable's Gemma extraction pilot stopped on elevated host
memory pressure. Coverage preserves that exact stop reason, labels the pilot
incomplete, and does not transfer admission from the previous binary.

**HardBoiled.** All 35 configurations reached the sidecar boundary, preserving
36 ordered raw calls. The 30 GPU generators completed with the separately
acquired sidecar. The five instruction-selection programs produced partial
captures before an original Linux/x86 JIT dependency failed (`fopen64`). The
artifact does not pin that external sidecar; its additional revision and
Egglog submodule are recorded separately, so continuation is not claimed as
an artifact-exact reproduction. Mechanically adapted current-CLI probes preserve the active
`keep-best` operation and fail because it is unsupported. No query or timing
is invented for those captures.
The existing default Conv1D-32 fixture comments out `keep-best` and later
schedules; it remains a bounded legacy fixture rather than standing in for
these complete source invocations.

**MISAAL.** All 102 source configurations are inventoried and obtainable.
The pinned modified Halide frontend has now been recovered and built under
monitoring after two isolated CMake-only adaptations. The original x86 `mul`
generator compiles, but its source-default execution fails at
`DistributeVec.cpp:950`: `shift_left` operands produce one versus four chunks.
This occurs before generated Python or any Egglog/proof execution. The
[capture receipt](local/family-followup-20260923/issues/misaal-prerequisites/x86-mul-generator/capture.log.json)
and [source-level diagnosis](local/family-followup-20260923/issues/MISAAL-preparation.md)
record that preparation failure. The catalog retains it for x86 `mul`; 100
other configurations still await generation. No new replay was admitted.
The existing lookahead option is an unrun configuration diagnostic, not a
compiler fix or a silently substituted source configuration.

The checked-in x86 `add` program remains the one captured case. Its completed
Egglog phase has one invocation after memoization; the external LLVM legalizer
was intentionally not run. The
[completed-phase record](local/recovery-20260922/misaal-hardboiled/misaal-regenerated-20260922-attempt2/phase.json)
retains that boundary, and the
[recovered replay record](local/recovery-20260922/misaal-hardboiled/misaal-regenerated-20260922-attempt2/cases.json)
retains two historical failed-attempt aliases separately. Replacing its terminal
extraction with a derived equality gives an initialization-only negative check
and a successful scheduled check, but strict proof validation rejects a local
substitution shadowed by a later global. This is tracked in
[encoding issue #85](https://github.com/saulshanabrook/egglog-encoding/issues/85)
with the full file and reduced reproducer. The canonical failed replay remains
excluded from performance conclusions.

The existing default HVX dot-product fixture is a separate committed test
program; it is not substituted for any of the 102 source configurations.

**Churchroad.** Both Verilog frontends and the driver's original
`saturate (seq typing transform mapping)` phase were captured. The expansion
does not use the default fixture's 17-cycle truncation. Later Lakeroad
synthesis, returned commands, and external simulation remain outside this
phase. The wide-multiply query checks its low-half fragment, not the complete
output. Unscheduled module-enumeration rules need the custom `debruijnify`
primitive. Six Egglog feature files and three embedded Rust tests remain
separately inventoried rather than being presented as mapping benchmarks.
Current global aliases are renamed hygienically to avoid collisions with
mapping-rule variables; raw fragments, literal port names, rules, and schedules
remain unchanged. Both initialization-only controls fail specifically on the
query. The simple multiplier succeeds with the original schedule; the wide
multiplier reaches the 120-second bound even with proofs off. The
[recovery record](local/recovery-20260922/eggcc-churchroad/churchroad-recovery.json)
verifies both replay hashes and distinguishes prior control outcomes from
recovered inputs. The original control logs were deleted.

**DialEgg.** All ten inputs produced 25 raw calls. Ten calls, one per source
input, have a derived equality suitable for replay. Eight calls lack an
extraction target; seven other calls only establish seeded equalities.
Those 15 calls remain in capture accounting with explicit reasons. The
negative control preserves initialization, removes the schedules, and
requires an actual failed equality check. Original call ordinals survive
selection; a third source call is still labeled as call three.

**SpEQ.** All eight preserved FIR inputs reach the reference-matching recorder.
Four reproduce the formerly combined cases: `taco_spmv_csc`,
`csparse_spmv_csc_nostruct`, `npb_is_hist`, and `parboil_hist`. Their command
streams match the existing split fixtures apart from provenance comments.
The other four reach extraction but fail their expected `gemm`/`gemv` query;
their extracted terms and failure logs are retained. The complete [artifact](https://zenodo.org/records/10963236) was streamed and
indexed: 73,109 members and all 6,259,975,347 bytes, with the published MD5
`813c94e4c12a3466909849f38b6ac1fe`. Its table-generation script maps TPAL to
`tpal_spmv` and TSVC2 to `tsvc`, but comments both out of the selected cases.
Their named C and LLVM IR inputs are absent from the full member index. Both
remain blocked; no unrelated program is substituted. The exact mapping,
expected paths, and verified-index evidence are retained in the
[reconciliation record](local/evidence/speq-paper-reconciliation.json).

## Environment and validation

The local campaign runs on an Apple M4 (10 CPU cores, 16 GiB RAM), macOS 26.6
(build 25G72). The source base is `fdd4eac12c1318c578badbf5d1299e0e3eb4e6c0`
with the benchmark expansion and existing local figure changes applied.
Exact executable and input hashes are retained in pilot evidence, measured
rows, and figure data; the source commit alone does not identify these binaries.

The complete root `make check` passed, including the Rust workspace tests.
The subsequent safety and storage changes passed all 316 Python tests and two snapshots,
formatting, lint, and type checking. The guarded public smoke passed 20 fresh
runs using a temporary cache. Nine figure tests passed, including numerical
agreement with the existing Fieller implementation, incomplete observations,
and missing-result geometry, including a wholly unavailable 96-case family.
Expanded Make tests cover sequential collection
under parallel Make, pilot exit handling, and selective image rebuilding.
Re-running data preparation preserves all nine data files. An unchanged
expanded rendering invocation preserves the contents and modification times of
all 27 data/image files and leaves the measurement cache unchanged.

Expanded designs passed independent review with synthetic data at 180 mm.
Actual Math, SpEQ, and DialEgg data also passed independent reading tasks,
coverage accounting, and comparison against the production Fieller intervals.
The reviewed SVG bytes and PNG pixels match fresh compilation. See the
[figure review](../figures/REVIEW.md). The long family
figures are intended for scrolling or full-width inspection, not shrinking
an entire suite onto one manuscript page.

## Interpreting results

Pilot admission is bound to current executable, workload, fact, and policy
hashes. The timeout is 120 seconds, and aggregate process-group RSS is sampled
against an 8-GiB threshold. This is a monitored threshold, not a kernel
allocation limit. Pilot observations never enter the measured cache.

After the user reported memory exhaustion, the continuation added a stricter
operational guard: 6-GiB workload RSS cap, normal macOS memory pressure, and
2 GiB of estimated available headroom. Expanded collection is sequential.
Known oversized cases are deferred before launch; an in-flight safety stop
retains a failed observation and halts subsequent launches. No unrelated
applications are terminated. Newly measured times include monitoring overhead;
compatible older cached measurements remain reusable.
All selected current-binary expanded observations were collected with the
guard. Prior-binary observations remain in the cache but are not selected for
the current figures. A small alternating
[sleep control](local/recovery-20260922/egglog-memory-guard-control-20260922.json)
found no systematic added wait, but cannot establish zero engine interference.
The monitor also halts after an unexplained signal-9 termination or a recorded
post-exit peak above the cap, including spikes missed by sampling.

DialEgg NMM80 passed its original pilot but reached 6.194 GiB, so measurement
is deferred under the host safety cap. NMM160 exited on signal 9 at a sampled
6.12 GiB and remains a failed pilot; that signal alone does not establish the
cause. All other admitted pilots peaked below 1.4 GiB. The safety deferral is
reported separately from correctness admission and remains visible in the
figures and coverage.

Admitted workloads request 30 measured observations per endpoint using the
default append-only `.reports.jsonl`. Compatible observations are reused
regardless of their original label. A failed measured round remains part of
the selected sample; repeated execution does not replace failures merely to
make a complete-looking plot.

The expanded Math plot shows all four engine/proof conditions over the eleven
cutoffs. Family-specific overhead figures retain each case and unavailable
outcome. Data preparation only selects and projects raw observations;
Vega-Lite computes means, variances, ratios of means, and 95% Fieller intervals.
There is no aggregate suite mean or predetermined slowdown bound. Claims apply
to the admitted cases and the recorded machine/versions, with the coverage
report supplying the omitted-population context.
