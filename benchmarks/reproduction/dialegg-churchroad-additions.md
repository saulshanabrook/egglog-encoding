# DialEgg NMM-160 and remaining Churchroad workloads

Current Churchroad selection has **23 prepared workloads: two within the time
window and twenty-one too fast**. Ten additional phases now extract their actual
behavioral circuit and pass strict proof checking. Two feedback MACs still cannot
produce a finite expression, and four signed inputs fail import. Subsequent
hardware-compiler failure does not disqualify completed Egglog work.
NMM-160 remains blocked by host memory pressure.

The user requested these additions on 28 September 2026 after the limited corpus
qualification completed. Preserve the existing corpus and measurements while
adding DialEgg NMM-160 and the 27 inventoried Churchroad evaluation inputs.
Keep this broader input population distinct from the WOSET 2024 worked example.

Complete standalone Egglog optimizations are the unit of work. Reuse existing
captures and native prerequisites where valid; preserve original rules, schedules,
outputs, shared state, and source aliases. Record every attempted source outcome.
Device simulation and unrelated native execution are outside this task.

Qualify additions through `./bench.py` and the existing `.reports.jsonl`, using
30 proofs-off observations, a 300-second timeout, and the strict mean-time window
`0.1 < wall_sec < 30`. Proof measurements remain a subsequent stage. The safety
policy remains one heavy process at a time, a 10-GiB process-group threshold,
normal host memory pressure, and a 2-GiB host reserve. Do not retry safety stops
automatically or pool different executable hashes.

## Source results

All 28 requested source configurations have a recorded outcome. Four additional
Churchroad inputs produced complete persistent replays and passed their native
output contracts: unsigned zero-stage multipliers 8×8→8, 8×8→16, 16×16→16, and
16×32→32. The remaining 23 did not complete hardware compilation: four signed-import
assertions, four 120-second Lakeroad synthesis timeouts, and 15 missing structural
output selections. The initial admission rule rejected every failed parent.
However, 19 had completed Egglog saturation before a downstream failure; seven
also retained native specification selections. The output-selection panic is
exposed by our capture hook; the original hardware emitter requires the same
missing structural choice.

The HDL inputs are pinned to Churchroad evaluation `af615fa4`; the optimizer
remains `9f82ca23`. Although this checkout is from June 2025, its 27-input manifest
is identical to the September 2024 manifest (`2db88f18`). The evaluation driver
itself invokes Vivado and regular Yosys, not Churchroad. Applying Churchroad to
all 27 is therefore an additional experiment, not reproduction of a documented
27-case Churchroad evaluation. The WOSET paper
[demonstrates a complete unsigned 16×32→32 multiplier](https://woset-workshop.github.io/PDFs/2024/7_Scaling_Program_Synthesis_Ba.pdf),
and our corresponding `wide_mul` full capture and ordinary replay succeeded.

On 28 September the user clarified that a completed Egglog optimization with
a meaningful extraction or check is sufficient even when later synthesis or
hardware emission fails. Recovery of those phases is tracked separately in
`benchmarks/local/reproduction/churchroad-phase-recovery-20260929/`. The seven
phases with observed selections passed replay and strict proof validation.
The subsequent behavioral-extraction recovery below handles the twelve
empty-proposal phases separately. Preserve all
preceding graph state and the complete saturation schedule, and label this
boundary as mapping/specification selection rather than full hardware emission.

NMM-160 remains resource-blocked. The first historical-backend attempt used an
unoptimized debug build and stopped on host pressure. The artifact's own build
script specifies release mode, so a separately recorded build of the same pinned
backend was produced (93.97 seconds, 548 MiB peak during compilation). With that
release executable, native optimization reached 7.13 GiB and macOS pressure rose
to warning level; the guard stopped it after 41.47 seconds of native execution.
This is an ambient host-pressure interruption, not a 10-GiB threshold failure or
proof error. Neither attempt is a performance observation or a qualified replay.
No failed attempt was automatically retried with the same configuration.

## Initial full-session integration and validation

The new immutable corpus contains 831 distinct files: all 827 original identities
plus four Churchroad replays. Excluding the eight retained SpEQ files leaves 823
performance candidates. Churchroad has six prepared files in total; DialEgg still
has 26. The current experimental executable remains SHA-256
`009d3db72644c8c2993859ee8c07c43cb8c35d8e68540e3ff77540f9ef6816c4`.

Publication preserves the 1,942 unrelated source/configuration rows and all 117
previous independent-call validation jobs. Each new Churchroad replay is bound
to its own captured input, optimizer configuration, validation receipt and file
hashes. Independent review accepted these checks. Source-root dispatch and guard
checks passed 317 focused tests; publication checks passed 41 more. `make check` passed all 1,848 Python and 1,487 Rust tests (six existing Rust tests
ignored). `make benchmark-smoke` passed with 20 temporary-cache observations.
The tests and builds ran sequentially under the memory guard.

## Initial full-session normal-mode qualification

All four additions completed 30 observations each. The runner appended exactly
120 successful `off` rows; the original 47,099 rows are byte-for-byte intact.
The other 819 retained baseline samples are unchanged. A second identical command
collected nothing and preserved both cache bytes and selection bytes/mtime.

| Added Churchroad input | Mean wall time | Time-window result |
|---|---:|---|
| Unsigned 8×8→8 multiplier | 0.0879 s | Too fast |
| Unsigned 8×8→16 multiplier | 0.0629 s | Too fast |
| Unsigned 16×16→16 multiplier | 0.0751 s | Too fast |
| Unsigned 16×32→32 multiplier | 0.1539 s | Selected |

The cohort now has **434 selected workloads**, 387 too fast, zero too slow,
and two previously recorded MISAAL host-pressure failures. Nothing remains
pending among the 823 prepared candidates. This qualifies normal-mode runtimes;
proof-treatment success is not established by this collection.

| Family | Prepared files | Selected | Too fast | Cached failure |
|---|---:|---:|---:|---:|
| Eggcc | 575 | 219 | 356 | 0 |
| HardBoiled | 42 | 39 | 3 | 0 |
| MISAAL | 174 | 172 | 0 | 2 |
| DialEgg | 26 | 2 | 24 | 0 |
| Churchroad | 6 | 2 | 4 | 0 |

Under the initial whole-session policy, NMM-160 and all 23 incomplete
hardware-compilation inputs were outside those prepared-file counts. Seven
of the latter now contribute the explicitly scoped phases described below.
The eight SpEQ source files/evidence remain preserved but are excluded from this
performance cohort.

## Completed Egglog phase recovery

Later hardware synthesis or emission need not succeed when the completed Egglog
phase already has a meaningful observed result. The new offline recovery path
retains definitions, imported circuit, rules and the entire original saturation
schedule, ending with query-only equality checks for the mapping proposals and
specifications selected by the native driver. It inserts no output assumptions
and performs no new Lakeroad calls. The failed parent and exact phase boundary
remain recorded separately.

Seven additional files passed ordinary native-output validation and strict proof
checking. Removing the final saturation makes each terminal check fail, showing
that the query requires the optimization phase. The original six complete
Churchroad files and all 408 existing catalog entries are unchanged; only seven
new entries were appended. The full retained corpus now contains 838 distinct
files, including eight excluded SpEQ files.

| Recovered phase | Mean normal-mode wall time | Samples | Time-window result |
|---|---:|---:|---|
| 8×16→24 multiply, 0 stages | 8.91 ms | 30 | Too fast |
| 8×16→24 multiply, 1 stage | 8.89 ms | 30 | Too fast |
| 8×16→24 multiply, 2 stages | 8.96 ms | 30 | Too fast |
| 8×16→24 multiply, 3 stages | 9.07 ms | 30 | Too fast |
| Unsigned 16×16 multiply-add | 8.89 ms | 30 | Too fast |
| 8×8→16 MAC | 8.94 ms | 30 | Too fast |
| 16×16→32 MAC | 8.87 ms | 30 | Too fast |

All 210 new timed observations are successful `off` rows in `.reports.jsonl`.
Its original 47,219-row prefix and all 823 previous baseline samples are
unchanged. The combined cohort has 830 candidates: 434 selected, 394 too fast,
zero too slow, two historical MISAAL host-pressure failures, and zero pending.
The seven additions are available through `--suite churchroad` but do not enter
the 0.1–30 second cohort; strict proof diagnostics are not timed observations.

The updated pipeline passed independent correctness review, `make check`
(1,867 Python tests; 1,487 Rust tests; six existing ignored tests), and
`make benchmark-smoke` with a temporary cache. A fully cached rerun launched
no benchmark processes and preserved all report contents and selection bytes.
All execution was guarded.

At this checkpoint, sixteen of the 27 extra configurations remained excluded:
twelve had no mapping proposal or selected specification, and four failed circuit
import. The next recovery stage relaxes the output requirement to behavioral
circuit extraction, as requested by the user.

Evidence is in `benchmarks/local/reproduction/churchroad-phase-recovery-20260929/`:
`recovery.json` accounts for all 23 initially rejected parents;
`validation-outcomes.json`, `query-diagnostics/results.json`,
`publication-audit.json`, and `collection-audit.json` bind the recovered files,
checks, unchanged prior population and cache observations. `candidates-phases.json`
and `corpus/manifest.json` retain every source failure and alias.

Recovery from a retained failed-parent stage is explicit and offline:

```sh
uv run --locked python -m scripts.suite_capture_eggcc_churchroad churchroad \
  --recover-mapping-phase ORIGINAL_STAGE_JSON --output NEW_DIRECTORY
```

The output still requires ordinary replay validation and corpus publication;
recovery alone does not admit it. Regular `./bench.py --suite churchroad` uses
the published files and does not invoke Lakeroad or the hardware compiler.

## Behavioral circuit extraction

The user subsequently accepted ordinary extraction of the actual output circuit,
including an unchanged result, without requiring a successful DSP mapping or a
proof that needs saturation. This recovers ten of the twelve empty-proposal phases.
All ten passed ordinary execution, proof-recording execution, and strict
`--proof-testing` validation on the unchanged experimental executable.

The replay retains the imported graph and full original saturation schedule. It
marks only `Wire`, `PrimitiveInterfaceDSP`, and `PrimitiveInterfaceDSP3` as
`:unextractable`, then ends with ordinary `(extract OUTPUT_ALIAS)` commands for
the original output ports. These flags affect extraction, not rule matching or
graph construction. Existing proof treatments control whether the commands become
`prove-extract`; no proof commands or assumed target equalities are embedded in
the benchmark file. Returned programs contain real `Mul`, `ZeroExtend`, and `Var`
expressions. They need not improve on the input.

This is an adapted behavioral extractor, not Churchroad's original structural
hardware extractor or its cost policy. The output contract records that distinction,
the original ports, terminal extraction commands, and hashes of preceding state.
It rejects placeholders anywhere in a returned circuit. Strict proof diagnostics
remain separate from timed observations.

The two remaining MACs, unsigned 32×32→64 and 64×64→128, were actually replayed.
Both failed with `Unextractable root`: their accumulator feeds back through
`Reg` and `Add`, leaving no finite closed expression after excluding `Wire`.
Recovering them would require an explicit representation of sequential feedback;
this change does not cut the loop or introduce assumptions. Four signed inputs
remain blocked by the historical importer's unsigned assertions. Thus six of the
27 extra configurations remain unavailable; failures after completed Egglog work
alone are not a reason to exclude a case.

Recovery uses retained native evidence and runs no new synthesis:

```sh
uv run --locked python -m scripts.suite_capture_eggcc_churchroad churchroad \
  --recover-mapping-phase ORIGINAL_STAGE_JSON --circuit-extract --output NEW_DIRECTORY
```

Evidence is under
`benchmarks/local/reproduction/churchroad-circuit-extraction-20260929/`.
`validation-outcomes.json` retains all twelve replay outcomes;
`proof-diagnostics/results.json` records the successful proof checks;
`publication-audit.json` verifies that the prior 838 corpus identities and metadata
are unchanged. The new corpus has 848 files, including eight excluded SpEQ files.
`candidates-circuits.json` and `corpus/manifest.json` retain source failures and
aliases alongside successful captures.

The ten additions each completed 30 normal-mode measurements using the existing
cache. Means range from **9.29 to 9.65 ms**, so all ten are below the 0.1-second
admission threshold. The collector appended exactly 300 successful `off` rows;
the original 47,429 rows and all 830 previous baseline samples are unchanged.
Only ten catalog entries were appended; all 415 prior entries are unchanged.
Churchroad now has 23 prepared files, of which two are selected and 21 are too
fast. The combined five-family cohort has 840 candidates: 434 selected, 404 too
fast, zero too slow, two historical MISAAL host-pressure failures, and zero
pending. `collection-audit.json` records each new mean and the preserved cache
prefix. No proof-performance samples were collected for these too-fast additions.

Independent correctness review passed. `make check` passed 1,894 Python tests
and 1,487 Rust tests (six existing ignored tests); `make benchmark-smoke` passed
using a separate temporary cache. All builds, checks and collection ran
sequentially under the memory guard. A fully cached rerun collected no observations,
preserved the report bytes and selection bytes/mtime, and passed the checks in
`cached-verification.json`.

## Evidence and continuation

Evidence lives under `benchmarks/local/reproduction/family-additions-20260928/`:

- `requested-cases.json`: the 28 requested source identities.
- `churchroad-evidence/outcomes.md`: per-input failures with full-log links.
- `nmm160-generation/` and `nmm160-release-generation/`: both guarded attempts.
- `nmm160-release/attempt-0001/preparation.json`: original-source release build.
- `candidates-additions.json`, `corpus/manifest.json`, `publication-audit.json`:
  preserved population, published files, and original/new identity accounting.
- `final-checks/`: final validation logs.
- `collection-audit.json` and `baseline-selection-final.json`: sample counts,
  per-workload means, cached identities, and unchanged historical observations.
- `collection/cached-result.json`: no-op rerun and byte/mtime checks.

Normal-mode collection uses the existing cache and skips source blockers:

```sh
./bench.py --suite eggcc --suite hardboiled --suite misaal \
  --suite churchroad --suite dialegg \
  --baseline-window --baseline-only --target figures=. \
  --rounds 30 --timeout-sec 300
```

Proof-mode measurements remain a later stage. NMM-160 requires a deliberate new
attempt with more available memory or a larger host; its saved source-capture
failure is not automatically retried by this benchmark command.
