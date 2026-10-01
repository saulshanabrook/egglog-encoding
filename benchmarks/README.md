# Expanded proof-performance suites

The expanded campaign covers Math, Eggcc, Luminal, HardBoiled, MISAAL,
Churchroad, DialEgg, and SpEQ. Herbie and pointer analysis are excluded from
this campaign. The existing default suite remains unchanged. SpEQ is retained in source
accounting but excluded from the measured expanded cohort.

The source catalog accounts for expected inputs before selecting measurements.
Source configurations, captured Egglog invocations, and successful benchmarks
are different populations. A failed export, missing proof witness, unsupported
operation, timeout, or memory stop remains part of the coverage report.

## Measurement unit

One workload is a complete, independent e-graph computation: add its inputs,
run the supplied analysis or optimization rules, then extract or check a result.
Sequential stages that reuse graph state remain one workload. A fresh graph,
or a self-contained push/pop scope with its own inputs, is a separate workload;
shared declarations and rules alone do not make two scopes dependent.
A compiler input can produce several such workloads. Its entire compiler or
external execution pipeline is not included in these Egglog timings.

Captured calls are provenance, not automatically benchmark candidates. Explicit
per-case `benchmark_selection.workloads` lists select the substantive computations
and document their source-role reason. The selector applies before baseline
collection, proof-mode collection and figure generation. Omitted helper/setup exports
stay in capture accounting but do not become missing proof results. Reimporting
captures preserves these selections; an allowlist that no longer matches the
capture paths must be reviewed rather than silently admitting other calls.
Cases without an explicit selection retain all their captured workloads.

DialEgg retains all ten optimization kernels and three distinct shape-inference
computations. Eleven other exports have no seeded operator matching their
rules and are excluded from collection. A helper's name, a short runtime, an
unchanged extracted expression, or a proof failure alone is not an exclusion.
The three shape-inference computations remain because they actually derive
facts. All MISAAL and HardBoiled calls already initialize independent graphs;
their full schedules remain selected. Churchroad's state-sharing fragments stay
combined, and each SpEQ push/pop scope supplies its own application inputs.

Source invocation order and parent input remain recorded.
Identical workload/fact hashes share measurements without losing their source
aliases. Compilation, input generation, strict proof validation, and report
analysis are outside the timed workload. Collection uses one plan across the
cohort per treatment, with a separate executable launch for each observation.
There is no preliminary one-observation screening pass.

Only Math has a matched native Egg implementation in this campaign. The other
families compare both proof recording alone and recording plus extraction
against the same proofs-off sample. The paired source Math-analysis and Lambda examples with
known semantic discrepancies are excluded: this campaign does not repair
their analyses or binding rules to obtain favorable comparisons.

## Math checkpoints

Every Math checkpoint starts a fresh graph with the original seven seeds and
24 rules, using simple/seminaive scheduling without backoff or internal node
limits. Each cutoff from 1 through 11 has one frozen equality that must fail
at N−1 and succeed at N in both engines. Cutoffs 12–100 from the original
artifact are deferred.

The statement supported by a boundary test is “this equality is first
established by these schedules at iteration N.” It is not a claim that the
equality is mathematically false before N, or that every proof requires N
steps. Failure can mean that a required term is not yet represented.

Queries must not insert their target terms. Verification compares all 13
shared logical Math constructor counts and the Math class count, excluding
proof and permanent-term bookkeeping. Equal sizes are a useful parity check,
not a proof of graph isomorphism. Strict proof validation is separate from
extraction-only timing.

Each workload file includes its cutoff and equality. The native runner only
accepts recognized complete workload contents. This keeps the benchmark's
existing binary/file/facts/treatment/timeout cache identity sufficient; there
is no hidden iteration or query parameter outside the hashed input.
Cutoff 11 reuses the unchanged original Rational Math fixture, so compatible
observations from the original figure remain reusable.

## Preparation and collection policy

Collect normal-mode samples, freeze the time-selected cohort, then collect each
proof treatment with one plan across that cohort. Each plan requests 10
observations per condition and reuses compatible rows in `.reports.jsonl`. A
workload's first failure stops its remaining repetitions; a memory-guard stop
halts the invocation. There is no separate timed screening pass.

Correctness runs through `make check`, outside benchmark collection. Its proof
tests cover the engine and checked-in fixtures, not every ignored local corpus
file. Additional corpus proof validation and Math boundary/parity diagnostics
remain explicit, separate work with logs under `benchmarks/local/`. Missing
diagnostic evidence does not block collection or performance plots. Old pilot
timings are never imported into the measurement cache.

Each case is ready, resource limited, a proof error after normal execution
succeeds, or preparation blocked. Missing source inputs, generator failures,
and normal-mode incompatibilities are preparation blockers. Distinguish proof
extraction errors from strict-validation errors, and identify which phase timed
out or hit a resource limit. A proof-validation failure prevents a performance
conclusion even when timed executions succeeded. Timed errors are specific to
the requested mode; strict-validation failures suppress both proof comparisons.

Suite preparation and collection enable the host memory guard automatically,
including required builds. Run one heavy process at a time. The local guard
stops above 10 GiB of sampled process-group RSS, non-normal macOS memory pressure,
or less than 2 GiB of estimated available headroom. It checks before launching,
kills only the owned process group, and fails closed on monitoring errors.
Polling cannot prevent every instantaneous allocation spike. The process
timeout is 300 seconds for expanded Make targets; the ordinary CLI default is
1800 seconds; Make supplies its shorter campaign timeout explicitly. No timeout limit is reported as a measured time.

Explicitly authorized acquisition and correctness diagnostics can opt into
warning-level host pressure through `run_bounded_command(allow_warning_pressure=True)`.
The process cap, host reserve, critical-pressure stop, and monitoring checks
still apply. These diagnostics do not enter the performance cache; measured
collection continues to require normal pressure.

The operational and strict-preparation ceilings are now both 10 GiB, leaving
6 GiB outside the workload on this 16 GiB Mac. Pressure and the host reserve
can stop a run earlier; this ceiling is not a promise of available memory.
The 300-second timeout creates separate measurement identities, so older 120-second samples
and failures remain in the cache without being pooled into the new campaign.
Historical reports and logs retain their original limits.

Known timeouts, memory limits, and proof errors are retained without automatic
retries. A fresh ordinary failure ends repetitions for its comparison; a guard
stop preserves the attempt and halts the entire invocation. An ambient host
pressure stop is not evidence that the workload itself needs too much memory.
Pending cases remain pending after an interruption. Explicit retries append
evidence; they do not erase previous failures or create success-only samples.
Lowering the request to 10 does not hide a failure in the previous 30-row window:
that historical outcome still blocks automatic collection and ratios. To make a
deliberate replacement sample for such a case, request `--force-run --rounds 30`
without `--baseline-window`. No cached observations are deleted.

Preparation and measurement reuse require the exact executable, workload,
facts, treatment, and timeout identities. Labels and round counts do not create
separate caches. Keep source accounting and failed outcomes with the figures;
report per-workload results without a suite average or predetermined slowdown
bound. Larger-host experiments must measure both conditions there and remain
separate from this machine's observations.

## Source boundaries

| Family | Expected source population | Capture boundary |
| --- | --- | --- |
| Math | 11 initial cutoffs; 89 deferred | One unchanged combined-seed run and one boundary witness |
| Eggcc | 96 passing programs | One complete first-pass graph per program |
| Luminal | Seven exported model programs | Original complete schedules plus derived lowering checks |
| HardBoiled | Published Conv1D, convolution/resampling, ML, case-study, and AMX configurations | Complete fresh sidecar graphs; all store roots and saturation stages stay together |
| MISAAL | 102 target/program pairs over 39 names | Complete fresh expression-rewriting/swizzle graphs; recursive calls exchange expressions, not graph state |
| Churchroad | Two integration circuits; feature tests inventoried separately | Mapping phase; custom-operation and external-synthesis dependencies remain explicit |
| DialEgg | Five applications and five NMM sizes | Complete kernel/shape-analysis graphs; exclude eleven exports without matching rule work |
| SpEQ | Ten paper applications; eight preserved FIR programs | Independent application scopes with their complete three-stage schedule |

The pinned URLs, revisions, source case names, and capture outcomes belong in
`catalog.json`. Generated source trees and large replay files live under
ignored `benchmarks/local/`; they do not enter the routine fixture tests.

## Reproduce and inspect

The source catalog is checked in; large acquired inputs, compiler builds, and
pilot logs are local artifacts under `benchmarks/local/`. Acquisition is
separate from normal benchmark collection. Source acquisition commands run
from the repository root:

```sh
cargo build --release -p egglog-experimental
cargo build --release -p egg-math-benchmark
uv run --locked python -m scripts.suite_acquisition capture-available
uv run --locked python -m scripts.suite_capture_eggcc_churchroad eggcc --prepare
uv run --locked python -m scripts.suite_capture_eggcc_churchroad churchroad --prepare
uv run --locked python -m scripts.suite_capture_dialegg_speq \
  --family dialegg --egglog target/release/egglog-experimental

uv venv benchmarks/local/toolchains/speq-python --python 3.12
uv pip install --python benchmarks/local/toolchains/speq-python/bin/python \
  egglog==13.2.0 lark==1.3.1 z3-solver==4.15.3.0
uv run --locked python -m scripts.suite_capture_dialegg_speq --family speq \
  --speq-python benchmarks/local/toolchains/speq-python/bin/python
```

Build the two packages separately, as the benchmark runner does. A combined
Cargo build unifies dependency features differently and changes executable
hashes, invalidating admission and measurement reuse.

The DialEgg/SpEQ commands default to this Mac's Homebrew LLVM 18/17 paths;
override `--llvm18-prefix` and `--llvm17-config` for another installation.
For SpEQ, `SparseCompRow_matmult`, `spmv_npb`, and `sparsebench_spmv_csr`
regenerate application FIR from the artifact's original C and frontend passes.
The recorder retains every emitted FIR chunk and checks the unchanged reference
hashes and expected GEMV result. This is a native LLVM adaptation, not a Docker
reproduction. The four previously successful preserved-FIR fixtures are
unchanged. PolyBench's unmatched GEMM and the missing TPAL/TSVC2 inputs remain
explicit preparation blockers.
SpEQ can use an extracted archive via `--speq-artifact`; otherwise it streams
the archive and saves only the hash-verified recorder prerequisites. The
separate `--index-artifact-only` command retains the complete member index and
verifies the archive MD5 without storing the large archive itself (6.26 GB
transferred). Its paper-case reconciliation only claims a named input is
missing after checking the complete index and source-mapping hashes:

```sh
uv run --locked python -m scripts.suite_capture_dialegg_speq --index-artifact-only
```

HardBoiled and MISAAL need their original compiler dependencies. The
`suite_capture_hardboiled_misaal` module documents its `hardboiled`,
`misaal-program`, and `misaal-blocked` modes. Pass a prepared pinned checkout,
build directory, and fresh evidence output directory. Build commands, patches,
extra sidecar provenance, and observed platform failures are retained in
`benchmarks/local/evidence/{hardboiled,misaal}/`; a different sidecar is
not silently treated as the artifact's original dependency.

Capture does not silently modify the source inventory. Import its result
files explicitly; the importer checks replay existence and raw-input hashes:

```sh
uv run --locked python -m scripts.suite_acquisition import-captures \
  benchmarks/local/evidence/eggcc/stable-results.json \
  benchmarks/local/evidence/churchroad/stable-results.json \
  benchmarks/local/evidence/dialegg-capture-results.json \
  benchmarks/local/evidence/speq-capture-results.json \
  benchmarks/local/evidence/hardboiled-misaal-final/cases.json \
  benchmarks/local/evidence/speq-artifact-paper-cases.json
```

The HardBoiled/MISAAL argument is the local consolidated outcome file;
new acquisition attempts can supply their own result paths instead. The last
argument applies the complete-index paper-case reconciliation after the replay
capture results. Preserve
all attempts rather than overwriting failures with a later success.

Each capture retains raw invocations before adaptation, the source revision,
input digest, invocation order, and generation outcome. Original extraction
requests retain all their roots, variant counts, order, and graph scopes.
Extraction can legitimately return an initial term before any rule runs;
initialization-only negative controls apply to intentional derived checks,
not these extraction requests. Churchroad's captured mapping phase is explicitly a prefix of its full
external-synthesis driver. The original saturating mapping schedule is kept;
the default workload's 17-cycle truncation is not used for this expansion.

For MISAAL captures made with the original backend, prepare replay candidates
from the saved calls, preserving their original extraction requests:

```sh
uv run --locked python -m scripts.suite_capture_hardboiled_misaal misaal-capture-replay \
  --capture PATH/TO/capture.json --output PATH/TO/FRESH-DIRECTORY
```

This preserves declarations, seeds, and the source iteration count; only terminal
global names and extraction syntax change. Successful calls from partial captures
remain candidates, with failures and all source aliases retained. Candidates need
ordinary execution before timing classification; source preparation alone
does not establish performance or proof correctness.

```sh
make expanded-pilot       # Finish normal-mode samples and freeze baseline selection.
make expanded-bench       # Finish baselines, both proof modes, and paired Math iteration 11.
make expanded-coverage    # Refresh full source-case coverage from existing evidence/cache.
make figures-expanded    # Collection, grouped reports, and SVG/PNG exports.
```

Collect normal-mode samples first, then proof overhead for the selected cohort:

```sh
./bench.py --suite expanded --baseline-window --target figures=. \
  --treatment proofs --compare-treatment off \
  --rounds 10 --timeout-sec 300

./bench.py --suite expanded --baseline-window --target figures=. \
  --treatment proof-extraction --compare-treatment off \
  --rounds 10 --timeout-sec 300
```

All conditions request 10 observations. Older cached rows remain intact, and
selection uses the newest matching rows. The cohort is recomputed from 10 normal
runs; its membership can change near either time cutoff compared with the earlier
30-run selection.

Selection requires 10 successful normal-mode observations with mean external
wall time strictly above 0.1 seconds and below 30 seconds. Memory and proof
outcomes do not enter this decision. Both the time
and memory figures use this same cohort. Previously blocked proof cases can
therefore receive their missing normal-mode observations without retrying
proof extraction. Existing cache identities and observations are unchanged.

Repeat `--suite` to choose a subset, such as `--suite eggcc --suite luminal`.
Both comparisons reuse Off observations; neither runs strict proof validation. Restoring original
extracts changes input hashes and a new engine changes its executable hash, so
those identities require fresh measurements. Historical single-check timings
are never presented as measurements of all original extraction roots.

`--baseline-only` stops after normal-mode collection. The current selection,
source aliases, exact binary/input/facts hashes, timeout, cache row indices,
and sample digest are written to `benchmarks/local/baseline-selection.json`.
The console and selection JSON include per-family selected, too-fast (at most
0.1 seconds), too-slow (at least 30 seconds), pending, and failed counts.
Only complete successful baselines can be classified as too fast or too slow.
Aliases do not duplicate a workload within a family; a shared workload can
appear in multiple family counts while counting once in the overall population.
Completed selections also have immutable copies in `baseline-selections/`.
Unsuccessful normal runs prevent eligibility; incomplete baselines remain
unresolved. Selected proof failures remain in the denominator of the overhead
plots. Known strict-validation failures remain explicit and suppress ratios.

A family with no eligible replays contributes no programs to the paper
comparison. Keep its source inventory and exclusion reasons in the coverage
report. Do not conclude that a family is too fast while normal samples or
source preparation are incomplete, or when failed runs leave the timing
unknown. The 30-second upper bound selects a cohort; it is separate from the
300-second process timeout used by expanded Make targets. A later change to the selection window must be
declared and applied to every family using the same cached baseline samples,
with a new frozen selection snapshot. It must not depend on proof results.

The dedicated Math figure requires paired Egg/Egglog observations for
iteration 11, independently of the overhead cohort. `make expanded-bench`
collects each engine's extraction/off comparison without a correctness pilot.
Classified failures remain visible; safety or infrastructure failures stop the pipeline. Source acquisition is a separate step: Make benchmarks the
available complete replays, not missing artifact inputs.

`make figures-expanded` runs four benchmark commands, one per comparison, and
renders only the final Math and combined overhead PNG/SVG pairs. The first
command finishes baseline collection itself; `make expanded-pilot` is an optional
baseline-only entrypoint, not an extra prerequisite. Each proof mode uses a
single collection plan across the selected cohort. Off samples are shared
between proof modes, and there are no screening or strict-validation runs. Both
time and memory come from the same measured process, with no separate memory
benchmark.

The eleven DialEgg exports without matching rule work are omitted before both
baseline and paired collection. Their unchanged files and capture records remain
available as provenance, with explicit source-selection reasons. Four other
calls (three distinct identities) have validated shape-inference queries using
supported `Vec i64`, `vec-of`, and `vec-get`; they remain standalone workloads.
These queries establish derived dimensions, not a matrix optimization.
Substantive normal-only workloads in other families still receive baseline
collection independently of their proof-query or proof-validation status.

Omitting `--baseline-window` collects the full selected suite without the time window.
With `--suite`, the defaults are proof extraction versus proofs off, 10 rounds,
and the ordinary 1800-second timeout. Expanded Make targets explicitly use
300 seconds. Explicit options override these defaults.
`--suite math-11` selects only iteration 11;
`--suite math-growth` selects the eleven Math checkpoints. To collect the older
growth figures as well, use `make figures-expanded FIGURE_MATH_SUITE=math-growth`
followed by `make -C figures expanded-details`. Repeated `--suite`
arguments select a stable union and deduplicate identical workloads without
losing source aliases. Suites cannot be combined with positional input files
or a fact-directory override. Bare `./bench.py` still selects its existing
defaults and its original treatments and round count.

Baseline-selected collection measures proof modes only after all baselines
are classified. Suite collection does not require a correctness pilot.
Classified failures remain visible and do not trigger repeated collection. `--force-run` is an
explicit request for a fresh attempt or batch; it never deletes old rows or
establishes strict proof validity. Baseline-window mode rejects `--force-run`
so it cannot silently replace the selection sample. Resolve a known proof
error through separate correctness testing before drawing a conclusion from
that case. Interactive reports retain known invalid outcomes. A
`./bench.py` exit code of 0 means the invocation completed, including classified
workload errors or timeouts; 2 denotes a handled infrastructure or safety
interruption. Expanded Make targets stop on every nonzero exit, including
unexpected Python or launcher failures.

The complete generated report is
`benchmarks/local/coverage.md` (with corresponding JSON). Its rows retain
source cases without any replay or measurements, partial capture reasons,
ordered invocation identities, and failures. `benchmarks/catalog.json` holds
shared pinned source provenance; report links and file hashes bind the local
evidence. Source-case counts must not be interpreted as successful-run counts.

## Overnight collection on this Mac

This command finishes normal-mode collection, then collects the
selected proof comparisons:

```sh
/usr/bin/caffeinate -i make expanded-bench
```

Normal mode, recording-only, and recording-plus-extraction run sequentially.
A safety or infrastructure failure stops the command before later stages;
classified workload errors and timeouts do not. Rerunning fills missing normal samples
and proof samples for selected ready cases, without retrying known failures.

`caffeinate -i` prevents idle sleep while the command runs. Keep the laptop open
and connected to power. Close unused apps before starting; the memory guard
remains active. All observations append to `.reports.jsonl`. Existing samples
count toward 10 per condition, so the same command resumes interrupted
collection without repeating complete samples or known failures.

For selected families, replace `--suite expanded` with repeated selections such
as `--suite eggcc --suite hardboiled`. Do not run collectors concurrently.
Source blockers and classified failures remain in the report; missing
correctness evidence does not launch extra benchmark or validation processes.
After collection, `make expanded-coverage` refreshes the coverage files. A zero
collection exit status does not mean all cases succeeded; inspect the report.
