# Paper benchmark figures

From the code repository root:

```sh
./bench.py figures
cp -R figures/output/eval ../extended-egglog-paper/figures/
./bench.py figures --help
./bench.py figures math-runtime slotted-runtime
./bench.py figures --rounds 3 --memory-limit --report /tmp/figures-quick.jsonl --output-dir /tmp/figure-previews
./bench.py figures --config path/to/catalog.json
./bench.py figures --output-dir ../extended-egglog-paper/figures/eval
```

Install the root Python environment with `uv sync --locked`, the pinned Rust
toolchain, and Node.js/npm. The command builds release executables and invokes
pinned standalone `npx` packages: Vega 6.4.0, Vega-Lite 6.4.3, Vega CLI 6.4.0,
Canvas 3.2.3. No npm project or separate PDF converter is required. PDF text uses
embedded font subsets. The first run may download the pinned renderer packages.

Bare `./bench.py figures` writes one ignored output folder at
`figures/output/eval/` in this checkout, independent of the invocation directory.
Each of the six figures has seven companions: PDF, SVG, 3x PNG, `.bound.vl.json`,
`.results.json`, `.numbers.tex` and `.table.tex`. Authored specifications remain
under `figures/eval/`. Absolute artifact paths are printed on stderr.

After inspecting the outputs, copy the `eval` folder into the manuscript's
`figures/` directory with the command above. This preserves existing
`figures/eval/` PDF and TeX include paths. Generation does not require the paper
repository. PDF and TeX files are manuscript inputs with no JSON runtime
dependency; bound specifications retain the original grouped-cache URL and need
that cache for rerendering. Results JSON includes the selected observations and
their provenance. `--output-dir PATH` overrides the common output folder;
relative overrides resolve from the invocation directory.

A subset invocation updates only its selected figure filenames. Outputs from
removed or renamed catalog entries can remain in the folder. Inspect the folder
before copying it, and remove obsolete artifacts explicitly when needed.

| Figure | Comparison |
| --- | --- |
| `disequality-runtime` | Runtime/RSS boxplots with outliers for native DE, native NEE and relation-based Egglog NEE; proofs off |
| `math-runtime` | Twelve-round Math; Egg/Egglog off/checked proofs; time, peak RSS and within-engine overhead |
| `corpus-congruence-cdf` | Congruence-only time and peak-RSS overhead across the application replays |
| `corpus-proof-recording-cdf` | Recording-only proof time and peak-RSS overhead across the same replays; strict correctness coverage retained |
| `corpus-proofs-cdf` | Full proof recording, extraction and checking time and peak-RSS overhead across the same replays |
| `slotted-runtime` | Full 44-rule SDQL kernels/phases; aligned runtime/RSS encoding-to-native ratio panels and a table of both metrics |

## Flat configuration and automatic reuse

[`catalog.json`](catalog.json) contains global `rounds` and `timeout_sec` settings
and a `figures` object. Each figure declares `spec`, `files` and
`treatments`, with optional correctness-only `checks`, using shared treatment strings:

```json
{
  "rounds": 10,
  "figures": {
    "example": {
      "spec": "example.vl.json",
      "files": ["../benchmarks/corpus/eggcc/*.egg"],
      "treatments": ["off", "term", "proof-testing"]
    }
  }
}
```

No names selects every figure; names select a subset. An alternate catalog is
selected with `--config`, not a positional path. Help lists that catalog without
expanding files, reading the observation cache or building engines. Spec and
workload paths resolve relative to the catalog. Globs expand in sorted order;
recursive `**` is supported. Overlapping patterns retain each path once.
Different paths with identical bytes remain a duplicate-workload error.

Each figure requests the product of its own files and treatments. Collection
merges identical requests across figures into one plan and one progress display.
Runtime and memory views therefore share launches. It reuses compatible cached
observations and collects only missing observations; there is no separate
cached/render-only mode. Ordinary errors remain cached. Memory-limit failures
are retried after raising the cap; timeouts are retried after raising the deadline.
Completed successes remain reusable after either guard changes, including a lower
limit or removing the memory limit. Guards affect fresh work and retries rather
than the identity of completed observations.
Repeating an unchanged completed invocation launches no
additional measurements and renders the requested images again.

The default source is this checkout with label `figures`. `--target figures=@main`
selects another source using the ordinary target syntax; label-only lookups are
not source targets. `--report /tmp/figure-test.jsonl` isolates test observations.
Command-line paths resolve relative to the invocation directory. The production
catalog requests ten runs per condition. `--rounds N` overrides that count for
collection, sample selection and intervals without changing the catalog.
Use `--rounds 1` and a temporary report for CLI smoke checks.

Figures share the resource defaults in `benchmarking/config.py` with comparisons,
nightly, profiling, and paper tests: 500 seconds and a 16 GiB allocator/address-space
cap where supported, enabled without any memory flag. `--timeout-sec N` and
`--memory-limit-gib N` override them; fractional GiB values such as `2.5` are
accepted. `--memory-limit` selects the 16 GiB default explicitly, and
`--no-memory-limit` opts out for uncapped collection. `--memory-limit-bytes`
remains available for existing scripts. Peak RSS is measured
independently; the original native disequality drivers do not implement a cap.
Use three rounds and temporary report/output paths for verification. Retain the
machine and environment description with the final ten-observation results.

[`../benchmarks/ignore.json`](../benchmarks/ignore.json) is shared with the normal
Rust paper tests. Each resource or unsupported exclusion records a reason and
evidence; a cap-specific exclusion does not apply to uncapped collection. Excluded
conditions remain visible and never become successful observations. Ordinary
semantic/proof failures fail the correctness suite.
An explicitly reviewed `expected-failure` records a known bug and its exact
ordinary/candidate table counts. Rust executes that case, rejecting unexpected
passes and other failures. Figure timings include these known table-size cases;
only the figure-local timing inputs omit `expected-failure` exclusions.
All correctness checks and their exact expectations remain unchanged.
The disequality catalog retains native EE/OEE under correctness-only `checks`.
Timed `proofs`/`proof-extraction` aliases inherit `proof-testing` oracles and
exclusions; native Egg aliases similarly inherit `egg-proof-testing`.
Rust normalizes these names before registration and ignore filtering. Figure
collection and selection retain the corresponding resource and unsupported
restrictions, and exact-identity strict validation failures veto recording-only
measurements too.

The shared collection progress estimates remaining time across all missing runs.
`ETA ~` prefers current-binary cached and newly measured durations, then the
latest successful timing for the same input and treatment across
binary versions. Historical timings affect estimates only; sample selection still
requires the requested executable identity. Truly unseen conditions use the
remaining plan's known mean, or a rough one-second guess until a timing is
available; fully cached cases do not inflate that fallback.
Failures remove skipped repetitions from the estimate. Cached runs contribute
timing information without counting as elapsed work. Redirected per-run logs
include the same approximate remaining time. Build and rendering time are excluded.

Preparation phases are named on stderr before input resolution, corpus metadata,
cache loading and target resolution begin. `-v`/`--verbose` adds their elapsed
times and known counts, plus per-attempt start lines when output is redirected.
Each figure reports `Rendering NAME` before rendering and prints all output paths.

## Selection and statistics

The runner refreshes the shared typed `.reports-grouped.json`, including current
label-to-engine identities when every observation is already cached. This binding
belongs to the current grouped artifact; raw label-only lookup remains based on
recorded observations. Source targets are checked and rebound on each figure
invocation. An ordinary comparison that assigns the same label/engine to two
different binaries is rejected before launch. The raw
`.reports.jsonl` remains append-only. The shared selector matches the current
executable, physical input file hash, and treatment. Resource failures
are selected under the shared retry rule; successes remain reusable when guards
change. It binds their original row
indices into the Vega-Lite specifications. They never borrow missing measurements
from an older executable.
Native disequality `.in` and logical Egglog `.egg` inputs remain distinct.

The shared selector chooses the newest requested N applicable rows per identity, ordered by
timestamp and physical row index, including failures. Exports retain every selected
observation. Before publishing any output, the command requires all N rows to
succeed with finite runtime and positive RSS for every requested condition.
Partial observations, timeouts, missing metrics, strict validation failures and
remaining exclusions stop the command, preserving the previous output bundle. With N >= 2,
absolute mean intervals use Student's t at 95%. N = 1 permits a mean point but
no interval. Math overhead uses independent-sample Fieller-style 95% intervals;
unavailable or unbounded intervals retain their explanation. The t critical
value is the only statistical scalar supplied to the plots: Vega performs means,
sample variances, ratios, Fieller calculations, cohort selection and ranking.
The companion exports use the existing Python report estimators; a shared
fixture checks numerical parity against executed Vega transforms.

Disequality and Math absolute panels use the same gray/black boxes: medians,
interquartile ranges and 1.5-IQR whiskers. Only generated outliers appear as
individual points; there is no all-run overlay. These are distributions, not
confidence intervals for a mean. Runtime and RSS use independent absolute scales, and Math labels
each engine/proof condition directly. Actual arithmetic means and their
Student-t intervals remain in the exports.
Disequality ratios and their 95% intervals are exported for prose against the
fixed native DE baseline, with no ratio panels. Math within-engine ratios and
Slotted encoding/native ratios use uniform small black squares with capped,
asymmetric Fieller 95% whiskers and a 1x reference. No lines connect workloads.
Slotted runtime/RSS panels share the workload order and ratio scale; the
companion table contains both metrics and their intervals for every kernel/phase.

Whole-process time includes launch, input reading, parsing, lowering, execution
and requested proof work. Compilation and input conversion occur beforehand.
Checked proofs include recording, extraction/materialization and checking.
The corpus `proofs` treatment measures recording only, without extraction or
verification; its strict correctness oracle remains separate. Math retains the
checked-proof treatments, absolute costs and within-engine proof-overhead ratios.
Each corpus title states the timed treatment. Proof recording and full checked
proofs both include the congruence pass; the shared specification distinguishes
recording-only `proofs` from full `proof-testing` in its title and subtitle.
Native Egg materializes explanations in memory with explanation-length
optimization disabled; these timings do not serialize proof files. Egglog does
simplify extracted proofs. The two metrics use the same selected executions.

The corpus contains 486 saved deduplicated replays from Eggcc, HardBoiled,
MISAAL, Churchroad, DialEgg and Luminal, excluding Math. Select only a complete,
successful baseline's mean wall time >= 0.2 seconds, with no upper cutoff.
Memory and candidate outcomes never select membership. Each file has equal
weight; projects contribute different numbers of files. All three corpus figures
and both metrics share the selected denominator. Complete measurements support
empirical median/95th-percentile annotations. Incomplete conditions stop export
instead of producing partial CDFs. These CDFs are sample
summaries, not population confidence bands.
Each corpus metric gets a full-range overview only when its zoom excludes valid
values. The detail expands to the full maximum when this increases its upper
bound by at most 20%, avoiding an overview for a marginal tail. The runner binds
these layout domains from the same exported per-file ratios and omits the whole
overview composition, including its axes and space, when neither metric needs
it. Domains are recorded in the bound specification and results provenance.
Statistical points, intervals, ranks and coverage remain in Vega; changing these
viewing bounds never changes ranks or denominators.

Corpus metadata is projected lazily for selected published inputs. Aliases,
preparation blockers and exact-identity strict-validation failures are retained.
Strict-proof errors veto checked and recording proof series across resource bounds;
resource-limit outcomes stay in observation reporting. Congruence-only measurements
remain independent of strict-proof validation. Custom non-corpus figures require no corpus
validation. Collection never acquires sources, regenerates inputs or invokes
separate validators; those remain under
[benchmark reproduction](../benchmarks/reproduction/README.md).

## Inspect and hand off

The runner reads each authored specification once and binds its declared
parameters and grouped JSON URL in a temporary copy. The standard parameters are
`target_label`, `timeout_sec`, `rounds`, `t_critical`, `selected_inputs` and
`source_blockers`. Expected inputs include physical identities, selected row IDs
and corpus metadata. They scope subset configurations; statistics remain in
the authored Vega transforms. Vega resolves other
relative assets from the authored specification's directory.

Each invocation stages all requested companions and replaces the previous
images, bound specifications and numeric exports only after every requested
condition is complete and all formats succeed.
The raw JSONL and grouped JSON retain observation
provenance, including recorded resource bounds, source/binary hashes, statuses and row IDs. Preserve these
with the catalog, authored specifications, validated Math12 boundary evidence and
disequality contradiction-agreement results when handing off measurements.
Fill paper result sentences only from complete measurements; collection errors
remain explicit on stderr and in the append-only cache.

The per-figure `.results.json` retains full-precision means, bounded CI endpoints,
ratios, selected row IDs, sample counts, issues, exclusions and source provenance.
Corpus exports include the common cohort denominator, measured/failed/missing/
excluded counts and empirical median/95th-percentile values; unavailable values are
`null`. Invalid or missing measurements never become zero. The named TeX macros
and ready-to-include tables need no JSON reader or extra LaTeX package:

```tex
\input{figures/eval/slotted-runtime.numbers.tex}
\EgglogFigureNumber{slotted-runtime/batax-1st-44rules/slotted-no-aliasing-over-slotted-ref-nested/runtime/ratio}
\input{figures/eval/slotted-runtime.table.tex}
```

Keys use the figure, readable workload label, treatment and metric (`runtime` or
`memory`); suffixes include `mean`, `ratio`, `ci-low`, `ci-high`, and sample
counts. `.numbers.tex` rounds to three significant digits; JSON retains full
precision. Missing estimates/endpoints and unknown keys render `unavailable`.
Tables escape workload labels and report `CI unavailable` when a point lacks a
bounded interval. Three-round runs are layout previews; retain ten observations
and the required correctness evidence before using numbers as paper claims.

```sh
make check
```

The figure tests use synthetic snapshots without writing the benchmark cache.
They cover sample counts, means/intervals, missing/failing outcomes, label and
subset selection, cohort boundaries and coverage. Inspect all six PDFs/PNGs at
manuscript width for unclipped labels, tails and uncertainty; use `pdffonts` to
verify embedding. `make check` includes the catalog-driven Rust correctness suite:
visible table sizes, stable source results, extraction correspondence and strict proof
verification; native Math/disequality oracles; matched-policy slotted counts and
actual timing-pair targets. Only verified equal-cost single-best extraction ties
are normalized, with per-request notices. Term-mode alternatives are checked in
the ordinary pre-command graph; strict alternatives use checked source proofs.
Variant order, costs and actual proof
right-hand sides remain exact. See [the root workflow](../README.md) for the fixtures
and filters. The Python suite also checks the public comparison CLI.
