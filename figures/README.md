# Paper benchmark figures

From the code repository root:

```sh
./bench.py figures
cp -R figures/output/eval ../extended-egglog-paper/figures/
./bench.py figures --help
./bench.py figures math-runtime slotted-runtime
./bench.py figures slotted-multipattern-runtime
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
Each of the seven figures has seven companions: PDF, SVG, 3x PNG, `.bound.vl.json`,
`.results.json`, `.numbers.tex` and `.table.tex`. Authored specifications remain
under `figures/eval/`. Absolute artifact paths are printed on stderr.

The default catalog also includes the **LMFAO execution table**. Follow its
[setup instructions](../benchmarks/lmfao/README.md#reproduce) before a full run.
`./bench.py figures lmfao` selects only that experiment; other named subsets do
not require LMFAO. Missing or mismatched external inputs fail before collection.
Its outputs are `lmfao.table.tex`, `lmfao.caption.tex`, `lmfao.numbers.tex`, `lmfao.md` and
`lmfao.results.json`; plans, generated C++ and checks are retained under `lmfao/`.
The table includes paired replays of `lmfao/slotted/proof.egg` with proofs off
and with proofs generated and checked, collected through the same benchmark
harness; see the [proof replay instructions](../benchmarks/lmfao/README.md#proof-replay).
Use `\input{figures/eval/lmfao.table.tex}` inside the manuscript's table and
`\input{figures/eval/lmfao.caption.tex}` for its caption.
Load `lmfao.numbers.tex` to refer to the requested repetition count with
`\EgglogFigureNumber{lmfao/rounds}`. Completed and failed counts remain in JSON.

After inspecting the outputs, copy the `eval` folder into the manuscript's
`figures/` directory with the command above. This preserves existing
`figures/eval/` PDF and TeX include paths. Generation does not require the paper
repository. PDF and TeX files are manuscript inputs with no JSON runtime
dependency. Bound specifications and results JSON retain the selected observations
and their provenance for portable `--reuse-from DIR --no-runs` replay, without
the original working cache. `--output-dir PATH` overrides the common output folder;
relative overrides resolve from the invocation directory.

A subset invocation updates only its selected figure filenames. Outputs from
removed or renamed catalog entries can remain in the folder. Inspect the folder
before copying it, and remove obsolete artifacts explicitly when needed.

| Figure | Comparison |
| --- | --- |
| `disequality-runtime` | Runtime/RSS boxplots with outliers for the original DE implementation in Disegg and extlog; proofs off |
| `math-runtime` | Twelve-round Math; Egg/Egglog off/checked proofs; time, peak RSS and within-engine overhead |
| `corpus-congruence-cdf` | Congruence-only time and peak-RSS overhead across the application replays |
| `corpus-proof-recording-cdf` | Recording-only proof time and peak-RSS overhead across the same replays; strict correctness coverage retained |
| `corpus-proofs-cdf` | Full proof recording, extraction and checking time and peak-RSS overhead across the same replays |
| `slotted-runtime` | Full 44-rule SDQL kernels/phases; runtime ratios of extlog to Reference sorted in increasing order, with absolute runtime tables |
| `lmfao` (table) | Favorita covariance queries: LMFAO, slotted and ordinary egglog; preparation time, memory use and query-time ratios |
| `slotted-multipattern-runtime` | Complete multipattern matching on the original SDQL kernels/phases, omitting pairs with a resource-failing endpoint |

The two Slotted figures share the authored `eval/slotted-runtime.vl.json`
specification. `slotted-runtime` keeps its ten original SDQL inputs, restricted
matcher and syntactic native substitution baseline. The complete comparison uses
`slotted` and `slotted-ref-multi`, with snapshot substitution in both systems.
Its catalog uses the same SDQL glob as the baseline, followed by explicit
`!` selectors for BATAX's and MTTKRP's second phases. If either endpoint times out
or exceeds the memory limit, the entire pair
is omitted from this graph and the failing side and bound are reported in the text.
BATAX's second phase is omitted: its encoded run hit the 16 GiB allocation guard
and its native reference run timed out at 600 seconds. MTTKRP's second phase is also omitted
because its native reference timed out at 600 seconds; its encoded run succeeded.
Eight matched pairs remain. Every retained pair requires complete successful
observations on both endpoints; unexpected incomplete data still stop atomic
publication.

This supplemental comparison uses ten observations per retained endpoint at
600 seconds and 16 GiB: `./bench.py figures slotted-multipattern-runtime --rounds 10 --timeout-sec 600 --memory-limit-gib 16`.
Native Slotted is the pinned slotted-egraphs fork, a separate engine from Egg; the frozen input manifest records
its source revision and hashes.

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

The optional top-level `lmfao` entry supplies `data` and `backend` paths, relative
to the catalog. The default points to `benchmarks/local/lmfao/`, as prepared by
the case-study guide. `--lmfao-data` and `--lmfao-backend` override those paths;
`--lmfao-cxxflags` supplies custom generated-program flags, such as a Boost include
path. The selected repetition count, timeout, memory cap, report and output
directory also apply to LMFAO. It currently requires the source target to be this
checkout. A memory limit or timeout for ordinary egglog appears in the table;
publishing the table requires successful slotted measurements and checked results
from the generated programs.

No names selects every figure and table; names select a subset. An alternate catalog is
selected with `--config`, not a positional path. Help lists that catalog without
expanding files, reading the observation cache or building engines. Spec and
workload paths resolve relative to the catalog. Globs expand in sorted order;
recursive `**` is supported. Process `files` selectors in order: a positive glob
adds its matches once, while `!pattern` removes matching paths currently selected.
A later positive glob can re-add a removed path at the end. Every positive or
negative glob must match filesystem files; matching only unselected files is a
valid removal with no effect. Directories, unmatched patterns and an empty final
selection are errors. This is ordered glob selection, not gitignore syntax.
Workload counts use the resolved files, not the number of selector tokens.
Different retained paths with identical bytes remain a duplicate-workload error.

Each figure requests the product of its own files and treatments. Collection
merges identical requests across figures into one plan and one progress display.
Runtime and memory views therefore share launches. It reuses compatible cached
observations and collects only missing observations; there is no separate
cached/render-only mode. Ordinary errors remain cached. Memory-limit failures
are retried after raising the cap; timeouts are retried after raising the deadline.
Completed successes remain reusable after either guard changes, including a lower
limit or removing the memory limit. Guards affect fresh work and retries rather
than the identity of completed observations.
Repeating an unchanged completed figure invocation launches no additional
egraph measurements and renders the requested images again. LMFAO contributes
its two encodings to the same collection plan and cache. Its C++ preparation,
answer checks and execution measurements run afresh; these records have their
own schema in `lmfao.results.json` and are not egraph-cache observations.

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

The runner refreshes the shared typed `data-cache/reports-grouped.json`, including current
label-to-engine identities when every observation is already cached. This binding
belongs to the current grouped artifact; raw label-only lookup remains based on
recorded observations. Source-target invocations check and rebind their targets;
exported-data replay retains its recorded bindings. An ordinary comparison that assigns the same label/engine to two
different binaries is rejected before launch. The raw
`data-cache/reports.jsonl` remains append-only. The shared selector matches the current
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
Each Slotted figure has one runtime-ratio panel sorted in increasing ratio order.
Its companion table reports Reference and extlog mean runtimes in seconds with
95% intervals in the same order; the numeric exports retain peak-RSS statistics.

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
counts. Figure-level `FIGURE/rounds` and `FIGURE/workload-count` macros retain the
invocation's requested observation count and selected workload count.
`.numbers.tex` rounds to three significant digits; JSON retains full
precision. Missing estimates/endpoints and unknown keys render `unavailable`.
Tables escape workload labels and report `CI unavailable` when a point lacks a
bounded interval. Three-round runs are layout previews; retain ten observations
and the required correctness evidence before using numbers as paper claims.

```sh
make check
```

The figure tests use synthetic snapshots without writing the benchmark cache.
They cover sample counts, means/intervals, missing/failing outcomes, label and
subset selection, cohort boundaries and coverage. Inspect all seven PDFs/PNGs at
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

### Reuse exported figures

A figure directory is portable data and configuration: each `.results.json`
contains selected raw observations and measured engine/input identities; each
`.bound.vl.json` contains the saved drawing and settings. Gzip versions of either
file are accepted. The Slotted AST table has its own `.ast.json` snapshot.
Only selected observations are exported; unused per-ruleset profiling and the
whole local benchmark history are not copied.

```sh
./bench.py figures --reuse-from /path/to/exported/eval --no-runs
./bench.py figures disequality-runtime --reuse-from /path/to/exported/eval --no-runs
```

Without names, directory reuse discovers exported figures, including historical
names absent from the current catalog. Complete replay needs no original
workload files, checkout, executable, global report, or AST compiler. `--no-runs`
forbids measurement, builds, and AST compilation and leaves measurement caches
untouched; it still renders images and tables. Each figure retains its recorded
sample count, guards, selection, and measured versions. The renderer's revision
is recorded separately. Explicit CLI settings override recorded settings.
Exports use `figure_data_version: 2` and the current report schema. Older
exports are rejected before grouping or collection; regenerate their data and
exports with the current runtime.

Edit the saved bound specification to change a drawing directly. Alternatively,
use `--config PATH` to take drawing specifications from an authored catalog
while retaining the saved samples/settings; its workload globs are not read.
To fill missing observations, omit `--no-runs`: matching imported/local data is
reused first, then only the deficit is collected. Historical collection requires
the original input bytes and an available executable with the recorded hash;
unavailable or changed artifacts are explicit blockers. `--target SOURCE`
intentionally retargets current inputs to a new endpoint instead of silently
substituting current main for a historical measurement.

### Slotted input list and program sizes

The ignored `data-cache/` directory holds `reports.jsonl` (append-only timing
history), `reports-grouped.json` (derived timing data), and `slotted-ast.jsonl`
(compact compiler/input/pipeline measurements). Explicit cache paths remain
relative to the invocation. These local caches need not accompany portable
per-figure exports.

`slotted-runtime` exports its selected `.egg`/`.ref` file list and AST counts in
JSON, CSV, Markdown, and LaTeX. Imported tables retain recorded compiler identity
and unsupported outcomes, without storing or compiling desugared programs.
To redraw or explicitly collect AST measurements alone:

```sh
uv run --locked python -m benchmarking.slotted_ast_cli
uv run --locked python -m benchmarking.slotted_ast_cli --collect
```

The first command uses the latest recorded compiler cohort; the second resolves
the current compiler and collects only missing identities. `--compiler PATH`
selects an exact existing compiler. Ordinary fresh figure collection also uses
the current compiler; `--no-runs` never builds it. Build failures and interruptions
are not stored as unsupported programs.

Counts give one S-expression node per list, atom, or literal, excluding comments
and whitespace. The stages are input, restricted-aliasing Slotted output, and
public `ProofMode::Prove` followed by core congruence/proof lowering. Diagnostic
`Check` counts do not replace the Proofs stage, and AST input/compiler identities
must be compared separately with those of the timing figure.
The Proofs stage supports the suite's beta-substitution rule. Counts cover
emitted commands; they exclude retained source programs and Rust runtime code.
Collecting sizes does not execute the workload or check a proof.
