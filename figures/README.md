# Paper benchmark figures

From the code repository root:

```sh
./bench.py figures
./bench.py figures --help
./bench.py figures math-runtime
./bench.py figures slotted-runtime
./bench.py figures --rounds 3
./bench.py figures --config path/to/catalog.json
./bench.py figures --output-dir ../extended-egglog-paper/figures/eval
```

Install the root Python environment with `uv sync --locked`, the pinned Rust
toolchain, and Node.js/npm. The command builds release executables and invokes
pinned standalone `npx` packages: Vega 6.4.0, Vega-Lite 6.4.3, Vega CLI 6.4.0,
Canvas 3.2.3. No npm project or separate PDF converter is required. PDF text uses
embedded font subsets. The first run may download the pinned renderer packages.

The configured PDFs replace the paper's `figures/eval/` placeholders. SVG and 3x PNG
companions, inspectable bound specifications, and provenance receipts are
written alongside them. Absolute image paths are printed on stderr. The default
output directory is each authored specification's directory, `figures/eval/`
for the bundled catalog. The paper repository is needed only when selecting it
as the output destination.

| Figure | Comparison |
| --- | --- |
| `disequality-runtime` | Native DE, EE, NEE, OEE and Egglog NEE; absolute time/RSS and Egglog/native ratios; proofs off |
| `math-runtime` | Twelve-round Math; Egg/Egglog off/checked proofs; absolute time/RSS and within-engine proof overhead |
| `corpus-congruence-cdf` | Congruence-only runtime and peak RSS overhead across the application replays |
| `corpus-proofs-cdf` | Checked-proof runtime and peak RSS overhead across the same runtime-selected replays |
| `slotted-runtime` | Ten SDQL cases; restricted-aliasing encoding versus native nested matcher; absolute time/RSS and encoding/native ratios |

## Flat configuration and automatic reuse

[`catalog.json`](catalog.json) contains global `rounds` and `timeout_sec` settings
and a `figures` object. Each figure declares only `spec`, `files` and
`treatments`, using existing treatment strings:

```json
{
  "rounds": 10,
  "timeout_sec": 500,
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
cached/render-only mode. Ordinary errors remain cached. Memory-limit and timeout
failures are retried only after the corresponding bound increases. Successful
runs remain reusable across bound changes; after lowering the timeout, their
recorded timeout or completed wall time must fit the new deadline.
Repeating an unchanged completed invocation launches no
additional measurements and leaves unchanged images alone.

The default source is this checkout with label `figures`. `--target figures=@main`
selects another source using the ordinary target syntax; label-only lookups are
not source targets. `--report /tmp/figure-test.jsonl` isolates test observations.
Command-line paths resolve relative to the invocation directory. The production
catalog requests ten runs per condition. `--rounds N` overrides that count for
collection, sample selection, intervals and receipts without changing the catalog.
Use `--rounds 1` and a temporary report for CLI smoke checks.

The shared collection progress estimates remaining time across all missing runs.
`ETA ~` prefers current-binary cached and newly measured durations, then the
latest successful timing for the same input, facts, treatment and encoding across
binary versions. These historical hints affect estimates only, never cache reuse.
Truly unseen conditions use the remaining plan's known mean, or a rough one-second
guess until a timing is available; fully cached cases do not inflate that fallback.
Failures remove skipped repetitions from the estimate. Cached runs contribute
timing information without counting as elapsed work. Redirected per-run logs
include the same approximate remaining time. Build and rendering time are excluded.

Preparation phases are named on stderr before input resolution, corpus metadata,
cache loading and target resolution begin. `-v`/`--verbose` adds their elapsed
times and known counts, plus per-attempt start lines when output is redirected.
Each figure reports `Rendering NAME` or `NAME: unchanged`; all output paths are
printed in either case. Incomplete or unsuccessful conditions list the workload,
treatment, recorded failure reason and successful sample count, even when the
images are unchanged.

## Slotted comparisons

`slotted-runtime` covers the ten SDQL kernel/phase workloads, comparing the
restricted-aliasing encoding with the native nested matcher. The native
syntactic-substitution timing baseline differs from the encoding's snapshot
substitution, so these measurements are performance evidence rather than
equivalence certificates. The upper panels show whole-process runtime in seconds
and peak RSS in MiB from the same executions, with raw observations, arithmetic
means and 95% Student-t intervals. Lower panels show encoding/native ratios
with independent-sample Fieller-style intervals. Each metric has its own zero-preserving
symlog axis; unavailable RSS leaves the runtime estimate intact. The figure
uses ordinary terminal goals and excludes graph verification. The broader
array/logic inputs and full-matcher treatments remain
available through ordinary benchmark file selection. See the
[slotted input guide](../benchmarks/slotted/README.md) for provenance and treatment details.

## Selection and statistics

The runner refreshes the shared typed `.reports-grouped.json`, including current
label-to-engine identities when every observation is already cached. This binding
belongs to the current grouped artifact; raw label-only lookup remains based on
recorded observations. Source targets are checked and rebound on each figure
invocation. An ordinary comparison that assigns the same label/engine to two
different binaries is rejected before launch. The raw
`.reports.jsonl` remains append-only. The shared selector matches the requested
label, executable, physical input/facts hashes, treatment and encoding, then
selects rows applicable to the requested resource bounds. It binds their original
row indices into the Vega-Lite specifications. They never borrow missing
measurements from an older executable.
Native disequality `.in` and logical Egglog `.egg` inputs remain distinct.
Slotted's logical `.egg` and physical native `.ref` protocols likewise have
separate input hashes and executable identities.

The plot uses the newest requested N applicable rows per identity, ordered by
timestamp and physical row index, including failures. It retains good raw points but
reports an estimate only when all N rows succeeded and the metric is finite.
Partial observations, timeouts and missing RSS remain explicit. With N >= 2,
absolute mean intervals use Student's t at 95%. N = 1 permits a mean point but
no interval. Individual-workload ratios use independent-sample Fieller-style 95% intervals;
unavailable or unbounded intervals retain their explanation. The t critical
value is the only statistical scalar supplied by Python: Vega performs means,
sample variances, ratios, Fieller calculations, cohort selection and ranking.

Whole-process time includes launch, input reading, parsing, lowering, execution
and requested proof work. Executable builds and frozen input generation occur beforehand.
Checked proofs include recording, extraction/materialization and checking.
Native Egg materializes explanations in memory with explanation-length
optimization disabled; these timings do not serialize proof files. Egglog does
simplify extracted proofs. The two metrics use the same selected executions.

The corpus contains 486 saved deduplicated replays from Eggcc, HardBoiled,
MISAAL, Churchroad, DialEgg and Luminal, excluding Math. Select only a complete,
successful baseline's mean wall time >= 0.2 seconds, with no upper cutoff.
Memory and candidate outcomes never select membership. Each file has equal
weight; projects contribute different numbers of files. Both candidate curves
and both metrics share the selected denominator. Failed/missing ratios never
become finite timeouts or disappear from coverage.

Complete data support empirical median/95th-percentile annotations. With
incomplete outcomes, reached annotations are measured coverage thresholds;
unreached thresholds are explicitly unestablished. These CDFs are sample
summaries, not population confidence bands.

Corpus metadata is projected lazily for selected published inputs. Aliases,
preparation blockers and exact-identity strict-validation failures are retained.
The 156 unavailable source cases are separate from saved replay and baseline
counts. A historical strict-proof failure vetoes the checked-proof series only,
not congruence-only measurements. Custom non-corpus figures require no corpus
validation. Collection never acquires sources, regenerates inputs or invokes
separate validators; those remain under
[benchmark reproduction](../benchmarks/reproduction/README.md).

## Figure design

The figures target the manuscript's **139 mm** line width, checked at
526 pixels at 96 pixels/inch. The 13-point axis and annotation text scales to
approximately 8 points at this width. The exported PDFs are also checked in a
temporary paper build. These are screen inspections, not calibrated print tests.

Each figure places time on the left and peak RSS on the right. Math,
disequality and SDQL show individual process runs, means and 95% intervals in
their upper panels, with ratios and Fieller-style intervals below. Math compares
checked proofs with proofs off within each engine; disequality divides Egglog
NEE by each native encoding; SDQL divides the encoding by the native matcher.
Ratio panels retain a 1× reference. Direct labels identify configurations and
unavailable estimates. The corpus figures show ratios only.

The corpus figures separate congruence-only from checked proofs. Each figure
places runtime and peak RSS in adjacent columns, using the same executions and
runtime-selected denominator. Family colors identify dots within a pooled
ranking; they are not separately normalized family CDFs. A neutral step line
connects the pooled CDF beneath the dots. Each metric and configuration fits its
own x ranges. The full-range overview starts at zero and includes the largest
measured ratio and the 1× reference. The zoom includes 1×, starts at the observed
minimum rounded down to tenths when it is below 1×, and caps its upper bound at
twice the measured median or the full extent, whichever is smaller. Upper bounds
round upward to two significant digits; a 1.1× fallback keeps empty and zero
samples finite. This heuristic chooses the view only. Explicit range labels and
magnification identify the zoom, and the overview shades its exact interval.
Counts state how many observations fall outside the zoom; every measured tail
remains in the overview. Both views use the same ranks and
denominator. The y scales leave headroom above 100%, and scale padding keeps
boundary circles intact. Direct 50%/95% labels appear in the view containing
their crossing; an unreached crossing stays explicitly unestablished.
Valid/cohort counts appear once per metric, with failed/missing counts when
needed and one shared population summary. Detailed
family inventories remain in bound inputs and receipts instead of a second table
inside the image. Treatment identity, crossings and missingness remain readable
without hue; identifying every individual family still requires color.

The specifications use native layer inheritance and metric facets, and compute
CDF ranks once before applying viewing domains. They remain directly renderable
Vega-Lite files, without generated plotting code or precomputed statistics.

## Inspect and hand off

Each generated `.bound.vl.json` changes only declared invocation parameters and
the report data URL. The standard parameters are `target_label`, `timeout_sec`,
`rounds`, `t_critical`, `selected_inputs` and `source_blockers`. Expected inputs
include physical identities, selected original row indices and corpus metadata,
not precomputed statistics.
They scope subset configurations and keep missing conditions visible. The bound
copy can be rendered directly using the same pinned `npx vl2pdf` command, with
`--base` set to the authored specification's directory.

Each `.receipt.json` records requested resource bounds, source/binary hashes,
selected row identities and original provenance (including recorded timeouts and
the configured native allowance on allocation failures), metadata, rendering versions and output
hashes. Historical argv was not stored in the cache: command templates are
reconstructed, not claimed as recorded argv. Match `selection_sha256` between
runtime/memory receipts and hand off outputs from one invocation. Preserve the
validated Math12 boundary evidence and disequality contradiction-agreement test
results alongside the selected observations. Fill paper result sentences only
from validated measurements, keeping failed and missing cases visible.

```sh
make figures-test
make parameter-test
```

The figure tests use synthetic snapshots without writing the benchmark cache.
They cover sample counts, means/intervals, missing/failing outcomes, label and
subset selection, cohort boundaries and coverage. Inspect the configured PDFs/PNGs at
manuscript width for unclipped labels, tails and uncertainty; use `pdffonts` to
verify embedding. `make check` and `make benchmark-smoke` cover the full project.
