# Paper benchmark figures

From the code repository root:

```sh
./bench.py figures
./bench.py figures --help
./bench.py figures math-runtime math-memory
./bench.py figures --rounds 3 --report /tmp/figures-quick.jsonl
./bench.py figures --config path/to/catalog.json
./bench.py figures --output-dir ../extended-egglog-paper/figures/eval
```

Install the root Python environment with `uv sync --locked`, the pinned Rust
toolchain, and Node.js/npm. The command builds release executables and invokes
pinned standalone `npx` packages: Vega 6.4.0, Vega-Lite 6.4.3, Vega CLI 6.4.0,
Canvas 3.2.3. No npm project or separate PDF converter is required. PDF text uses
embedded font subsets. The first run may download the pinned renderer packages.

The five PDFs replace the paper's `figures/eval/` placeholders. SVG and 3x PNG
companions are written alongside them. Absolute image paths are printed on
stderr. The default output directory is each authored specification's directory,
`figures/eval/` for the bundled catalog. The paper repository is needed only when selecting it
as the output destination.

| Figure | Comparison |
| --- | --- |
| `disequality-runtime` | Native DE, EE, NEE, OEE and relation-based Egglog NEE; proofs off |
| `math-runtime` | Twelve-round Math; Egg/Egglog off/checked proofs; absolute time and within-engine overhead |
| `math-memory` | The same Math process executions, reporting peak RSS and overhead |
| `corpus-runtime-cdf` | Congruence-only and checked-proof overhead across the application replays |
| `corpus-memory-cdf` | The same configurations, executions and runtime-selected files, reporting RSS overhead |

## Flat configuration and automatic reuse

[`catalog.json`](catalog.json) contains global `rounds` and `timeout_sec` settings
and a `figures` object. Each figure declares only `spec`, `files` and
`treatments`, using existing treatment strings:

```json
{
  "rounds": 10,
  "timeout_sec": 300,
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
additional measurements and renders the requested images again.

The default source is this checkout with label `figures`. `--target figures=@main`
selects another source using the ordinary target syntax; label-only lookups are
not source targets. `--report /tmp/figure-test.jsonl` isolates test observations.
Command-line paths resolve relative to the invocation directory. The production
catalog requests ten runs per condition. `--rounds N` overrides that count for
collection, sample selection and intervals without changing the catalog.
Use `--rounds 1` and a temporary report for CLI smoke checks.

The shared collection progress estimates remaining time across all missing runs.
`ETA ~` prefers current-binary cached and newly measured durations, then the
latest successful timing for the same input, facts, treatment and encoding across
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
executable, physical input/facts hashes, treatment and encoding, then selects
rows applicable to the requested resource bounds. It binds their original row
indices into the Vega-Lite specifications. They never borrow missing measurements
from an older executable.
Native disequality `.in` and logical Egglog `.egg` inputs remain distinct.

The shared selector chooses the newest requested N applicable rows per identity, ordered by
timestamp and physical row index, including failures. It retains good raw points but
reports an estimate only when all N rows succeeded and the metric is finite.
Partial observations, timeouts and missing RSS remain explicit. With N >= 2,
absolute mean intervals use Student's t at 95%. N = 1 permits a mean point but
no interval. Math overhead uses independent-sample Fieller-style 95% intervals;
unavailable or unbounded intervals retain their explanation. The t critical
value is the only statistical scalar supplied by Python: Vega performs means,
sample variances, ratios, Fieller calculations, cohort selection and ranking.

Whole-process time includes launch, input reading, parsing, lowering, execution
and requested proof work. Compilation and input conversion occur beforehand.
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
counts. Strict-proof errors veto the checked-proof series across resource bounds;
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
and corpus metadata. They scope subset configurations and keep missing conditions
visible; statistics remain in the authored Vega transforms. Vega resolves other
relative assets from the authored specification's directory.

Each invocation renders temporary PDF/SVG/PNG files and replaces the previous
images after all three succeed. The raw JSONL and grouped JSON retain observation
provenance, including recorded resource bounds, source/binary hashes, statuses and row IDs. Preserve these
with the catalog, authored specifications, validated Math12 boundary evidence and
disequality contradiction-agreement results when handing off measurements.
Fill paper result sentences only from validated measurements, keeping failed
and missing cases visible.

```sh
make figures-test
make parameter-test
```

The figure tests use synthetic snapshots without writing the benchmark cache.
They cover sample counts, means/intervals, missing/failing outcomes, label and
subset selection, cohort boundaries and coverage. Inspect all five PDFs/PNGs at
manuscript width for unclipped labels, tails and uncertainty; use `pdffonts` to
verify embedding. `make check` and `make benchmark-smoke` cover the full project.
