# Frozen paper benchmark support

These tools read selected cached observations or reproduce a small variant of a
pinned benchmark source. They do not collect new observations.

## Recording-only CDF

`export_recording_cdf.py` reads the self-contained selected observation artifact
published with the paper figures. Supply paths explicitly:

```sh
python3 scripts/benchmark_support/export_recording_cdf.py \
  --selected /path/to/applications-corpus-proof-recording.selected.json.gz \
  --output-dir /tmp/recording-cdf
```

The selected artifact supplies the OFF and `proofs` observations, endpoint pins,
workload metadata, and figure template. The exporter requires ten successful
observations for each endpoint and workload, with matching binary, source,
worker count, timeout, and memory limit. It writes the results, bound Vega-Lite
specification, and TeX numbers/table. Add `--render` to render a PDF with the
pinned Vega npm packages; npm may download packages when they are uncached.

Each input contributes one recording/OFF ratio of arithmetic means. Percentiles
use the inverse empirical CDF. Per-input independent-sample Fieller intervals are
retained in the results; they are not a population confidence band. The plot has
no title or trendline and uses the x-axis label **Proof overhead**. The selected
486-input artifact yields median 3.6543605757500455 and p95 4.7032147389185015.

`proofs` means `--proofs`: record proof evidence while retaining ordinary program
checks and term extraction. It does not extract or verify proof certificates.

## Checked Math without simplification

`checked-unsimplified-d627.patch` is a frozen benchmark-support patch for source
`d627d94e9aef9adcfd72e1aa2d042ed51990eae3`. Apply it only to an export of that
revision, rather than to another runtime revision:

```sh
mkdir -p /path/to/export
git archive d627d94e9aef9adcfd72e1aa2d042ed51990eae3 | tar -x -C /path/to/export
cd /path/to/export
patch -p1 < /path/to/checked-unsimplified-d627.patch
cargo build --release --locked -p egglog-experimental \
  --no-default-features --features bin --bin egglog-experimental
cargo test --release --locked -p egglog --lib --no-default-features \
  --features bin checked_unsimplified_mode_preserves_validation_and_extracts
```

Use the pinned export's toolchain and lockfile. The new treatment is
`proof-testing-unsimplified`; its CLI flag is `--proof-testing-unsimplified`.
It records, extracts, and checks proofs while skipping optional simplification.
Required materialization, lifting, container normalization, and witness handling
remain. Unsimplified proofs are checked once; existing treatment behavior is
unchanged. The native Math driver already disables explanation-length
optimization; use `--proof-mode check --math12` for its matching checked mode.

Use the same patched executable for one- and four-worker Math observations.
Record a new binary SHA-256 and the base revision plus patch identity; the export
is a patched source, not a clean instance of the base revision. At four workers,
omit `--timing-summary`, which the pinned runtime supports only at one worker.
Keep recording-only Math overhead observations separate from this checked mode.

## Headline speedups

Generate the four headline macros from public selected figure results:

```sh
python3 scripts/benchmark_support/export_headline_speedups.py \
  --figures-dir /path/to/paper/figures/eval \
  --output /tmp/headline-speedups.numbers.tex
```

Math uses `math-checked-unsimplified.results.json.gz`: proof extraction and
checking are included, while optional proof simplification is disabled in both
implementations. Disequality and restricted SDQL use the fixed-suite means in
`integrated-runtime-means.results.json.gz`. Each speedup is the native mean
divided by our serial mean; it is neither a mean of per-input speedups nor a
comparison against four-worker execution. Speedups are formatted to two decimal
places. The project count comes from the congruence CDF's selected metadata.
The output provides `headline/math-checked-speedup`,
`headline/disequality-speedup`, `headline/slotted-restricted-speedup`, and
`headline/corpus-project-count` through `\EgglogFigureNumber`.

## Appendix CDFs

Both exporters take explicit selected-data and output paths and preserve the
published points, plot styles, and inverse empirical CDF quantiles:

```sh
python3 scripts/benchmark_support/export_corpus_congruence_cdf.py \
  --selected /path/to/corpus-congruence-cdf.selected.json.gz \
  --output-dir /tmp/congruence-cdf
python3 scripts/benchmark_support/export_corpus_proof_stages_cdf.py \
  --selected /path/to/corpus-proof-stages-cdf.selected.json.gz \
  --output-dir /tmp/proof-stages-cdf
```

The congruence plot compares term encoding against OFF. The two proof-stage
panels show recording plus extraction, and recording plus extraction plus
checking, against OFF. These retained corpus modes preserve their original
simplification behavior; they are separate from the unsimplified Math
comparison. The exporters consume only existing selected results and never
collect observations or launch an engine. Add `--render` for the pinned npm PDF
renderer; without it, only JSON and TeX artifacts are written.
