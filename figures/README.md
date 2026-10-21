# Benchmark figures

The authored Vega-Lite specifications load the typed `.reports-grouped.json`
written by `bench.py`. Vega performs selection, means, ratios, ranks and
percentile annotations. The root Makefile uses pinned `npx` packages; no npm
project or per-figure measurement export is required.

```sh
make figures-all                # Collect missing observations, then render.
make figures-all-cached         # Render existing data without collection.
make expanded-bench-recording   # Collect recording-only versus off.
make figures-parameter          # Existing parameter-analysis comparison.
```

Paper collection requests five observations with a 300-second timeout. Change
these with `EXPANDED_ROUNDS=N` and `EXPANDED_TIMEOUT_SEC=N`. It runs three
comparisons serially, including under `make -j`: recording/off, fully checked
proofs/off, and native Egg checked proofs/off for Math. Compatible off rows are
reused, and a cached failed condition is not automatically repeated.

All 487 checked-in corpus inputs are offered to collection. Collection and
rendering never acquire sources, regenerate inputs or run separate validation.
Those operations are explicit under [benchmark reproduction](../benchmarks/reproduction/README.md).

The commands print absolute paths for PNG/SVG pairs:

- `expanded/math-cutoff-11`: Egg and Egglog, proofs off and on, for time and
  peak RSS. On includes recording, extracting and checking the same terminal
  equality, with Egg proof minimization disabled.
- `expanded/proof-overhead-cdf`: recording-only and fully checked overhead,
  family colors, full and zoomed views, and measured 50%/90% coverage.

`figures` aliases `figures-all`. `figures-expanded` and
`figures-expanded-cached` remain aliases for the expanded figures. Cached
rendering refreshes only input/validation metadata; it neither builds engines
nor collects observations or rewrites the grouped snapshot. Direct image
targets render one specification. Unchanged metadata keeps its modification
time, so unchanged images are not regenerated.

## Selection and interpretation

The manifest retains all source aliases and preparation blockers; the small
figure inventory projects only fields consumed by the specifications. Labels
in the grouped snapshot identify the latest executable per engine, and exact
input/facts/treatment/encoding/timeout identities select its observations.
Compatible observations originally collected under other labels remain usable.
A missing condition is never filled using an older executable.

Vega uses all matching observations, with actual sample counts rather than an
assertion that every endpoint has exactly five. A mean requires a nonempty,
wholly successful finite sample. Ordinary CLI reports retain their existing
newest-requested-N selection.

CDF membership depends only on proofs-off mean whole-process time, strictly
between 0.1 and 30 seconds. The specification's `min_wall_sec` and `max_wall_sec`
parameters own this window. Memory and proof performance do not select the
cohort. Each dot represents one deduplicated replay; families are not weighted
equally. Failed or missing proof ratios remain in the selected denominator.
The chart states when a percentile threshold cannot yet be established; a
timeout is never substituted for runtime.

Ratios divide arithmetic proof-mode means by arithmetic off means. The CDF
shows measured replay ratios, not a population confidence interval. Math dots
are independent executable launches and black ticks are means. Checked timing
includes proof verification; separate strict correctness tests still run.
Matching known strict-validation failures suppress conclusions. Historical
`proof-extraction` rows are preserved but cannot satisfy the checked series.

## Review

Following [UW CSE 512](https://courses.cs.washington.edu/courses/cse512/26sp/),
check the comparison title, shared positional scales, distinct variability and
uncertainty meanings, readable labels and redundant family labels. Inspect
screen and manuscript sizes for clipping, percentile readability, visible
tails and explicit missing outcomes.
Use the CDF at approximately 180 mm manuscript width; its adjacent full/zoom
panels and coverage table are too small at an 85 mm single-column width.

```sh
make figures-parameter-test figures-expanded-test
```
