# Benchmark figures

All figures read the shared typed `.reports-grouped.json` written by `bench.py`.
Vega-Lite owns selection, means, ratios, ranks, and annotations. Rendering uses
pinned `npx` packages in the root Makefile; no npm project or per-figure
measurement export is required.

```sh
make figures-parameter        # Collect missing parameter observations, then render.
make figures-parameter-cached # Existing parameter observations only.
make figures-expanded         # Collect expanded proof comparisons, then render.
make figures-expanded-cached  # Existing expanded observations only.
```

The cached targets neither build nor run benchmark executables. They refresh
exports, render changed images, and print their absolute paths. Unchanged JSON
keeps its modification time. Each renderer depends on its specification, data,
and the root Makefile containing the pinned tool versions.

Outputs, in both PNG and SVG:

- `figures/parameter-analysis`: six parameter-analysis implementations, proofs off.
- `figures/expanded/math-cutoff-11`: Egg and Egglog, proofs off and recording plus
  extraction, showing individual whole-process times and peak RSS.
- `figures/expanded/proof-overhead-cdf`: recording-only and recording plus
  extraction overhead, with the same selected replay population for time and RSS.

`make figures` aliases `figures-expanded`. The earlier per-family projections,
nested Makefile, npm manifests, and exploratory chart pipeline have been
superseded by these final specifications. Course research and design history
remain under `references/` and `REVIEW.md`; their older reproduction commands
are historical. Use the root commands above.

## Selection and interpretation

The grouped snapshot retains every cached observation, original provenance, and
physical row index. Its labels identify the latest executable for each engine;
compatible observations collected under earlier labels remain reusable. Charts
use all observations of the selected exact identity, with no fixed sample-count
assertion. The ordinary CLI report still selects the requested newest N runs.
A nonempty wholly successful finite sample permits a mean; any failed observation
suppresses that endpoint's mean. A successful three-run sample is three runs,
not an inferred promise to collect ten. Collection itself requests ten by default.

The expanded figures also read `benchmarks/local/figure-inventory.json`. This
small typed catalog export supplies current workload/fact hashes, names, source
aliases, absent captures, deliberate source exclusions, and matching strict
validation failures. It contains no benchmark observations or statistics.
Identical workload/fact identities count once, with aliases retained in metadata.
The first catalog alias supplies the family color. A family does not receive
extra weight because it has fewer workloads.

Expanded plots use the timeout in that inventory, set by
`EXPANDED_TIMEOUT_SEC` (300 by default). The `figures` label is a Vega-Lite
parameter. Current catalog hashes prevent old inputs from reappearing merely
because they have the same path. Missing current observations remain missing.
Report schemas are not migrated: older incompatible caches and changed
executables require fresh observations. Preserve historical evidence separately.

CDF membership uses proofs-off wall time alone: a nonempty wholly successful
sample with `0.1 < mean seconds < 30`. This applies the same time window as
collection, but the chart uses all observations while collection selects the
requested newest ten; membership near a boundary can therefore differ.
Memory availability and proof outcomes never select the cohort. Missing or
failed proof measurements remain in its denominator and are counted explicitly.
A 90% label appears only when at least 90% of the selected replays have a valid
ratio; it reports measured coverage, not an imputation for the missing cases.

Ratios are arithmetic proof-mode means divided by arithmetic proofs-off means.
Runs are independent executable launches, not cross-engine pairs. The CDF shows
estimated replay ratios, not confidence intervals for a population. Math dots
show individual runs and black ticks show means. Proof extraction includes
materialization and simplification, while strict proof verification belongs in
tests outside the timed runs. See [parameter notes](parameter-analysis.md) and
[expanded-suite provenance](../benchmarks/README.md).

## Review and tests

The [course-derived rubric](references/review-criteria.md) asks whether titles
state the comparison, positional scales support reading tasks, variability and
uncertainty have clear meanings, and color has redundant labels. Check exported
images at screen and manuscript size, especially percentile labels and failures.

```sh
make figures-parameter-test figures-expanded-test
make python-check
```

Synthetic Vega tests cover dynamic counts, ratios of means, ties, exact input
identities, absent endpoints, strict failures, timeout labels, and shared
cohort denominators. Python tests check catalog completeness, stable aliases,
exact validation identities, unchanged output mtimes, serial collection under
parallel Make, and cached rendering without benchmark execution.
