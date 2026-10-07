# Benchmark figures

The authored Vega-Lite specifications read the shared typed
`.reports-grouped.json` written by `bench.py`. Vega-Lite performs selection,
means, ratios, cumulative ranks, and annotations. Rendering uses pinned `npx`
packages in the root Makefile; no npm project or per-figure measurement export
is required.

```sh
make reproduce-benchmarks       # Prepare the author-derived expanded inputs.
make figures-all               # Collect missing observations, then render.
make figures-all-cached        # Render the existing grouped snapshot only.
make figures-expanded-archive  # Cached render, then gather portable evidence.
make figures-parameter         # Existing parameter-analysis comparison.
```

Outputs are printed as absolute paths. The expanded PNG/SVG pairs are:

- `expanded/math-cutoff-11`: Egg and Egglog, proofs off and recording plus
  extraction, with individual whole-process times and peak RSS.
- `expanded/proof-overhead-cdf`: recording-only and recording plus extraction
  overhead, with family-colored dots, full-range and zoomed views, and measured
  50%/90% coverage annotations for time and RSS.

`make figures` aliases `figures-all`; `figures-expanded` and
`figures-expanded-cached` remain compatible names. Parameter figures stay
separate. `make figures-data` collects expanded
comparisons and refreshes metadata without rendering. Collection is sequential,
including under parallel Make, and compatible observations are reused.

The cached target refreshes only workload/validation metadata. It does not
build an engine, collect observations, or refresh the grouped snapshot from the
JSONL. Ordinary benchmark invocations already update that snapshot. To render
just one existing specification, name its image target directly:

```sh
make figures/expanded/math-cutoff-11.png
make figures/parameter-analysis.svg figures/parameter-analysis.png
```

Rendering depends on the specification, grouped snapshot, metadata inventory,
and Makefile containing the renderer pins. Unchanged generated metadata retains
its modification time, so unchanged images are not regenerated.

## Selection and interpretation

The grouped snapshot preserves every cached observation and its original
provenance. Labels identify the latest executable per engine; compatible runs
originally collected under another label remain reusable. Current workload and
fact hashes come from a small metadata-only inventory, preventing stale inputs
from reappearing because a path or label matches.

Expanded analysis and collection use all observations for each exact identity.
Ten is the default collection request, not a chart sample-count assertion.
A nonempty wholly successful finite sample permits a mean; any failed
observation suppresses its endpoint's mean. Counts reflect the available data,
including incomplete campaigns. The ordinary positional CLI report retains its
newest-N selection.

CDF membership depends only on the proofs-off mean whole-process time, strictly
between 0.1 and 30 seconds. The `min_wall_sec` and `max_wall_sec` parameters in
the CDF spec own this window; collection runs all prepared workloads. Memory and
proof results do not select membership.
Checked-in known failures remain visible as unavailable outcomes; their proof
ratios cannot silently disappear from a selected cohort's denominator.
Each dot represents one deduplicated replay, with source aliases retained in
metadata. Families are not weighted equally. Failed/missing proof ratios stay
in the selected denominator: a 90% threshold is shown only when at least 90%
of selected replays have valid ratios. No timeout limit is treated as a runtime.

Ratios divide arithmetic proof-mode means by arithmetic proofs-off means.
The CDF describes measured replay ratios, not a population confidence interval.
Math dots are independent executable launches; black ticks are means. Strict
proof verification is outside timed collection. Known matching verification
failures suppress conclusions; missing evidence does not establish correctness.

The `figures` label is a spec parameter; the inventory records the timeout
(`EXPANDED_TIMEOUT_SEC`, default 300). Input, executable, or timeout changes need
matching observations. Old report schemas are not migrated into the cache.

## Portable evidence

`make figures-expanded-archive` writes `figures/expanded/paper-evidence.zip`; override
`FIGURE_ARCHIVE` for another destination. It gathers the specifications, images,
grouped measurements, input files, recipes, and provenance without transforming
measurements. The layout preserves relative data URLs. Its README gives a
render-only command using the included Makefile and pinned packages. The ZIP
is ignored by Git and can accompany the paper; it is not another measurement
cache and is not published automatically.

## Review and tests

Following [UW CSE 512](https://courses.cs.washington.edu/courses/cse512/26sp/),
check that the title identifies the comparison, shared positions support the
reading task, labels explain variability and uncertainty, and color has
redundant text. Inspect PNG/SVG at screen and manuscript size for clipping,
readable percentile labels, tail visibility, and explicit missing outcomes.

```sh
make figures-parameter-test figures-expanded-test
make python-check
```

Tests cover arbitrary/unequal counts, ratios of means, ties, current input and
label identities, missing endpoints, failures, shared denominators, cohort
boundary cases, unchanged output mtimes, and Make ordering. See the
[source and measurement notes](../benchmarks/README.md) and
[parameter figure notes](parameter-analysis.md).
