# Slotted startup optimization stack: benchmark evidence

Five cumulative commits start at main `37b148e741755823f37ec29570b12f474821c278`. Each plot
compares its commit with its immediate parent, plus parent/child comparisons
against native nested Slotted from fixed commit `155b6812c334bca00f91d8ecc33ac14acf873c86`.

Across the complete five-layer stack versus main:

Nested (10 workloads): **1.073×** final/main (95% interval 1.012–1.135); **7.3% higher measured suite time — regression**.

Encoded multipattern (8 workloads): **1.038×** final/main (95% interval 0.999–1.077); **direction inconclusive**.

[Full cumulative suite and workload results](data/cumulative-results.json). These suite results include the measured regressions alongside the smaller-query gains.

These are PR comparison pilots: 3 observations per condition,
CPU 22, 500-second watchdog, 16 GiB allocator cap.
Before each of two timing windows, its task builds/tests finished. Concurrent
builds, tests, rendering, and other heavy task work were excluded during each
window; lightweight progress monitoring was allowed.
The host is shared. Native multipattern is omitted at the user's request;
encoded multipattern remains. No benchmark exclusion policy changed.

Window 1 collected the original five-layer campaign. Full-query substitution
caused a large encoded-multipattern regression, so layers 4–5 were revised before
publication. The revised substitution strategy applies directly only in ordinary
nested mode; multipattern retains queued refinements and proof lowering is unchanged.
Window 2 measured 108 observations for those revised sources and
reused 246 observations for unchanged main/native/layers 1–3. All 354 original
observations remain in the complete export; none were removed or favorably rerun.
The final selection has 354 observations, and the export retains 462. Temporal
and shared-host effects across windows are not eliminated by the intervals.

[Complete first-window diagnostic evidence](diagnostics/first-window-cecac74c/README.md)
includes its original source, validation, manifest, full export, all five plots,
and audit. Its source is preserved at
[`cecac74c2a2a4fcdc9400b3e6fadf560b51aed89`](https://github.com/saulshanabrook/egglog-encoding/commit/cecac74c2a2a4fcdc9400b3e6fadf560b51aed89).

Ratios below 1 mean less runtime. Suite time is the sum of workload means;
large workloads dominate it. Intervals are independent Fieller 95% intervals.
Small or inconclusive changes should not be treated as established gains.

| Layer | Suite | Child / parent | 95% interval | Interpretation |
|---|---|---:|---|---|
| [1/5] Skip per-round assembly for empty-table queries | Nested (10 workloads) | 1.019× | 0.980–1.059 | direction inconclusive in this pilot |
| [1/5] Skip per-round assembly for empty-table queries | Encoded multipattern (8 workloads) | 0.993× | 0.940–1.047 | direction inconclusive in this pilot |
| [2/5] Share ordinary slotted match queues by schema | Nested (10 workloads) | 1.005× | 0.964–1.047 | direction inconclusive in this pilot |
| [2/5] Share ordinary slotted match queues by schema | Encoded multipattern (8 workloads) | 0.977× | 0.932–1.026 | direction inconclusive in this pilot |
| [3/5] Avoid reparsing generated slotted machinery | Nested (10 workloads) | 1.013× | 0.961–1.068 | direction inconclusive in this pilot |
| [3/5] Avoid reparsing generated slotted machinery | Encoded multipattern (8 workloads) | 1.024× | 1.011–1.036 | 2.4% higher measured suite time |
| [4/5] Let nested slotted substitution rounds converge | Nested (10 workloads) | 1.021× | 0.976–1.068 | direction inconclusive in this pilot |
| [4/5] Let nested slotted substitution rounds converge | Encoded multipattern (8 workloads) | 1.032× | 0.978–1.086 | direction inconclusive in this pilot |
| [5/5] Skip unused correspondence trees during core lowering | Nested (10 workloads) | 1.014× | 0.961–1.067 | direction inconclusive in this pilot |
| [5/5] Skip unused correspondence trees during core lowering | Encoded multipattern (8 workloads) | 1.013× | 0.956–1.075 | direction inconclusive in this pilot |

Validation: The final stack tip ff3ff072 passed root make check with only the exact MTTKRP-2 paper group filtered: nits, 1,167 Python tests, the ordinary Rust workspace suite (including 195 slotted proof fixtures with 2 existing exclusions), 511 paper groups, and 25 Vega tests. The actual MTTKRP-2 input then passed both encoded modes and both native nested policies separately. Native multipattern MTTKRP-2 was omitted per the requested scope; the repository ignore policy was unchanged. This is scoped final-tip validation, not an unfiltered full-suite claim for every intermediate commit. The substitution revision also passed 48 focused tests, 5 snapshots, 12 proof examples, and 24 emitted-program equivalence comparisons.

`plots/` contains five PNG/SVG/PDF bundles, bound Vega-Lite specifications,
and results with selected observations and source/binary/input hashes.
All five plots were inspected near 800 pixels wide; PDF fonts are embedded.
`data/` includes the complete public grouped export, a cumulative baseline
comparison, and the four-row nested ΣMMM/MMM focus summary with selected
observations. Raw tool-owned JSONL is not included. Public CLI tables are in
`reports/`; full protocol and source revisions are in `reproduction/`.

For reproduction, recreate the recorded worktrees, update absolute paths in a
copy of the manifest, and select a fresh report path. `collect.py` without
`--run` prints commands. The wrapper requires matching prepared-build markers;
original markers identify the measured binaries and must be regenerated for a
new build. The scripts record the exact runner source and renderer versions.
Rendered plots and bound specs require no measurement cache to view or share.
