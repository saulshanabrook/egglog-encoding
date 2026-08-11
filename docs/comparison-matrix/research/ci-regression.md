# Continuous-benchmarking prior art: commit-vs-commit comparison pages and comparison-matrix machinery

Research date: 2026-08-11. Question: how do mature systems specify WHAT to compare across a factor lattice (target × backend × treatment × workload × metric), how do they display big comparison matrices, and how do they decide which deltas matter? Focus systems: rustc-perf, LLVM LNT, Mozilla Perfherder, arewefastyet, Chromium perf/Pinpoint, the MongoDB change-point line (Daly → Hunter → Otava → Nyrkiö), CodSpeed/Bencher/Conbench, plus CLI-scale tools (benchstat, asv, pyperf) and the statistics/vis literature that functions as a "conceptual language" for comparisons.

---

## 1. rustc-perf / perf.rust-lang.org compare page (the deep dive)

Repo: https://github.com/rust-lang/rustc-perf — live page: https://perf.rust-lang.org/compare.html

### 1.1 The factor lattice

From the glossary (https://github.com/rust-lang/rustc-perf/blob/master/docs/glossary.md):

- **test case** (compile-time) = benchmark × **profile** × **scenario** × **backend** × **target**.
  - profile: `check` (cargo check), `debug` (cargo build), `opt` (`--release`), `doc`, `doc-json`, `clippy`.
  - scenario: `full` (non-incremental), `incr-full` (incremental, cold cache), `incr-unchanged` (warm cache, no change), `incr-patched` (warm cache + a source patch; a benchmark can define several patches, e.g. "println").
  - backend: `llvm`, `cranelift`; target: e.g. `x86_64-unknown-linux-gnu`.
  - benchmark **category**: `primary` (real-world crates), `secondary` (stress tests), `stable`.
- **metric**: `instructions:u` (default), wall-time, `cycles:u`, `max-rss`, `size:linked_artifact` etc. Instruction count is default because it is "quite stable (=resistant to measurement noise)" and "usually relatively highly correlated with wall time" (Kobzol, "Exploring the Rust compiler benchmark suite", 2023: https://kobzol.github.io/rust/rustc/2023/08/18/rustc-benchmark-suite.html). ~50 benchmarks × ~13 configurations × 3 iterations per artifact.
- **test result** = the **minimum** of the 3 iterations' statistics (glossary: "the minimum value of a statistic from all the test iterations is used for analysis").
- **artifact comparison** = set of **test result comparisons** between two artifacts (commit SHAs, tags, or try builds). Default baseline for a master commit is its **parent master commit**; PR "try" builds are rebased onto master and compared against that master artifact.

The comparison "specification language" is just URL parameters — `compare.html?start=<sha>&end=<sha>&stat=<metric>` — the page then enumerates *every* test-case comparison and the user prunes with filters. Specification burden is pushed onto filtering, not enumeration.

### 1.2 Significance machinery (docs/comparison-analysis.md + site/src/comparison.rs)

Doc: https://github.com/rust-lang/rustc-perf/blob/master/docs/comparison-analysis.md — code: https://github.com/rust-lang/rustc-perf/blob/master/site/src/comparison.rs

- Relative change: `100 * ((statisticForArtifactB - statisticForArtifactA) / statisticForArtifactA)`.
- **Historical noise model, learned per test case**: take the last `NUM_PREVIOUS_COMMITS = 30` master commits, compute abs deltas between adjacent results divided by the value (i.e., a distribution of commit-to-commit relative changes), and set the **significance threshold** by IQR fencing: `threshold = Q3 + (Q3 − Q1) * IQR_MULTIPLIER` with `IQR_MULTIPLIER = 3.0`. Lower fence ignored ("result data is bounded by 0"). If fewer than 30 commits of history exist, fall back to `DEFAULT_SIGNIFICANCE_THRESHOLD = 0.002` (0.2%).
- **significant** ⇔ `|relative_change| >= significance_threshold`.
- **significance factor** = `|relative_change| / significance_threshold` ("how many times the threshold this change is") — displayed per row in the UI.
- **Magnitude** = a 5-bucket ordinal (`VerySmall..VeryLarge`) computed as the *average of two ordinal scales*:
  1. over-threshold scale: change < 1.5×, 3×, 6×, 12× threshold → VerySmall/Small/Medium/Large, else VeryLarge;
  2. absolute-% scale (metric-dependent): change% / `noise_factor` < 0.2, 1, 2, 5 → VerySmall/Small/Medium/Large, else VeryLarge, where `noise_factor = 2.0` for every metric except `instructions:u` ("we conservatively consider everything except instructions to be noisy").
  A guard returns VerySmall outright if the change < 0.01% regardless of threshold ratio.
- **relevant** ⇔ significant ∧ magnitude ≥ Small. Non-relevant rows are hidden by default.
- **Summary rollup** (per artifact comparison): label = improvement / regression / **mixed**, with rules: both directions have medium+ magnitude → mixed; one direction medium+ and the small-magnitude other direction is ≥15% of total changes → mixed; all-small changes → mixed unless ≥90% are one direction.
- **Relevance of the whole summary** (High/Medium/Low) gates reporting: PR try-run bot comments post if "somewhat relevant"; the weekly triage report only includes "definitely relevant" comparisons.

### 1.3 UI: default rollup + drill-down + filters

Compare-page filter panel (https://github.com/rust-lang/rustc-perf/blob/master/site/frontend/src/pages/compare/compile/filters.vue): free-text benchmark filter; checkbox sets for profile, scenario, backend (LLVM/Cranelift), target, category (primary/secondary), artifact type (binary/library), change direction (regressions/improvements); toggles "Show non-relevant results", "Display raw data", "self compare backend". A metric selector switches the whole page between instructions/walltime/cycles/max-rss/size. Summary tiles show counts of relevant regressions/improvements and range/mean of change per primary/secondary. Each row expands to per-test-case detail (history chart, self-profile query deltas).

### 1.4 Triage process (human loop)

https://github.com/rust-lang/rustc-perf/blob/master/triage/README.md — weekly report generated by `curl "https://perf.rust-lang.org/perf/triage?start=$PARENT"` (a *series* of pairwise parent comparisons over the week); `&metric=size:linked_artifact` variant for binary size. Triage advice: instruction count, max-rss, binary size are what to scan; "max rss is much more variable than instruction count. Recheck the 'Absolute data' checkbox otherwise the noise becomes unmanageable"; rollup merges are dissected via per-PR "unrolled build" perf runs (`@rust-timer build $SHA`). Noise verdicts come from eyeballing the history graph — the significance model reduces but does not eliminate human noise adjudication.

**Takeaway**: rustc-perf is the most principled *pairwise* comparison UI in production, and its whole significance stack is ~300 lines: per-cell empirical noise window (30 commits, IQR fence ×3), a scalar significance factor, 5 magnitude buckets from averaging two ordinals, and counting rules for rollup labels. Everything is derived from data the system already stores.

---

## 2. LLVM LNT

Docs: https://llvm.org/docs/lnt/concepts.html — code: https://github.com/llvm/llvm-lnt

- Data model: **order** ("the x-axis... the thing that is changing" — revision or version), **machine** ("any configuration you are interested in tracking", e.g. "ArmMachine-Release" vs "ArmMachine-Debug" — note: LNT models config variants by multiplying *machines*, a known-clunky choice), **test**, **sample**, **run** (one submission = one order × machine × samples).
- Analysis (`lnt/server/reporting/analysis.py`, https://github.com/llvm/llvm-lnt/blob/main/lnt/server/reporting/analysis.py): verdicts `REGRESSED / IMPROVED / UNCHANGED_PASS / UNCHANGED_FAIL`. Aggregation function is min by default (flips to max when `bigger_is_better`). Gauntlet of checks, in order:
  1. ignore if binary hash unchanged (`ignore_same_hash`) — a *provenance-based* noise filter;
  2. ignore if `|pct_delta| < MIN_PERCENTAGE_CHANGE = .01` (1%) **and** ignore if `|delta| < MIN_PERCENTAGE_CHANGE` absolute (comment admits: "There is no mathematical basis for this... practical evidence indicates what we currently have isn't good enough");
  3. ignore if `|delta| <= 2 * value_precision * 2.576` (quantization guard, `MIN_VALUE_PRECISION = 0.0001`);
  4. **Mann-Whitney U test** at `confidence_lv = 0.05` when both sides have ≥4 samples → UNCHANGED if not rejected;
  5. else stddev-based symmetric CI: significant iff `|delta| > stddev * 2.576`;
  6. else report changes above 0.2%.
- UI: **daily report** page — "how performance evolved over the past 7 days, one column for each day", sparklines, background color from binary-hash identity; run pages show "performance changes seen since the previous run" with per-function profile diffs (LLVM blog, "Using LNT to Track Performance", 2016: https://blog.llvm.org/2016/06/using-lnt-to-track-performance.html).

**Takeaway**: LNT is the cautionary tale — a stack of ad-hoc floors (1% pct + absolute + quantization) bolted around a nonparametric test, and config variants encoded by machine-name multiplication. Its two good tricks: min-aggregation to kill right-tail noise, and skipping comparisons when the artifact hash proves nothing changed.

---

## 3. Mozilla Perfherder compare view (and PerfCompare)

- Wiki: https://wiki.mozilla.org/TestEngineering/Performance/Sheriffing/CompareView — docs: https://firefox-source-docs.mozilla.org/testing/perfdocs/standard-workflow.html — successor tool announcement: https://blog.mozilla.org/performance/2022/06/30/introducing-a-new-performance-comparison-tool-perfcompare/ (PerfCompare, https://perf.compare).
- Model: **base** revision vs **new** revision (possibly different repos, e.g. try vs mozilla-central), rows = test × platform, columns: base avg, new avg, delta %, magnitude bar, **confidence**.
- Confidence = the two-sample **t-test value** displayed as a number plus a categorical label. Exact thresholds in treeherder source (https://github.com/mozilla/treeherder/blob/master/ui/perfherder/perf-helpers/constants.js): `tValueCareMin = 3` ("Anything below this is 'low' in confidence"), `tValueConfidence = 5` ("Anything above this is 'high'"), i.e. low < 3 ≤ med ≤ 5 < high. When a side has a single sample, stddev is imputed as `0.15 * avg` (`getTTest` in https://github.com/mozilla/treeherder/blob/master/ui/perfherder/perf-helpers/helpers.js).
- Workflow lever: **retriggers** — the documented way to firm up a suspicious row is to rerun that test N more times on both revisions and recompute ("Retriggering tests will increase the number of data points... produce a higher confidence").

**Takeaway**: Perfherder's contribution is the *confidence column as a first-class display element* (continuous t-value + 3 coarse labels) and the retrigger loop: sample size is adaptively increased only where the comparison is interesting-but-uncertain.

---

## 4. arewefastyet (two of them)

- Mozilla AWFY (JS-engine shootout, arewefastyet.com, now defunct as originally built): multi-*system* (SpiderMonkey vs V8 vs JSC) commit-series line charts on shared benchmarks — comparison by **superposition of time series**, no significance machinery. Historical reference: https://github.com/mozilla/arewefastyet.
- Vitess arewefastyet (https://github.com/vitessio/arewefastyet, https://benchmark.vitess.io): cron + PR-triggered executions; macro (sysbench OLTP/TPCC) and micro benchmarks; compare pages parameterized by two SHAs *plus configuration coordinates* — e.g. `/macrobench/queries/compare?left=<sha>&right=<sha>&type=oltp&left_planner=V3&right_planner=Gen4Fallback` — note this URL grammar lets *any* coordinate differ between left and right, not just the commit (announcement: https://vitess.io/blog/2021-07-08-announcing-vitess-arewefastyet/; docs: https://github.com/vitessio/arewefastyet/blob/main/docs/arewefastyet.md).

**Takeaway**: Vitess's URL scheme is the germ of a general endpoint algebra: a comparison = two full coordinate tuples, and "compare planners at same commit" vs "compare commits at same planner" fall out of one mechanism. That is exactly the user's {commit}×{treatment} need.

---

## 5. Chromium: ChromePerf dashboard + Pinpoint

- Dashboard: https://chromium.googlesource.com/catapult/+/HEAD/dashboard/README.md — bisection docs: https://chromium.googlesource.com/chromium/src/+/HEAD/docs/speed/bisects.md
- **Alerting is series-based, not pairwise.** `dashboard/find_change_points.py` (https://chromium.googlesource.com/catapult/+/HEAD/dashboard/dashboard/find_change_points.py): "A simplified change-point detection algorithm... In 2019, we also integrate a successive bisection with combined Mann-Whitney U-test and Kolmogorov-Smirnov tests to identify potential change points. This is not exactly the E-divisive algorithm, but is close enough. See: https://arxiv.org/abs/1306.4933". A `ChangePoint` carries median before/after, sizes, window, relative change, stddev before, and Welch's t-test statistics (t, dof, p).
- **Pinpoint** (culprit bisection between two commits) — `dashboard/pinpoint/models/compare/compare.py` (https://chromium.googlesource.com/catapult/+/HEAD/dashboard/dashboard/pinpoint/models/compare/compare.py): verdict is tri-state `SAME / DIFFERENT / UNKNOWN` (+`PENDING`). `p_value = min(KolmogorovSmirnov(a,b), MannWhitneyU(a,b))` compared against **two** alphas: `low_threshold` (reject ⇒ DIFFERENT) and `high_threshold` (fail to clear ⇒ SAME); in between ⇒ UNKNOWN ⇒ **collect more repeats**. The expected effect size ("magnitude") is expressed as "a multiple of the interquartile range (IQR)" for performance mode, and required sample counts are derived from it. Functional-mode floors: `_MIN_LOW_THRESHOLDS_FUNCTIONAL = 0.05`, `_MIN_HIGH_THRESHOLDS_FUNCTIONAL = 0.10`.

**Takeaway**: Chromium separates concerns cleanly — change-point detection on the commit series decides *which pair of commits deserves attention*; Pinpoint then does *sequential-sampling pairwise* comparison with an explicit "not enough data yet" state that triggers more runs. The tri-state verdict + adaptive repeats is directly copyable by a local harness.

---

## 6. The change-point line: MongoDB → Hunter → Otava → Nyrkiö

- **Paper**: "The Use of Change Point Detection to Identify Software Performance Regressions in a Continuous Integration System", David Daly, William Brown, Henrik Ingo, Jim O'Leary, David Bradford — ICPE 2020, https://doi.org/10.1145/3358960.3375791, preprint https://arxiv.org/abs/2003.00584. MongoDB replaced per-commit threshold comparisons (too many false positives/negatives, tedious manual graph triage) with **E-Divisive means** change-point detection over each metric's commit series; output is a triage list of candidate change points for humans. Core claim: series-level statistics dramatically cut false positives and caught smaller regressions than pairwise thresholding.
- **Algorithm origin**: "A Nonparametric Approach for Multiple Change Point Analysis of Multivariate Data", David S. Matteson, Nicholas A. James — JASA 109(505), 2014, https://arxiv.org/abs/1306.4933 (E-Divisive: hierarchical splitting on an energy-distance statistic with permutation significance tests).
- **Hunter**: "Hunter: Using Change Point Detection to Hunt for Performance Regressions", Matt Fleming, Piotr Kolaczkowski, Ishita Kumar, Shaunak Das, Sean McCarthy, Pushkala Pattabhiraman, Henrik Ingo — ICPE 2023, https://doi.org/10.1145/3578244.3583719, preprint https://arxiv.org/abs/2301.03034. DataStax open-source tool; modified E-divisive means with Student's-t significance for speed; designed for build pipelines.
- **Apache Otava (incubating)** = Hunter donated to ASF: https://github.com/apache/otava. Reads results from **CSV files, PostgreSQL, BigQuery, or Graphite**; "finds change-points and notifies about possible performance regressions"; tunables: "the level of accepted probability of false-positives" and "the minimal accepted magnitude of changes"; supports validating a feature branch against main's history. Algorithmic-performance follow-up: "8 Years of Optimizing Apache Otava...", https://arxiv.org/abs/2505.06758 (incremental E-divisive from O(n³) toward constant-time per new point).
- **Nyrkiö**: open-source change-detection platform + GitHub Action (https://github.com/nyrkio/nyrkio, https://nyrkio.com/), E-Divisive-based, claims detection of 1–2% shifts under larger noise. Independent evaluation: "Detection of Performance Changes in MooBench Results Using Nyrkiö on GitHub Actions", David Georg Reichelt, Henrik Ingo et al. — SSP 2025, https://arxiv.org/abs/2510.11310.
- **Conbench** (Apache Arrow's CB framework, https://github.com/conbench/conbench) sits between: the **"lookback z-score method"** (https://conbench.github.io/conbench/pages/lookback_zscore.html) scores a contender result against the distribution of historical results *that share all its contextual properties* (hardware, context), with git-aware baseline-commit fallback rules — i.e., a per-cell learned noise model like rustc-perf's, expressed as a z-threshold.

**Takeaway**: the literature's verdict is consistent: *pairwise thresholding on noisy series is the false-positive machine; change-point detection on the ordered series is the fix*. Pairwise comparison survives as (a) the drill-down artifact once a change point selects the pair, and (b) the pre-merge gate where you control both endpoints.

---

## 7. Commercial/product threshold models

- **CodSpeed** (https://codspeed.io/docs, https://github.com/CodSpeedHQ/codspeed): measures via **CPU simulation instrumentation** ("simulates CPU behavior for <1% variance regardless of system load" — https://docs.codspeed.io/instruments/cpu/), which makes single-run PR-vs-base comparison meaningful; default **global regression threshold 10%** vs default branch, per-benchmark overrides 0–50% (https://codspeed.mintlify.app/features/customization); reports land as PR status checks + comments (https://docs.codspeed.io/features/performance-checks). The determinism-first strategy (make measurement exact, then a plain percentage threshold suffices) parallels rustc-perf's `instructions:u` choice.
- **Bencher** (https://bencher.dev/docs/explanation/thresholds/): a **Threshold** is bound to the triple **Branch + Testbed + Measure**; test kinds: Static, Percentage, z-score (needs ≥30 history), t-test, Log Normal, IQR, Delta IQR; each with **Lower/Upper Boundary** producing a "Boundary Limit"; history controlled by `--threshold-min-sample-size`, `--threshold-max-sample-size`, `--threshold-window`; `--err` fails CI on alert. Bencher is the cleanest *productized* statement of "noise model per (branch, machine, metric) cell".
- Disambiguation: the older Django **Codespeed** (https://github.com/tobami/codespeed) powers speed.python.org-style trend dashboards; simple percentage-change reporting, no serious significance model.

---

## 8. CLI-scale prior art (what a small local harness most resembles)

### 8.1 Go `benchstat` — the closest thing to a "Vega-Lite for comparison matrices"

https://pkg.go.dev/golang.org/x/perf/cmd/benchstat (redesigned 2023; projection language spec: https://pkg.go.dev/golang.org/x/perf/benchproc/syntax)

- Every result is a bag of key:value coordinates from the benchfmt format: `.name`, `.fullname`, `.file`, `.config`, `/subkey` (per-benchmark name keys like `/format=json`), file-level keys (`goos`, `goarch`, `pkg`), `.unit`.
- Display is a **projection**: `-table KEYS` (one table per value), `-row KEYS`, `-col KEYS`; default `benchstat -table .config -row .fullname -col .file old.txt new.txt`. Sort annotations: `key@alpha`, `key@num`, `key@(fixed order list)` (fixed order also filters). Column labels via `O=old.txt N=new.txt`.
- **Filter mini-language**: `-filter "/format:json goos:linux .unit:(ns/op OR B/op)"` with AND/OR/NOT/regex.
- Stats: median ± CI per cell, **Mann-Whitney U** across columns ("vs base" delta % with `(p=0.000 n=10)`), `~` when insignificant at `-alpha 0.05`, `geomean` summary row, `-confidence` for CI level. `assume=exact` unit metadata turns off distributional machinery for deterministic metrics and *warns if variation appears*. Docs explicitly warn about the multiple-testing trap: with many benchmarks "expect ~5% to show significance by chance".
- Warning `benchmarks vary in .fullname` fires when a projection collapses a dimension that actually distinguishes results — i.e., it detects an ill-specified matrix.

This is a real, shipped **grammar**: coordinates + filter + (table, row, col) projection + baseline column + per-cell test. It is exactly the shape the user asked about, at CLI scale.

### 8.2 asv (airspeed velocity)

https://asv.readthedocs.io/en/stable/using.html

- `asv compare v0.1 v0.2 [--factor=1.1] [--split] [--machine M]`: before/after/ratio columns; marks: `-`/green improvement, `+`/red worse beyond factor, `~` statistically insignificant, `x` not comparable, `!`/`*` failure introduced/fixed. `asv continuous BASE HEAD` = run both + compare in one shot (the pre-merge pairwise gate).
- Web UI regressions tab uses genuinely sophisticated **step detection** (https://asv.readthedocs.io/en/stable/step_detection.html): fit a piecewise-constant model minimizing `γk + Σ_r Σ_i w_i |y_i − μ_r|` (weighted L1 with per-point weights from measured CIs), γ chosen by a Schwarz/BIC-like criterion `r(m)k + ln Σ w|y−μ|` with `r(m) = β ln(m)/m`, extended to AR(1) Laplace noise. Same lesson as Chromium/MongoDB: series model for detection, pairwise for inspection.

### 8.3 pyperf / hyperfine / critcmp

- `pyperf compare_to a.json b.json --table [--table-format md]`: per-benchmark "1.02x faster / not significant" via **two-sample Student's t-test**, plus **geometric mean** of normalized means for suite rollup (https://pyperf.readthedocs.io/en/latest/cli.html, https://pyperf.readthedocs.io/en/latest/analyze.html).
- `hyperfine 'cmd1' 'cmd2'`: "Summary: 'x' ran 1.23 ± 0.04 times faster than 'y'" — ratio with propagated error from both distributions (https://github.com/sharkdp/hyperfine).
- `critcmp` compares named Criterion baselines within/between runs (https://github.com/BurntSushi/critcmp).

---

## 9. Conceptual languages: what the statistics and vis literature already provides

The user asked "is there a Vega-Lite for comparisons?" Short answer: **no single artifact**, but three mature vocabularies cover the space between them.

### 9.1 Factorial designs and contrasts (the language for WHAT to compare)

- A run set over {commit} × {treatment} × {workload} is a **factorial experiment**; the canonical engineering treatment is Raj Jain, *The Art of Computer Systems Performance Analysis*, Wiley 1991, chs. on 2^k and 2^k·r factorial designs and "allocation of variation" (https://www.cse.wustl.edu/~jain/books/perfbook.htm).
- The **model-formula notation** `log(time) ~ commit * treatment + workload` *is* a specification language for comparisons: Wilkinson & Rogers, "Symbolic Description of Factorial Models for Analysis of Variance", JRSS-C 22(3), 1973, https://doi.org/10.2307/2346786 — the ancestor of R/statsmodels formulas.
- **Contrasts / estimated marginal means**: the R `emmeans` package (Russell Lenth, https://cran.r-project.org/package=emmeans) provides exactly the requested algebra: `pairs(emmeans(...))` for pairwise cell contrasts, and **interaction contrasts** ("contrasts of contrasts") for the "did the proofs overhead itself get worse" question. On the log scale, *ratio of ratios = interaction contrast = difference of differences of log-means* — this is also econometrics' **difference-in-differences** (https://en.wikipedia.org/wiki/Difference_in_differences). One fitted linear model on log(seconds) yields every ratio and ratio-of-ratios the user listed, each with a CI, uniformly.
- Ratio CIs specifically: the harness's Fieller CI is the classical exact approach (E. C. Fieller, "Some Problems in Interval Estimation", JRSS-B 16(2), 1954, https://www.jstor.org/stable/2984043); the PL-benchmarking literature's modern treatment is Tomas Kalibera & Richard Jones: "Quantifying Performance Changes with Effect Size Confidence Intervals", Univ. of Kent TR 4-12, 2012, https://kar.kent.ac.uk/33611/ and "Rigorous Benchmarking in Reasonable Time", ISMM 2013, https://doi.org/10.1145/2464157.2464160 — random-effects hierarchy (iterations within executions within builds) + bootstrap CIs on performance-change *ratios*. Also Georges, Buytaert & Eeckhout, "Statistically Rigorous Java Performance Evaluation", OOPSLA 2007, https://doi.org/10.1145/1297027.1297033; and the classic caution on hidden factors: Mytkowicz, Diwan, Hauswirth & Sweeney, "Producing Wrong Data Without Doing Anything Obviously Wrong!", ASPLOS 2009, https://doi.org/10.1145/1508244.1508275.
- **Multiple testing**: a matrix of m cell tests at α=0.05 yields ~0.05m false alarms; the standard fix when you insist on per-cell tests is Benjamini & Hochberg, "Controlling the False Discovery Rate: A Practical and Powerful Approach to Multiple Testing", JRSS-B 57(1), 1995, https://www.jstor.org/stable/2346101. rustc-perf instead sidesteps per-cell inference by rolling up to counting rules; benchstat just warns.

### 9.2 Visual comparison taxonomy (the language for HOW to display)

- Michael Gleicher, Danielle Albers, Rick Walker, Ilir Jusufi, Charles D. Hansen, Jonathan C. Roberts, "Visual Comparison for Information Visualization", *Information Visualization* 10(4), 2011, https://doi.org/10.1177/1473871611416549 — the canonical taxonomy: **juxtaposition** (side-by-side), **superposition** (overlay), **explicit encoding** (draw the difference itself). A comparison table of ratios is explicit encoding; overlaid history charts are superposition.
- Michael Gleicher, "Considerations for Visualizing Comparison", IEEE TVCG 24(1), 2018, https://doi.org/10.1109/TVCG.2017.2744199 — scalability strategies for large comparison sets: scan sequentially, select/subset, **summarize then drill down** — precisely the rollup+filter pattern rustc-perf converged on independently.
- Sehi L'Yi, Jaemin Jo, Jinwook Seo, "Comparative Layouts Revisited: Design Space, Guidelines, and Future Directions", IEEE TVCG 27(2), 2021 (VIS 2020), https://arxiv.org/abs/2009.00192 — empirical guidance on juxtaposition vs superposition vs explicit-encoding trade-offs.
- Vega-Lite itself contributes only **faceting** (row/column encoding channels, https://vega.github.io/vega-lite/docs/facet.html) — i.e., the display half; it has no comparison-contrast semantics. benchstat's projection grammar (§8.1) is the nearest executable analogue on the spec side.

---

## Implications for this harness

**1. Name the coordinate system; derive comparisons instead of enumerating them.** Every mature system bottoms out in a typed coordinate tuple (rustc-perf "test case" + "statistic description"; Bencher branch+testbed+measure; benchfmt keys). Yours is `(workload, target, backend, treatment, metric[, phase, ruleset])`. The winning spec pattern is *not* "list the comparisons" but "list the endpoints, then mechanically emit every comparison that differs in exactly one coordinate" (rustc-perf: two artifacts, all cells; Vitess: left/right full tuples). A request like `targets={old,new} × treatments={off,proofs}` should auto-generate the 4 cells, the 4 one-coordinate ratios, and the single interaction — nothing else to specify but which axes are "varied" vs "held".

**2. Steal benchstat's projection grammar for the CLI — nearly verbatim.** `--table/--row/--col/--filter` over your coordinate keys, with `@(fixed order)` doubling as filter+sort and the first column of `--col` as baseline, is a proven, tiny (couple hundred lines), composable display language. It answers "big matrix on a CLI" directly: e.g. `bench cmp --table workload --row treatment --col target --filter 'backend:main metric:wall'` renders per-workload 2×2s with "vs base" ratio columns. Copy its `benchmarks vary in KEY` warning: detect when a collapsed axis still distinguishes observations. This is the single highest-leverage artifact found.

**3. Do the algebra in log space; get interactions for free.** Ratios-of-ratios via Fieller compounds awkwardly. Model `log(wall)` per (workload, metric): cell means with t-CIs, every ratio = difference of log-means, the "did proofs overhead worsen" question = the 2×2 interaction contrast `(new,proofs) − (new,off) − (old,proofs) + (old,off)`, all with uniform CIs (exponentiate at the end). This is textbook factorial analysis (Jain 1991; emmeans' "interaction contrasts"; econometrics' difference-in-differences). Keep Fieller for the headline pair if you like — it agrees with the log-space t-interval to first order at benchmark-scale CVs — but the *general* machinery should be one linear model, not recursive ratio propagation.

**4. Copy rustc-perf's cheap noise model — your JSONL already contains it.** Their entire significance stack needs only per-cell history: distribution of adjacent-run relative changes → `threshold = Q3 + 3·IQR`, `significance factor = |Δ|/threshold`, magnitude = average of (over-threshold ordinal, absolute-% ordinal with a 2× slack for noisy metrics like max-RSS vs a tight scale for anything deterministic), `relevant = significant ∧ magnitude ≥ small`, hide non-relevant by default. Fallback constant (theirs: 0.2%) when history is thin. Also copy LNT's two floors verbatim for per-phase times: suppress anything below both a relative floor *and* an absolute floor (a 40% change in a 3 ms rebuild phase is not news), and skip comparisons when binary sha + file sha are identical (LNT's `ignore_same_hash`).

**5. Rollups are counting rules, not statistics — and that's fine.** For the matrix headline, emit rustc-perf-style labels (improvement/regression/mixed by magnitude-bucket counts, with their 15%/90% rules) plus a geomean row per comparison (benchstat/pyperf). Don't hand the user m p-values as the top-level view; per-cell tests inflate false positives ~5%/cell (benchstat's own warning) — either roll up to counts or apply Benjamini-Hochberg if p-values must headline.

**6. Pairwise vs series: know which regime you're in.** The literature's strongest single finding (Daly ICPE 2020; Chromium; asv) is that *deciding which commits changed* from noisy per-commit data is a change-point problem, not a pairwise-threshold problem. Your harness is pre-merge/pair-first, which is the regime where pairwise is correct — but the moment "more than one pair" becomes "a series of commits per treatment", don't build an N×N pairwise grid; run E-divisive per (workload, backend, treatment, metric) series and use the pairwise page as drill-down on detected change points. Apache Otava reads plain CSV — a JSONL→CSV exporter gets series analysis for free before you write any stats code.

**7. Adopt Pinpoint's tri-state verdict + adaptive repeats.** `SAME / DIFFERENT / UNKNOWN`, with UNKNOWN meaning "CI straddles the threshold → schedule more repetitions of *only this cell*", converts fixed-N benchmarking into sequential sampling that spends wall-clock where the answer is genuinely uncertain (Perfherder's retriggers are the manual version). For a local harness with an append-only cache this is a small loop, and it composes with the matrix: rerun until every *displayed* comparison resolves or hits a budget.

**8. Don't build a general comparison grammar.** Nothing Vega-Lite-shaped exists even at Google/Mozilla/rust-lang scale; every system converged on (a) fixed coordinate vocabulary, (b) filter + projection mini-language, (c) hardcoded rollup→drill-down pages, (d) a noise model per cell. The already-general layers exist elsewhere: statsmodels formulas + contrast matrices if you want principled interactions, and Gleicher's taxonomy (explicit encoding for tables of ratios; superposition for history charts; summarize-then-drill-down for scale) as the display checklist. Budget accordingly: coordinate schema + benchstat-style projection + rustc-perf significance ≈ a week; a comparison DSL ≈ a research project with no prior art to crib from.
