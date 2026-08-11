# Grammars and algebras for specifying comparisons and matrix displays
### ("Is there a Vega-Lite for comparisons?") — research report, 2026-08-11

**TL;DR.** There is no single "Vega-Lite for comparisons," but the problem decomposes cleanly into three well-studied layers, each with a mature conceptual language:

1. **Cells** — an OLAP **data cube**: dimensions (target, backend, treatment, workload) × measures (wall, RSS, phases). Gray et al. 1997.
2. **Contrasts** — comparisons as **derived members of a dimension** (MDX "calculated members"): `new/old` is a new member of the *target* dimension; an interaction ("did proofs overhead get worse") is a calculated member of one dimension evaluated *at* a calculated member of another. This is the key conceptual unlock: once a contrast is a member, the layout layer needs no special machinery for it.
3. **Layout** — a **table algebra** (Polaris/Tableau `cross`/`nest`/`concat`; Vega-Lite `facet`/`layer`/`concat`/`repeat`) assigning each dimension to rows, columns, facets, or collapse. The closest existing artifact to "Vega-Lite for benchmark comparisons" is **Go's `benchstat`** with its `-table/-row/-col` projection flags — a working, terminal-native table algebra over benchmark dimensions, but hardwired to a single comparison axis ("vs base").

Perceptual theory (Gleicher) classifies every possible display as juxtaposition / superposition / explicit encoding; a ratio column **is** explicit encoding, side-by-side mean columns **are** juxtaposition. The standard statistical display for "many ratio+CI rows with subgroup structure" already exists: the **forest plot**.

---

## 1. The grammar-of-graphics lineage: algebras that generate table layouts

### 1.1 Wilkinson's Grammar of Graphics

- **Leland Wilkinson, *The Grammar of Graphics*, 2nd ed., Springer, 2005.** https://link.springer.com/book/10.1007/0-387-28695-0 ; overview: https://en.wikipedia.org/wiki/Wilkinson%27s_Grammar_of_Graphics

Wilkinson decomposes a chart spec into data → transformations → **algebra** → scales → statistics → geometry → coordinates → aesthetics. The algebra operates on "varsets" (variable sets) with **three binary operators: blend (`+`), cross (`*`), nest (`/`)**, evaluated nest-first, blend-last. `cross` is a Cartesian product in the range; `blend` is a union; `nest` restricts to combinations present in the data. This algebra is what generates paneled/faceted layouts *and* performs set operations on data — a point Stolte et al. later criticize (see §1.2). Wilkinson's operators are the direct ancestors of Polaris shelves, ggplot2 `facet_grid(rows = vars(a), cols = vars(b))` (https://ggplot2.tidyverse.org/reference/facet_grid.html), and Vega-Lite's `row`/`column` channels.

### 1.2 Polaris / Tableau: a literal algebra for "how to lay out a big matrix"

- **Chris Stolte, Diane Tang, Pat Hanrahan, "Polaris: A System for Query, Analysis, and Visualization of Multidimensional Relational Databases," IEEE TVCG 8(1):52–65, 2002** (earlier version InfoVis 2000, Stolte & Hanrahan). PDF: https://graphics.stanford.edu/papers/polaris/polaris.pdf ; CACM 2008 reprint: https://dl.acm.org/doi/pdf/10.1145/1400214.1400234

Polaris is the most directly relevant formalism. Verified from the paper (primary source):

- A table configuration is **three expressions** in a table algebra: x-axis, y-axis, and z-axis (layers). Operands are field names; ordinal fields evaluate to their ordered domain `A = domain(A) = {a1,…,an}`, quantitative fields to the singleton `{P}`. "Ordinal fields will partition the table into rows and columns, whereas quantitative fields will be spatially encoded as axes within the panes."
- **Operators, in precedence order: cross (×), nest (/), concatenation (+)**, with exact set semantics:
  - `A + B = {a1,…,an,b1,…,bm}` — ordered union → adjacent blocks on one axis (e.g., a wall-time block followed by an RSS block).
  - `A × B` — Cartesian product → hierarchical two-level headers `{a1b1,…,anbm}`; `A × P = {a1P,…,anP}` puts a quantitative axis inside each ordinal slot (exactly BenchmarkDotNet-style grouped headers).
  - `A / B = {ai bj | ∃ record r s.t. A(r)=ai ∧ B(r)=bj}` — "B within A": only combinations that occur in the data. Their example: `quarter/month` yields 3 months per quarter; `quarter × month` yields 12 per quarter (mostly empty).
- Every expression reduces to a **normalized set form**, and "the table axis is partitioned into columns (or rows or layers) so that there is a one-to-one correspondence between set entries in the normalized set and columns." The same specification also **generates the SQL/OLAP queries** that fetch the data — layout and query derive from one algebra.
- Panes are typed by their axes into ordinal-ordinal / ordinal-quantitative / quantitative-quantitative families — a useful check for what mark belongs in each cell of a comparison matrix (a heatmap cell is O-O; a CI-bar cell is O-Q).

**Takeaway:** "assign each dimension to an axis-shelf expression built from ×, /, +" is a complete, 24-year-old answer to "how do I specify the layout of a big matrix." `nest` (`/`) matters for ragged cubes — e.g., a treatment that only exists for one backend.

### 1.3 Vega-Lite: the view-composition algebra, and how a ratio matrix maps onto it

- **Arvind Satyanarayan, Dominik Moritz, Kanit Wongsuphasawat, Jeffrey Heer, "Vega-Lite: A Grammar of Interactive Graphics," IEEE TVCG (Proc. InfoVis 2016), 2017.** PDF: https://idl.cs.washington.edu/files/2017-VegaLite-InfoVis.pdf ; project pages: https://vis.csail.mit.edu/pubs/vega-lite/ , https://github.com/vega/vega-lite

Verified from the paper: starting from **unit specs** (one mark + encodings), Vega-Lite composes views with four operators:

- `layer([unit1, unit2, …], resolve)` — superposition; scales union by default, `resolve` can make them independent (dual-axis).
- `hconcat([view1,…], resolve)` / `vconcat(…)` — juxtaposition; shared scale+axis if aligned channels use the same field.
- `facet(channel, data, field, view, scale, axis, resolve)` — trellis: partitions data by distinct field values; channel = `row` or `column`. Quantitative scales shared by default; **ordinal scales independent by default, "akin to Polaris' nest operator"** (their quarter/month example again).
- `repeat(channel, values, scale, axis, view, resolve)` — replicates the *full* dataset per cell, parameterizing the inner spec (SPLOMs; repeating over *measures*). Their own footnote: "As the repeat operator requires parameterization of the inner view, **it is not strictly algebraic**."
- The paper positions this against Wilkinson/Polaris: "Both Wilkinson's grammar and Polaris/Tableau achieve this through a table algebra over data fields… In contrast, we contribute a view algebra."
- In the concrete JSON syntax, `encoding.row` / `encoding.column` channels are sugar for the facet operator (docs: https://vega.github.io/vega-lite/docs/facet.html).

**Mapping a benchmark ratio matrix to Vega-Lite** (what an HTML export would literally be):
- `facet: {row: {field: "workload"}}` (+ `column: {field: "measure"}` or a `repeat` over measures — `repeat`, not `facet`, because each measure is a different column of the same records);
- per cell, `layer` of: `mark: rule` from `x: lo` to `x2: hi` (the CI), `mark: point` at `x: ratio`, and a reference `rule` at `x: 1`;
- `x` scale `{type: "log"}`;
- the CI must be **precomputed** (Fieller/log-delta): Vega-Lite's `errorbar` composite mark only derives extents (`ci`, `stderr`, `stdev`, `iqr`) from raw samples, which is statistically wrong for a ratio of means. Ratios themselves are computable in-spec via `pivot` + `calculate` transforms, but there is no reason to: compute upstream.

### 1.4 Trellis displays / small multiples

- **Richard A. Becker, William S. Cleveland, Ming-Jen Shyu, "The Visual Design and Control of Trellis Display," Journal of Computational and Graphical Statistics 5(2):123–155, 1996.** https://www.tandfonline.com/doi/abs/10.1080/10618600.1996.10474701 ; R lattice descends from it: https://cran.r-project.org/web/packages/lattice/refman/lattice.html

Panels laid out in rows, columns, **and pages**, each showing a subset defined by *conditioning* on other variables. Two ideas worth stealing beyond mere faceting: **main-effects ordering** (order panels/rows by a summary statistic — e.g., sort workloads by geomean ratio, not alphabetically) and the page dimension (pagination is a legitimate third layout axis for a CLI). Gleicher's 2011 survey cites Tufte's dictum that small-multiple "comparison must take place within the eyespan" (Tufte, *Envisioning Information*, via https://graphics.cs.wisc.edu/Papers/2011/GAWJHR11/paper.pdf).

---

## 2. The data-cube lineage: cells, margins, and named contrasts

### 2.1 The CUBE operator

- **Jim Gray, Surajit Chaudhuri, Adam Bosworth, Andrew Layman, Don Reichart, Murali Venkatrao, Frank Pellow, Hamid Pirahesh, "Data Cube: A Relational Aggregation Operator Generalizing Group-By, Cross-Tab, and Sub-Totals," Data Mining and Knowledge Discovery 1(1):29–53, 1997.** https://link.springer.com/article/10.1023/A:1009726021843 ; PDF: https://web.stanford.edu/class/cs345d-01/rl/olap.pdf

Verified from the paper: `CUBE` computes the power set of GROUP BYs; super-aggregates are represented with the distinguished **`ALL` value** ("the point (ALL,ALL,…,ALL, sum(*)) represents the global sum"); `ROLLUP` produces just the prefix hierarchy for drill-down reports; "Going up the levels is called rolling-up the data. Going down is called drilling-down"; and "The cross tab array representation is equivalent to the relational representation using the ALL value. Both generalize to an N-dimensional cross tab." Slice/dice = fixing/selecting dimension values.

Relevance: the harness's JSONL cache is already a fact table keyed by `(binary sha, backend, treatment, file sha, timeout)`; a *report* is a small cube over it. Marginal rows ("all workloads", i.e., geomean) are exactly `ALL` members — the geomean row in benchstat *is* a `ROLLUP` row.

### 2.2 MDX calculated members = comparisons as first-class dimension members

- **Microsoft, "MDX Calculated Members – Query-Scoped Calculated Members."** https://learn.microsoft.com/en-us/analysis-services/multidimensional-models/mdx/mdx-calculated-members-query-scoped-calculated-members ; tutorial with ratio examples: https://learn.microsoft.com/en-us/analysis-services/multidimensional-tutorial/lesson-6-1-defining-calculated-members?view=asallproducts-allversions

`WITH MEMBER [Target].[new/old] AS [Target].[new] / [Target].[old]` defines a **new member of the Target dimension** whose value at every coordinate of the rest of the cube is the ratio. Calculated measures (measure₂/measure₃) are the same idea on the measures dimension. This is the only mainstream formalism where **a contrast is an object the layout algebra can place on an axis** like any other member. The interaction the user wants is then just composition — the member `[Target].[new/old]` evaluated at `[Treatment].[proofs/off]`, where `[Treatment].[proofs/off]` is itself a calculated member: a **ratio of ratios appears automatically at the crossing of two contrast members**, with no dedicated "interaction" machinery. (Statistical caveat in §5.)

---

## 3. Comparison-visualization theory (what the display *is*, perceptually)

### 3.1 The Gleicher taxonomy

- **Michael Gleicher, Danielle Albers, Rick Walker, Ilir Jusufi, Charles D. Hansen, Jonathan C. Roberts, "Visual Comparison for Information Visualization," Information Visualization 10(4):289–309, 2011.** PDF: https://graphics.cs.wisc.edu/Papers/2011/GAWJHR11/paper.pdf ; https://journals.sagepub.com/doi/10.1177/1473871611416549

Verified from the paper: all comparison designs are assembled from **juxtaposition** (objects shown separately, in space or time), **superposition** (overlaid in one coordinate system), and **explicit encoding** (compute the relationship, encode *it*). "The three categories can be distinguished by the principal mechanism used to make connections between objects: juxtaposition uses the viewer's memory, superposition uses the visual system and explicit encodings use computation to determine the relationships." Hybrids of two are common; they found no hybrid of all three.

Applied to this harness: two mean columns side by side = juxtaposition (reader does the division in their head — bad for >a few rows); overlaid per-phase bars = superposition; **the ratio+CI column is explicit encoding** — the relationship (speedup) is computed and displayed directly. An interaction column is explicit encoding *of a relationship between relationships*, which is exactly why it feels exotic: it is two levels of computation away from the data, and readers need the intermediate level visible to trust it.

### 3.2 Considerations for scale

- **Michael Gleicher, "Considerations for Visualizing Comparison," IEEE TVCG 24(1):413–423, 2018.** https://pubmed.ncbi.nlm.nih.gov/28866530/ ; https://www.semanticscholar.org/paper/9301b63e3d86f9a02a3d65b3e6d58d610b21656d ; talk slides: https://graphics.cs.wisc.edu/Talks/Gleicher/2017/VisComp-given.pdf

Four considerations: (1) identify the comparison's **elements** — the target set of related items and the *action* on the relationship; (2) recognize **challenges of scale** — number of items, complexity of items, complexity of the relationship; (3) **scalability strategies**: *scan sequentially*, *select subset*, *summarize somehow*; (4) then choose among the three designs. For a k-endpoint harness the scale explosion is in *pairs* (C(k,2) per workload per measure), so the design question is which strategy each report mode uses: a regression gate *selects a subset* (only significant rows); a survey report *summarizes* (geomean rows); drill-down *scans*.

### 3.3 Follow-on design space

- **Sehi L'Yi, Jaemin Jo, Jinwook Seo, "Comparative Layouts Revisited: Design Space, Guidelines, and Future Directions," IEEE TVCG (Proc. InfoVis 2020).** https://arxiv.org/abs/2009.00192

Reviews 127 papers + 15 user studies; refines Gleicher with distinctions like chart-wise vs item-wise juxtaposition and seven actionable guidelines; useful if an HTML report ever gets serious.

---

## 4. Statistical display idioms for "many ratios with structure"

### 4.1 Forest plots — the standard display for exactly this shape of data

- Intro/interpretation: **"The 5 min meta-analysis: understanding how to read and interpret a forest plot," Eye 36:673–675, 2022.** https://www.nature.com/articles/s41433-021-01867-6
- Construction reference: **Harrer et al., *Doing Meta-Analysis in R*, ch. 6 "Forest Plots."** https://bookdown.org/MathiasHarrer/Doing_Meta_Analysis_in_R/forest.html ; Stata's spec: https://www.stata.com/manuals/metametaforestplot.pdf

Conventions (verified across the above): one row per study = point estimate (square whose **area encodes weight ≈ 1/SE²**) + CI whisker on a shared axis; **ratios plotted on a log scale** so CIs are symmetric and 0.5×/2× are equidistant from 1; a vertical **"line of no effect" at 1** for ratios (0 for differences); **subgroups get their own summary diamonds** (diamond width = CI of the pooled estimate) stacked in labeled sections; an overall diamond at the bottom; left column = labels, right column = numeric `RR [95% CI]`.

**Mapping to the harness is one-to-one**: workload → study; log wall-ratio → effect size; inverse-variance of the log-ratio → weight; workload suite/category → subgroup; geomean (with propagated CI) → diamond. A "many pairs" report is a forest plot per contrast, or one forest plot with contrast as the subgroup factor. This is the display idiom to copy for the terminal, not invent.

### 4.2 Tukey mean-difference / Bland–Altman

- **J. Martin Bland, Douglas G. Altman, "Statistical methods for assessing agreement between two methods of clinical measurement," The Lancet 327(8476):307–310, 1986.** https://en.wikipedia.org/wiki/Bland%E2%80%93Altman_plot ; https://www.statisticshowto.com/bland-altman-plot/

Plot (mean of the two measurements) on x vs (difference) on y — for ratios, (log-mean, log-ratio), i.e., an MA-plot. Answers "does the speedup depend on how big/slow the workload is?" — a *continuous* interaction that a table hides. Cheap and high-value as one exported chart.

### 4.3 Paired speedup scatter

Old-vs-new per-workload scatter on log-log axes with the y=x diagonal; distance from the diagonal = speedup. Same information as Bland–Altman rotated 45°; familiar to systems audiences. Not worth a terminal rendering; trivial in Vega-Lite (`point` + diagonal `rule`, both scales log).

### 4.4 Heatmap matrices

A workloads × contrasts (or targets × treatments) grid colored by log-ratio with a **diverging colormap centered at ratio = 1** is the compact O-O display when rows × columns exceed forest-plot capacity. Loses CIs; standard mitigation is overprinting significance (benchstat's `~` analog). (Design-space context: L'Yi et al., https://arxiv.org/abs/2009.00192.)

### 4.5 The statistics of ratios, geomeans, and ratios-of-ratios

- **Philip J. Fleming, John J. Wallace, "How not to lie with statistics: the correct way to summarize benchmark results," CACM 29(3):218–221, 1986.** https://dl.acm.org/doi/10.1145/5666.5673 — normalized results (ratios) must be summarized with the **geometric mean**; arithmetic-mean-of-ratios conclusions flip depending on the normalization machine.
- **Tomas Kalibera, Richard Jones, "Quantifying Performance Changes with Effect Size Confidence Intervals," U. Kent TR 4-12, 2012 / arXiv:2007.10899.** https://arxiv.org/abs/2007.10899 — the statistical model for "A is faster than B by 5.5% ± 2.5% with 95% confidence" under multi-level nondeterminism; found 65/122 systems papers quantified changes as time ratios, almost none with uncertainty. Companion: **"Rigorous Benchmarking in Reasonable Time," ISMM 2013.** https://dl.acm.org/doi/10.1145/2464157.2464160
- **Douglas G. Altman, J. Martin Bland, "Interaction revisited: the difference between two estimates," BMJ 326:219, 2003.** https://pfeifer.phas.ubc.ca/refbase/files/Altman-BMJ-2003-326-219.pdf — the exact recipe for the user's "did proofs overhead get worse": work in **log space**, where the interaction is a difference of two log-ratios: `log RoR = (log new_p − log new_o) − (log old_p − log old_o)` and, for *independent* estimates, `SE(log RoR) = sqrt(SE₁² + SE₂²)` (extends to the sum of all four cell variances of the log-means); exponentiate for the ratio-of-ratios CI. Test against 0 in log space.
  - **Caveat vs the harness's Fieller CI:** Fieller is exact-ish for one ratio of normal means but does not compose. Log-space delta-method CIs (`Var(log m̂) ≈ CV²/n`) are the composable currency: contrasts add, variances add (when cells are independent — true here since each cell is separate runs), and the geomean across workloads is an arithmetic mean in log space. Keep Fieller as a cross-check for single-pair headline numbers where CV is high; do everything multi-way in logs.
- **Multiplicity:** a matrix of contrasts is a multiple-comparisons machine; benchstat's docs already frame α=0.05 as "expect 5% false positives" (https://pkg.go.dev/golang.org/x/perf/cmd/benchstat). With dozens of cells, either report Benjamini–Hochberg-adjusted significance or (benchstat's choice) just mark insignificant cells `~` and educate.

---

## 5. Existing performance-comparison DSLs and tools

### 5.1 benchstat — the closest thing to "Vega-Lite for benchmark comparisons"

- **golang.org/x/perf/cmd/benchstat.** https://pkg.go.dev/golang.org/x/perf/cmd/benchstat ; worked examples of projections: https://www.bwplotka.dev/2024/go-microbenchmarks-benchstat/

Verified from the docs: benchmark results carry **key-value dimensions** — file-level config (`goos`, `goarch`, `pkg`, or arbitrary labels), sub-name keys (`BenchmarkEncode/format=json` → `/format`), `.name`, `.fullname`, `.file` (settable as `benchstat O=old.txt N=new.txt`), `.unit`. The report is specified by **projection flags — a genuine table algebra on the CLI**:

```
-table KEYS   # facet: one table per distinct value (default .config)
-row KEYS     # rows   (default .fullname)
-col KEYS     # the COMPARISON axis (default .file)
-filter EXPR  # e.g. "/format:json goos:linux .unit:(ns/op OR B/op)"
-confidence 0.95  -alpha 0.05
```
plus sort/order control embedded in keys: `{key}@alpha`, `{key}@num`, `{key}@(gob json)` (fixed order, doubles as a filter). Output: first `-col` value is the base; each subsequent column gets a **`vs base`** sub-column with `±x%`, `p=…`, `n=…`; insignificant deltas print **`~`** (Mann–Whitney U test; medians with CIs per cell); last row is the **`geomean`**. Example from the docs:

```
        │   old.txt   │               new.txt               │
        │   sec/op    │   sec/op     vs base                │
Encode/format=json-48   1.718µ ± 1%   1.423µ ± 1%  -17.20% (p=0.000 n=10)
Encode/format=gob-48    3.066µ ± 0%   3.070µ ± 2%        ~ (p=0.446 n=10)
geomean                 2.295µ        2.090µ        -8.94%
```

**Limits:** exactly one comparison dimension (`-col`), always "each column vs first column" — no within-row second contrast, no interaction, no ratio-of-ratios. But `-col` is any key: `benchstat -col /treatment file.txt` compares treatments instead of files. This flag set is the right UX skeleton to copy.

### 5.2 BenchmarkDotNet — baselines, ratio columns, grouped headers

- https://benchmarkdotnet.org/articles/features/baselines.html ; https://benchmarkdotnet.org/articles/samples/IntroRatioSD.html

`[Benchmark(Baseline = true)]` per method or per **job** (runtime/config axis!) yields **`Ratio`** and, when the ratio distribution is wide, **`RatioSD`** columns (ratio computed distributionally, not as ratio-of-means; the column was renamed from `Scaled` precisely to stop people reading it as mean₁/mean₂). `RatioStyle` = `Value | Percentage | Trend`. With `[BenchmarkCategory]` + `GroupBenchmarksBy(BenchmarkLogicalGroupRule.ByCategory)`, **each category group gets its own baseline** → per-group ratios — the exact precedent for "proofs/off *within each* commit." Its two-level column headers (measure group → statistic) are the terminal-rendering precedent for `A × P` cross headers.

### 5.3 The rest of the field (one comparison axis each)

- **pyperf `compare_to`** (https://pyperf.readthedocs.io/en/latest/cli.html): `pyperf compare_to ref.json changed.json [changed2.json …] --table --table-format=md -G/--group-by-speed --min-speed=N`; two-sample t-test; output like `[py36] 4.70 us ± 0.18 us -> [py38] 4.22 us ± 0.08 us: 1.11x faster`; **geometric mean of normalized means** as the suite summary. Supports *multiple* candidate files against one reference (k columns, still one contrast axis).
- **google/benchmark `compare.py`** (https://github.com/google/benchmark/blob/main/docs/tools.md): baseline vs contender executables or JSON; per-benchmark deltas; optional **Mann–Whitney U test** with repetitions.
- **hyperfine** (https://github.com/sharkdp/hyperfine): `Summary: 'x' ran 1.25 ± 0.03 times faster than 'y'` (relative-speed summary against the fastest); `--parameter-scan N low high` / `--parameter-list` generate a *parameter dimension*; `--export-json/csv/markdown`. Matrix generation without matrix display.
- **asv (airspeed velocity)** (https://asv.readthedocs.io/en/stable/commands.html): `asv compare hash1 hash2 [--factor F --split --only-changed --sort ratio]`, `asv continuous` for CI pairs, `--interleave-rounds` to fight drift; benchmarks can be parameterized over grids, and the HTML dashboard plots time series per parameter combination.
- **critcmp** (https://github.com/BurntSushi/critcmp): compares named Criterion baselines in a row-per-benchmark, column-per-baseline table.
- **Continuous-benchmarking platforms** — Conbench (https://github.com/conbench/conbench), Bencher (https://bencher.dev/, with a prior-art survey at https://bencher.dev/docs/reference/prior-art/ covering Horreum, Nyrkiö, ReBench, etc.), LLVM LNT (https://llvm.org/docs/lnt/): store runs keyed by (branch, testbed, benchmark, measure), do threshold/changepoint detection vs a base branch. Dimensional data models, dashboard display — but again, contrast = "vs base," never an algebra of contrasts.

**Field conclusion: no existing tool has a contrast language.** Every tool hardwires one comparison axis with a distinguished base level. The user's `{old,new} × {off,proofs}` with three ratio families plus an interaction is expressible in none of them. benchstat's projections + MDX's calculated members are the two halves of the missing design, already proven separately.

---

## 6. Difficulties specific to a comparison algebra (why this is genuinely harder than facets)

1. **Contrasts live one level above cells.** Table algebras (Polaris, Vega-Lite facet) partition *data*; a ratio is a function of *two* partitions. The MDX move (contrast = derived member of a dimension) is the only formalism that closes this loop so layout stays uniform. Without it you grow ad-hoc "vs base" special cases (the entire §5 field).
2. **Statistics must compose along with the algebra.** If `⊘_target` and `⊘_treatment` are contrast operators, the displayed uncertainty of `⊘_target ∘ ⊘_treatment` must be derivable — which forces log-space delta-method variances (Altman & Bland 2003, §4.5) as the internal representation; Fieller doesn't compose.
3. **Correlation from shared cells.** `new-off/old-off` and `new-proofs/old-off` share a denominator cell → their log-ratios are positively correlated; a naive "compare these two contrasts" display double-counts the shared noise. (Cells themselves are independent runs, so *within* one contrast the SE₁²+SE₂² rule is fine; it's contrast-vs-contrast displays that need care — or a note.)
4. **Ragged cubes.** Some (backend, treatment) combos won't exist (dd × causal-proofs, say). This is exactly Polaris `nest` vs `cross`: axes should be generated by `/` against observed cells, not blind Cartesian products, or the matrix fills with holes.
5. **Baseline asymmetry & direction conventions.** Every ratio needs an explicit orientation (candidate/baseline, "lower is better" flips coloring); forest-plot practice solves this with an axis annotation ("favours A ⟷ favours B"), benchstat with signed % vs base.
6. **Scale.** k targets × t treatments → C(kt,2) pairwise ratios per workload per measure; nobody wants all of them. Gleicher 2018's answer: the *user names the contrasts of interest* (select subset) and everything else stays a cell. Named contrasts are also the multiplicity-control point.

---

## Implications for this harness

**The factoring (recommended even if nothing is built now):**

1. **Keep the cache a pure cube of cells.** The append-only JSONL keyed by `(binary sha, backend, treatment, file sha, timeout)` is a fact table; never cache a comparison. Dimensions: `target`, `backend`, `treatment`, `workload`, plus a `measure` dimension (wall, max-RSS, phase:*, ruleset:*, and future egg-equivalence measures slot in as new members, not new code paths). Store per-cell `n`, mean, and **log-space mean+variance** alongside; that's the composable currency (§4.5).
2. **Contrasts = named calculated members, one dimension each.** A contrast spec is `dim: name = numerator/denominator`, e.g. `target: dnew = new/old`, `treatment: overhead = proofs/off`. Ratio-of-ratios needs **no third concept**: it is the cell at `(target=dnew, treatment=overhead)` — the cube evaluates calculated members at calculated members, and log-space SEs add across the four cells (Altman & Bland formula). The user's whole example is: two contrast declarations + a 2×2 layout.
3. **Layout = benchstat-style projection flags.** Every dimension gets exactly one role: `--fix dim=value` (slice), `--row`, `--col`, `--table` (facet/page), or it's consumed by a contrast. Adopt benchstat's ergonomics wholesale: `@(a b)` ordering-as-filter, `--filter`, default `--row workload --col <the contrast>`, `geomean` row (Fleming & Wallace) with propagated CI as the `ALL`/diamond row. This is Polaris `×`/`+` with `/`-style nesting against observed cells (§6.4).

**Terminal rendering — borrow, don't invent:**
- **A forest-plot column**: fixed-width shared **log** axis per table, `│` at 1×, per-row `├──●──┤` from CI-lo to CI-hi; numeric `1.32× [1.21,1.44]` beside it; benchstat's `~` for insignificant rows; **sort rows by main effect** (Trellis main-effects ordering), geomean diamond row last. This single idiom covers 90% of "big matrix" needs because most real reports are (many workloads) × (few named contrasts).
- **BenchmarkDotNet-style two-level headers** for the `A × measure` cross when showing >1 measure or >1 contrast column.
- Cap terminal output at 2 layout dims + `--table` pagination; beyond that, refuse and point at the HTML export (Gleicher scale strategies: select or summarize).

**Punt to HTML/Vega-Lite export:** the full matrix at ≥3 layout dims, per-phase stacked bars (superposition), Bland–Altman/speedup scatters (does speedup correlate with workload size?), and interactivity. The export is mechanical from the same factored spec: `facet` row=workload / column=contrast, `layer`(rule x/x2 + point, log x, reference rule at 1), `repeat` over measures — with CIs precomputed upstream because Vega-Lite's errorbar extents can't do ratio statistics (§1.3).

**Reasons *not* to build much:** if 95% of invocations remain one pair, benchstat's shape (one comparison axis + `~` + geomean) already covers them; the contrast algebra pays off only at the `{2 targets}×{2 treatments}` interaction question and beyond. The cheap insurance is factoring the *data model* as in (1)–(2) — cube + log-space stats — so today's pair-only report is the trivial special case (one contrast, `--row workload`) of a design you can grow, instead of a dead end. The expensive parts (HTML, interactivity, >2-dim terminal layout) have off-the-shelf landing zones (Vega-Lite, forest-plot R/observable idioms) and should not be hand-rolled.
