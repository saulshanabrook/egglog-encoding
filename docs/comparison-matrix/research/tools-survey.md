# Survey: How benchmark tools express comparisons and display multi-configuration results

Date: 2026-08-11. Method: WebSearch + WebFetch of primary docs/READMEs (URLs inline). Focus: (a) the *expression* surface — CLI flags/config for saying WHAT to compare; (b) the *display* surface — how N-configuration results are rendered; (c) what maps onto a cached, endpoint-addressed store like the one in `benchmarking/` (pair-only today: endpoint = target × backend × treatment; measures = wall/RSS/phases; JSONL cache keyed by content hashes).

---

## 1. Tool-by-tool survey

### 1.1 hyperfine (CLI process benchmarking)

**Expression.** Parameters are declared on the command line and substituted into command templates with `{var}`:

- `-P/--parameter-scan <VAR> <MIN> <MAX>` (numeric range; step via `-D/--parameter-step-size`): `hyperfine --parameter-scan num_threads 1 12 'make -j {num_threads}'`
- `-L/--parameter-list <VAR> <v1,v2,...>` (categorical): `hyperfine -L compiler gcc,clang '{compiler} -O2 main.cpp'`
- Multiple `-L` flags yield the **cross product** of all parameter values applied to every command template (users have asked for non-crossed, per-command parameters — open issue [#637](https://github.com/sharkdp/hyperfine/issues/637)).
- `-n/--command-name` renames a command for display/export.
- Demand for a *designated* baseline (rather than "fastest wins") tracked in issue [#577 "Allow choice of reference benchmark"](https://github.com/sharkdp/hyperfine/issues/577), which led to a `--reference <command>` option in recent releases.

**Display.** Per-command mean ± σ, then a relative-speed summary anchored at the *fastest* command:

```
Summary
  'rg "error" /var/log/' ran
    6.56 ± 0.58 times faster than 'grep -r "error" /var/log/'
```

(sample shapes: [tecmint writeup](https://www.tecmint.com/hyperfine-find-command-execution-time-linux/), [Linode guide](https://www.linode.com/docs/guides/installing-and-using-hyperfine-on-linux/)). The uncertainty on the ratio is propagated from both σs. Markdown export renders a `Relative` column (`--export-markdown`, also `--export-csv`, `--export-json`, `--export-asciidoc`; [README](https://github.com/sharkdp/hyperfine)).

**Post-hoc analysis is delegated to scripts over the JSON export.** JSON contains, per result, `command`, `mean/stddev/median/min/max`, raw `times`, `exit_codes`, and a `parameters` object carrying the `-L`/`-P` values — i.e., the export preserves the *factor levels*, enabling faceted plots. The [`scripts/`](https://github.com/sharkdp/hyperfine/tree/master/scripts) folder ships `advanced_statistics.py`, `plot_benchmark_comparison.py`, `plot_histogram.py`, `plot_parametrized.py`, `plot_progression.py`, `plot_whisker.py`, `welch_ttest.py` (Welch's t-test between two exported runs).

**Takeaway:** parameters-as-CLI-lists + `{var}` templating is the most ergonomic *expression* surface surveyed; comparison display is deliberately thin (single anchored ratio list), with statistics/plots pushed to JSON + scripts.

### 1.2 BenchmarkDotNet (.NET) — the gold-standard table

**Expression.** Attribute-driven matrix:

- `[Params(100, 200)] public int N;` — "you will get results for each combination of params values": multiple `[Params]` fields form a **cross-product** of cases; also `[ParamsSource]`, `[ParamsAllValues]`, `[Arguments]`/`[ArgumentsSource]` ([parameterization docs](https://benchmarkdotnet.org/articles/features/parameterization.html)).
- `[Benchmark(Baseline = true)]` marks a *method* baseline; `[SimpleJob(runtimeMoniker: RuntimeMoniker.Net462, baseline: true)]` marks a *job* (runtime/config) baseline; `[BenchmarkCategory(...)]` + `[GroupBenchmarksBy(BenchmarkLogicalGroupRule.ByCategory)]` gives **per-category baselines** ([baselines docs](https://benchmarkdotnet.org/articles/features/baselines.html)).

**Display.** One row per method × job × param combination. Param values become **their own columns to the left of the measures** (ordering controllable via column `Priority`):

```
|    Method |   A |  B |     Mean |   Error |  StdDev |
| Benchmark | 100 | 10 | 115.3 ms | 0.13 ms | 0.12 ms |
| Benchmark | 100 | 20 | 125.4 ms | 0.14 ms | 0.12 ms |
```

With a baseline, `Ratio` and `RatioSD` columns appear. Crucially, **Ratio is not mean/mean**: "we divide the first measurement of `Time50` into the first measurement of `Time100` (the baseline), the second measurement … and so on" — i.e., a paired per-measurement ratio distribution; `RatioSD` is the standard deviation of that distribution:

```
    Method | Runtime |     Mean |     Error |    StdDev | Ratio | RatioSD |
 SplitJoin |     Clr | 19.42 us | 0.2447 us | 0.1910 us |  1.00 |    0.00 |
 SplitJoin |    Core | 13.00 us | 0.2183 us | 0.1935 us |  0.67 |    0.01 |
 SplitJoin |    Mono | 39.14 us | 0.7763 us | 1.3596 us |  2.02 |    0.07 |
```

Per-category baselines reset Ratio=1.00 inside each visual group (blank separator rows between categories). ([baselines docs](https://benchmarkdotnet.org/articles/features/baselines.html))

**Takeaway:** the strongest *within-one-run* display design: factor columns left, measures right, one designated baseline yielding a ratio column, groups with local baselines. It has **no** cross-run/cross-commit story — everything compared must run in the same session.

### 1.3 criterion.rs + critcmp + cargo-criterion (Rust)

**Expression.** Named saved baselines decouple measurement from comparison ([CLI options](https://bheisler.github.io/criterion.rs/book/user_guide/command_line_options.html)):

- `cargo bench -- --save-baseline <name>` — compare against `<name>` then overwrite it.
- `cargo bench -- --baseline <name>` — compare against `<name>` without overwriting.
- `cargo bench -- --load-baseline <new> --baseline <master>` — compare two *stored* baselines without re-measuring.

Documented multi-revision workflow: checkout master, `--save-baseline master`; checkout feature, `--save-baseline feature`; then compare stored baselines pairwise. Default console output annotates each benchmark with a change estimate of the canonical shape `change: [-6.2% -3.1% +0.9%] (p = 0.28 > 0.05) — No change in performance detected.` (CI on relative change + significance verdict).

**critcmp** ([BurntSushi/critcmp](https://github.com/BurntSushi/critcmp)) generalizes to **N baselines × benchmarks**:

- `critcmp before change` — table with one column-group per baseline (time + throughput); within each row results are normalized so the best baseline shows ratio 1.00.
- `-f 'regex'` filter; `-t 5` hide rows where all diffs ≤5%; `-g '\w+/(input1)'` — regex **capture groups define comparison groups**, letting you compare *across benchmark names* (e.g., `impl_a/input1` vs `impl_b/input1`) — a poor-man's projection.
- `critcmp --export before > before.json` persists a baseline to a file; file args and named baselines mix (`critcmp before.json change.json`); `--baselines` lists; `--list` switches to a flat list when columns get unwieldy.

**cargo-criterion** adds `--message-format=json`: one JSON message per benchmark with `id`, raw `iteration_count`/`measured_values`, CI'd estimates (`typical`, `mean`, `median`, `median_abs_dev`, `slope`), and a `change` object (`mean`/`median` % vs previous run + verdict `NoChange|Improved|Regressed`) ([external tools docs](https://bheisler.github.io/criterion.rs/book/cargo_criterion/external_tools.html)); plus historical HTML reports ([README](https://github.com/bheisler/cargo-criterion)).

**Takeaway:** *named baselines* are the key move — a baseline is an addressable snapshot; comparison is a post-hoc query. critcmp's `-g` capture-group trick shows the demand for re-keying benchmark names into comparable groups (a projection language wants to exist here).

### 1.4 divan (Rust)

Parameterization via attributes: `#[divan::bench(args = [1, 2, 4, 8, 16, 32])]`, plus consts/generic-type/thread matrices ([README](https://github.com/nvzqz/divan)). Display is a **hierarchical tree** (group → benchmark → arg) with columns `fastest │ slowest │ median │ mean │ samples │ iters`:

```
example       fastest  │ slowest  │ median   │ mean     │ samples │ iters
╰─ fibonacci           │          │          │          │         │
   ├─ 1       0.626 ns │ 1.735 ns │ 0.657 ns │ 0.672 ns │ 100     │ 819200
   ├─ 2       2.767 ns │ 3.154 ns │ 2.788 ns │ 2.851 ns │ 100     │ 204800
```

**No baseline or cross-run comparison at all** — a deliberate scope cut. Takeaway: tree layout handles a deep case hierarchy well but doesn't compose with comparison columns.

### 1.5 Google Benchmark + tools/compare.py (C++)

**Expression.** Families are name-encoded (`BM_memcpy/64` via `->Args({...})`/`->Range(...)`, templated fixtures) — config lives *in the benchmark name*, like Go ([user guide](https://github.com/google/benchmark/blob/main/docs/user_guide.md)). Comparison is an explicit external subcommand with **three modes** ([docs/tools.md](https://github.com/google/benchmark/blob/main/docs/tools.md)):

```
compare.py benchmarks <baseline> <contender>                      # two binaries/JSON files
compare.py filters <benchmark> <filter_base> <filter_contender>   # two regex families in ONE binary
compare.py benchmarksfiltered <b1> <filter1> <b2> <filter2>       # cross product of the above
```

Mode 2 is notable: comparing *two name-filters within one run* is exactly the "proofs vs off within one commit" shape.

**Display.** Per-benchmark rows of relative difference computed as `(new - old) / |old|`, e.g. `BM_memcpy/64  -0.0468  -0.0470  76  73  76  73` (Time/CPU relative diff, then old/new absolute values). With repetitions ≥9 (docs: "**LARGE** (no less than 9) number of repetitions") it runs a **Mann–Whitney U-test** and emits p-value rows:

```
benchmark/threads:1/process_time/real_time_pvalue  0.0000  0.0000
  U Test, Repetitions: 27 vs 27
```

Green/red coloring keyed on p < `--alpha`; `--no-utest` disables.

**Takeaway:** the "explicit pair subcommand + U-test annotation" pattern; also the earliest example of *filters-as-comparison-operands* (compare two slices of one result set, not just two files).

### 1.6 asv / airspeed velocity (Python; numpy/scipy/pandas infra)

**Expression.** Three orthogonal surfaces ([using](https://asv.readthedocs.io/en/latest/using.html), [commands](https://asv.readthedocs.io/en/latest/commands.html), [writing benchmarks](https://asv.readthedocs.io/en/latest/writing_benchmarks.html)):

1. **What to measure:** git rangespecs — `asv run main..mybranch`, `asv run ALL`, `asv run v0.1^!`, `asv run NEW`, `asv run HASHFILE:hashes.txt`, `--steps N` (evenly-spaced subsample), `--skip-existing-commits` (cache-aware).
2. **Benchmark-level factors:** `params` as list-of-lists = cross product, with `param_names`:
   ```python
   time_ranges.params = ([10, 1000], ['range', 'arange'])
   time_ranges.param_names = ['n', 'function']
   ```
   Measure type is encoded in the *name prefix*: `time_`, `mem_`, `peakmem_`, `track_` (arbitrary metric), `timeraw_`.
3. **What to compare:** `asv compare revision1 revision2` and `asv continuous [base] branch` (run + compare in one step; base defaults to parent commit). Shared flags: `--factor F` ("the factor above or below which a result is considered problematic", default 1.1), `--split` (partition output into improved / unchanged / worsened tables), `--only-changed`, `--sort {name,ratio,default}`, `--machine`, `-E env`.

**Display.** before/after/ratio rows, hash- and tag-labeled columns:

```
       before           after         ratio
     [3bfda9c6]       [bf719488]
     <v0.1>           <v0.2>
      11.5±0.08μs     11.0±0μs       0.96  benchmark_name
```

Ratio column marks: `~` insignificant, green `-` improvement, red `+` regression, gray `x` incomparable. `asv continuous` ends with a verdict banner, e.g. `SOME BENCHMARKS HAVE CHANGED SIGNIFICANTLY. PERFORMANCE INCREASED.` (e.g. [scikit-image CI README](https://github.com/raybellwaves/scikit-image/blob/main/benchmarks/README_CI.md)). `asv publish` generates a static website: per-benchmark time series across commits, parameterized results split by param/machine/env, and an automatic "Regressions" tab ("statistically significant decreases of performance … based on the available data").

**Takeaway:** closest full-system analog to the harness: commits × environments × parameterized benchmarks with a results store, a pair CLI (`compare`), a run+compare convenience (`continuous`), triage ergonomics (`--factor`, `--split`, `--sort ratio`), and a *website* for the full matrix — the CLI never tries to show more than a pair.

### 1.7 pyperf (CPython's tool)

**Expression.** `pyperf compare_to ref.json changed1.json changed2.json ...` — first file is the reference, **arbitrarily many** contender files ([CLI docs](https://pyperf.readthedocs.io/en/latest/cli.html)).

**Display.** Prose per benchmark:

```
Mean +- std dev: [py36] 4.70 us +- 0.18 us -> [py38] 4.22 us +- 0.08 us: 1.11x faster
```

or table mode (`--table`, `--table-format md|rest`) — **one column per file**, cells annotated with the ratio vs the reference column, `(ref)` marker, and a **Geometric mean** footer row ("geometric mean of benchmark results means normalized to the reference"):

```
| Benchmark      | mult_list_py36 | mult_list_py37        | mult_list_py38        |
| [1,2]*1000     | 3.70 us        | 5.28 us: 1.42x slower | 3.18 us: 1.16x faster |
| Geometric mean | (ref)          | 1.22x slower          | 1.09x faster          |
```

Significance: "Student's two-sample, two-tailed t-test with alpha equals to 0.95"; insignificant results are hidden unless `-v`. Triage: `-G/--group-by-speed` (Slower/Faster/Same speed buckets), `--min-speed=PERCENT` threshold filter.

**Takeaway:** the cleanest *N-files-as-columns with a designated reference* CLI; per-file labels come from filenames; geomean footer standard.

### 1.8 JMH (Java)

`@Param({"1", "31", "65", "101", "103"}) public int arg;` — multiple `@Param` fields walk the **full cross product** ("the experiments require walking the configuration space"); override at the CLI with `-p arg=41,42` ([JMHSample_27_Params](https://github.com/openjdk/jmh/blob/master/jmh-samples/src/main/java/org/openjdk/jmh/samples/JMHSample_27_Params.java)). Result table has one `(paramName)` column per param, left of the score — same layout philosophy as BenchmarkDotNet:

```
Benchmark            (arg)  (certainty)  Mode  Cnt   Score    Error  Units
Bench.test               1            0  avgt   25   ...  ±   ...   ns/op
```

No built-in cross-run diff; ecosystem fills the gap (JSON output + external visualizers).

### 1.9 Go: benchstat + benchfmt + benchproc — **the closest prior art**

([pkg.go.dev/golang.org/x/perf/cmd/benchstat](https://pkg.go.dev/golang.org/x/perf/cmd/benchstat))

**Data model.** The Go benchmark text format ([design doc: "Proposal: Go Benchmark Data Format", Russ Cox & Austin Clements, 2016](https://go.googlesource.com/proposal/+/master/design/14313-benchmark-format.md)) is a stream of records: file-level `key: value` config lines + result lines `BenchmarkName/subkey=val-8 N value unit [value unit ...]`. All configuration is **key=value pairs living in the data**, not in tool state.

**Expression.** `benchstat [flags] inputs...`:

- `benchstat old.txt new.txt` — files become **columns**; `benchstat O=old.txt N=new.txt` names them (`label=path`).
- The 2023 rewrite ("second edition") exposes a full **projection language** (defaults shown): `benchstat -table .config -row .fullname -col .file old.txt new.txt`. Any key can go on any axis: `.name`, `.fullname`, `.file`, `.config`, `.unit`, `/name-key` (sub-name config, e.g. `/format`), `{file-config-key}` (e.g. `goos`).
- `-col /format new.txt` — compare **within one file** across a name key (json vs gob), no second file needed:
  ```
            │    json     │                 gob                  │
            │   sec/op    │   sec/op     vs base                 │
  Encode-48   1.423µ ± 1%   3.070µ ± 2%  +115.82% (p=0.000 n=10)
  ```
- Ordering/filter fused: `-col "/format@(gob json)"` fixes column order *and* filters to those values; `@alpha`, `@num` sorts (numeric understands `2k`, `1Mi`).
- `-filter EXPR` with a real grammar: `key:value`, `key:"quoted"`, `key:/regexp/`, `key:(v1 OR v2)`, `AND`/juxtaposition, `OR`, `-x` negation, `(...)`, `*` — full spec in [benchproc/syntax](https://pkg.go.dev/golang.org/x/perf/benchproc/syntax):
  ```
  expr    = andExpr {"OR" andExpr}
  andExpr = match {"AND"? match}
  match   = "(" expr ")" | "-" match | "*" | key ":" value | key ":" "(" value {"OR" value} ")"
  ```
  and projection: `part = key | key "@" order | key "@" "(" word {word} ")"`.
- `-confidence 95`, `-alpha 0.05`; unit metadata `assume=exact` for noiseless measures (binary size).

**Display.** Column-group per `-col` value; **first column is the base**; every later column gets a `vs base` sub-column with delta% + `(p=… n=…)`; `~` when insignificant (Mann–Whitney U, medians, 95% CI — "assumes nothing" non-parametric); **geomean footer row**; **one table per unit** (`sec/op`, `B/op`, `allocs/op` — units are normalized/"tidied"); tables further split by `-table` keys; footnote warnings when a projection hides variation ("¹ benchmarks vary in .fullname" — resolve with `-ignore`):

```
                      │   old.txt   │               new.txt               │
                      │   sec/op    │   sec/op     vs base                │
Encode/format=json-48   1.718µ ± 1%   1.423µ ± 1%  -17.20% (p=0.000 n=10)
Encode/format=gob-48    3.066µ ± 0%   3.070µ ± 2%        ~ (p=0.446 n=10)
geomean                 2.295µ        2.090µ        -8.94%
```

Docs also state the multiple-testing caveat explicitly: with α=0.05, expect ~5% of rows to be false positives.

**Takeaway:** benchstat is a **pivot-table algebra over a self-describing record stream** — filter + {table, row, col} projections + positional baseline + per-unit faceting + geomean. This is the closest existing "Vega-Lite for comparisons". Its one hard gap: **only one `-col` grouping key set at a time and no interaction/ratio-of-ratios** — a 2×2 (commit × treatment) must be flattened (e.g., `-col .file` where files are endpoint exports, or `-table /treatment -col .file`).

### 1.10 bencher.dev (continuous benchmarking service)

Dimension model: a **Threshold** is "a unique combination of: Branch, Testbed, and Measure" plus a statistical Model ([thresholds docs](https://bencher.dev/docs/explanation/thresholds/)). Tests: `static`, `percentage`, `z_score`, `t_test` (prediction intervals), `log_normal`, `iqr`, `delta_iqr`. Boundaries are directional ("Lower Boundary is used when a smaller value would indicate a performance regression" — throughput; Upper for latency). "An Alert is generated when a new Metric is below a Lower Boundary Limit or above an Upper Boundary Limit." Baseline window controlled by `--threshold-min-sample-size`, `--threshold-max-sample-size`, `--threshold-window` (seconds). CLI: `bencher run --branch B --testbed T --threshold-measure M --threshold-test t_test --threshold-upper-boundary 0.99 --err ...`. The perf explorer UI addresses a view as project × branches × testbeds × benchmarks × measures encoded in the URL — i.e., **comparisons are saved queries against named dimensions**, not files.

**Takeaway:** "endpoint-addressed" taken to its logical end: every observation is addressed by (branch, testbed, benchmark, measure); comparison = query + statistical model against the addressed history. No factorial/interaction support either.

### 1.11 conbench (Apache Arrow)

"Language-independent Continuous Benchmarking (CB) Framework" ([repo](https://github.com/conbench/conbench)); results published as JSON with tags/context/machine info; comparison = **lookback z-score**: "assigns a numeric z-score value to a benchmark result that represents how consistent the result is in the context of the historic distribution of similar results", where the history "must share the contender's contextual characteristics" ([lookback z-score docs](https://conbench.github.io/conbench/pages/lookback_zscore.html)). Notable operational detail: genuine perf changes must be **flagged to the server** so pre-/post-change data aren't mixed ("causing artificially-inflated variance that causes false negatives"). Takeaway: context-matching (only compare observations whose non-varied keys agree) is made explicit and first-class.

### 1.12 CodSpeed

CI service; per-repo default regression threshold 10% relative to the default branch, per-benchmark overrides 0–50% ([performance checks](https://docs.codspeed.io/features/performance-checks), [impact metrics](https://codspeed.io/docs/features/understanding-the-metrics)). Reporting is a PR comment + status check: "Performance will be reported if there is a significant improvement … or a failure (a regression or a drop)". Takeaway: the *pair* (head vs default branch) is hard-wired; the expression surface is just thresholds. Deterministic (instruction-count) measurement sidesteps run-to-run statistics.

### 1.13 rustc-perf compare UI (bonus — a real 3-factor matrix in production)

[perf.rust-lang.org/compare.html](https://perf.rust-lang.org/compare.html): pick two commits; the table is benchmark × **profile** (check/debug/opt/doc) × **scenario** (full/incr-full/incr-unchanged/incr-patched) with % change per cell, filters over each factor, and significance judged against per-benchmark historical noise (the "significance threshold"; see [comparison analysis docs](https://github.com/rust-lang/rustc-perf/blob/master/docs/comparison-analysis.md)). Takeaway: even with 3 factors they keep the *comparison* binary (two artifacts) and put the factors on rows/facets — the matrix is in the rows, never in the comparison operator.

### 1.14 Ad-hoc conventions

The dominant real-world practice for anything beyond a pair: export per-configuration files and (a) paste into a spreadsheet/pivot table, (b) run benchstat over relabeled files (`benchstat A=a.txt B=b.txt C=c.txt` works for N≥2 columns; each non-first column compared to the first), or (c) one-off matplotlib/pandas scripts (hyperfine's `scripts/` institutionalizes this). The Go format's design goal was exactly to make (b) composable: tools "emit and consume a common text format" so files are the interchange unit ([format proposal](https://go.googlesource.com/proposal/+/master/design/14313-benchmark-format.md)).

---

## 2. Conceptual languages & literature

- **Pivot/projection algebra over key=value records** — [benchproc syntax spec](https://pkg.go.dev/golang.org/x/perf/benchproc/syntax) (filter grammar + projection grammar + `@(...)` order-filter fusion). This *is* the "Vega-Lite of benchmark comparison": a small closed language mapping data keys to {table, row, col} axes with a positional baseline. No academic paper; the spec is the artifact.
- **Vega-Lite** — "Vega-Lite: A Grammar of Interactive Graphics", A. Satyanarayan, D. Moritz, K. Wongsuphasawat, J. Heer, IEEE TVCG 23(1) (InfoVis), 2017. [https://idl.cs.washington.edu/papers/vega-lite/](https://idl.cs.washington.edu/papers/vega-lite/). Relevant precisely for its `row`/`column` **facet channels** and layered composition: a comparison table is a faceted visualization with a text mark. Vega-Lite's lesson: pick a tiny set of orthogonal channels (x, y, row, column, color) and let data fields bind to them — benchstat's `-table/-row/-col` is the same design with `col` implying "compare".
- **Tidy data** — H. Wickham, "Tidy Data", Journal of Statistical Software 59(10), 2014. [https://www.jstatsoft.org/article/view/v059i10](https://www.jstatsoft.org/article/view/v059i10). One observation per row, one variable per column: the precondition for any projection language. The harness's JSONL is already tidy; treatments/targets/backends are variables, not file identities.
- **Design of experiments / factorial vocabulary** — R. Jain, *The Art of Computer Systems Performance Analysis*, Wiley, 1991, Part IV (2^k and 2^k·r factorial designs, main effects, **interactions**, sign tables, allocation of variation). [https://www.cse.wustl.edu/~jain/books/perfbook.htm](https://www.cse.wustl.edu/~jain/books/perfbook.htm). Also G. Box, J. S. Hunter, W. G. Hunter, *Statistics for Experimenters*, 2nd ed., Wiley, 2005. [https://www.wiley.com/en-us/Statistics+for+Experimenters%2C+2nd+Edition-p-9780471718130](https://www.wiley.com/en-us/Statistics+for+Experimenters%2C+2nd+Edition-p-9780471718130). This is the existing *conceptual language* for "did the proofs overhead get worse": commit and treatment are **factors**, the ratio-of-ratios is the **interaction effect**, and in log space it is literally the interaction coefficient of the linear model `log(time) ~ commit + treatment + commit:treatment`.
- **Statistics for ratios and their composition** —
  - T. Kalibera, R. Jones, "Rigorous Benchmarking in Reasonable Time", ISMM 2013. [https://dl.acm.org/doi/10.1145/2464157.2464160](https://dl.acm.org/doi/10.1145/2464157.2464160) — hierarchical random-effects model deciding how many repetitions at each level; CIs for ratios of means.
  - T. Kalibera, R. Jones, "Quantifying Performance Changes with Effect Size Confidence Intervals", Univ. of Kent TR 4-12, 2012. [https://kar.kent.ac.uk/33611/](https://kar.kent.ac.uk/33611/) — argues for reporting effect-size CIs on the ratio rather than p-values alone.
  - A. Georges, D. Buytaert, L. Eeckhout, "Statistically Rigorous Java Performance Evaluation", OOPSLA 2007. [https://dl.acm.org/doi/10.1145/1297027.1297033](https://dl.acm.org/doi/10.1145/1297027.1297033) — CIs + ANOVA/Tukey HSD when comparing >2 alternatives (the multiple-comparison problem the harness will hit at N configs).
  - E. C. Fieller, "Some Problems in Interval Estimation", JRSS B 16(2), 1954. [https://www.jstor.org/stable/2984043](https://www.jstor.org/stable/2984043) — the ratio CI already used by the harness; note it does not compose into ratio-of-ratios; log-space deltas do (variances add).
  - P. J. Fleming, J. J. Wallace, "How not to lie with statistics: the correct way to summarize benchmark results", CACM 29(3), 1986. [https://dl.acm.org/doi/10.1145/5666.5673](https://dl.acm.org/doi/10.1145/5666.5673) — geometric mean is the only valid mean for normalized ratios: justifies the geomean footer everywhere.
  - T. Hoefler, R. Belli, "Scientific Benchmarking of Parallel Computing Systems: Twelve ways to tell the masses when reporting performance results", SC '15. [https://dl.acm.org/doi/10.1145/2807591.2807644](https://dl.acm.org/doi/10.1145/2807591.2807644) — reporting rules (CIs, nonparametric tests, don't average ratios arithmetically).
- **Benchmark data format as the interop layer** — R. Cox, A. Clements, "Proposal: Go Benchmark Data Format", 2016. [https://go.googlesource.com/proposal/+/master/design/14313-benchmark-format.md](https://go.googlesource.com/proposal/+/master/design/14313-benchmark-format.md). Design principles worth stealing: line-oriented, self-describing key=value config at file and per-benchmark scope, units in-band, tool-agnostic.

**Literature gap:** no surveyed tool or paper offers a *language* for interactions/ratio-of-ratios on a CLI. The DOE literature has the concepts (interaction effects, factorial ANOVA); the tools all stop at "N columns vs one base". The closest expressible workaround is two-pass composition (compute within-commit ratio as a derived measure, then compare that measure across commits).

---

## 3. Recurring patterns (synthesis)

### Expression patterns

| Pattern | Tools | Shape |
|---|---|---|
| **Factor lists → cross product** | hyperfine `-L`/`-P`, BDN `[Params]`, JMH `@Param`/`-p`, asv `params` list-of-lists, divan `args` | declare levels; tool enumerates the matrix; cases carry their factor values |
| **Named saved baselines** | criterion `--save-baseline/--baseline/--load-baseline`, critcmp, hyperfine JSON files | measurement decoupled from comparison; baseline = addressable snapshot |
| **N files as columns** | benchstat (`label=path`), pyperf `compare_to --table`, critcmp | file identity = configuration identity; labels from filenames |
| **One designated baseline + ratio column** | BDN `Baseline=true` (method/job/category), benchstat first column, pyperf first arg, asv `revision1`, hyperfine `--reference` | ratio/delta always *vs base*, never all-pairs |
| **Explicit pair subcommand** | `asv compare`/`continuous`, `compare.py benchmarks`, `pyperf compare_to` | comparison as a verb over two result sets |
| **Filters as comparison operands** | `compare.py filters` (two regexes in one file), critcmp `-g` capture groups, benchstat `-col /key` | compare two *slices of one dataset* — no second run needed |
| **Projection mini-language** | benchstat/benchproc `-table/-row/-col/-filter`, `@(...)` | the only true grammar; any data key on any table axis |
| **Named-dimension service** | bencher (Branch×Testbed×Measure), conbench (context matching), CodSpeed (head vs default branch) | comparison = query + statistical model over an addressed history |

### Display patterns

| Pattern | Tools | Notes |
|---|---|---|
| Config/factor columns left of measures | BDN, JMH `(param)` columns | long format; scales in rows, not columns |
| One column-group per file/config, `vs base` sub-column | benchstat, pyperf table, critcmp | wide format; caps at ~3–5 columns on a terminal |
| Delta% + `(p=… n=…)`; `~` for insignificant | benchstat, compare.py (U-test rows), asv (`~`/`x` marks), criterion (`p = … > 0.05`) | annotation belongs *in the cell*, verdict marks beat raw p-values for scanning |
| Practical-significance threshold distinct from statistical | asv `--factor 1.1`, pyperf `--min-speed`, CodSpeed 10%, critcmp `-t` | two independent filters; both needed |
| Triage partitions | asv `--split`, pyperf `-G` (Slower/Faster/Same), `--sort ratio` | improved/unchanged/worsened buckets |
| Geomean footer | benchstat, pyperf | per Fleming–Wallace, only valid summary of normalized ratios |
| Facet: one table per unit/measure | benchstat (`sec/op` vs `B/op` vs `allocs/op` tables) | *measures multiply tables, not columns* |
| Hierarchy tree | divan | good for case explosion, incompatible with comparison columns |
| Row-normalize to best | critcmp, hyperfine summary | ok for "which is fastest", wrong for "what changed" |

---

## Implications for this harness

**1. The store is already benchstat-shaped; the missing piece is a projection layer, not a new pair runner.** Each JSONL observation keyed by (binary sha, backend, treatment, file sha, timeout) is a tidy record with factor keys. Benchstat proves the right decomposition for exactly this situation: **filter → {table, row, col} projection → first-projected-column-as-baseline → per-unit facet → geomean footer**. Concretely, a `bench report` command with `--filter`, `--table`, `--row`, `--col KEY[@(v1 v2)]` where `@(...)` fixes order (baseline = first) *and* filters, covers every comparison the user listed without any pair enumeration: `--col treatment@(off proofs) --table target` gives proofs-overhead per commit; `--col target@(old new) --table treatment` gives per-treatment commit deltas; `--row workload` always. Steal the grammar wholesale from [benchproc/syntax](https://pkg.go.dev/golang.org/x/perf/benchproc/syntax) — it is small, proven, and documented.

**2. Cheapest possible prototype: emit benchfmt and run real benchstat.** Serialize each observation as `Benchmarkworkload/target=old/backend=main/treatment=proofs 1 1.234 sec/op 51234567 max-RSS-bytes 0.42 search-sec/op 0.11 apply-sec/op …` and `benchstat -row /workload -col /treatment -table /target results.txt` works today, including delta+p (Mann–Whitney), `~`, geomean, and **per-phase facet tables for free** because phases are just extra units ([format](https://go.googlesource.com/proposal/+/master/design/14313-benchmark-format.md), [benchstat](https://pkg.go.dev/golang.org/x/perf/cmd/benchstat)). This is a day of work and answers "is the matrix view actually useful" before committing to native code. Caveats: benchstat's stats are nonparametric medians (fine, arguably better than the current t-CI for skewed wall times) and it won't do Fieller ratios or interactions.

**3. Endpoints stay the atoms; add a matrix *selector*, not matrix *state*.** Follow hyperfine's `-L` for expression: `--endpoints target=old,new treatment=off,proofs backend=main` expands to the cross product; the cache makes the expansion nearly free for already-measured cells (asv's `--skip-existing-commits` is the same insight). Because the store is content-addressed, criterion-style *named baselines* are unnecessary — a "baseline" is just a saved endpoint alias/filter, which is strictly better (conbench's context-matching rule: only compare records whose non-varied keys agree; make that a hard error, not a footnote — benchstat's "¹ benchmarks vary in .fullname" warning is the model).

**4. Interaction ("did proofs overhead get worse") — no tool has it; build it as a derived measure, not a new table type.** Two designs, in order of preference:
   - **Derived ratio measure (recommended):** materialize `overhead = proofs/off` per (target, workload) as a first-class measure with a CI, then feed it through the *same* projection machinery: `--measure ratio(treatment: proofs/off) --col target@(old new) --row workload`. The ratio-of-ratios is then just the ordinary "vs base" column of a derived-measure table — compositional, one new primitive, display unchanged. Do the derived-ratio CI in **log space** (Δlog with variances added in quadrature, or bootstrap over the cached raw times); Fieller intervals do not compose into second-order ratios cleanly ([Fieller 1954](https://www.jstor.org/stable/2984043), [Kalibera & Jones 2012](https://kar.kent.ac.uk/33611/)).
   - **Log-linear model:** per workload fit `log t ~ target * treatment`, report `exp(coef)` with CIs; the interaction term is exactly the user's question and it generalizes to k factors ([Jain, Part IV](https://www.cse.wustl.edu/~jain/books/perfbook.htm)). Statistically cleaner, but harder to display and explain; keep as a `--model` power-tool later, not the default.

**5. Display: adopt the benchstat conventions verbatim; cap width; facet aggressively.**
   - Wide format (column-group per config, `vs base` sub-column with `delta% (p=… n=…)` and `~`) for ≤4 configs; beyond that fall back to long format with factor columns on the left (BDN-style) or `--list` (critcmp's escape hatch).
   - **Measures/phases multiply tables, not columns** (benchstat's unit faceting). With wall + RSS + 6 phases + upcoming egg-equivalence measures, any design that puts measures in columns dies immediately; per-measure tables with a `--measure` filter is the only shape that survives.
   - Keep both thresholds: statistical (`p`/CI, with a multiple-comparisons note — at 30 rows × α=0.05 expect ~1–2 false flags, per benchstat's own docs) and practical (asv's `--factor`, pyperf's `--min-speed`); add `--split`/`--sort ratio` triage buckets for wide sweeps.
   - Geomean footer only over ratio columns, never arithmetic mean ([Fleming & Wallace](https://dl.acm.org/doi/10.1145/5666.5673)).
   - Beyond the CLI, don't build a dashboard yet: hyperfine's model (JSON export + small plotting scripts keyed on the `parameters` field) covers one-off questions; asv's published site is the eventual shape if the matrix becomes a standing artifact.

**6. What NOT to build.** (a) A full Vega-Lite-class grammar — 4 projection knobs + `@(...)` + derived ratio measure covers every comparison enumerated, and each additional operator multiplies the test surface; (b) all-pairs comparison output (nobody does it; always one base per table); (c) run-coupled comparison à la `asv continuous`/`compare.py` — with a content-addressed cache, *measurement* and *reporting* should stay separate commands; the report command should be a pure function of the store.

**Bottom line:** the problem has strong prior art; the winning combination is benchfmt/benchstat's record + projection model for expression and display, hyperfine's factor-list ergonomics for selecting the matrix, BDN's paired-ratio rigor for the ratio columns, and one genuinely novel (but small) primitive — the derived within-factor ratio measure in log space — to answer interaction questions no existing tool can express.
