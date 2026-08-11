# Statistically Sound Comparison of Benchmark Results Across Multiple Configurations

Research survey, 2026-08-11. Context: the egglog benchmarking harness is today pair-only (baseline vs candidate endpoint, per-cell mean + t CI, ratio + Fieller CI, append-only JSONL cache). The user wants a *matrix* of endpoints — e.g. {old, new} × {off, proofs} — with within-row ratios, within-column ratios, and interactions ("did proofs overhead itself get worse?"), soon multiplied by more measures. This report maps the literature on (a) sound estimates/CIs per comparison, (b) aggregation across workloads, (c) interactions (ratio-of-ratios), (d) multiplicity control for big matrices, (e) run planning/stopping, and (f) existing *languages* for specifying and displaying benchmark comparisons.

---

## 1. Why single numbers lie: noise and bias in the measurement layer

Any matrix design inherits the validity of its cells, so the measurement-bias literature is the floor.

- **Mytkowicz, Diwan, Hauswirth, Sweeney — "Producing Wrong Data Without Doing Anything Obviously Wrong!" (ASPLOS 2009)**. UNIX environment-variable size and link order alone changed SPEC CPU2006 conclusions; measurement bias is "significant and commonplace." Remedies: *experimental setup randomization* (randomize link order, env size, etc. across runs) and causal analysis to detect bias. https://dl.acm.org/doi/10.1145/1508284.1508275 (summary: https://sape.inf.usi.ch/publications/asplos09)
- **Curtsinger & Berger — "STABILIZER: Statistically Sound Performance Evaluation" (ASPLOS 2013)**. Re-randomizes code/stack/heap layout *during* execution so layout effects become i.i.d. Gaussian noise, licensing t-tests/ANOVA. Headline result: LLVM `-O3` vs `-O2` on SPEC CPU2006 is statistically indistinguishable from noise once layout is randomized. Paper: https://people.cs.umass.edu/~emery/pubs/stabilizer-asplos13.pdf ; code: https://github.com/ccurtsinger/stabilizer
- **Barrett, Bolz-Tereick, Killick, Mount, Tratt — "Virtual Machine Warmup Blows Hot and Cold" (OOPSLA/PACMPL 2017)**. Krun controls machine state (reboots per process execution, pinned CPU frequency, temperature checks, fresh user, network off); PELT changepoint analysis classifies each run as warmup / flat / slowdown / no-steady-state. ≤43.5% of ⟨VM, benchmark⟩ pairs consistently reached "good" steady state; they bootstrap CIs *within* changepoint segments, never across, and use a tolerance band (variance-based + 0.001 s absolute) to call segments equivalent. https://dl.acm.org/doi/10.1145/3133876 ; HTML: https://soft-dev.org/pubs/html/barrett_bolz-tereick_killick_mount_tratt__virtual_machine_warmup_blows_hot_and_cold_v6/
- **Tratt — "Minimum Times Tend to Mislead When Benchmarking" (blog, 2019)**. Programs have a *set* of performance points (e.g., Rust HashMap ordering randomization → >6× spread between min and max legitimate times); the minimum systematically underestimates what users see and can invert algorithm choices. Report "something about the distribution as a whole," preferably CIs. https://tratt.net/laurie/blog/2019/minimum_times_tend_to_mislead_when_benchmarking.html
  - Counterpoint for *microbenchmarks*: **Chen & Revels — "Robust benchmarking in noisy environments" (arXiv 2016, BenchmarkTools.jl)** defends the minimum as a robust location estimator when noise is strictly additive and one-sided. https://arxiv.org/pdf/1608.04295 . For whole-program wall time with genuine performance multimodality (your case), Tratt's argument wins.
- **Maricq, Duplyakin, Jimenez, Maltzahn, Stutsman, Ricci — "Taming Performance Variability" (OSDI 2018)**. ~900k datapoints across 835 servers; heavy non-normality and multimodality in practice; recommends nonparametric CIs (CIs on medians/quantiles), explicit sample-size planning, and randomized/interleaved run orders because environment drifts over time. https://www.usenix.org/system/files/osdi18-maricq.pdf
- **SIGPLAN Empirical Evaluation Checklist** (Berger, Blackburn, et al., 2018) is the community checklist form of all the above. https://www.sigplan.org/Resources/EmpiricalEvaluation/

Matrix-relevant consequences: (1) cells measured in different *sessions* (your JSONL cache reuses old baseline observations) are confounded with environment drift — the exact failure mode Mytkowicz/Maricq document; headline comparisons should be measured interleaved in one session, or the cache key should include a session/machine-state fingerprint. (2) Any per-cell summary should be defensible under multimodality (median or mean-with-bootstrap, not minimum).

## 2. Per-cell inference: the Georges and Kalibera–Jones line

- **Georges, Buytaert, Eeckhout — "Statistically Rigorous Java Performance Evaluation" (OOPSLA 2007)**. Surveyed prevalent practice (best-of-N, single runs, means without variation) and showed it can invert conclusions. Prescribes: multiple VM invocations × multiple iterations, mean + CI per configuration, ANOVA/Tukey for >2 alternatives, and the *visual overlapping-CI test* as a conservative screen. Ships JavaStats, which **adaptively runs until the CI half-width is within a chosen fraction of the mean** — an early sequential-stopping rule (see §7 caveat). PDF: https://dri.es/files/oopsla07-georges.pdf ; summary: https://dri.es/statistically-rigorous-java-performance-evaluation
- **Kalibera & Jones — "Quantifying Performance Changes with Effect Size Confidence Intervals" (U. Kent TR 4-12, 2012; arXiv 2020)**. The most complete treatment of exactly your problem shape. Key ideas:
  - Model the experiment as an **n-level random-effects hierarchy** (iterations within executions within compilations within …): total variance σ² = Σᵢ σᵢ². Estimate per-level variance with S₁²…, unbiased Tᵢ²: `T₁² = S₁²`, `Tᵢ² = Sᵢ² − Sᵢ₋₁²/nᵢ₋₁`; if Tᵢ² ≤ 0 that level contributes nothing and can be collapsed.
  - Report the **effect size as a ratio-of-means CI** — "A is faster than B by 5.5% ± 2.5% with 95% confidence" — constructed either parametrically (Fieller-style, asymptotic normality of the per-level means) or by **hierarchical bootstrap** (resample *at each level*, preserving nesting; 1000 replicates; take the 2.5%/97.5% quantiles of the simulated ratio).
  - The ratio CI **subsumes NHST**: interval excludes 1 ⇒ significant; and you can test *practical* significance by checking the CI against e.g. [0.97, 1.03].
  - arXiv: https://arxiv.org/abs/2007.10899 ; TR PDF: https://www.cs.kent.ac.uk/pubs/2012/3233/content.pdf
- **Kalibera & Jones — "Rigorous Benchmarking in Reasonable Time" (ISMM 2013)**. The "cookbook": run a **pilot (dimensioning) experiment** to estimate the Tᵢ², then compute **optimal repetition counts per level** minimizing CI width for a fixed time budget — counts depend only on adjacent-level cost ratios and variance ratios, `nᵢ = ⌈√((cᵢ/cᵢ₋₁)·(Tᵢ²/Tᵢ₊₁²))⌉` (notation as in the TR §3; n at the top level is then whatever the budget affords). Then in the real experiment, repeat only at the levels that matter (e.g., if within-process variance is negligible, do 1 iteration × many process executions). https://dl.acm.org/doi/10.1145/2464157.2464160 ; https://kar.kent.ac.uk/33611/
- **Nonparametric alternative for cells**: Go's **benchstat** defaults to **median + CI on the median** per cell and **Mann–Whitney U** for A/B deltas ("assume=nothing"); `assume=exact` for noise-free metrics like binary size (§10 has the full flag set). https://pkg.go.dev/golang.org/x/perf/cmd/benchstat
- **Chen, Guo, Temam, Wu, Bao, Xu, Chen — "Statistical Performance Comparisons of Computers" (HPCA 2012 / IEEE TC 2015)**: nonparametric **Hierarchical Performance Testing (HPT)** — Wilcoxon-style tests within benchmarks, rank-based across benchmarks — precisely because small-n per cell rarely justifies normality. https://dl.acm.org/doi/10.1109/TC.2014.2315614
- **Touati, Worms, Briais — "The Speedup-Test" (Concurrency & Computation 2013)**: a decision protocol (Shapiro–Wilk → t-test or Wilcoxon–Mann–Whitney) distinguishing "speedup of the mean" from "speedup of the median," distributed as an R tool. https://onlinelibrary.wiley.com/doi/abs/10.1002/cpe.2939 ; https://inria.hal.science/inria-00443839v2

## 3. Ratios: Fieller, delta method, bootstrap, and the log transform

**Fieller's theorem** (1954) gives the exact CI for a ratio of (possibly correlated) normal means. For independent samples with means x̄ (numerator), ȳ (denominator), squared standard errors v₁ = s²ₓ/nₓ, v₂ = s²ᵧ/nᵧ, and t the critical value, the bounds are the roots of a quadratic; with `g = t²v₂/ȳ²` the interval is finite iff **g < 1** (denominator significantly ≠ 0); as g→1 it becomes infinite, and for g>1 it is the *complement* of an interval. Wikipedia (formula and conditions): https://en.wikipedia.org/wiki/Fieller%27s_theorem ; accessible derivation: https://statisticaloddsandends.wordpress.com/2022/04/23/fiellers-confidence-sets-for-ratio-of-two-means/ . For benchmark data (CV ≪ 1, so g ≈ 0), Fieller ≈ delta method ≈ log-t; the differences only matter when the denominator CI approaches 0 — for wall times that never happens, so **the choice of ratio-CI machinery is not the bottleneck; the experiment design is** (Kalibera & Jones make the same point by offering Fieller and bootstrap interchangeably).

**Log transform.** `log` turns ratios into differences: the ratio of geometric means of A and B is `exp(mean(log tA) − mean(log tB))`, with a plain **Welch t CI on the difference of log-means**: `SE = √(s²_logA/nA + s²_logB/nB)`, df by Welch–Satterthwaite, CI `exp(d ± t·SE)`. Advantages: (i) ratios/speedups compose additively, so *any* contrast — including interactions — is a linear combination of log-means with textbook CIs; (ii) execution times are right-skewed and closer to lognormal, so log-scale normality assumptions are more honest (benchmark distributions are non-normal in practice: Maricq §1; the geometric-mean-as-lognormal-model argument: Mashey §5); (iii) the geomean across workloads is just the arithmetic mean of log-ratios (§5). Caveat: log requires strictly positive data — fine for wall time and RSS, *not* fine for per-phase times that can be 0 (use bootstrap or absolute deltas there). Precision of GM vs mean under lognormality is analyzed in Thelwall & Fairclough, "The precision of the arithmetic mean, geometric mean and percentiles for citation data" (arXiv 2015): https://arxiv.org/pdf/1512.01688

**Bootstrap.** The assumption-free fallback for any statistic: hierarchical/percentile bootstrap as in Kalibera & Jones (resample runs within cell → recompute the statistic → quantiles). Widely productized: Haskell criterion and Rust **criterion.rs** bootstrap their estimates and regression slopes (https://bheisler.github.io/criterion.rs/book/analysis.html). Use ≥1000 replicates; percentile or BCa intervals.

## 4. Interactions: the ratio-of-ratios cell

The question "did proofs overhead get worse from old→new?" is the 2×2 interaction `(new-proofs/new-off) / (old-proofs/old-off)` — a **difference-in-differences on the log scale** (DiD background: https://en.wikipedia.org/wiki/Difference_in_differences).

- **Fieller does not extend cleanly.** Fieller covers one ratio of two normal quantities. A ratio of ratios is a nonlinear function of four means; there is no exact quadratic trick. The generalization people actually use in biostatistics is **MOVER-R** (Method Of Variance Estimates Recovery for ratios; Donner & Zou 2012, Newcombe 2016), which recovers a ratio CI from the separate CIs of numerator and denominator and *contains Fieller as a special case* — you can feed it two Fieller intervals to get a ratio-of-ratios interval. Newcombe, "MOVER-R confidence intervals for ratios and products of two independently estimated quantities": https://journals.sagepub.com/doi/abs/10.1177/0962280213502144 ; overview: https://pmc.ncbi.nlm.nih.gov/articles/PMC10769102/ ; R impl: https://rdrr.io/cran/pairwiseCI/man/MOVERR.html
- **The practical answer is the log scale.** On logs the interaction is the linear contrast `I = (μ̂₁₁ − μ̂₁₀) − (μ̂₀₁ − μ̂₀₀)` of four cell log-means, `SE(I) = √(Σᵢ s²ᵢ/nᵢ)`, Welch–Satterthwaite df `≈ (Σ s²ᵢ/nᵢ)² / Σ (s²ᵢ/nᵢ)²/(nᵢ−1)`, and `exp(I ± t·SE)` is the CI for the ratio-of-ratios. Equivalently fit `log t ~ commit * treatment` (per workload) and read the interaction coefficient. This generalizes to any lattice of contrasts and to mixed models with workload as a random effect — which is exactly Kalibera & Jones's random-effects view (§2).
- **Or bootstrap**: resample runs within each of the four cells, recompute the ratio-of-ratios, take quantiles. Correct under skew/multimodality and works for phase times with zeros. This is the only method of the three that doesn't need positivity or normality.

One caution: interactions of *ratios* silently ignore magnitudes. "Proofs overhead worsened 1.10×" may be 5 ms on a 50 ms workload. Pair each interaction ratio with the absolute per-run delta-of-deltas in seconds.

## 5. Aggregating across workloads: the means war

- **Fleming & Wallace — "How Not to Lie with Statistics: The Correct Way to Summarize Benchmark Results" (CACM 1986)**: arithmetic mean of *normalized* results depends on the normalization machine and can invert rankings; the **geometric mean is consistent under normalization** (GM of ratios = ratio of GMs). https://dl.acm.org/doi/10.1145/5666.5673
- **Smith — "Characterizing Computer Performance with a Single Number" (CACM 1988)**: rebuttal — GM of ratios predicts *no* physically meaningful quantity (not total time on any workload mix); if you care about a workload's total time, use time-weighted arithmetic (or, for rates, harmonic) means on *unnormalized* data. https://dl.acm.org/doi/10.1145/63039.63043
- **Mashey — "War of the Benchmark Means: Time for a Truce" (SIGARCH CAN 2004)**: reconciliation — the fight is really about the implied *population model*. If benchmarks are a random sample from a workload population whose runtimes are **lognormal**, the GM (= exp of mean of logs) is the right location estimator and comes with a standard deviation (of logs) and CIs; the arithmetic/harmonic means answer a different question (performance on a *specified* mix). https://dl.acm.org/doi/10.1145/1040136.1040137
- **Citron, Hurani, Gnadrey — "The harmonic or geometric mean: does it really matter?" (SIGARCH CAN 2006)**: empirically, for SPEC-like data the choice rarely flips rankings, but the *question being answered* differs. https://dl.acm.org/doi/10.1145/1186736.1186738
- **Eeckhout — "R.I.P. Geomean Speedup: Use Equal-Work (Or Equal-Time) Harmonic Mean Speedup Instead" (IEEE CAL 2024)**: modern re-litigation — geomean speedup corresponds to no realizable workload; equal-work HM speedup does. https://users.elis.ugent.be/~leeckhou/papers/CAL-2024-geomean.pdf
- **Practice**: SPEC CPU2017 computes per-benchmark ratios vs a reference machine and reports the **geometric mean**; runs are median-of-3 (or slower-of-2). https://www.spec.org/cpu2017/Docs/overview.html . Go's benchstat prints a **geomean row per column** and warns when geomeans are incomparable (different benchmark sets). https://pkg.go.dev/golang.org/x/perf/cmd/benchstat

Resolution for a suite of heterogeneous .egg files (no meaningful "total workload"): the **GM of per-workload ratios** is the right *typical relative change* summary, and on the log scale it is simply the mean of per-workload log-ratios — so its CI is a paired t interval over workloads (workload = blocking factor), or a bootstrap over workloads if the suite is small/heterogeneous. Report it as "typical ratio," never as "the suite got X% faster in total." If total time across the suite is actually meaningful to you, additionally report the ratio of summed times (equal-work arithmetic view, per Smith/Eeckhout).

**Rank-based alternative for "which config wins overall":**
- **Demšar — "Statistical Comparisons of Classifiers over Multiple Data Sets" (JMLR 2006)**: Wilcoxon signed-ranks for 2 systems over N workloads; **Friedman test + Nemenyi post-hoc** for k systems; **critical-difference diagrams** as the display. Canonical for "k configurations × N benchmarks" matrices; robust to a few outlier workloads dominating a geomean. https://dl.acm.org/doi/10.5555/1248547.1248548 ; overview: https://davidstutz.de/statistical-comparisons-of-classifiers-over-multiple-data-sets-demsar/
- **Benavoli, Corani, Demšar, Zaffalon — "Time for a Change: a Tutorial for Comparing Multiple Classifiers Through Bayesian Analysis" (JMLR 2017)**: Bayesian replacement (Bayesian signed-rank / hierarchical model) yielding P(A better), P(equivalent within ROPE), P(B better) — see §8. https://jmlr.org/papers/v18/16-305.html ; hierarchical version: https://arxiv.org/pdf/1609.08905

## 6. Keeping a big matrix honest: multiplicity, filtering, minimum effects

A {2 targets × 2 treatments} × 20 workloads × 6 phase measures matrix is hundreds of implicit hypothesis tests; at α=0.05 you *will* ship false "regressions." Standard machinery:

- **Bonferroni** (α/m) — simplest, very conservative for large m.
- **Holm (1979)** step-down — uniformly better than Bonferroni, still controls familywise error (FWER); reject smallest p against α/m, next against α/(m−1), …
- **Benjamini–Hochberg (1995) FDR** — sort p₍₁₎≤…≤p₍ₘ₎, find largest k with `p₍ₖ₎ ≤ (k/m)·q`, reject 1..k; controls the *expected fraction of false discoveries* at q; the right trade-off for dashboards where you want power across many cells and can tolerate a bounded proportion of false flags. **Benjamini–Yekutieli** if tests are arbitrarily dependent. Implementation: `scipy.stats.false_discovery_control` (`method="bh"` or `"by"`): https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.false_discovery_control.html ; operating characteristics: https://pubmed.ncbi.nlm.nih.gov/18052910/
- **Family definition matters more than the correction**: correct within a *displayed table* (one measure, one contrast type, all workloads), not across your whole database — otherwise adding measures forever erodes power. This "family = the set of claims read together" convention is the practical standard in large A/B platforms (FDR for many simultaneous treatment effects: https://arxiv.org/pdf/1808.04904).
- **Significance filtering as UI**: benchstat's approach — show the delta only when the Mann–Whitney p < α, else print `~` with `(p=…, n=…)` — is multiplicity control by *display convention* rather than by correction, plus explicit warnings (too-few-samples, incomparable geomeans). https://pkg.go.dev/golang.org/x/perf/cmd/benchstat
- **Minimum practical effect**: a CI excluding 1.0 is not interesting if the effect is 0.4%. Kalibera & Jones explicitly support testing bounds against a practical band (e.g. [0.97, 1.03]); Bayesian ROPE formalizes the same (§8); the VM-warmup paper's tolerance band (variance-based + 0.001 s absolute) is the same idea for equality-calling. Distinguish three cell states: *different* (CI outside band), *equivalent* (CI inside band — this is a positive claim, cf. equivalence testing / TOST: https://daniellakens.blogspot.com/2017/02/rope-and-equivalence-testing.html), *inconclusive* (CI straddles).

## 7. How many runs, and when to stop

- **Plan from a pilot** (Kalibera & Jones ISMM 2013, §2 above): estimate per-level variance once per (workload, endpoint) family, then fix repetition counts; re-plan occasionally. This is the statistically clean option and caches beautifully.
- **Adaptive stopping on CI width** (JavaStats; also pyperf-style tooling) *biases coverage slightly* but is benign if the stopping rule looks only at CI *width*, not at whether the effect is significant.
- **Stopping on significance is the trap**: continuous monitoring inflates false positives to 3–8× nominal — **Johari, Koomen, Pekelis, Walsh, "Peeking at A/B Tests: Why It Matters, and What To Do About It" (KDD 2017)**; the fix is **always-valid p-values / confidence sequences** (mSPRT), which stay valid under optional stopping at ~20–30% wider intervals. https://dl.acm.org/doi/10.1145/3097983.3097992 ; journal version "Always Valid Inference" (Operations Research 2022): https://dl.acm.org/doi/10.1287/opre.2021.2135 ; deployment at scale: https://dl.acm.org/doi/abs/10.1145/3543873.3584635
- **Distribution-stability stopping**: **PT4Cloud (He et al., ESEC/FSE 2019)** stops when the bootstrapped performance *distribution* stops changing between test blocks (95.4% accuracy at 62% fewer runs, cloud setting). https://dl.acm.org/doi/10.1145/3338906.3338912 ; PDF: https://wwang.github.io/papers/PT4Cloud.pdf
- **Steady-state detection**: changepoint analysis (PELT) rather than fixed warmup-iteration counts (Barrett et al. §1); follow-up showing fixed heuristics still mis-classify Java steady state: Traini et al., "Towards effective assessment of steady state performance in Java software" (EMSE 2022): https://arxiv.org/pdf/2209.15369

## 8. Bayesian estimation alternatives

- **Kruschke — "Bayesian Estimation Supersedes the t Test" (BEST, J. Exp. Psych. General 2013)**: posterior over the difference of means (t-likelihood, robust to outliers) plus **ROPE** decisions: accept "no meaningful change" if the 95% HDI lies inside the ROPE, "changed" if outside. This is the only mainstream framework that lets a dashboard *affirm* "no regression" rather than "failed to detect." ROPE tooling: https://easystats.github.io/bayestestR/reference/rope.html
- **Benavoli et al. (JMLR 2017)** and **Corani et al. hierarchical model (arXiv 2016)** (§5) apply exactly this to the "k systems × N benchmarks" matrix, outputting per-pair probabilities P(faster)/P(ROPE)/P(slower) — arguably the most honest cell content for a comparison matrix, at the cost of MCMC machinery and priors. https://jmlr.org/papers/v18/16-305.html ; https://arxiv.org/pdf/1609.08905
- In benchmarking practice Bayesian methods appear mostly via these classifier-comparison tools and via ROPE-style thresholds; frequentist CIs + FDR remain the deployed norm in perf CI systems (§9).

## 9. Matrices over *time*: continuous-benchmarking practice

Not your immediate question, but the same statistical problem with commits as one axis; the deployed answers are instructive:

- **Daly et al. — "The Use of Change Point Detection to Identify Software Performance Regressions in a CI System" (ICPE 2020, MongoDB)**: E-divisive change-point detection over per-benchmark time series replaced per-commit threshold tests, slashing false alarms. https://dl.acm.org/doi/10.1145/3358960.3375791 ; blog: https://www.mongodb.com/blog/post/using-change-point-detection-find-performance-regressions
- **Hunter / Apache Otava (ICPE 2023)**: productized E-divisive with significance testing. https://dl.acm.org/doi/10.1145/3578244.3583719 ; https://arxiv.org/pdf/2301.03034
- **asv (airspeed velocity)** detects regressions by fitting a **piecewise-constant (Potts-model) step function** with per-point noise weights, solved by dynamic programming. https://asv.readthedocs.io/en/latest/step_detection.html
- **conbench (Apache Arrow)**: "lookback z-score" — flag a result whose z-score vs a rolling historical distribution exceeds a threshold. https://conbench.github.io/conbench/pages/lookback_zscore.html
- **bencher.dev**: per-(branch, testbed, measure) *thresholds* with pluggable tests — `--threshold-test t_test`, percentage bands, etc. https://bencher.dev/docs/explanation/thresholds/
- Mozilla's comparative study of CPD techniques for perf anomaly detection: https://arxiv.org/pdf/2606.18377

## 10. Languages for specifying comparisons; display conventions

Is there a "Vega-Lite for benchmark comparison"? Not exactly — but there are five distinct traditions with partial answers, and one of them (benchstat) is very close to what you want.

**(a) Data-format + projection algebra: Go's benchmark ecosystem (closest prior art).**
- The **Go benchmark data format** (design doc: https://go.googlesource.com/proposal/+/master/design/14313-benchmark-format.md) is a tiny language: file-level `key: value` configuration lines (goos, commit, …), benchmark names carrying sub-benchmark dimensions as slash-separated `name=value` pairs (`BenchmarkDecode/format=json/size=1e4-8`), values with units, and unit metadata (`better=lower`, `assume={nothing,exact}`).
- **benchstat** then provides a *projection algebra over those keys*: `-table KEYS` (facet into tables), `-row KEYS`, `-col KEYS` (which dimension is being *compared*), `-ignore KEYS`, a filter expression language (`-filter "/format:json goos:linux .unit:(ns/op OR B/op)"`, with AND/OR/NOT, regex, value alternation), sort orders (`@alpha`, `@num`, fixed order `@(off proofs)` which also filters), `-confidence`, `-alpha`. Cells show `median ± CI%`; comparison columns show `vs base` percent deltas with `(p=… n=…)`, `~` when insignificant; a **geomean row**; and *ambiguity warnings* when a projection collapses distinct configurations ("¹ benchmarks vary in .fullname"). https://pkg.go.dev/golang.org/x/perf/cmd/benchstat ; worked multi-dimension examples: https://www.bwplotka.dev/2024/go-microbenchmarks-benchstat/
  This is precisely a declarative "what to compare" spec: **dimensions → {facet, row, col(compare-against-base)}** is the Vega-Lite-style encoding channel mapping, for tables instead of charts. Its limits: only one comparison dimension at a time (no interaction cells), pairwise vs-base only, no FDR across the table.
- **(a′)** `benchstatn` extends benchstat to >2-way comparisons: https://github.com/lkarlslund/benchstatn
- **(a″)** Rust criterion.rs encodes only baseline comparisons (`cargo bench -- --baseline NAME`, `critcmp`); bootstrap analysis per cell: https://bheisler.github.io/criterion.rs/book/analysis.html ; **hyperfine** does pairwise CLI comparisons with Welch t-test in `scripts/`: https://github.com/sharkdp/hyperfine

**(b) Experiment-specification configs: ReBench.**
**ReBench** (Marr) is a declarative YAML language for the *execution* side: benchmark suites × executors × experiments, invocations/iterations counts, and scheduling; **ReBenchDB** stores results and generates comparison reports. It answers "what to run, reproducibly," not "what contrasts to compute." https://rebench.readthedocs.io/en/latest/config/ ; https://github.com/smarr/ReBenchDB . Marr's own analyses then drop into R (https://stefan-marr.de/2011/09/using-r-to-understand-benchmarking-results/). Conbench similarly fixes a schema (benchmark, case permutations, context, machine) and provides comparison endpoints. https://ursalabs.org/blog/announcing-conbench/

**(c) Statistical-analysis specification languages (HCI/stats community).**
- **Tea (Jun et al., UIST 2019)**: declarative programs stating variables, study design (independent/dependent), assumptions, and hypotheses; a constraint solver picks valid statistical tests and runs them. https://dl.acm.org/doi/10.1145/3332165.3347940 ; https://tea-lang.org/
- **Tisane (Jun et al., CHI 2022)**: specify conceptual relationships (causes, moderates) + measurement/hierarchy; it derives an appropriate (generalized) linear mixed model interactively. Directly relevant conceptually: your "workload = random block, target × treatment = crossed fixed factors" is exactly a Tisane-shaped model. https://dl.acm.org/doi/10.1145/3491102.3501888
- **PlanOut (Bakshy, Eckles, Bernstein, WWW 2014)**: Facebook's DSL for specifying randomized experiment *assignment* (factors, randomization units). https://facebook.github.io/planout/
- **Boba (Liu, Kale, Althoff, Heer, IEEE TVCG 2021)**: DSL for *multiverse* analyses — write shared analysis code once with declared decision points; compiler emits the cross-product of analysis scripts; visualizer shows result sensitivity across the decision space. A good conceptual match for "did my conclusion depend on which summary statistic/filters I picked?" https://arxiv.org/abs/2007.05551
- Classical **design-of-experiments vocabulary** underlies all of these: factors, levels, full/fractional factorial designs, allocation of variation, interactions — Jain, *The Art of Computer Systems Performance Analysis* (Wiley 1991), part IV: https://www.cse.wustl.edu/~jain/books/perfbook.htm

**(d) Display conventions for many comparisons.**
- benchstat tables (above): baseline column absolute, other columns as ratio/Δ% + significance mark + footnoted warnings; geomean row.
- **Critical-difference diagrams** (Demšar §5): one axis = mean rank across workloads; bars join configurations that are statistically indistinguishable. The standard "k systems, N benchmarks" one-glance picture.
- SPEC-style: per-benchmark ratio bars + a single geomean; median-of-3 run selection (https://www.spec.org/cpu2017/Docs/overview.html).
- Perf-CI dashboards (conbench/bencher/asv): time-series per cell with flagged change points, not matrices.

**(e) The gap.** No existing tool combines: (i) benchstat's projection algebra, (ii) contrast *types* beyond vs-base (interactions, ratio-of-ratios), (iii) CI-per-cell with FDR across the displayed family, and (iv) equivalence/ROPE semantics. That combination is small and well-defined — the literature supplies every component; nobody has packaged it. That is the honest answer to "is there a Vega-Lite for this": *no, but the grammar is short and you'd be assembling known pieces, with benchstat as the syntax precedent and Kalibera–Jones + BH as the semantics.*

---

## Implications for this harness

Opinionated takeaways, in decreasing order of leverage.

### 1. Move all comparison math to the log scale; keep Fieller only as a cross-check
Store per-observation `log(wall)`, `log(rss)`. Every cell of every comparison becomes a **linear contrast of cell log-means** with a Welch t CI, exponentiated for display:
- Simple ratio (new-off vs old-off): `exp(d ± t·SE)`, `d = m̂₁ − m̂₀`, `SE = √(s²₁/n₁ + s²₀/n₀)`.
- **Interaction** ("proofs overhead worsened"): `I = (m̂_new,pf − m̂_new,off) − (m̂_old,pf − m̂_old,off)`, `SE = √(Σ₄ s²ᵢ/nᵢ)`, Welch–Satterthwaite df; `exp(I)` is the ratio-of-ratios with a CI. **Do not try to extend Fieller** — it doesn't compose; MOVER-R exists (https://journals.sagepub.com/doi/abs/10.1177/0962280213502144) but the log-contrast is simpler, and a hierarchical percentile bootstrap (resample runs within each cell, ≥1000 reps) is the assumption-free fallback and the *only* correct option for phase times that can be 0. Your existing Fieller code stays as a validation path: for CV ≲ 10% it must agree with log-t to well under a percentage point; disagreement is a red flag for multimodality → bootstrap that cell.

### 2. A cell is: estimate + CI + n + state, never a bare ratio
Per (workload, contrast): point ratio, 95% CI, n per side, and one of three states — **different** (CI outside the practical band), **equivalent** (CI entirely inside the band; a positive claim), **inconclusive** (straddles). Adopt a default band of ±2% *relative* AND a per-workload absolute floor (e.g. 5 ms), VM-warmup-style, so 3× "regressions" on 1 ms phases don't page anyone. Render benchstat-style: significant cells get the %Δ, insignificant get `~ (p=…, n=…)`; equivalence gets `≈`. Every table footnotes warnings (small n, cross-session data, phase sums ≠ total).

### 3. Aggregate across workloads with the geomean of ratios — computed as the mean of log-ratios — plus a rank check
Because workloads are paired across endpoints (same .egg file), the geomean row's CI is a **paired t over per-workload log-ratios** (or bootstrap over workloads for small suites). Label it "typical ratio," and never present it as total-time change (Smith 1988 / Eeckhout 2024 objection); if suite total time matters, add a separate "Σtime ratio" row. For "which endpoint wins overall" across ≥3 endpoints, use Friedman + Nemenyi ranks / a critical-difference view (Demšar) rather than eyeballing geomeans — it is robust to one workload dominating.

### 4. Control multiplicity per displayed family with BH FDR; make the family explicit
Family = one rendered table = (one measure) × (one contrast type) × (all workloads). Compute p-values from the log-scale t (or bootstrap), run **Benjamini–Hochberg at q = 0.05** (`scipy.stats.false_discovery_control`), and let significance-filtering (`~`) reflect the *adjusted* decisions. Do not correct across measures or across tables the user didn't open — that erodes power pointlessly; do print "m = 24 comparisons, FDR 5%" in the table header so readers know the guarantee. Phase-time tables deserve this most: 6 phases × N workloads × k contrasts is where false discoveries will breed. (Phases are also compositional — they sum to the total — so always show the absolute Δseconds column beside the ratio.)

### 5. Interactions get their own column, not their own mental math
In a {targets} × {treatments} table, render three contrast columns per workload row: `new/old @ off`, `new/old @ proofs`, and `Δoverhead = (proofs/off)_new ÷ (proofs/off)_old` with its CI from §1. This is the piece no existing tool gives you and the piece your users will otherwise compute wrongly by dividing two point estimates.

### 6. Fix the session confound before trusting the cache
Cross-session comparisons (cached old-endpoint runs vs fresh new-endpoint runs) are confounded with environment drift (Mytkowicz, Maricq). Cheap mitigations: (a) record a session id + machine fingerprint (kernel, governor, load) per observation and mark any cross-session comparison in the output (footnote, not refusal); (b) for headline numbers, re-run all cells of the matrix **interleaved in randomized order within one session** (round-robin across endpoints, not blocks) — this also breaks slow thermal/frequency drift; (c) when re-measuring is too expensive, at least re-run a canary workload from the cached side and check it reproduces within its old CI.

### 7. Plan n from a pilot; if you adapt, adapt on CI width only
Use Kalibera–Jones dimensioning: a pilot per (workload, endpoint) estimates between-run variance; pick n per cell to hit a target CI half-width (e.g. ±1% on log scale ⇒ n ≈ (t·s/0.01)²). Cache the variance estimates in the JSONL. Never "run until significant" (peeking inflates false positives severalfold — Johari et al. KDD 2017); stopping when the CI is narrower than the practical band is fine. If you later want fully sequential behavior in CI, use always-valid confidence sequences, but that's overkill for a local harness.

### 8. Build the small grammar; skip the general tool
The comparison-spec language worth building is tiny because your key space is already fixed: dimensions `{target, backend, treatment, workload, measure, phase, session}`. A spec is:
```
facet:   measure            # one table per measure
rows:    workload           # + aggregate rows: geomean, Σtime
cols:    target@(old new)   # the contrast dimension, with baseline = first level
holding: backend=dd
extra:   interaction(target, treatment)   # adds the Δoverhead column
band:    2% | 5ms           # practical-equivalence band
fdr:     0.05               # per-table BH
```
i.e. benchstat's `-table/-row/-col/-filter` algebra (proven syntax: https://pkg.go.dev/golang.org/x/perf/cmd/benchstat) plus two extensions benchstat lacks: an `interaction(dimA, dimB)` contrast and band/FDR semantics. Emitting the underlying observations in the Go benchmark text format (workload and treatment as `name=value` sub-benchmark keys, target/backend as file-level config keys) is worth considering purely to get benchstat interop for free while your own renderer matures. Do **not** build a general stats DSL (Tea/Tisane territory) or a dashboard; one table renderer (CLI + optional HTML) over one contrast engine covers everything described here.

### 9. What to deliberately not do
- No minimum-time summaries for whole-program cells (Tratt); median or mean-with-CI only. Keep min/max as diagnostics.
- No arithmetic mean of per-workload ratios, ever (Fleming & Wallace).
- No unbounded matrix: a spec must name its family; "show me everything vs everything" output should refuse to attach stars/flags and render CIs only.
- No Bayesian machinery *initially* — ROPE-style bands (§2) capture 90% of the benefit; revisit Benavoli-style P(faster)/P(equiv)/P(slower) cells only if users demand "probability this got slower" phrasing.
- No change-point/time-series layer until you actually track commits continuously; when you do, copy asv's step detection or Otava rather than inventing one.

### Minimal reading list (in order)
1. Kalibera & Jones, effect-size CIs — https://arxiv.org/abs/2007.10899
2. Kalibera & Jones, ISMM'13 cookbook — https://dl.acm.org/doi/10.1145/2464157.2464160
3. benchstat docs (syntax to steal) — https://pkg.go.dev/golang.org/x/perf/cmd/benchstat
4. Demšar 2006 (k×N matrices, CD diagrams) — https://dl.acm.org/doi/10.5555/1248547.1248548
5. Johari et al. 2017 (why not to peek) — https://dl.acm.org/doi/10.1145/3097983.3097992
6. Fleming & Wallace 1986 + Mashey 2004 (means) — https://dl.acm.org/doi/10.1145/5666.5673 , https://dl.acm.org/doi/10.1145/1040136.1040137
