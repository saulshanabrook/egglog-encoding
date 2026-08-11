# DOE / Factorial Vocabulary as a Language for Benchmark Comparison Matrices

Research report, 2026-08-11. Question: does Design-of-Experiments (DOE) give a ready-made conceptual language for the harness's move from pair-only comparison to a `{targets} x {backends} x {treatments}` grid over workloads — and specifically for "which ratios are worth reporting" and "did the proofs overhead itself get worse between commits"?

Short answer: yes, almost perfectly. The harness's grid **is** a factorial design; "which ratios to report" is the classical theory of **contrasts**; "did the overhead change" is a textbook **2x2 interaction**, identical in math to econometrics' difference-in-differences; and taking logs of wall time converts every ratio question into ordinary additive linear-model machinery. The systems-performance community already imported this vocabulary once (Jain 1991; Yi/Lilja/Hawkins 2003; Kalibera & Jones 2013), so there is precedent for using it verbatim in a benchmarking tool.

---

## 1. Core DOE vocabulary, with the harness mapping

Primary sources: NIST/SEMATECH e-Handbook of Statistical Methods, Section 5 (Process Improvement / DOE), glossary at [5.7](https://www.itl.nist.gov/div898/handbook/pri/section7/pri7.htm); Raj Jain, *The Art of Computer Systems Performance Analysis* (Wiley, 1991, ISBN 0471503363, [publisher page](https://www.wiley.com/en-us/The+Art+of+Computer+Systems+Performance+Analysis:+Techniques+for+Experimental+Design,+Measurement,+Simulation,+and+Modeling-p-9780471503361)), Ch. 16 "Introduction to Experimental Design" ([slides](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_16ied.pdf)).

| DOE term | Definition (NIST/Jain) | Harness equivalent |
|---|---|---|
| **Response variable** | The outcome measured (Jain 16: "throughput, response time") | a *measure*: wall seconds, max RSS, per-phase time, per-ruleset time, (soon) egg-equivalence stats |
| **Factor** | "Process inputs an investigator manipulates to cause a change in the output" (NIST 5.7); Jain: "variables that affect the response … also called predictor variables" | `target` (git ref/PR/path), `backend` (main/dd), `treatment` (off/term/proofs/causal-receipts/causal-proofs) |
| **Level** | "The values that a factor can assume" (Jain 16) | `off`, `proofs`, …; a specific commit sha |
| **Treatment / treatment combination / run** | "A specific combination of factor levels whose effect is to be compared with other treatments" (NIST 5.7) — NIST explicitly says *run* = treatment combination | one endpoint config = (target, backend, treatment). Note the harness already uses "treatment" for one factor; DOE's "treatment combination" is the harness's "endpoint" |
| **Cell** | A treatment combination's slot in the design table; observations in it are its replicates (NIST "balanced design" entry) | one row-group in the JSONL cache: key (binary sha, backend, treatment, file sha, timeout) — the cache key **is** a cell identifier, plus block |
| **Replication** | "Performing the same treatment combination more than once" — this is what lets you separate random error from real effects (NIST 5.7) | repeated runs behind the per-cell mean + t CI |
| **Block / blocking** | "A schedule for conducting treatment combinations … such that any effects due to known changes in materials, operators, machines … become concentrated in the blocking variable" (NIST 5.7). Box's slogan quoted by NIST [5.3.3.2](https://www.itl.nist.gov/div898/handbook/pri/section3/pri332.htm): "**Block what you can, randomize what you cannot**" | each `.egg` **workload** is a block: it's not a factor whose effect you care to estimate for its own sake, but a known source of huge variation you must not average across naively. Machine/session is a second (currently implicit) block |
| **Experimental unit** | "Any entity that is used for experiments … generally no interest in comparing the units" (Jain 16) | a single process invocation |
| **Primary vs. secondary factors** | Factors whose effects need quantifying vs. those that don't (Jain 16) | target/treatment are primary; workload is secondary — this is exactly why "workload = block, not factor" is the right call |
| **Main effect** | "How changing the settings of a factor changes the response," averaged over the other factors (NIST 5.7) | "how much slower is proofs vs off, averaged over commits" |
| **Interaction** | "The effect of one factor on a response depends on the level of another factor" (NIST 5.7; Jain 16) | "did the proofs overhead change between commits" |
| **Full factorial** | Run all level combinations: `2^k` runs for k two-level factors (NIST [5.3.3.3.2 worked 2^3 example](https://www.itl.nist.gov/div898/handbook/pri/section3/pri3332.htm)) | the `{2 targets} x {2 treatments}` grid, per block |
| **Fractional factorial** | "Only an adequately chosen fraction of the treatment combinations … is selected to be run" (ASQC def. quoted in NIST [5.3.3.4](https://www.itl.nist.gov/div898/handbook/pri/section3/pri334.htm)) | deliberately not running some cells (e.g., dd backend only at off/proofs) — fine *if* you track what gets aliased |
| **Confounding / aliasing** | "When the estimate of an effect also includes the influence of one or more other effects … the effects are said to be aliased" (NIST 5.7) | e.g., comparing cached old-commit numbers (measured in June) against fresh new-commit numbers confounds `target` with `measurement epoch` |
| **Randomization** | "A schedule for allocating treatment material … such that conditions in one run neither depend on nor predict conditions in subsequent runs" (NIST 5.7) | run ordering: interleave/shuffle cells rather than all-baseline-then-all-candidate |

Jain Ch. 16 also names the design the harness has today: **"simple design" / one-factor-at-a-time** — vary one factor while holding others fixed — and is blunt about it: "Not statistically efficient. Wrong conclusions if the factors have interaction. **Not recommended.**" ([slides 16-10](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_16ied.pdf)). The user's instinct to want the 2x2 instead of two separate pairs is literally the founding argument of factorial design (Fisher's, via NIST [5.3.3.3](https://www.itl.nist.gov/div898/handbook/pri/section3/pri333.htm)): factorial designs measure interactions, OFAT cannot.

---

## 2. Contrasts: the formal answer to "which ratios are worth reporting"

**Definition** ([Wikipedia: Contrast (statistics)](https://en.wikipedia.org/wiki/Contrast_(statistics))): a contrast is a linear combination `Σ aᵢ μᵢ` of cell means whose coefficients sum to zero, `Σ aᵢ = 0`. Two contrasts are **orthogonal** when `Σ aᵢbᵢ = 0`. Jain's 2^k chapter makes the identification explicit for factorial effects: "effects are linear combinations of responses. Sum of the coefficients is zero → **contrasts**" ([Ch. 17 slides, 17-7](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_172kd.pdf)). Jain Ch. 18 gives the CI: for contrast `u = Σ hᵢ qᵢ` with `Σ hᵢ = 0`, variance is `s²ₑ Σhᵢ²/(2^k r)` and the CI uses `t[1−α/2; 2^k(r−1)]` ([Ch. 18 slides, 18-15/18-16](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_182kr.pdf)).

For the 2x2 grid with cell means `m_ij` (i = target ∈ {old, new}, j = treatment ∈ {off, proofs}), the cells span 4 degrees of freedom: 1 grand mean + exactly **3 orthogonal contrasts**. In the classical ±1 sign-table parameterization (Jain Ch. 17: model `y = q₀ + q_A x_A + q_B x_B + q_AB x_A x_B`, effects computed by multiplying the sign column into the response column):

| Contrast | coefficients on (old-off, old-proofs, new-off, new-proofs) | Meaning | On log scale = which ratio |
|---|---|---|---|
| main effect of target | (−1, −1, +1, +1)/2 | avg. commit-to-commit change | geomean(new-off/old-off, new-proofs/old-proofs) |
| main effect of treatment | (−1, +1, −1, +1)/2 | avg. proofs overhead | geomean(old-proofs/old-off, new-proofs/new-off) |
| **interaction** | (+1, −1, −1, +1) | change in the overhead | **(new-proofs/new-off) ÷ (old-proofs/old-off)** — the ratio of ratios |

The user's four wished-for ratios are **not** 4 independent quantities — they are 4 *simple effects* (a.k.a. simple contrasts: differences within a row or column) living in the same 3-dimensional contrast space:

- `new-off/old-off` and `new-proofs/old-proofs` = simple effects of target at each treatment;
- `proofs/off` within each commit = simple effects of treatment at each target;
- "did the overhead get worse" = the interaction = (simple effect at new) − (simple effect at old) — either direction gives the *same* number: `(m₂₂−m₂₁)−(m₁₂−m₁₁) = (m₂₂−m₁₂)−(m₂₁−m₁₁)`.

Two DOE prescriptions follow directly:

1. **Report the interaction first.** If it is non-negligible, the main effects ("proofs costs X% on average") are misleading summaries and you should report simple effects per level instead. If the interaction is ≈ 0, collapse to the two main effects and gain precision (they're then estimated from all 4 cells). This "test interaction → conditionally collapse" workflow is the standard factorial-ANOVA reporting discipline (NIST [5.3.3.3](https://www.itl.nist.gov/div898/handbook/pri/section3/pri333.htm), Jain Ch. 22).
2. **Diagonal ratios are confounded contrasts.** `new-proofs/old-off` has log-scale coefficients (−1, 0, 0, +1) = ½(target effect) + ½(treatment effect) + ½(interaction) — a mixture of all three. DOE vocabulary gives you a principled reason to *refuse to print it* (or to print it only as a derived quantity): it answers no single question. This is the precise sense in which "which ratios are worth reporting" has a formal answer: **the ratios worth reporting are the ones whose log-contrast coefficients isolate one effect**.

Generalization: an `a x b` grid has `(a−1)` + `(b−1)` + `(a−1)(b−1)` contrast dimensions. For {2 targets} x {5 treatments}: 1 target contrast, 4 treatment contrasts (e.g., each treatment vs `off` — "treatment-vs-control", Dunnett-style), and 4 interaction contrasts ("did *each* treatment's overhead change"). The treatment-vs-control structure means `off` should be a distinguished level in the harness vocabulary, not just one of five.

---

## 3. Interaction = difference-in-differences = ratio of ratios on the log scale

Econometrics reinvented the 2x2 interaction under the name **difference-in-differences** ([Wikipedia: Difference in differences](https://en.wikipedia.org/wiki/Difference_in_differences)): in the regression `y = β₀ + β₁·T + β₂·S + β₃·(T·S) + ε`, the DiD estimate is the interaction coefficient `β̂₃ = [E(y|T=1,S=1) − E(y|T=0,S=1)] − [E(y|T=1,S=0) − E(y|T=0,S=0)]`. With log outcomes, β₃ is interpreted as a proportional effect — a ratio of ratios. Mapping: T = treatment on/off, S = commit; DiD's **parallel-trends assumption** ("both groups would experience identical changes absent treatment") has a useful harness analogue: interpreting the interaction as "the proofs *machinery* got slower" assumes the off-mode change would have applied equally to the proofs path — worth stating, not assuming, when the off-path change is large (e.g., a rewrite that only accelerates the non-instrumented hot loop).

**Why log scale is the load-bearing choice.** Jain Ch. 18 ("Multiplicative Models for 2^2r Experiments", [slides](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_182kr.pdf)) works Example 18.8: processor/benchmark times spanning `y_max/y_min = 147.90/0.0118 ≈ 12,534`. Fit additively, residuals grow with the response and a large spurious "interaction" appears; after `log y`, "interaction is almost zero" and "unexplained variation is only 0.2%". His modeling assumptions for the additive analysis — IID normal errors, equal variance everywhere, additive effects — are all violated by raw wall-times and all approximately restored by logs. He also notes the general tool (Box–Cox transformations) and the sanity limit: "knowledge about the system behavior should always take precedence over statistical considerations."

Consequences for the harness, stated as identities:

- `mean(log t)` per cell ↔ **geometric mean** time; difference of cell means of logs ↔ log of ratio of geometric means.
- The candidate/baseline **Fieller CI** currently used is the machinery for a ratio of *arithmetic* means. On the log scale a ratio CI is just `exp(t-CI on the difference of log-means)` — plain Student-t arithmetic, no Fieller, and it composes: the interaction CI is `exp(t-CI on a 4-coefficient contrast)`, something Fieller does not give you at all. Fieller answers "ratio of arithmetic means" (see [Fieller's theorem](https://en.wikipedia.org/wiki/Fieller%27s_theorem)); the log-t answers "ratio of geometric means." For right-skewed timing data the geometric target is defensible and is what makes the whole matrix additive.
- Fleming & Wallace, "How not to lie with statistics: the correct way to summarize benchmark results," CACM 29(3), 1986 ([ACM DL](https://dl.acm.org/doi/10.1145/5666.5673)): arithmetic means of normalized ratios give base-dependent, contradictory rankings; geometric means of ratios are base-independent. I.e., aggregating per-workload *ratios* across blocks must be geometric — which is again just "average the log differences."

Caveats on logs: fine for wall time and RSS; per-phase times include near-zero phases (`unattributed`, tiny `merge`), where `log` explodes — model phases on the raw scale or as shares, and beware that shares are compositional (one phase's share rising forces others down).

---

## 4. ANOVA, allocation of variation, and Jain's 2^k chapters

Jain Ch. 17 ([2^k Factorial Designs slides](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_172kd.pdf)) gives the effect algebra: sign table with orthogonal ±1 columns; effect `q_A` = (sign column A) · (response column) / 2^k; **allocation of variation**: `SS_A = 2^k q_A²` (for 2², `SSA = 4q_A²`), and *importance of a factor = fraction of total variation it explains* — e.g., his memory/cache study: memory 76%, cache 19%, interaction 5%; his Omega/Crossbar network case study: reference pattern 77% of variation, network type second, interaction small. Ch. 18 adds replication: `2^k r` observations, `SSE` with `2^k(r−1)` df, per-effect standard errors `s_e/√(2^k r)`, t-based CIs for effects and contrasts, "CI does not include zero → significant", plus the visual checks (residual-vs-predicted trend, normal Q-Q).

Allocation of variation is a reporting idiom the harness could adopt wholesale: before printing 20 ratios, print one line per factor — *"across this suite, workload explains 88% of variance in log-time, treatment 9%, target 0.6%, target:treatment 0.1%, residual 2%"*. It instantly tells the reader whether the commit even matters relative to noise, and it is cheap (sums of squares of the same contrasts you already computed). Ch. 19 covers `2^(k−p)` fractional factorials and confounding structure ([slides](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_19ffd.pdf)); Ch. 20 one-factor ANOVA ([slides](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_20ofe.pdf)).

---

## 5. Ratio games: Jain's chapter on how matrices of ratios lie

Jain Ch. 11 "Ratio Games" ([slides](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_11rg.pdf)) is a catalogue of exactly the failure modes a comparison-matrix feature can institutionalize:

- **Base choice flips conclusions.** Case study 11.1 (6502 vs 8080): ratio-of-totals says 6502 is 4.7% worse; normalizing per-benchmark with 6502 as base says 6502 is 1% *better*; with 8080 as base, 6% worse. Same numbers, three headlines. Case study 11.2 is the Patterson/Séquin RISC-I code-size dispute — same table, opposite conclusions by base choice.
- His guidelines: if one system wins on *all* benchmarks, no ratio game can reverse the conclusion (only exaggerate it); if wins are split, contradictory conclusions are constructible in some cases; for a higher-is-better metric, an advocate benefits from using the *opponent* as base, etc. There is even a "strategy" slide (elongate benchmarks that favor you). The slide deck's summary: "Ratio games arise from use of incomparable bases."
- **Percentage traps**: Simpson-style reversal ("System B is better on both systems ... System A is better overall"), 1000% vs 11x, "400% reduction," small samples disguised as percentages.

Design lesson: a matrix UI must fix the base *by convention* (control level per factor: `old`, `off`), display geometric means when aggregating across blocks (Fleming & Wallace, §3), and never silently sum raw times across workloads (that's ratio-of-totals, weighted by whichever workload is longest).

---

## 6. DOE applied to systems: the direct precedents

- **Yi, Lilja & Hawkins, "A Statistically Rigorous Approach for Improving Simulation Methodology," HPCA-9, 2003** ([PDF](https://www.cs.ucr.edu/~gupta/hpca9/HPCA-PDFs/26-yi.pdf)). Uses a **Plackett–Burman** saturated screening design (Plackett & Burman, Biometrika 1946): estimate N main effects in ~N+1 runs (next multiple of 4), with a "foldover" variant at ~2N runs that frees main effects from 2-factor aliasing. They rank 40+ SimpleScalar parameters by effect on CPI, classify benchmarks by effect-vector similarity, and evaluate an enhancement by how it *changes the effect ranking*. Relevance: (a) proof-of-concept that raw DOE vocabulary transfers to systems tooling; (b) the pattern to reach for when the factor list grows (many treatments x backends x runtime knobs): screen with a fraction, then run the full factorial only on the survivors. Their key caution transfers too: levels that are too far apart inflate a factor's apparent effect.
- **Kalibera & Jones, "Rigorous Benchmarking in Reasonable Time," ISMM 2013** ([Kent repository](https://kar.kent.ac.uk/33611/), [ACM DL](https://dl.acm.org/doi/10.1145/2464157.2464160)). The replication question DOE calls "experimental unit structure": variation arises at multiple nested levels (build/compilation, execution, in-process iteration), and you should replicate most where variance is largest, with formulas for optimal counts per level and for CIs on *ratios* of means of hierarchical experiments. For this harness: binary-build and process-execution are distinct replication levels; the JSONL cache keyed by binary sha silently fixes the build level at r=1.
- **Georges, Buytaert & Eeckhout, "Statistically Rigorous Java Performance Evaluation," OOPSLA 2007** ([PDF](https://dri.es/files/oopsla07-georges.pdf), [ACM DL](https://dl.acm.org/doi/10.1145/1297027.1297033)). Prevalent single-number reporting misleads; report CIs from replicated runs — the harness already does this per-cell; the paper is the standard citation for why.
- **Mytkowicz, Diwan, Hauswirth & Sweeney, "Producing Wrong Data Without Doing Anything Obviously Wrong!," ASPLOS 2009** ([ACM DL](https://dl.acm.org/doi/10.1145/1508244.1508275), [PDF](https://users.cs.northwestern.edu/~robby/courses/322-2013-spring/mytkowicz-wrong-data.pdf)). Link order and even UNIX environment size change measured speedups enough to flip conclusions; remedy = **setup randomization** — DOE's randomization/blocking applied to code layout. Relevance: `target` is confounded with binary layout by construction; treat layout as an acknowledged aliased nuisance factor, and treat *measurement session* as a block (don't compare June's cached cells to today's cells and attribute the difference to the commit).
- **Run ordering / nuisance control**: classical DOE controls two nuisance dimensions at once with Latin / **Graeco-Latin squares** ([Wikipedia](https://en.wikipedia.org/wiki/Graeco-Latin_square); NIST [5.3.3.2](https://www.itl.nist.gov/div898/handbook/pri/section3/pri332.htm) for randomized blocks). For a single-machine harness the cheap version suffices: randomize or round-robin cell order within a session (ABBA/interleaved, not AABB) so thermal drift, background load, and cache warmth land equally on all cells; a Latin-square schedule becomes worth it only if runs spread across machines x times of day.

---

## 7. Is there a "Vega-Lite for comparisons"? The closest existing languages

There is no widely adopted standalone spec language for "comparison matrices over benchmark grids." What exists, in decreasing order of directness:

1. **R model-formula + emmeans**: the de facto contrast-specification language. Formula `log(wall) ~ target * treatment + workload` declares the design (main effects + interaction, workload as additive block); then the [emmeans package's comparisons vignette](https://cran.r-project.org/web/packages/emmeans/vignettes/comparisons.html) shows the comparison vocabulary: `contrast(emm, "pairwise")`, `"trt.vs.ctrl"` (everything vs `off`), `"consec"`, custom coefficient vectors, `by =` for simple effects within a level, `contrast(emm, interaction = "pairwise")` for interaction contrasts (the ratio-of-ratios), `adjust = "tukey"/"mvt"` for multiplicity, and — decisive for this use case — `type = "response"` back-transforms log-model estimates so **everything prints as ratios with CIs automatically**. This is a complete, battle-tested semantics for "what to compare"; the harness could either emit data for it or copy its nouns (`pairwise`, `trt.vs.ctrl`, `by`, `interaction`).
2. **Statistical notation itself**: the design matrix / sign table (Jain Ch. 17) is a full formal language: any report line = a coefficient vector over cells. A harness config could literally accept named coefficient vectors as the extension escape hatch.
3. **Vega-Lite analogy**: Vega-Lite's insight was a small algebra (mark + encoding + faceting) covering most charts. The DOE analogue is: **grid** (factors x levels) + **block** (facet) + **measure** + **contrast set** (pairwise / vs-control / interaction) + **scale** (log→ratios). That 5-part tuple is arguably the whole language; §8 sketches it.

---

## 8. Implications for this harness

**A. Adopt the vocabulary (it costs one glossary comment and pays forever).**

- `measure` — response variable: wall, max_rss, phase:search, … (one analysis per measure).
- `factor` — `target`, `backend`, `treatment`. Reserve DOE's bare "treatment" by renaming the current treatment axis internally to a factor like any other; the current "endpoint" = a **cell** = one treatment combination.
- `block` — a workload file; second implicit block = measurement session/machine. Never a factor to average over silently.
- `grid` — the requested factorial: `targets={old,new} x treatments={off,proofs}` (backend fixed = a **held-constant factor**; record it, per Yi/Lilja's warning that held-constant choices condition all conclusions).
- `contrast` — any zero-sum coefficient vector over cells; named families below.
- `interaction` — the contrast family answering "did effect X change with Y."

**B. Analyze on the log scale; make ratios the display format, logs the math.** Define effects as differences of mean log-time. Then: per-cell summary = geometric mean; every reported ratio = `exp(contrast)`; CIs = plain t on contrasts (Fieller machinery retires, or survives only for raw-scale arithmetic-mean ratios if you want both); cross-workload aggregation = mean of log-ratios = geometric mean (Fleming & Wallace-safe); and the whole grid is one ordinary linear model `log t = μ + block + Σ factors + Σ interactions + ε` (Jain Ex. 18.8 is the canonical justification). Phase times: raw scale or shares, not logs.

**C. For the 2x2, the meaningful contrasts are exactly these five lines (per block, plus geometric-mean across blocks):**

1. `target @ off` — new-off/old-off (simple effect: did the base engine regress),
2. `target @ proofs` — new-proofs/old-proofs,
3. `treatment @ old` — old-proofs/old-off (overhead before),
4. `treatment @ new` — new-proofs/new-off (overhead after),
5. `interaction` — (4)÷(3) ≡ (2)÷(1), coefficients (+1,−1,−1,+1) on log cell means — **"did the proofs overhead itself change."**

Print (5) with a CI, then (1)–(4); suppress or demote main effects when (5)'s CI excludes 1, per standard factorial reporting discipline. Refuse diagonal ratios (`new-proofs/old-off`) by default — they are confounded contrasts (§2). For `k` treatments: `trt.vs.ctrl` against `off` gives `k−1` overhead lines and `k−1` interaction lines; that's the whole meaningful set, not `O(k²)` pairwise ratios.

**D. Add an allocation-of-variation header.** One line per measure: % of log-variance explained by block, each factor, interactions, residual (`SS_effect = 2^k r q²` per Jain Ch. 17/18). It is the single cheapest guard against "13 impressive-looking ratios that are all noise," and against burying "workload explains 90%" (which would mean: report per-block, don't aggregate).

**E. Design/caching hygiene the DOE lens makes visible.**

- *Epoch confounding*: cells resolved from an old cache put `target` in perfect alias with `measurement date`. Either (a) always re-measure the baseline cells in the same session as candidate cells (blocking on session), or (b) record session id per observation and flag cross-session contrasts in output. This is the harness's parallel-trends assumption.
- *Unbalanced cells*: unequal replicate counts across cells (natural with append-only caching) destroy contrast orthogonality — effect estimates become correlated and "% variation" stops summing cleanly. Per-cell means keep point estimates honest; just compute contrast variances from per-cell `s²/nᵢⱼ` rather than a pooled formula that assumes balance.
- *Run ordering*: within a session, interleave cells (randomized or round-robin), never AABB (Mytkowicz; NIST randomization).
- *Replication levels*: binary-build vs process-run are different levels (Kalibera & Jones); the binary-sha cache key currently pins build replication at 1 — acceptable, but say so, since link-order effects then alias with `target` (Mytkowicz).
- *Growth path*: when the grid becomes 2x2x5 (+ machine, + egg-equivalence measures), don't run it full — screen (Plackett–Burman/foldover, Yi/Lilja/Hawkins) or pick an explicit fraction and print its aliasing, rather than ad-hoc hole-punching in the grid.

**F. A minimal spec language (the Vega-Lite-shaped answer).** A comparison request is a 5-tuple; a CLI sketch:

```
bench compare \
  --grid target=old,new treatment=off,proofs \        # factors x levels (cells)
  --fix backend=main \                                # held-constant factors, recorded
  --blocks suites/*.egg \                             # facet, never averaged silently
  --measure wall \                                    # response (repeatable)
  --contrasts vs-control:treatment=off,interaction \  # named families; custom: coeff vectors
  --scale log                                         # ratios + geomean aggregation
```

Output = per-block table of cells (geomean ± CI) + effects panel (the §C five lines) + allocation-of-variation header. That's the entire language; `pairwise`, `vs-control`, `consec`, `interaction`, and raw coefficient vectors (emmeans' nouns) cover every request the user listed and every one DOE considers meaningful.

**G. What *not* to build.** A general contrast algebra with arbitrary nesting is emmeans re-implemented in Python — a large, well-solved problem. The 80/20: keep the harness responsible for *design* (balanced cells, session blocking, ordering, cache keys as cell ids) and a fixed contrast vocabulary; additionally emit a tidy long-format table (one row per observation: block, session, all factor columns, all measures) so any escape-hatch analysis is a 5-line `statsmodels`/R script. DOE's real gift here is not new statistics — the harness's t-CIs are fine — it's the **naming discipline** (cell/block/contrast/interaction/alias) that makes "which of the 24 possible ratios do we print" a solved question instead of a UI debate.

---

## Source list

- NIST/SEMATECH e-Handbook of Statistical Methods (Handbook 151), esp. §5 Process Improvement: [handbook home](https://www.itl.nist.gov/div898/handbook/), [5.7 glossary](https://www.itl.nist.gov/div898/handbook/pri/section7/pri7.htm), [5.3.3.2 randomized block designs](https://www.itl.nist.gov/div898/handbook/pri/section3/pri332.htm), [5.3.3.3 full factorial](https://www.itl.nist.gov/div898/handbook/pri/section3/pri333.htm), [5.3.3.3.2 2^3 example](https://www.itl.nist.gov/div898/handbook/pri/section3/pri3332.htm), [5.3.3.4 fractional factorial](https://www.itl.nist.gov/div898/handbook/pri/section3/pri334.htm); [NIST publication record](https://www.nist.gov/publications/handbook-151-nistsematech-e-handbook-statistical-methods).
- Raj Jain, *The Art of Computer Systems Performance Analysis*, Wiley 1991 ([Wiley](https://www.wiley.com/en-us/The+Art+of+Computer+Systems+Performance+Analysis:+Techniques+for+Experimental+Design,+Measurement,+Simulation,+and+Modeling-p-9780471503361)); author slides: [Ch. 11 Ratio Games](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_11rg.pdf), [Ch. 16 Intro to Experimental Design](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_16ied.pdf), [Ch. 17 2^k Factorial](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_172kd.pdf), [Ch. 18 2^k r Factorial w/ Replications (incl. multiplicative models)](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_182kr.pdf), [Ch. 19 2^(k−p) Fractional](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_19ffd.pdf), [Ch. 20 One-Factor](https://www.cse.wustl.edu/~jain/cse567-08/ftp/k_20ofe.pdf).
- Joshua J. Yi, David J. Lilja, Douglas M. Hawkins, "A Statistically Rigorous Approach for Improving Simulation Methodology," HPCA-9, 2003 — [PDF](https://www.cs.ucr.edu/~gupta/hpca9/HPCA-PDFs/26-yi.pdf).
- Tomas Kalibera, Richard Jones, "Rigorous Benchmarking in Reasonable Time," ISMM 2013 — [Kent](https://kar.kent.ac.uk/33611/), [ACM](https://dl.acm.org/doi/10.1145/2464157.2464160).
- Andy Georges, Dries Buytaert, Lieven Eeckhout, "Statistically Rigorous Java Performance Evaluation," OOPSLA 2007 — [PDF](https://dri.es/files/oopsla07-georges.pdf), [ACM](https://dl.acm.org/doi/10.1145/1297027.1297033).
- Todd Mytkowicz, Amer Diwan, Matthias Hauswirth, Peter F. Sweeney, "Producing Wrong Data Without Doing Anything Obviously Wrong!," ASPLOS 2009 — [ACM](https://dl.acm.org/doi/10.1145/1508244.1508275), [PDF](https://users.cs.northwestern.edu/~robby/courses/322-2013-spring/mytkowicz-wrong-data.pdf).
- Philip J. Fleming, John J. Wallace, "How not to lie with statistics: the correct way to summarize benchmark results," CACM 29(3), 1986 — [ACM](https://dl.acm.org/doi/10.1145/5666.5673).
- Wikipedia: [Contrast (statistics)](https://en.wikipedia.org/wiki/Contrast_(statistics)), [Difference in differences](https://en.wikipedia.org/wiki/Difference_in_differences), [Fractional factorial design](https://en.wikipedia.org/wiki/Fractional_factorial_design), [Graeco-Latin square](https://en.wikipedia.org/wiki/Graeco-Latin_square), [Fieller's theorem](https://en.wikipedia.org/wiki/Fieller%27s_theorem).
- emmeans R package, "Comparisons and contrasts" vignette — [CRAN](https://cran.r-project.org/web/packages/emmeans/vignettes/comparisons.html).
