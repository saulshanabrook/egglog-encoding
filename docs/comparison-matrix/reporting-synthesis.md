# From Pairwise Benchmarks to Explainable Comparison Reports

**Status:** research synthesis and design exploration<br>
**Date:** 2026-08-12<br>
**Project snapshot:** `origin/main` at `bd4752e`; paper-comparison PR #54 at `9fc1846`<br>
**Implementation permission:** none; this report proposes directions and open decisions

## Audience and purpose

This report is for maintainers deciding how `egglog-encoding` should summarize
and display benchmark data when one baseline/candidate pair is no longer enough.
It synthesizes the existing comparison-matrix reports, checks their claims
against the current repository and primary literature, and turns that evidence
into concrete reporting ideas.

The intended reader outcome is to be able to answer four questions:

1. What comparisons does the current cache already support?
2. Which comparisons answer distinct questions, rather than merely producing
   more ratios?
3. What summary statistics are honest for each metric and workload set?
4. What should a useful terminal or HTML report actually look like?

This is not an implementation specification. It does not select a final
estimand, practical-equivalence threshold, CLI syntax, or multiplicity policy.
It also does not propose reviving DuckDB, emitting every pairwise comparison,
or reducing all benchmark evidence to one score.

## Executive summary

The repository does not primarily have a collection problem. It has a
**question-definition and presentation problem**.

The append-only JSONL already stores independent observations of cells in a
factor space: binary, backend, treatment, workload, facts, timeout, and metric.
The collector can plan multiple endpoints and reuse each exact cell
independently. The pair restriction enters above that layer: the public CLI,
`ComparisonSpec`, analysis views, presentation language, and interactive scope
all assume one baseline and one candidate. The interactive report nevertheless
discovers every endpoint in the cache, which demonstrates that the cache is
already a small data cube.

The right response is not to print a complete matrix of ratios. A report should
start from a **named question** and derive only the comparisons that answer it:

- a **simple effect** changes one coordinate, such as `new/off ÷ old/off`;
- a **scenario effect** deliberately changes several coordinates, such as
  `new/proofs ÷ old/off`;
- an **interaction** asks whether one effect changed with another, such as
  `(new/proofs ÷ new/off) ÷ (old/proofs ÷ old/off)`;
- a **versus-control family** compares many treatments with one declared
  control, without expanding to all pairs.

The diagonal old/off-to-new/proofs comparison is therefore valid. It measures
the total migration effect. It is not suitable for attributing that effect to
the new target or to proofs. That distinction should be expressed in the
question label and report provenance, not by refusing the comparison.

The report should use progressive disclosure:

1. validity and provenance;
2. one decision-oriented headline;
3. the observed cell grid;
4. a short list of named effects with estimates and intervals;
5. a per-workload confidence-interval view;
6. phase, ruleset, and raw-observation drill-down.

The most important statistical decision is still open. Today's report estimates
ratios of **arithmetic means** and uses Fieller intervals. A mean-log model would
make interactions easy, but it estimates ratios of **geometric means** instead.
The implementation must not silently change that target. A conservative first
path is to keep today's leaf ratios and use a cell-level bootstrap for compound
contrasts. A log-contrast mode is attractive, but should be adopted only after
its different interpretation is explicitly accepted.

Finally, exact cache reuse and experimental comparability are different.
Content hashes safely decide whether an observation belongs to a cell. They do
not show that a cached July run and a fresh August run experienced the same
machine state. Session and machine provenance should be added as evidence
metadata, while the existing content-addressed cache identity remains intact.

## 1. The project problem, grounded in current code

### 1.1 The data layer is cell-oriented

One persisted row is one observation. On current `origin/main`, a row records
target provenance, binary and workload hashes, backend, treatment, timeout,
status, wall time, peak RSS, and timing details. The exact reusable key is:

```text
(binary_sha256,
 file_sha256,
 treatment,
 timeout_sec,
 backend,
 fact_directory_sha256)
```

There is no baseline or candidate in that identity. See the stable snapshot of
[`ReportRecord` and `CacheKey`](https://github.com/saulshanabrook/egglog-encoding/blob/bd4752e9777ec46632acd303bdfe787f9562ccf4/benchmarking/reports/store.py#L51-L106).

The collection planner accepts a tuple of endpoints, constructs every
endpoint-by-file request, and selects cached observations for each exact key.
Missing counts are computed independently per request. See
[`build_collection_plan`](https://github.com/saulshanabrook/egglog-encoding/blob/bd4752e9777ec46632acd303bdfe787f9562ccf4/benchmarking/collection.py#L107-L149).
The tests explicitly establish independent endpoint reuse and force-run
behavior in
[`test_pair_collection_reuses_each_endpoint_independently_and_force_runs_both`](https://github.com/saulshanabrook/egglog-encoding/blob/bd4752e9777ec46632acd303bdfe787f9562ccf4/tests/test_collection.py#L304-L323).

This means a report can combine exact cached cells from several earlier pair
runs without changing the observation schema or collecting them again.

### 1.2 The reporting surface is pair-shaped

The pair enters at `ComparisonSpec`, which owns exactly `baseline` and
`candidate`, and at analysis, which numbers endpoints `0` and `1`. See
[`ComparisonSpec`](https://github.com/saulshanabrook/egglog-encoding/blob/bd4752e9777ec46632acd303bdfe787f9562ccf4/benchmarking/models.py#L152-L171)
and
[`_selected_observations`](https://github.com/saulshanabrook/egglog-encoding/blob/bd4752e9777ec46632acd303bdfe787f9562ccf4/benchmarking/reports/analysis.py#L201-L210).
The public CLI and presentation layer repeat the same two roles, and the
interactive form offers two endpoint selectors plus Swap.

At the same time, the interactive runtime enumerates every distinct endpoint,
file, timeout, and available row count in the loaded JSONL. See
[`_cache_universe`](https://github.com/saulshanabrook/egglog-encoding/blob/bd4752e9777ec46632acd303bdfe787f9562ccf4/benchmarking/reports/interactive_runtime.py#L306-L355).
It is already an any-pair browser over a many-cell cache.

The nightly runner exposes the same split. It populates several treatment
endpoints into one cache, but invokes the pair CLI once per endpoint against
`main/off`. See
[`ENDPOINTS`, `BASELINE`, and `_run`](https://github.com/saulshanabrook/egglog-encoding/blob/bd4752e9777ec46632acd303bdfe787f9562ccf4/scripts/nightly_bench.py#L57-L115).

The conclusion is precise: **collection and storage are already plural;
analysis, question selection, and presentation are singular.**

### 1.3 The factor space is ragged, not a Cartesian product

The relevant coordinates are becoming:

```text
target × backend × treatment × workload × metric × measurement session
```

Engine is currently best treated as a property of a treatment, not as an
independently selectable axis. PR #54's exact snapshot defines nine treatments
across egglog and egg, but permits egg treatments only on the fixed Math
fixture. See its
[`TREATMENT_SPECS` and workload validation](https://github.com/saulshanabrook/egglog-encoding/blob/9fc18467162b2d6f96b092441a3872af4aff1da8/benchmarking/engines.py#L9-L67).
The `dd` backend permits only `term` and `proofs`, while `main` permits all nine
treatments in that branch. See
[`BACKEND_SPECS`](https://github.com/saulshanabrook/egglog-encoding/blob/9fc18467162b2d6f96b092441a3872af4aff1da8/benchmarking/models.py#L22-L45).

A report must therefore distinguish at least four states:

| Cell state | Meaning | Example |
| --- | --- | --- |
| observed | enough exact rows exist | `main/proofs` on a supported fixture |
| missing | legal, but rows are absent or too few | current binary has only 2 of 6 rounds |
| failed | a run was attempted and failed or timed out | benchmark process exited nonzero |
| illegal | the endpoint/workload combination has no defined execution | `dd` with an egg treatment |

Generating axes only from observed rows would hide the difference between
missing and illegal. Generating a blind Cartesian product would fill the report
with meaningless holes. The layout needs the requested factor grid plus a
legality predicate.

### 1.4 Content identity is not measurement-session identity

The cache key is deliberately strict about executable, input, treatment,
backend, facts, and timeout. This yields two useful properties:

- two target labels or Git commits that produce a byte-identical executable
  and identical workload automatically share observations;
- a source-level belief that “the off path did not change” cannot reuse rows if
  the binary hash differs.

That fail-closed behavior is correct. But a matching cache key says nothing
about thermal state, background load, kernel, toolchain environment, or the time
between observations. Current rows record `started_at`, but not a run-group ID,
machine fingerprint, or environment snapshot.

This is the project-specific form of a long-standing benchmarking problem.
Mytkowicz et al. demonstrated that environmental and layout factors can bias
results without an obviously incorrect benchmark, and advocate detection and
randomization rather than assuming the setup is neutral
([ASPLOS 2009](https://sape.inf.usi.ch/publications/asplos09.html)). Go's
benchstat likewise recommends interleaving before and after runs so noise is
distributed across the comparison, and warns against rerunning until a result
becomes significant
([official documentation](https://pkg.go.dev/golang.org/x/perf/cmd/benchstat)).

The cache should continue to answer “is this the same executable workload
cell?” A separate evidence grade should answer “how directly comparable were
the observations?”

### 1.5 History says to avoid implicit output, not matrices

The project already had a multi-target, multi-backend, multi-treatment runner.
Before the pair simplification, selecting several endpoints implicitly produced
cross-target, within-target-overhead, and cross-backend tables. During PR #21,
one experimental implementation also built a DuckDB reporting catalog and live
scope editor. The final pair design removed both the implementation tax of the
SQL/Python mirror and the uncontrolled fan-out of tables.

The corrected history is in
[`research/git-archaeology.md`](research/git-archaeology.md). The important
lesson is not “multiple cells are too complex.” It is:

> Cell selection, scientific comparison, and table layout must be separate
> choices. Do not let selecting data implicitly volunteer every possible
> comparison.

## 2. Three bodies of literature fit together

No surveyed benchmark CLI supplies the complete answer, but three mature bodies
of work align unusually well with this repository.

### 2.1 Experimental design names the questions

Design of experiments calls target, backend, and treatment **factors**; their
values are **levels**; an endpoint/workload combination is a **cell**; repeated
observations are **replicates**; and a known nuisance dimension such as workload
or session can be treated as a **block**. NIST defines a full factorial as
observing every combination of factor levels and notes that the corresponding
model contains main effects and interactions
([full-factorial design](https://www.itl.nist.gov/div898/handbook/pri/section3/pri333.htm),
[DOE models](https://www.itl.nist.gov/div898/handbook/pri/section4/pri43.htm)).

For `{old,new} × {off,proofs}`, let `m(target,treatment)` denote a cell
location on an accepted analysis scale. The useful effects are:

```text
base target change
    = m(new, off)    - m(old, off)

proof-mode target change
    = m(new, proofs) - m(old, proofs)

old proof overhead
    = m(old, proofs) - m(old, off)

new proof overhead
    = m(new, proofs) - m(new, off)

interaction: change in proof overhead
    = [m(new, proofs) - m(new, off)]
    - [m(old, proofs) - m(old, off)]
```

If `m` is a mean log time, exponentiating these differences gives ratios and
the interaction becomes a ratio of ratios. If `m` is the log of an arithmetic
mean, the same point-estimate algebra holds, but its uncertainty must be derived
for that estimand.

Altman and Bland describe an interaction as the difference between two effect
estimates and show how to combine the standard errors of independent estimates,
including on a log scale for ratio measures
([BMJ 2003](https://www.bmj.com/content/326/7382/219)). The `emmeans` package
implements the wider vocabulary directly: simple contrasts within factor
levels, combined contrast families, and **interaction contrasts as contrasts of
contrasts**
([official interaction vignette](https://rvlenth.github.io/emmeans/articles/interactions.html)).

This vocabulary also corrects an overstatement in the earlier DOE report.
`new/proofs ÷ old/off` is not meaningless and need not be refused. Under that
report's own contrast coding, its log coefficients equal the target main-effect
contrast plus the treatment main-effect contrast; there is no interaction
coefficient. It answers a compound migration question, while failing to
attribute the answer to either changed factor.

### 2.2 Benchmarking literature says to expose the estimand and uncertainty

Kalibera and Jones model multiple levels of performance variation and derive
confidence intervals for ratios of mean execution times. Their central lesson
is that an effect estimate without its uncertainty is not enough, and that the
experimental hierarchy determines where repetition matters
([effect-size confidence intervals](https://arxiv.org/abs/2007.10899)).

This creates a productive tension with the desire for one composable contrast
engine:

- **Current semantics:** each cell uses an arithmetic mean; a pair reports the
  ratio of arithmetic means with a Fieller interval. The code is visible in
  [`_ratio_estimate`](https://github.com/saulshanabrook/egglog-encoding/blob/bd4752e9777ec46632acd303bdfe787f9562ccf4/benchmarking/reports/analysis.py#L262-L294).
- **Log-sample semantics:** each cell uses `mean(log observation)`; differences
  compose naturally and exponentiate to ratios of geometric means.
- **Bootstrap semantics:** resample observations within each cell, recompute the
  chosen statistic—including a ratio of arithmetic means or ratio of
  ratios—and use the replicate distribution for uncertainty.

The second option is algebraically elegant but changes the question. Fleming
and Wallace showed why the geometric mean is stable for normalized benchmark
ratios
([CACM 1986](https://doi.org/10.1145/5666.5673)). Mashey's later synthesis is
the more useful policy guide: arithmetic, harmonic, and geometric means answer
different population questions; the correct choice depends on the workload and
distribution model
([SIGARCH 2004](https://ece.uprm.edu/~nayda/Courses/Icom6115F06/Papers/paper3.pdf)).

Therefore the report should name both the estimate and its interpretation. It
should never relabel a ratio of geometric means as if it were today's ratio of
arithmetic means.

### 2.3 Visualization literature separates data, relationships, and layout

Gleicher et al. classify comparison visualizations as **juxtaposition**,
**superposition**, and **explicit encoding**
([Visual Comparison for Information Visualization](https://graphics.cs.wisc.edu/Papers/2011/GAWJHR11/)).
A four-cell table juxtaposes values; an interaction line plot superposes trends;
a ratio or ratio-of-ratios column explicitly encodes a relationship. A useful
benchmark report needs all three, but at different levels of detail.

Polaris extends pivot tables into a formal way to map multidimensional data to
rows, columns, and nested displays
([Stolte, Tang, and Hanrahan 2002](https://research.google/pubs/polaris-a-system-for-query-analysis-and-visualization-of-multidimensional-relational-databases/)).
Vega-Lite shows how a small composition algebra can build layered and
multi-view interactive displays without hard-coding every chart combination
([Satyanarayan et al. 2017](https://vis.mit.edu/pubs/vega-lite/)).

Go benchstat is the closest terminal precedent. It projects self-describing
records through `-table`, `-row`, and `-col`; treats the first projected column
as the baseline; prints an estimate, uncertainty, versus-base comparison, and
geomean row; and warns when hidden configuration still varies
([official projection documentation](https://pkg.go.dev/golang.org/x/perf/cmd/benchstat)).
It solves layout and one-baseline comparison, but not interactions.

For many workload-level estimates, a forest-plot idiom is a good fit: one row
per workload, a point estimate and confidence interval, a vertical no-effect
line, and adjacent text columns. The plot should use a log axis for ratios and
plain-language direction labels
([CDC forest-plot guidance](https://www.cdc.gov/wcms/4.0/cdc-wp/data-presentation/forest-plot.html)).

These sources suggest a clean factoring:

```text
cell selection        filter a typed coordinate space
question              choose named effects or scenarios
estimation            compute each effect on an explicit scale
layout                project effects to tables, rows, columns, and facets
interaction           link overview and drill-down without collecting data
```

## 3. A question taxonomy for benchmark reports

The report should require a named question family before it computes
relationships. The following set covers the current use cases without becoming
a general statistics language.

| Question family | Example | What it answers | Minimum cells | Default display |
| --- | --- | --- | ---: | --- |
| cell estimate | `new/proofs` | how this endpoint behaved | 1 | estimate, interval, `n`, status |
| simple effect | `new/proofs ÷ new/off` | proof overhead on the new target | 2 | one effect row plus workload drill-down |
| scenario effect | `new/proofs ÷ old/off` | total change in a declared migration | 2 | headline card marked `joint` |
| interaction | `(new proofs/off) ÷ (old proofs/off)` | whether proof overhead changed | 4 | interaction first, then its four simple effects |
| versus control | every treatment ÷ `off` | overhead of several treatments | `k+1` | narrow treatment table, not all pairs |
| configuration ranking | several complete endpoints over a workload population | which configurations tend to rank best | `k × N` | rank view or critical-difference plot |

The final row deserves caution. Demšar's Friedman/post-hoc and
critical-difference framework is a useful precedent for comparing several
methods across several data sets
([JMLR 2006](https://jmlr.org/papers/v7/demsar06a.html)). It is appropriate only
when workloads are being treated as a sample of a broader workload population.
The six fixed repository fixtures are not automatically statistical replicates
of one another.

### 3.1 Scenarios and causal attribution must remain separate

The existing pair report already handles this distinction well. If more than
one of target, backend, and treatment changes, it warns that the ratio describes
the joint endpoint change and does not isolate one cause. See the current
[`joint-comparison` warning](https://github.com/saulshanabrook/egglog-encoding/blob/bd4752e9777ec46632acd303bdfe787f9562ccf4/benchmarking/reports/presentation.py#L137-L150).

A many-cell report should preserve and strengthen that behavior:

- allow a scenario comparison when the user names it;
- label every coordinate that changed;
- do not present it under a single-factor heading;
- offer the missing simple effects or interaction as follow-up questions.

### 3.2 Semantic comparability comes before statistical comparison

Hash equality shows that bytes match. It does not show that two engines or
treatments computed comparable work. Cross-engine comparisons in PR #54 are
meaningful only on the deliberately shared Math fixture and correctness gate.
At the current PR snapshot, both implementations require 11 iterations and
establish the same terminal equality. The egg runner checks its terminal
equivalence directly, while the egglog test establishes failure at 10 and
success at 11. See
[`egg-math-benchmark`](https://github.com/saulshanabrook/egglog-encoding/blob/9fc18467162b2d6f96b092441a3872af4aff1da8/egg-math-benchmark/src/main.rs#L16-L117)
and
[`terminal_math_equality_requires_iteration_eleven`](https://github.com/saulshanabrook/egglog-encoding/blob/9fc18467162b2d6f96b092441a3872af4aff1da8/egglog-experimental/tests/paper_benchmark_proofs.rs#L35-L53).

This corrects the stale implementation details in
[`research/compat-chat.md`](research/compat-chat.md): the current gate is at 11,
not 10, and the earlier claimed 13-table parity oracle is no longer present.
The report's higher-level finding remains sound: endpoint legality and semantic
comparability need explicit representation.

The shared correctness gate does not make every phase metric comparable. The
egg runner currently reports `merge_ns = 0` and folds proof extraction/checking
into `unattributed_ns`; see its
[`TimingSummaryV2` mapping](https://github.com/saulshanabrook/egglog-encoding/blob/9fc18467162b2d6f96b092441a3872af4aff1da8/egg-math-benchmark/src/main.rs#L91-L117).
Cross-engine wall time can therefore be a meaningful question while
cross-engine merge or unattributed time is not yet a like-for-like contrast.

## 4. Proposed summarization policy

This section is a design proposal derived from the evidence above. It is not a
description of current behavior.

### 4.1 Start every report with validity and provenance

Before any speedup, show:

- the selected endpoint coordinates and binary hashes;
- workload and fact-directory hashes;
- treatment/backend legality;
- semantic-comparability status and the oracle supporting it, when applicable;
- requested and observed rounds, including failures and timeouts;
- observation time range and run/session grouping;
- cached versus fresh provenance;
- whether the comparison changes one coordinate or several.

This information should be compact, but never hidden behind `--detail`. A ratio
whose cells are illegal, semantically incomparable, incomplete, or from an
unqualified cross-session mix should not receive a normal performance verdict.

### 4.2 Choose an estimand per metric family

One statistical mechanism should not be forced onto metrics with different
domains.

| Metric family | Primary summary | Companion information | Avoid |
| --- | --- | --- | --- |
| wall time | declared ratio estimand with interval | absolute seconds delta | an unlabeled switch between arithmetic and geometric means |
| peak RSS | ratio or percent change with interval | absolute bytes delta | treating one noisy maximum as exact |
| phase time | absolute delta and share of wall time | ratio only when denominator is safely positive | ratios with zero or near-zero denominators |
| ruleset time | top absolute contributors to total delta | per-ruleset raw values on demand | hundreds of unstructured p-values |
| correctness/equivalence data | pass/fail gate, counts, or structured difference | oracle and provenance | averaging logical validity into a performance score |
| failures/timeouts | counts and identities | censored/failed-cell annotation | silently dropping them from means |

For wall time and RSS, two coherent policies remain:

1. **Continuity policy:** keep arithmetic cell means and Fieller intervals for
   simple pairs. Use a within-cell bootstrap for scenario and interaction
   statistics, recomputing the ratio of arithmetic means in every replicate.
   If observations are deliberately paired or blocked by run group, resample
   whole blocks instead of treating the cells as independent.
2. **Composable-log policy:** define the estimand as a ratio of geometric means
   from mean log observations. Use linear contrasts and exponentiated intervals
   for simple effects and interactions.

The first preserves current meaning and is the safer incremental step. The
second gives a simpler general algebra. A measured comparison of both policies
on the actual cache should precede a project-wide choice.

Bootstrap intervals are not automatically reliable at the six-round sample
sizes common in the current cache. Before using them for verdicts, calibrate
coverage and failure behavior with simulations shaped by observed variance and
outliers. Call the method hierarchical only after the report records and uses
real nested measurement levels.

### 4.3 Keep workload summaries plural

There is no universally correct “overall benchmark result.” At least three
summaries answer different questions:

| Aggregate | Interpretation |
| --- | --- |
| per-workload effects | which fixtures improve or regress, without assuming commensurability |
| geometric mean of workload ratios | typical multiplicative change when each workload receives equal weight |
| ratio of summed mean times | change in total time for this exact, equally repeated suite |

If real usage weights exist, a fourth summary—a declared weighted workload
mix—is more meaningful than either unweighted aggregate.

Confidence across workloads requires the same clarity. A t interval over
workload effects treats the workloads as a sample from a population. If the
repository fixtures are the complete fixed suite of interest, the report should
instead propagate measurement uncertainty within each workload into the chosen
fixed-suite aggregate. It should not pretend that six unrelated programs are
six repeated measurements of one program.

### 4.4 Use effect size, uncertainty, and a practical threshold

Binary “significant/not significant” labels encourage readers to confuse
absence of evidence with evidence of no meaningful change. Each headline
effect should instead include:

- point estimate;
- interval;
- absolute delta where meaningful;
- sample count per cell;
- a predeclared practical threshold or band;
- a state derived from those quantities.

Suggested states are:

| State | Meaning |
| --- | --- |
| meaningful improvement | interval lies beyond the practical band in the favorable direction |
| meaningful regression | interval lies beyond the band in the unfavorable direction |
| equivalent | a predeclared equivalence procedure supports effects within the band |
| inconclusive | evidence does not establish difference or equivalence |
| invalid/incomplete | cell legality, comparability, or observation requirements failed |

“Equivalent” should not mean merely that a 95% difference interval includes
the null. Equivalence testing reverses the hypotheses and requires bounds set in
advance; the two one-sided tests procedure is a standard implementation
([Lakens 2017](https://pmc.ncbi.nlm.nih.gov/articles/PMC5502906/)). The project
must choose thresholds based on decision cost and metric, rather than adopting
an unexplained global `±2%` or `5 ms` rule.

### 4.5 Treat multiplicity as part of the question family

A single planned migration effect does not need the same policy as an
exploratory scan of hundreds of workload, phase, and ruleset rows.

- Headline question families should be declared before looking at the output.
- A small planned family can use simultaneous or family-wise intervals if a
  formal decision requires them.
- A large exploratory screen can use false-discovery-rate control, or avoid
  inferential verdicts and present effect estimates for drill-down.
- The displayed family and adjustment method must appear in the report header.

Benjamini and Hochberg introduced FDR as the expected proportion of false
discoveries among rejected hypotheses, trading stricter family-wise control for
power in many-test settings
([JRSS B 1995](https://www.math.tau.ac.il/~ybenja/MyPapers/benjamini_hochberg1995.pdf)).
It is one available policy, not an automatic default. Defining the family after
seeing the data would defeat much of its purpose.

### 4.6 Add evidence grades for cached comparisons

Keep the current content-addressed key, and add non-key provenance fields such
as `run_group_id`, machine identity, toolchain identity, and a compact machine
state snapshot. Then classify comparison evidence:

| Grade | Evidence |
| --- | --- |
| same-session | all required cells were interleaved in one declared run group |
| reproduced-cache | historical cells were reused and a fresh reference-side canary reproduced within its accepted tolerance |
| cross-session | exact cells exist, but no fresh reproduction connects their measurement epochs |
| mixed/unknown | session or environment provenance is missing |

These grades should affect language, not data selection. A cross-session result
can be useful exploratory evidence; it should not silently become a
same-session regression verdict.

## 5. Proposed display architecture

### 5.1 One report, six layers

The same conceptual report can render in Rich, Markdown, or HTML:

1. **Scope strip** — named question, selected factors, metric, rounds, evidence
   grade, and warnings.
2. **Decision card** — one requested headline effect in plain language.
3. **Cell grid** — observed cell estimates and coverage, including explicit
   missing/failed/illegal states.
4. **Effects panel** — only the named simple, scenario, versus-control, and
   interaction contrasts relevant to the question.
5. **Workload forest table** — per-workload estimates and intervals on a shared
   axis.
6. **Details** — phase decomposition, ruleset contributors, raw observations,
   and complete provenance.

This structure follows the visualization literature: juxtapose the cells,
explicitly encode the relationships, and reserve superposed or linked views for
drill-down.

### 5.2 A concrete 2×2 terminal sketch

The following numbers are illustrative. The point is the information hierarchy,
not the estimates.

```text
Question   Did proof overhead change from old to new?
Scope      target={old,new} treatment={off,proofs} backend=main metric=wall
Evidence   4 cells · 6 rounds/cell · same-session · all workloads comparable

Cell means (95% CI)
                         off                     proofs
  old              1.000 s [0.98,1.02]     1.800 s [1.75,1.85]
  new              1.050 s [1.02,1.08]     2.100 s [2.04,2.16]

Named effects                              ratio [95% CI]      absolute       state
  interaction · proof overhead new÷old      1.11 [1.05,1.18]   +250 ms ΔΔ     regression
  proofs/off @ new                          2.00 [1.93,2.08]  +1050 ms        regression
  proofs/off @ old                          1.80 [1.73,1.87]   +800 ms        regression
  new/old @ proofs                          1.17 [1.11,1.22]   +300 ms        regression
  new/old @ off                             1.05 [0.99,1.11]    +50 ms        inconclusive

Typical workload interaction               1.08 [1.02,1.15]
Ratio-of-summed-times interaction           1.10 [1.04,1.17]
```

The interaction appears first because it is the named question, not because
interactions must always headline every matrix. The four simple effects make
the interaction auditable. The cell grid prevents a derived number from
floating free of the observations that produced it.

### 5.3 Show scenario effects as first-class but explicitly joint

For an old-main/off to new/proofs migration, the top can instead be:

```text
Question   What is the total cost of moving from old/off to new/proofs?
Effect     new/proofs ÷ old/off = 2.10× [2.02,2.18] · +1.10 s
Changes    target: old → new · treatment: off → proofs
Meaning    joint migration effect; does not isolate proof overhead
Follow-up  proofs/off @ new requires {new/off, new/proofs}
           proof-overhead interaction requires all four cells
```

This preserves the useful diagonal comparison while preventing a causal
reading the data cannot support.

### 5.4 Use a forest table for workload heterogeneity

The terminal can render a compact shared log axis beside exact values:

```text
Proof-overhead interaction, new ÷ old       0.5×        1×         2×
  math               1.18 [1.10,1.27]                  │──●──
  eggcc              0.97 [0.90,1.05]              ├───●──┤
  pointer            1.42 [1.25,1.62]                  │────●──┤
  hardboiled         1.07 [0.99,1.16]              ├───│─●──┤
  luminal            1.11 [1.04,1.18]                  │─●──┤
  herbie             missing 2 rows                [incomplete]
  typical            1.14 [1.07,1.21]                  │──◆──┤
```

Exact numbers remain present for copying and accessibility. Color can reinforce
direction or state, but text and position must carry the meaning. The axis
should label “favors old” and “favors new” according to whether lower or higher
is desirable for the metric.

### 5.5 Match the view to the comparison shape

| Shape | Recommended overview |
| --- | --- |
| one pair | current benchstat-like two-column table plus joint-change warning |
| 2×2 factorial | cell grid plus named effects and interaction forest table |
| one control, many treatments | treatment rows, control estimate, versus-control effect, interval, state |
| many targets over time | history/change-point view; selected pair or interaction as drill-down |
| many endpoints, exploratory | coverage/point-estimate heatmap for navigation; never the sole inferential view |

A heatmap is useful for finding holes and large effects, but poor at showing
uncertainty. It should link to an interval view rather than encode confidence in
color saturation.

### 5.6 Separate selection, contrasts, and layout in the interface

An eventual command could have three independent pieces:

```text
selection:  targets={old,new} treatments={off,proofs} backend=main
questions:  scenario(old/off,new/proofs)
            simple(treatment@new)
            interaction(target,treatment)
layout:     row=workload table=metric detail=phases
```

The exact syntax is open. The design constraint is more important:

- selection determines which cells may be read or collected;
- questions determine which relationships are computed;
- layout determines where those cells and relationships appear.

Benchstat's projections are a good layout model. A small fixed contrast
vocabulary is preferable to an arbitrary nested-expression DSL. Exporting tidy
observations and derived effects would leave advanced analysis to R,
statsmodels, or Vega-Lite without embedding those systems in the runner.

### 5.7 HTML should link views, not invent different statistics

The existing self-contained report already recomputes any selected pair from
the embedded cache. A matrix extension should reuse the same analysis catalog
and add linked views:

- selecting a grid cell filters raw observations and provenance;
- selecting an effect filters the forest table to its workloads;
- selecting a workload opens phase and ruleset contributors;
- changing scope remains cache-only and never builds, collects, or appends;
- invalid requests leave the previous valid report in place.

Rich, Markdown, and HTML should differ in interaction and density, not in the
estimated quantities or state classification.

## 6. Worked decision: cached old main versus new proofs

The motivating shortcut is reasonable, but only after naming the question.

### If the question is the migration effect

`old/off → new/proofs` is exactly the requested comparison. Reuse old/off if
the exact cache key matches. Mark the result as a joint target-and-treatment
effect and report the evidence grade. A cross-session result can be a useful
first look; a release or regression decision should use a same-session run or a
fresh old-side canary.

### If the question is current proof overhead

The required contrast is `new/proofs ÷ new/off`. An old/off observation is not a
substitute merely because the off code path is believed unchanged. If the new
target builds to the same binary hash and the workload, facts, backend,
treatment, and timeout also match, the cache will reuse the observation
automatically. Otherwise, collecting new/off is the evidence needed for
attribution.

In the local July cache inspected for this research, off-mode runtime was much
cheaper than proof-mode runtime, so omitting fresh off cells saved little
measurement time relative to the loss of attribution. That is a contingent
observation, not a general law; the collection plan should show predicted work
before the user decides.

### If the question is whether proof overhead changed

All four cells are required:

```text
old/off    old/proofs
new/off    new/proofs
```

The interaction should be computed directly from the four cell observations,
not by dividing two printed interval endpoints. If old cells are historical and
new cells fresh, the interaction is also entangled with measurement epoch. At
minimum, rerun an old-side canary; for a headline claim, interleave all four
cells in one run group.

### Current snapshot note

On 2026-08-12, the primary checkout's 264-row July cache did not contain current
`origin/main` (`bd4752e`). The live PR #54 cache contained six interleaved
`off` and `proofs` rows for the rational Math fixture at `7ca3c9d`. The commits
from there to `9fc1846` did not touch that fixture or the egglog Rust sources;
they did touch benchmark plumbing and the separate egg runner. Current PR rows
also recorded the same egglog binary hash. This makes reuse likely for that
cell, but the complete cache key—not source inspection or a target label—is the
final test.

These cache counts are a dated inspection of mutable, ignored JSONL files, not
a repository invariant. They explain the concrete shortcut considered here;
the design conclusions do not depend on the counts remaining unchanged.

## 7. A staged path forward

### Stage 1: a cache-only reporting prototype

- Add no collection syntax.
- Select several exact endpoints already present in a report store.
- Render the cell grid, scenario effects, and versus-control families.
- Preserve today's arithmetic-mean/Fieller pair calculations.
- Add provenance and evidence-grade warnings.
- Optionally export benchfmt and test real benchstat projections as a UI
  experiment.

This validates whether the views answer real questions before committing to a
new analysis model.

### Stage 2: a native named-effect layer

- Introduce typed `cell`, `scenario`, `simple`, `vs-control`, and `interaction`
  requests.
- Keep question specification independent of layout.
- Add bootstrap uncertainty for scenario and interaction effects while
  preserving the arithmetic-mean estimand.
- Add the 2×2 cell/effects view and workload forest table.
- Represent observed, missing, failed, and illegal cells explicitly.

### Stage 3: measurement-session provenance

- Persist run-group and machine/toolchain metadata.
- Interleave multi-cell collections within a run group.
- Add reference-side canary workflows and evidence grades.
- Decide which evidence grades may produce CI verdicts, equivalence claims, or
  only exploratory annotations.

### Stage 4: deliberate statistical expansion

Only after measured evaluation on real cache distributions:

- decide whether a log/geometric estimand should replace or accompany current
  arithmetic-mean ratios;
- select practical-equivalence thresholds per metric or workload class;
- define multiplicity families and adjustment policies;
- add rank or time-series views only when their population assumptions match an
  actual project question.

## 8. Decisions still required

| Decision | Why it cannot be inferred from the literature | Evidence needed |
| --- | --- | --- |
| arithmetic versus geometric wall-time estimand | both are defensible and answer different questions | compare both on representative cached distributions and identify the project decision each serves |
| equivalence bounds | a statistical method cannot choose what is practically negligible | maintainer-defined cost thresholds per metric/workload class |
| workload population or fixed suite | determines whether across-workload inference is meaningful | explicit statement of what the benchmark suite represents |
| session evidence policy | exact content reuse and measurement comparability have different goals | decide which claims may use cross-session, canary-qualified, or same-session data |
| semantic comparability registry | legality does not prove equal work | workload-specific correctness or equivalence oracles |
| default contrast families | printing everything recreates the old failure mode | review the scenario, simple-effect, interaction, and versus-control mockups against actual decisions |

## 9. Evidence and source map

### 9.1 Project evidence matrix

| Knowledge unit | Current evidence | Coverage | Consequence for this report |
| --- | --- | --- | --- |
| observation identity | `ReportRecord`, `CacheKey`, focused reuse tests | convergent | retain raw cell cache; do not cache comparisons |
| plural collection | N-endpoint collection planner and nightly shared cache | convergent | matrix reporting does not require new measurement machinery |
| pair restriction | `ComparisonSpec`, analysis indices, pair wording, interactive two-selector form | convergent | redesign/reporting work is above the store |
| ragged legality | backend/treatment registry and PR #54 engine workload validation | convergent | distinguish illegal, missing, failed, and observed |
| semantic comparability | PR #54 fixed Math equality at iteration 11 | divergent by workload | require workload-specific oracle/provenance |
| session comparability | timestamps exist; session/machine identity does not | absent | add evidence metadata before strong historical-cache claims |
| interaction uncertainty | no current implementation | absent | bootstrap current estimand first; evaluate log estimand separately |
| high-volume display | generic report catalog exists; only pair views exist | divergent | add named effects and progressive disclosure, not implicit all-pairs |
| longitudinal regression | nightly history exists, but no local adjacent-commit noise model | deferred | revisit when the project asks a series/change-point question |

### 9.2 Validation ledger for the existing project reports

| Report | Finding retained | Validation result or correction |
| --- | --- | --- |
| [`README.md`](README.md) | the problem is above the cell-oriented cache; uncontrolled all-pairs output is undesirable | architectural core confirmed; proposal choices remain open rather than accepted design |
| [`research/code-map.md`](research/code-map.md) | storage and collection are plural while analysis and presentation are pair-shaped | confirmed by code inspection at `bd4752e`; the corresponding focused tests passed in the documentation worktree during this review |
| [`research/git-archaeology.md`](research/git-archaeology.md) | the project had a working matrix and later an expensive DuckDB/live-query experiment | confirmed from repository history; the lesson is to avoid implicit comparison fan-out, not to forbid matrices |
| [`research/compat-chat.md`](research/compat-chat.md) | PR #54 introduces a ragged engine/treatment space and needs semantic-comparability metadata | motivation confirmed; implementation details corrected to 11 iterations, no current 13-table oracle, and non-equivalent cross-engine phase mappings |
| [`research/stats-methodology.md`](research/stats-methodology.md) | effect sizes need uncertainty; aggregates, multiplicity, stopping, and failed cells need explicit policy | retained; current implementation specifically uses arithmetic means and Fieller intervals, while bootstrap/log-contrast extensions still require calibration and an estimand decision |
| [`research/doe-factorial.md`](research/doe-factorial.md) | factor, cell, block, simple-effect, and interaction vocabulary fits the problem | retained; its claim that the old/off-to-new/proofs diagonal contains an interaction term was algebraically incorrect and is corrected here |
| [`research/tools-survey.md`](research/tools-survey.md) | benchstat-style projections and versus-base output are useful precedents | checked against current official benchstat documentation; no surveyed tool supplies the full selection/question/layout design |
| [`research/viz-grammar.md`](research/viz-grammar.md) | cell, contrast, and layout grammars should be separate; forest and linked views fit the evidence | retained and connected to primary comparison-visualization, Polaris, Vega-Lite, and forest-plot sources |
| [`research/ci-regression.md`](research/ci-regression.md) | longitudinal systems add baselines, rollups, and change-point concepts | retained as future context; the local cache has no validated adjacent-commit noise model, so these are not claimed as present capabilities |

### 9.3 Primary external sources most directly used

1. Tomas Kalibera and Richard Jones,
   [*Quantifying Performance Changes with Effect Size Confidence Intervals*](https://arxiv.org/abs/2007.10899).
2. Douglas G. Altman and J. Martin Bland,
   [*Interaction revisited: the difference between two estimates*](https://www.bmj.com/content/326/7382/219).
3. NIST/SEMATECH,
   [full factorial designs](https://www.itl.nist.gov/div898/handbook/pri/section3/pri333.htm)
   and [DOE model selection](https://www.itl.nist.gov/div898/handbook/pri/section4/pri43.htm).
4. Go performance project,
   [`benchstat` command documentation](https://pkg.go.dev/golang.org/x/perf/cmd/benchstat).
5. Russell Lenth,
   [`emmeans` interaction-analysis vignette](https://rvlenth.github.io/emmeans/articles/interactions.html).
6. Michael Gleicher et al.,
   [*Visual Comparison for Information Visualization*](https://graphics.cs.wisc.edu/Papers/2011/GAWJHR11/).
7. Chris Stolte, Diane Tang, and Pat Hanrahan,
   [*Polaris: A System for Query, Analysis, and Visualization of Multidimensional Relational Databases*](https://research.google/pubs/polaris-a-system-for-query-analysis-and-visualization-of-multidimensional-relational-databases/).
8. Arvind Satyanarayan et al.,
   [*Vega-Lite: A Grammar of Interactive Graphics*](https://vis.mit.edu/pubs/vega-lite/).
9. Todd Mytkowicz et al.,
   [*Producing Wrong Data Without Doing Anything Obviously Wrong!*](https://sape.inf.usi.ch/publications/asplos09.html).
10. Philip J. Fleming and John J. Wallace,
    [*How Not to Lie with Statistics: The Correct Way to Summarize Benchmark Results*](https://doi.org/10.1145/5666.5673).
11. John R. Mashey,
    [*War of the Benchmark Means: Time for a Truce*](https://ece.uprm.edu/~nayda/Courses/Icom6115F06/Papers/paper3.pdf).
12. Daniël Lakens,
    [*Equivalence Tests: A Practical Primer*](https://pmc.ncbi.nlm.nih.gov/articles/PMC5502906/).
13. Janez Demšar,
    [*Statistical Comparisons of Classifiers over Multiple Data Sets*](https://jmlr.org/papers/v7/demsar06a.html).
14. Yoav Benjamini and Yosef Hochberg,
    [*Controlling the False Discovery Rate*](https://www.math.tau.ac.il/~ybenja/MyPapers/benjamini_hochberg1995.pdf).

### 9.4 Research-session provenance

The source corpus originated in Claude session
`177ee8d8-aeab-4cf2-a5cf-0b7015e884cd`, named `stats`. Its research workflow
`wf_32fa0533-199` produced the eight topical reports, and verification workflow
`wf_9ec71a7c-1ad` adversarially reviewed the original synthesis. The durable
inputs are the Markdown files listed above at commit `9daebfa`; the raw local
session and workflow logs remain under
`~/.claude/projects/-Users-saul-p-egglog-encoding/`.

Workflow conclusions were treated as leads, not authority. Where a generated
report or verifier conflicted with current code, arithmetic, or the live PR,
this synthesis used the primary evidence and records the correction in the
validation ledger.

## Conclusion

The scalable unit is not “a matrix” and not “a pair.” It is a **cell plus an
explicit question about cells**.

The current cache already provides the cells. DOE supplies the names for simple
effects and interactions. Benchmarking statistics supplies the obligation to
state the estimand, uncertainty, and experimental hierarchy. Comparison and
visualization systems supply projection, explicit relationship encoding,
forest-plot intervals, and progressive disclosure.

The most promising near-term design is therefore modest: keep exact observations
and the pair workflow, add a cache-only report that accepts a few named question
families, render provenance before conclusions, and show cell values beside the
derived effects. That is enough to make old/off-to-new/proofs scenarios,
proof-overhead comparisons, and four-cell interactions legible without
recreating either the old implicit table explosion or a general-purpose
statistics language.
