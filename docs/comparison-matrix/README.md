# The benchmark comparison matrix: a map of the problem space

2026-08-11 · branch `bench-comparison-matrix` (off `origin/main`, thinking doc — no code changes)

The question this document answers: today `./bench.py` compares exactly one
pair (baseline endpoint vs candidate endpoint). What would it mean to compare
*more* — e.g. `{old commit, new commit} × {off, proofs}` with all four ratios
plus "did the proofs overhead itself get worse"? Is there existing literature
or a conceptual language (a "Vega-Lite for comparisons") for specifying what
to compare and displaying the resulting matrix? And is it worth building
anything at all?

Method: eight parallel research agents (codex "compat" chat mining, git
archaeology, code mapping, benchmark statistics, design-of-experiments,
benchmark-tool survey, visualization grammars, continuous-benchmarking prior
art). Their full reports, with all citations, are in [`research/`](research/).
This file is the synthesis.

**TL;DR.** There is no single "Vega-Lite for comparisons" anywhere — not even
at Google/Mozilla/rust-lang scale. But the problem decomposes into three
mature vocabularies that click together: your grid **is a factorial design**
(DOE supplies the formal answer to "which ratios are worth reporting":
*contrasts*, and your ratio-of-ratios is the textbook *interaction*); the
statistics all become trivial **on the log scale** (where Fieller is a
dead-end that doesn't compose); and the closest shipped artifact is **Go
benchstat's projection algebra** (`-table/-row/-col/-filter`), which no tool
extends with interactions — that extension is small and genuinely novel.
Meanwhile your own JSONL cache is *already* the full matrix (pair-ness lives
only in a few Python modules above it), and your own git history contains both
a working matrix harness *and* the reason it was deleted. Several incremental
ways through exist, including a legitimate "change nothing."

---

## 1. Where you actually are

Three findings from your own repo/history/chats that frame everything else.

### 1.1 The cache is already the matrix; only the top of the stack is a pair

Each JSONL row is one observation keyed by
`CacheKey(binary_sha256, file_sha256, treatment, timeout_sec, backend, fact_directory_sha256)`
(`benchmarking/reports/store.py`) — no notion of baseline/candidate anywhere
in the data layer. `collection.py` is already N-endpoint (only its callers
pass 2). The nightly (PR #32) already populates one shared cache by running
the pair CLI once per endpoint, and the interactive HTML report already
enumerates *every* cached endpoint and can recompute any pair browser-side
(`interactive_runtime.py:_cache_universe`). Four modules would need real
redesign: `models.py` (`ComparisonSpec.baseline/candidate`), `benchmark.py`
(the `--X` / `--compare-X` flag grammar), `reports/analysis.py` (every
`*View` indexes endpoints `{0,1}`), and `reports/presentation.py` (pair
wording throughout); the interactive runtime/JS also hardcode a two-endpoint
scope form, but only mechanically. Full inventory with file:line in
[`research/code-map.md`](research/code-map.md).

**Consequence:** "compare everything" is a *reporting* problem, not a
*collection* problem. A matrix report over already-cached cells requires zero
new measurement machinery.

### 1.2 You already built the matrix once, and the record of why it died is good

Before commit `8f72ecb5` ("Simplify benchmark reports around pair
comparisons", 2026-07-17; merged in PR #21 on 07-20), `bench.py` took
repeated `--target` and comma lists for `--backend`/`--treatments`, and
auto-enumerated three families of comparison tables (cross-target per cell;
within-target overhead ratios; cross-backend). Your desired
`{old,new} × {off,proofs}` was literally
`./bench.py --target old=@A --target new=@B --treatments off,proofs`. At its
peak — which lived only ~2 days, inside the PR branch, never on main — the
matrix ran over a DuckDB SQL catalog (an ~800-line `analysis.sql`; ~1,100
SQL lines across analysis/presentation/schema) with `--duckdb-ui` and a
`--serve` live scope editor.

It was collapsed to a pair for two separable reasons:

1. **The DuckDB implementation tax** — ~900 lines of mirrored SQL/Python
   schema vs stdlib JSONL, measured across four preserved architecture
   experiments. This one is documented in the PR #21 body (the only written
   motivation record — itself AI-written; commit messages of that era are
   subject-line only). It was an implementation choice, not a cost of the
   matrix.
2. **Auto-enumeration** — every CLI selection fanned out into dozens of
   volunteered tables, each needing disclaimer captions ("These are not
   target-vs-baseline ratios"), diluting the single decision gate
   (proofs < 2×). This one is read off the old code itself — the captions
   are all over the old `bench.py`/`summary.py` — rather than stated in the
   PR. It was the real failure mode of flexibility.

Notably: the one thing you now want that **never existed** in either era is
the interaction estimate (ratio-of-ratios with a CI). The old system only let
you eyeball two overhead tables side by side. See
[`research/git-archaeology.md`](research/git-archaeology.md).

**Consequence:** the failure mode to design against is *volunteered
comparisons*, not *many cells*. Any future matrix should render exactly the
contrasts the user asked for, and nothing else.

### 1.3 The compat work breaks the pair model this month, by design

The "compat" codex session (egglog-paper compatibility) is adding egg 0.11.0
as a first-class engine: the treatment axis grows to nine — four egg lanes
(`egg`, `egg-proofs`, `egg-proof-extraction`, `egg-proof-testing`) plus a new
egglog `proof-testing`, joining `off`/`term`/`proofs`/`proof-extraction`
(main has four today; `relations-encoding` swaps in the two causal lanes) —
with the engine derived from the treatment via a registry in
`benchmarking/engines.py` (uncommitted, draft PR #54). Its own
validation plan is "run every egg and egglog treatment against plain egg" — a
9-cell, one-baseline star executed as 8 manual pair invocations. And the
comparison it exists to enable — is egglog's proof overhead worse than
egg's explanation overhead? — is another ratio-of-ratios.

Two structural lessons from that work
([`research/compat-chat.md`](research/compat-chat.md)):

- **Legality is part of the model.** Most of the full cross product is
  invalid (dd × egg rejected; egg treatments rejected on any workload except
  `math.egg`). A matrix display must distinguish *illegal cell* from
  *missing data* from *failed run*.
- **Comparability is semantic, not just dimensional.** Cross-engine ratios
  are licensed by committed oracles (the N=9/N=10 equality boundary, 13-table
  count parity). And measures carry per-engine caveats: egg's `merge_ns ≡ 0`,
  explanation time hides in "outside" — cross-engine *phase* comparisons need
  footnotes or should be refused.

---

## 2. The conceptual language (it exists, in three pieces)

### 2.1 Design of experiments: your grid is a factorial, and "what's worth comparing" has a formal answer

The mapping is 1:1 (Jain, *The Art of Computer Systems Performance
Analysis*, 1991; NIST/SEMATECH e-Handbook §5 — details and quotes in
[`research/doe-factorial.md`](research/doe-factorial.md)):

| DOE term | Here |
|---|---|
| response variable / **measure** | wall, max-RSS, phase times, ruleset times, future egg-equivalence stats |
| **factor** / level | `target` (a commit), `backend`, `treatment` |
| **cell** | one endpoint × workload — *your CacheKey is literally a cell id* |
| **block** | the workload file (and, implicitly, the measurement session) — a huge known variance source you facet by, never silently average over |
| **contrast** | a zero-sum weighted combination of cell means = "a ratio worth reporting" (on the log scale) |
| **interaction** | "did the effect of X change with Y" |

Today's harness is what Jain calls a one-factor-at-a-time ("simple") design,
which he flatly labels "not recommended" because it cannot see interactions.
Wanting the 2×2 instead of two separate pairs is the founding argument of
factorial design.

For your exact `{old,new} × {off,proofs}` example, the four wished-for ratios
plus the interaction are **not five independent quantities** — the 2×2 has a
grand mean plus exactly three orthogonal contrasts, and your five lines are
the standard reporting set:

| # | Ratio | DOE name |
|---|---|---|
| 1 | new-off / old-off | simple effect of target at `off` ("did the base engine regress") |
| 2 | new-proofs / old-proofs | simple effect of target at `proofs` |
| 3 | old-proofs / old-off | simple effect of treatment at `old` (overhead before) |
| 4 | new-proofs / new-off | simple effect of treatment at `new` (overhead after) |
| 5 | (4)÷(3) ≡ (2)÷(1) | **interaction** — "did the proofs overhead itself change" — coefficients (+1,−1,−1,+1) on log cell means; identical math to econometrics' difference-in-differences |

Two prescriptions fall out:

- **Report the interaction first.** If it's non-negligible, averaged "main
  effects" mislead; show simple effects per level. If it's ≈1, collapse to
  main effects and gain precision.
- **Diagonal ratios (new-proofs / old-off) are confounded contrasts** — a
  mixture of ½·target + ½·treatment + ½·interaction. DOE gives you a
  principled reason to refuse to print them: they answer no single question.
  This *is* the formal answer to "what's good to compare": the ratios whose
  log-contrast coefficients isolate one effect.

Generalization: `{2 targets} × {k treatments}` wants treatment-vs-control
(everything ÷ `off`, Dunnett-style) — `k−1` overhead lines and `k−1`
interaction lines, not O(k²) pairwise ratios. `off` (and `egg`) deserve
distinguished-baseline status in the vocabulary. The compat star ("everything
vs plain egg") is exactly this shape.

DOE also names your cache traps: comparing June's cached cells against fresh
cells **aliases `target` with measurement epoch** (the DiD "parallel trends"
assumption, violated); unbalanced replicate counts break contrast
orthogonality; AABB run ordering confounds with drift (the collector's
round-robin interleaving is already right).

### 2.2 The statistics: do everything in log space; Fieller is a dead-end for composition

This is the single most load-bearing technical finding
([`research/stats-methodology.md`](research/stats-methodology.md),
[`research/viz-grammar.md`](research/viz-grammar.md) §4.5):

- On logs, *every* comparison — simple ratio, geomean aggregation,
  ratio-of-ratios — is a **linear contrast of cell log-means** with a plain
  Welch t CI, exponentiated for display. One uniform mechanism.
- The current **Fieller CI does not compose.** It answers "ratio of two
  arithmetic means" and has no clean extension to ratios of ratios (the
  biostat workaround, MOVER-R, exists but is strictly more complex than
  logs). For benchmark CVs (≪ 1) Fieller ≈ log-t anyway, so nothing is lost;
  keep Fieller as a cross-check on headline pairs if continuity matters.
- The interaction CI is textbook: Altman & Bland (BMJ 2003, "Interaction
  revisited") give the SE of a difference of two independent estimates as
  `√(SE₁² + SE₂²)`, applied on the log scale for ratios. Composed over the
  four cells (their formula applied twice):
  `I = (m̂₁₁ − m̂₁₀) − (m̂₀₁ − m̂₀₀)`, `SE = √(Σ₄ s²ᵢ/nᵢ)`, with a
  Welch–Satterthwaite df as the standard small-sample refinement, and
  `exp(I ± t·SE)`. All inputs (mean, var_mean, n per cell) already exist in
  `_MetricEstimate`.
- **Geomean across workloads = arithmetic mean of log-ratios** (Fleming &
  Wallace 1986 — never arithmetic-mean ratios; Mashey 2004 for when geomean
  is the right model). Its CI is a paired t over per-workload log-ratios.
  Label it "typical ratio", never "the suite got X% faster in total"; if
  suite total matters, show the ratio-of-summed-times as a separate row (the
  current gate number). And for "which of ≥3 configurations wins overall",
  the standard is rank-based — Friedman + Nemenyi with critical-difference
  diagrams (Demšar 2006) — robust to one workload dominating a geomean.
- Caveats: logs need strictly positive data — fine for wall/RSS, **not** for
  phase times that can be ~0 (`merge`, `unattributed`). Phases stay on the
  raw scale (absolute Δ + share-of-wall, as today) or get bootstrap CIs.
- **A matrix is a false-positive machine.** m cells at α=0.05 ⇒ ~0.05·m false
  flags (benchstat's docs say this outright). Standard hygiene: three-state
  cells (*different* / *equivalent within a practical band, e.g. ±2% and a
  5 ms floor* / *inconclusive*), Benjamini–Hochberg FDR **per displayed
  table** (family = one measure × one contrast type × all workloads;
  `scipy.stats.false_discovery_control`), and never "run until significant"
  (peeking inflates false positives 3–8×; stopping on CI *width* is fine).
- One honesty rule for interactions: a ratio-of-ratios of 1.10× may be 5 ms
  on a 50 ms workload — always pair it with the absolute delta-of-deltas.

A cheap, high-value reporting idiom from Jain: an **allocation-of-variation
header** — "workload explains 88% of log-time variance, treatment 9%, target
0.6%, interaction 0.1%, residual 2%" — one line that tells the reader whether
the commit even matters before they read 20 ratios.

### 2.3 Cube + calculated members + table algebra: how the pieces name themselves

The "is there a Vega-Lite for this" question decomposes exactly
([`research/viz-grammar.md`](research/viz-grammar.md)):

1. **Cells form an OLAP data cube** (Gray et al. 1997): dimensions
   target/backend/treatment/workload × measures. Your JSONL is already the
   fact table; a geomean row is the cube's `ALL` member; slice/dice =
   `--fix`/filter.
2. **Contrasts become first-class as *calculated members*** (the MDX idea):
   `target: Δ = new/old` and `treatment: overhead = proofs/off` are derived
   members of their dimensions. Then the ratio-of-ratios needs **no third
   concept** — it is simply the cell where the two calculated members cross.
   This is the conceptual unlock that keeps layout uniform: once a contrast
   is a member, any layout algebra can place it on an axis like any level.
3. **Layout is a table algebra**: Polaris/Tableau `cross`/`nest`/`concat`
   (Stolte–Tang–Hanrahan 2002 — nest matters for your ragged, legality-
   constrained cube), Vega-Lite `facet`/`repeat` for the HTML end, and — the
   one *shipped on a CLI* — **benchstat's projections**.

Gleicher's comparison-vis taxonomy (2011) gives the display theory: side-by-
side mean columns are *juxtaposition* (reader divides in their head — bad
past a few rows); a ratio+CI column is *explicit encoding* (compute the
relationship, show it); an interaction column is explicit encoding **of a
relationship between relationships** — two computation levels from the data,
which is precisely why it feels exotic and why the intermediate ratios must
stay visible next to it. And the standard statistical display for "many
ratio+CI rows with subgroup structure" already exists: the **forest plot**
(workload → study, log axis, line at 1×, geomean → summary diamond) — copy
it, don't invent it. Terminal version: `├──●──┤` CI bars on a shared log
axis, benchstat's `~` for insignificance, rows sorted by effect (Trellis
"main-effects ordering"), cap at two layout dimensions and punt the rest to
HTML/Vega-Lite export with **precomputed** CIs (Vega-Lite's errorbar cannot
do ratio statistics).

---

## 3. Prior art: what exists, what's missing

Full survey with flags and output shapes:
[`research/tools-survey.md`](research/tools-survey.md),
[`research/ci-regression.md`](research/ci-regression.md).

| Tool | Expression | Display | Missing |
|---|---|---|---|
| **Go benchstat** (2023 rewrite) + benchfmt/benchproc | records are self-describing `key=value` coordinates; `-filter EXPR`, `-table/-row/-col KEY[@(v1 v2)]` projections; first projected column = baseline | per-unit tables, `vs base` Δ% + `(p= n=)`, `~` insignificant, geomean footer, "benchmarks vary in KEY" warning when a collapsed axis still varies | one comparison axis; **no interactions**; no FDR |
| BenchmarkDotNet | `[Params]` cross product; `Baseline=true` per method/job/category | factor columns left; paired-per-measurement `Ratio`/`RatioSD`; per-category local baselines; grouped headers | same-session only; no interactions |
| criterion.rs + critcmp | named saved baselines (`--save-baseline`), compare post hoc | N baselines × benchmarks matrix | no factors, no interactions |
| hyperfine | `-L`/`-P` factor lists → cross product, `{var}` templating | relative-to-fastest summary; JSON export + scripts | display deliberately thin |
| asv | parameterized benchmarks; `asv compare`, `--factor 1.1`, `--split` | before/after/ratio; `~`/`x` marks; website for the matrix | pair CLI only |
| pyperf | `compare_to ref.json a.json b.json --table` | N files as columns vs ref; geomean footer | one axis |
| Google Benchmark compare.py | pair subcommand; **filters-as-operands** (compare two regex slices of one run — the "proofs vs off within one commit" shape) | Δ + Mann–Whitney U rows (needs ≥9 reps) | pair only |
| rustc-perf compare page | two artifacts; the 3-factor matrix (profile × scenario × backend) lives in *rows/filters*, never in the comparison operator | learned per-cell noise thresholds (Q3+3·IQR of last 30 adjacent changes), significance factor, 5 magnitude buckets, relevance-filtered rollups | comparison is strictly binary |
| bencher/conbench/CodSpeed | thresholds per (branch, testbed, measure); context matching | alerts, PR checks | services; vs-base only |
| MongoDB/Hunter/Otava, Chromium | change-point detection over commit *series* decides which pairs matter; Pinpoint's tri-state SAME/DIFFERENT/UNKNOWN triggers adaptive re-runs | — | not a matrix language at all |

**The field conclusion:** every tool hardwires one comparison axis with one
distinguished base. Nobody — not even at rustc scale — ships a contrast
language. The two halves of the missing design (benchstat's projections; MDX
calculated members) are each proven separately; combining them plus log-space
CIs and FDR is small and well-defined, and would be genuinely novel. Also
consistently absent everywhere: your interaction question. rustc-perf's other
lesson: with 3 factors in production, they still keep the comparison binary
and put factors in rows + filters + rollup-then-drill-down — specification
burden goes to *filtering*, not enumeration.

---

## 4. Why this is genuinely hard (the honest list)

1. **The old failure mode is one config flag away.** Auto-enumeration killed
   the first matrix. Any design where the tool *volunteers* comparisons
   regenerates disclaimer-caption sprawl and dilutes the <2× gate.
2. **Contrasts live one level above cells.** Table algebras partition data; a
   ratio is a function of *two* partitions. Without the calculated-member
   move you accrete "vs base" special cases (the entire tool field is stuck
   there).
3. **Statistics must compose with the algebra.** Forced choice of log-space
   internals; Fieller retires from anything multi-way. Correlation between
   contrasts sharing a cell (new/old@off and new/old@proofs share nothing,
   but new-proofs/old-off-style chains do) means contrast-vs-contrast
   displays can double-count noise — one more reason to print only named,
   orthogonal contrasts.
4. **Phases break the clean story.** Zero-valued phases can't be logged;
   phases are compositional (shares sum to 1, one rising forces others down);
   cross-engine phase semantics differ (`merge ≡ 0` for egg). Phase tables
   stay raw-scale, absolute-Δ-first, and within-engine by default.
5. **The cache invites epoch confounding.** Cached-baseline vs fresh-candidate
   aliases target with session/machine state (Mytkowicz; Maricq). Also:
   `timeout_sec` fragments cells; cargo-feature-union builds silently split
   `binary_sha256` for the same commit (a run touching dd adds
   `--features dd-backend` to *every* endpoint sharing the checkout);
   unbalanced cells break orthogonality. None of these bite a single
   interleaved pair run; all of them bite matrix-from-cache. Cheap
   mitigations exist: record a session id / machine fingerprint per row;
   measure all cells of a headline contrast interleaved in one session; and
   when reusing cached cells, re-run one canary cell and require it to
   reproduce within its old CI before trusting cross-session contrasts.
6. **Legality and semantic comparability.** Post-compat, most of the cube is
   invalid, and some valid cells are only comparable under committed oracles.
   Cell states multiply: legal/illegal × cached/missing × success/failed ×
   comparable/caveated.
7. **Display bandwidth.** A terminal holds ~2 layout dimensions and ~4 value
   columns. Measures multiply *tables*, not columns (benchstat's unit
   faceting is the only shape that survives wall+RSS+6 phases+egg-equivalence
   measures). Everything bigger needs the HTML export.
8. **Multiplicity scales with the matrix**, and the family you correct over
   must equal the family you *display* or the stars stop meaning anything.
9. **A general grammar is a research project.** Everyone converged on: fixed
   coordinate vocabulary + filter/projection mini-language + hardcoded
   rollup→drill-down + per-cell noise model. Budget accordingly: coordinate
   schema + benchstat-style projection + rustc-perf-style significance ≈ a
   week (ci-regression's estimate); the contrast engine on top is small but
   is precisely the novel, unpriced piece; a true comparison DSL ≈
   open-ended with no prior art to crib from.

---

## 5. Ways through, ranked by cost (each is independently useful; all are optional)

**Option 0 — change nothing (legitimate).** The nightly pattern already
populates N endpoints into one cache; repeated pair invocations (cache-
deduped) already produce all four simple ratios of the 2×2; the interactive
HTML already browses any cached pair. What you cannot get today: the
interaction with a CI, and a single view of the grid. The compat star costs 8
manual invocations. If the 2×2 question comes up rarely, the honest answer is
"run the four pairs and, for the interaction, accept eyeballing" — knowing
that eyeballing ratios-of-ratios without CIs is exactly the thing the
statistics literature says humans get wrong.

**Option A — benchfmt exporter + real benchstat (~a day, zero risk).** Emit
each JSONL row as one Go-benchfmt line (workload/target/backend/treatment
all as sub-name `key=value` pairs, phases and RSS as extra units) and run
actual `benchstat -table /target -row /workload -col /treatment`. You get
projections, Mann–Whitney vs-base, `~`, geomean, per-unit faceting — today,
with zero maintenance. This is the cheapest possible experiment to learn
*whether you even like matrix views*, before designing one. Limits: medians +
U-test (no Fieller/log-t continuity), no interactions, no legality awareness.

**Option A′ — multi-treatment star with today's stats (~a day, native).** The
compat analysis names the cheapest native increment: accept multiple
`--treatment` values in one invocation and render one column of vs-baseline
ratios against a declared control cell — existing Fieller machinery, one pair
at a time, no new statistics or display concepts. It exactly serves the
compat validation star (9 treatments vs plain `egg`) that otherwise costs 8
manual invocations. No interaction, no grid; later subsumed by B.

**Option B — a report-only `contrasts` command over the existing cache (the
sweet spot, ~days).** No collection changes, no CLI breakage: a new
subcommand that (1) assembles cells from cached rows (reusing
`_cache_universe`-style discovery + `latest_records`), (2) takes an explicit,
user-stated contrast list — `vs-control` within a factor, `pairwise` along a
factor, `interaction(target, treatment)` — evaluated as log-space linear
contrasts (a small, well-bounded piece of statistics code — the Altman–Bland
contrast SE plus BH-FDR — over inputs already in `_MetricEstimate`),
and (3) renders one small table per *requested* contrast plus a per-cell
estimate grid, forest-style CI column, three-state verdicts, BH-FDR per
table, geomean row, cross-session/timeout/feature-split footnotes. This
restores PR #21's real win (every table answers an asked question) while
adding the one thing that never existed (the interaction CI). It also
directly serves the compat validation star
(`--contrast 'vs-control:treatment@egg'`).

To make "how would this even look" concrete, a sketch (not a spec) of your
2×2 rendered under Option B — cell grid first, then only the five meaningful
contrasts, interaction on top, forest column on a log axis:

```
$ ./bench.py contrasts --grid target=old,new treatment=off,proofs --measure wall
variation (log wall): workload 88% · treatment 9% · target 0.6% · interaction 0.1% · residual 2%

cells (geomean wall, 95% CI)      off             proofs
  old = @a1b2c3                   1.82s ±2%       3.61s ±3%
  new = .                         1.75s ±2%       3.72s ±4%

contrast (suite geomean)          ratio   95% CI          0.9×   1×      2×    verdict
  interaction  (proofs/off) new÷old  1.07×  [1.01, 1.13]        │├─●─┤          worse
  treatment@old  proofs/off          1.98×  [1.89, 2.08]        │           ├●┤ different
  treatment@new  proofs/off          2.13×  [2.01, 2.25]        │            ├●┤ different
  target@off     new/old             0.96×  [0.93, 0.99]     ├●┤│               different
  target@proofs  new/old             1.03×  [0.97, 1.09]      ├─●─┤             inconclusive
m = 5 contrasts × 5 workloads, BH-FDR 5% · per-workload rows behind --detail files
† cells from different sessions would be flagged here
```

**Option C — multi-cell collection front end (~days, on top of B).**
Hyperfine-style factor lists (`--grid target=old,new treatment=off,proofs`,
legality-filtered via the treatment/engine registry) expanding to a cell set,
looped over the *existing* N-ary collection with round-robin interleaving
(which also fixes the epoch confound for headline runs: measure all cells of
a contrast in one session). This is mostly CLI surface; the collection layer
needs nothing.

**Option D — the full factored model (only if B earns its keep).** The
small spec that §2 implies —
`grid` (factors × levels) + `fix` (held constants, recorded) + `blocks`
(workloads) + `measures` + `contrasts` (named families + coefficient-vector
escape hatch) + `scale=log` — with the cube/calculated-member internals, the
benchstat projection surface, per-cell noise learned from cache history
(rustc-perf's Q3+3·IQR is ~300 lines), Pinpoint-style
SAME/DIFFERENT/UNKNOWN→re-run-this-cell adaptivity, and the interactive HTML
(already a matrix browser one form away) as the drill-down. Prototype any of
this in the interactive report first — it ships the whole cache and the whole
Python stack to the browser already, so the spec language can be validated
with zero CLI/back-compat risk.

**Sequencing note** (from the compat chat's own staging): land compat (engine
axis via treatments) → land `remove-dd-benchmark-backends` (collapse the
backend axis) → *then* design the matrix over the cleaned two-factor space
(target × treatment). Building the matrix against today's three-axis space
buys permanent complexity for an axis that's about to be deleted.

**Deliberately not worth building** (consistent verdict across the reports
that address each item):
a DuckDB revival (ad-hoc SQL is one external
`duckdb -c "... read_json('.reports.jsonl')"` away); all-pairs output (nobody
does it; C(kt,2) is the explosion); arbitrary-nesting contrast algebra
(that's emmeans — if you ever need it, dump tidy long-format rows and use R/
statsmodels as the escape hatch); a dashboard; Bayesian machinery (practical-
equivalence bands capture most of the benefit); change-point detection until
commits become a tracked *series* (then: export CSV to Apache Otava rather
than writing stats).

---

## 6. The policy card (§2.2 condensed to one page, if a contrast engine ever exists)

- Per cell (endpoint × workload × measure): n, mean, var-of-mean on **log**
  data (wall, RSS); raw scale for phases.
- Every reported comparison = a named, zero-sum coefficient vector over cell
  log-means. Point = `exp(Σ hᵢ m̂ᵢ)`; `SE = √(Σ hᵢ² s²ᵢ/nᵢ)`;
  Welch–Satterthwaite df; CI exponentiated. Fieller retained only as a
  cross-check on single-pair headlines.
- Default contrast families: `vs-control` (within-factor, control = `off` /
  `egg` / first target), `pairwise`, `interaction(A,B)`. Diagonals refused by
  default (confounded); available only behind an explicit flag that names
  the confound in the caption.
- Verdict per comparison: different / equivalent / inconclusive against a
  practical band (default ±2% relative AND 5 ms absolute floor).
  BH-FDR at q=0.05 across each displayed table, header stating "m
  comparisons, FDR 5%".
- Aggregation row: geomean of per-workload ratios (= paired t over
  log-ratios), labeled "typical"; suite Σ-time ratio kept as the separate
  gate row.
- Header: allocation of variation per factor. Footnotes: cross-session
  cells, timeout mismatches, feature-split binaries, illegal/missing cells,
  per-engine measure caveats.
- Never: arithmetic mean of ratios; min-based summaries for whole-program
  time; run-until-significant.

---

## 7. Pointers

Full reports (all citations live there):

- [`research/compat-chat.md`](research/compat-chat.md) — what compat adds; the 9-treatment star
- [`research/git-archaeology.md`](research/git-archaeology.md) — the old matrix harness; PR #21's recorded motivation
- [`research/code-map.md`](research/code-map.md) — exhaustive pair-assumption inventory; blast radius
- [`research/stats-methodology.md`](research/stats-methodology.md) — log-scale contrasts, FDR, bands, stopping rules
- [`research/doe-factorial.md`](research/doe-factorial.md) — factors/cells/contrasts/interactions; ratio games
- [`research/tools-survey.md`](research/tools-survey.md) — per-tool flags and display shapes
- [`research/viz-grammar.md`](research/viz-grammar.md) — cube/calculated members/table algebra; forest plots
- [`research/ci-regression.md`](research/ci-regression.md) — rustc-perf significance stack; change-point line

Shortest external reading list: Kalibera & Jones (arXiv:2007.10899 and ISMM
'13); benchstat docs (the syntax to steal); Jain ch. 11 (ratio games) + 17–18
(2^k factorials, multiplicative models); Altman & Bland 2003 (the interaction
CI recipe); Fleming & Wallace 1986 (geomean); Gleicher 2011 (comparison
taxonomy).
