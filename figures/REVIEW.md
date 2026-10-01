# Figure review, 21 September 2026

This is an engineering inspection by the implementation agent and an independent
agent reviewer, not a controlled human reader study. The
[course rubric](references/review-criteria.md) defines the tasks and evidence.

## Measurement provenance

The collection used checkout `fdd4eac12c1318c578badbf5d1299e0e3eb4e6c0` on an
Apple M4 with 16 GiB memory, macOS 26.6 (25G72). The checkout had the figure
implementation changes; source paths, dirty flags, timestamps, and original
labels remain in each projected observation. No workload or engine source was
changed for this collection.

All 630 new observations succeeded. The overhead comparison collected 600;
the engine comparison reused its 30 Egglog Math observations and collected
only 30 Egg observations. The default cache grew from 700 to 1,330 rows.

| Artifact | SHA-256 |
| --- | --- |
| Egglog release executable | `fcfc0957eccbb1b6aa05896c5c38f360ea13edf69f9adf9aa154f192c0c7994b` |
| Egg release executable | `41d3799cd77d4c9370b1a1067ff29f10b8fa1525f64141d838c41f2ba083bb81` |
| `egg-vs-egglog.data.json` | `6e8b4237249d3da1101ef04b5731b7f1cb76ffc9f97c12311f151760712d55bf` |
| `proof-overhead.data.json` | `103f115f187bfb2bd89edf20a5684de045fd4c7a378497071bc8022376c4e489` |

These observations use the fixed serial collection order described in the
README. The confidence intervals do not cover systematic machine drift, and
these adapted workloads do not establish bounds for arbitrary applications.

## Initial design iterations

Initial SVGs, PNGs, specification hashes, and size/accessibility previews are
saved locally under `review/initial/` (ignored by Git). The size previews use
321 and 680 CSS pixels as approximate 85 mm and 180 mm widths at 96 CSS pixels
per inch. They are screen proxies, not a calibrated physical print test.

The initial inspection found two defects. Math's vertical offsets placed dots
above their corresponding mean marks, making the long mean tick resemble an
interval. Centering the offsets and shortening the tick restored the intended
meaning. In the overhead plot, narrow confidence intervals were mostly hidden
under the point marks. An aligned numeric interval column now lets readers
recover the bounds while retaining the true graphical interval width.

The revision also adds explicit 1× and 5× tick labels, identifies the logarithmic
axis, states that Math is one combined workload, and reduces unnecessary row
spacing. The 5× reference remains visually secondary and does not truncate
larger measurements.

The independent reviewer then read the revised images without consulting the
underlying data first. They identified Egglog at approximately 1.85 seconds
versus Egg at 2.95 seconds, with narrow, separated clouds; read Herbie as
3.341× with interval [3.284, 3.399]; and found Luminal as the largest slowdown
at 5.735× with interval [5.665, 5.806]. Pointer analysis is also above 5×,
at 5.136× [5.013, 5.263]. These are individual benchmark results, not a suite
average or a universal performance bound.

Retain the **raw dots with mean ticks** for Math. They answer the runtime and
spread questions directly. The ECDF adds a cumulative-proportion decoding
step and uses more space. The box-plus-dots alternative places its narrow
summary boxes beneath dense observations, providing little benefit here.
Retain **descending slowdown order** for overhead: the largest effects are
immediately visible, and finding a named workload among ten labels remains
straightforward. The stable-order alternative remains available.

The final 180 mm previews pass the reader tasks without clipping. Grayscale,
protanopia, and deuteranopia previews retain category identity and interval
readability through labels, position, shape, and numerical text. **180 mm is
the supported publication width.** The 85 mm overhead preview makes its
captions and numerical bounds too small for dependable reading; it should
not be used as the publication export size.

The synthetic review correctly exposed a wholly missing comparison and one
failed proof endpoint as unavailable, with no invented ratios. Its first
caption incorrectly asserted 30 runs despite the missing data; changing it
to **30 requested runs** made the caption accurate in incomplete cases. The
independent reviewer verified that repair. Final size/accessibility previews
and the clearly marked synthetic example are saved under `review/final/`.

This is a finite agent inspection, not evidence of human task speed or error
rates. Narrow intervals can remain visually smaller than the point marks;
the numeric column deliberately preserves their exact reported bounds.

## User-feedback revision

The next review removed complete-selection labels from both Math rows and
the unnecessary subtitle about confidence intervals. Incomplete selections
still show their counts and failure reasons. Both engines now use small
translucent circles, with deterministic vertical displacement and a thin mean
tick. The title specifies runtime with proofs, and the subtitle names the
24 rewrites and seven expressions **in one e-graph**. Lower annotations record
the eleven iterations, absence of backoff/match caps, disabled Egg internal
limits, outer 120-second timeout, and excluded proof verification. The linked
caption distinguishes this adaptation from the original 100-BackOff-iteration
PLDI evaluation.

We compared these marks with a fully overlapping low-opacity strip using
identical observations. Both show the runtime difference, but full overlap
collapses the narrow samples into short strips dominated by the mean tick.
The displaced dots preserve more visible runs. Official Vega-Lite and ggplot2
examples support this treatment of overlap; links are in the README.

The overhead revision removes the 5× reference line and all points covering
finite intervals. Thin lines with endpoint caps preserve the actual Fieller
bounds, and the numeric column supplies the ratio estimate and exact displayed
bounds. The equal-runtime line remains. A separate estimate tick and issue
annotation handle intervals that cannot be drawn. The lower caption explains
the interval and sample count; detailed workload sources are linked from the
accompanying prose caption.

The independent reviewer read the revised images before consulting data and
identified Math at roughly 1.85 s versus 2.95 s, Herbie at 3.341×
[3.284, 3.399], Churchroad at 0.486×, and Luminal at 5.735×. They preferred
the displaced translucent dots and found the interval-only marks readable at
180 mm. Their remaining ambiguity—whether the seven expressions were separate
tests—was resolved by adding “in one e-graph.” The 85 mm version remains too
small for dependable reading of the captions. Shape differences are no longer
needed: direct row labels identify the engines in grayscale and simulated
color-vision previews.

The local `review/user-feedback/` archive contains the full-overlap candidate
and updated 85/180 mm previews, including grayscale and color-vision versions.
All four compiled-Vega statistical tests pass after the revision, including
missing/failure cases. The two projected-data hashes above remain unchanged;
no benchmark collection was performed for this visual revision.

## Course-wide reduction and final review

The next pass reread all 16 public course decks and examined the available
coursework, with the coverage and per-element decisions recorded in the
[course-wide review](references/course-review.md). Three independent review
domains covered visual principles, the remaining technical topics, and
assignments/notebooks/readings; one reviewer followed the rendered figures
through revision to acceptance.

The resulting figures use one data hue, one-line question titles, a lighter
Math axis, shorter captions, and three-significant-digit ratio labels. Detailed
methods remain in the accompanying captions. The table-free overhead candidate
was rejected because it lost exact estimate/interval lookup. The reviewer
caught an ambiguous ratio subtitle and then an axis collision in a synthetic
Math failure example; both were corrected and rechecked. The final reviewer
reported no remaining concrete design objections at 180 mm. The 85 mm detail
limitation remains.

Local archives under `review/course-review-before/`, `review/course-candidates/`,
and `review/course-final/` retain the baseline, rejected candidate, final
specifications/data/images, and size/color/synthetic previews. Projected data
hashes are unchanged. All four compiled-statistics tests pass, SVG/PNG exports
are nonempty with finite geometry, and rerunning the rendering targets makes
no changes. No benchmark observations were collected for this revision.

## Validation

A fresh reviewer subsequently repeated the reading tasks without seeing the
earlier verdicts, then audited the current data and compiled marks. All 60 Math
runs and ten overhead comparisons were present; directly recomputed ratios and
Fieller bounds agreed within `6e-14`, and displayed rounding matched. Current
SVGs matched fresh compilation. The four focused tests and the size, grayscale,
color-vision, and synthetic exceptional-result checks passed. No additional
design change was warranted. The follow-up reading coverage and limitations
are recorded in the [course-wide review](references/course-review.md), with
local evidence under `review/course-continuation/`.

- `make check`: passed, including 196 Python tests and 1,462 Rust tests
  (six Rust tests ignored by the existing suite).
- `make benchmark-smoke`: passed with 20 successful observations in the
  temporary smoke cache; the default cache stayed at 1,330 rows.
- A temporary Math cache with 59 of 60 required observations collected
  exactly one missing run. Its next public CLI invocation collected none.
- Focused projection tests cover failures, missing groups, timestamp/append
  ordering, older labels, stale labeled binaries, changed binaries/inputs/facts,
  shared Math observations, and unchanged output modification times.
- A parallel Make regression verifies both collectors complete in sequence
  before projection and rendering, even when all three targets are requested
  together under `make -j8`.
- An independent read-only review found no defects in the Make ordering or
  selection/projection implementation.
- All 16 archived lecture PDF hashes verified: 1,279 pages, 197,471,232 bytes.
- Four Node tests evaluate the actual compiled Vega transforms against the
  existing Python analysis, including incomplete samples, failures, missing
  times, zero baselines, unbounded intervals, intervals reaching zero, ordering,
  and an entirely uncollected study with finite output geometry.
- A normal cached `make -j8 figures` reused all observations, preserved cache
  contents, and left all 12 canonical/alternative data and image modification
  times unchanged.
- In a temporary rendering directory, a changed Math specification rebuilt
  only its two images; changed overhead data rebuilt its four dependent images;
  and a changed lockfile invalidated all ten images. Dependency installation
  was instrumented for the last check; ordinary exports used the real locked
  renderer. Data JSON files were never treated as specifications.
- This machine's GNU Make 3.81 missed one subsecond timestamp change in the
  initial incremental check. Repeating with distinct whole-second timestamps
  verified the dependency graph. The README documents that tool limitation
  and the standard forced-rebuild command; no custom build system was added.

## Four Math conditions and manual auditability

The Math figure now includes proofs off and recording plus extraction for
both engines. Only the 30 Egg-off observations were missing; the public runner
collected those successfully and reused the other 90 Math observations. The
default cache now contains 1,360 rows. Existing suite measurements are unchanged.

The four directly labeled rows use a shared, zero-based time axis. Means are
0.752994 s and 2.948687 s for Egg off/on, and 0.445622 s and 1.852348 s for
Egglog off/on. A temporary second-panel candidate displayed the within-engine
ratios and 95% Fieller intervals: Egg 3.92 [3.80, 4.04], Egglog 4.16
[4.11, 4.21]. The independent reviewer could compare both engines and both
proof settings from the four rows without that panel. We omitted it because
its extra height and statistical transforms did not improve those reading
tasks; the Egglog ratio already appears in the suite figure. These numbers
describe this collection, whose serial, unpaired sampling limitations still
apply.

The data schema now groups observations by workload and condition, with shared
source provenance in an indexed array. Each run has only time, status,
timestamp, cache row index, and source index, plus any non-null error details.
Empty groups, failed runs, exact hashes, and original labels remain auditable.
For the same observations, data size fell 82.64%: the old two-condition Math
selection would be 13,456 bytes instead of 77,496, and the suite is 133,222
instead of 767,339. The expanded four-condition Math file is 26,365 bytes.
The projection function fell from 85 to 72 lines; it still contains no
statistics. Canonical specifications fell from 339 to 247 lines for Math and
967 to 480 for overhead, through shared encodings and condition aggregation,
removal of unused tooltips, and folding the two interval caps into one layer.
Named Fieller steps and exceptional-result guards remain explicit.

Independent review caught and resolved two simplification issues: inherited
encoding incorrectly filtered out the singleton 1× reference, and alternative
plots retained unused mean calculations solely for test discovery. Focused
tests now check the reference mark and absence of gridlines, and alternatives
test their actual completeness/status fields. Final review reported no
remaining concrete issues. The overhead PNG is pixel-identical to its approved
pre-refactor image, all ten ratios and interval bounds match exactly, and
compiled Math contains all 120 dots and four means.

Both figures were inspected at 85 mm and 180 mm, in color, grayscale, and
protanopia/deuteranopia simulations. Use 180 mm for readable labels and method
text. Local evidence is in `review/minimality/` and `review/minimality-final/`;
the before snapshot and rejected ratio candidate are in
`/tmp/egglog-figure-minimality-20260921/`.

Validation passed: `make check`, `make benchmark-smoke` using a temporary cache,
the eight focused Python projection/pipeline tests, and four compiled Vega
tests against the production Python analysis. All three collectors execute
sequentially. A cached `make -j8 figures` collected nothing, preserved the
default cache contents, and left all 12 generated data/image file contents and
modification times unchanged.

## Faceting the four Math conditions

User feedback superseded the prior four-row acceptance: the proof-off/on
comparison was harder to read. We revisited the actual course PDFs and tried
four layouts using the same 120 measurements. Relevant course evidence is
Visual Encoding pp. 24 and 63–65 (common-scale position and small multiples),
Perception pp. 60–63 (grouping by proximity, similarity, and connection), and
Tools Part 1 pp. 35–38 (trellis composition with common scales). These inform
the comparison tasks; they do not prescribe one winning layout.

Online examples and guidance reviewed:

- [Vega-Lite faceting](https://vega.github.io/vega-lite/docs/facet.html) and
  [jittered dots](https://vega.github.io/vega-lite/examples/point_offset_random.html)
  provide the declarative composition and raw-observation grammar.
- [Wilke, Multi-panel figures](https://clauswilke.com/dataviz/multi-panel-figures.html)
  shows labeled categorical grids, common scales, and consistent panel order.
- [Seaborn, Conditional means with observations](https://seaborn.pydata.org/examples/jitter_stripplot.html)
  overlays translucent observations and distinct means.
- [Xiong Bearfield et al., Grouping Cues](https://arxiv.org/abs/2310.02076)
  reports that grouping affects which comparisons viewers make in bar charts.
  Applying that result to these dots is a design hypothesis, assessed here by
  reading-task inspection rather than a controlled user study.

| Layout | Reading-task result |
| --- | --- |
| Two engine panels, shared vertical time axis | Selected. Off/on comparisons are adjacent within each engine; every condition remains directly comparable by height. No legend is needed. |
| Two proof-setting panels, shared vertical time axis | Good runner-up when comparing engines is the main task, but separates each engine's proof settings. |
| A literal 2×2 matrix, engine rows and proof-setting columns | Makes the factorial structure explicit, but off/on comparison crosses two horizontal axis origins and requires more numeric lookup. |
| Horizontal rows grouped by proof setting | Shorter labels improve the four-row baseline, but each engine's off/on observations remain in separate sections. |

The independent reviewer initially favored proof-setting panels from the
course evidence, then preferred engine panels after reading the actual charts.
At 180 mm they identified all four conditions, approximate runtimes, proof
effects, and the slower Egg-off run. The mean marks remain separate from the
raw dots, with no connecting lines that could imply paired measurements. Faint
horizontal guides help compare heights across panels. No ratio panel, extra
color, or legend was needed. Prototypes, the prior canonical figure, and the
180 mm comparison gallery are in `review/math-layouts/`.

Final faceted validation: six focused Node tests pass, including 120 raw marks,
four horizontal means, common physical heights for equal times across engines
with different ranges, and mixed missing/failure/timeout annotations. Status
labels wrap below the observations without overlapping adjacent conditions.
The original data hash and four numerical means are unchanged. Complete-data
reading passed at 180 mm in color and all three vision simulations; 85 mm
retains broad comparisons but not dependable method-text or run-detail reading.

## Expanded Math, actual measurements — 2026-09-22

Reviewed the four engine/proof panels and the per-cutoff Egglog overhead plot
using the rebuilt Egglog `4e93e5a5…` and native Egg `e97c20ca…` executables.
Every condition contains 30 selected attempts: 1,319 succeeded and one native
Egg proof run at cutoff 11 was stopped by host memory pressure. The figure
retains its successful run dots and omits that condition's mean.

The first export's rotated failure message inflated the space between rows.
Compact successful-run counts above the affected cutoff, with the fixed
30-run denominator in a shared footer, remove that gap. A star identifies a
safety stop from the original observation's error message. Moving `/30` into
the footer also prevents adjacent labels from touching in a dense missing-data
case; no timing or statistical calculation changed.

Independent reading tasks passed at 180 mm in color and grayscale: compare
both engines and proof settings at a cutoff, follow runtime growth, look up a
ratio and its interval, and explain the missing mean. The 85-mm detail remains
too small for dependable reading. Dense missing/safety-stop labels also pass
without clipping. All 1,319 raw dots and 43 mean marks retain their values and
within-panel positions. All eleven Fieller intervals agree with the production
statistical implementation within 1e-12; regenerated SVG bytes and PNG pixels
match the inspected exports. Local screenshots and the full audit are retained
under `figures/review/actual-math-20260922/`.

The caption notes that fresh-process timing includes library initialization.
Egg's approximately 0.2-second floor is consistent with Quanta's calibration
budget; the contribution was not isolated or subtracted.

## Expanded SpEQ and DialEgg, actual measurements — 2026-09-22

Independent review passed at 180 mm for both families. SpEQ retains four
measured and six unavailable source cases. DialEgg retains eight measured
inputs, two historical memory deferrals, and all fifteen excluded calls:
eight without a target and seven whose equalities were already seeded.
Call ordinals and the source-input denominator remain explicit in coverage.

The reviewer correctly read NMM40 as 8.77× [8.58, 8.97], explained why NMM80
and NMM160 have no current measurements, and distinguished SpEQ's four
admitted replays from its ten paper cases. All twelve finite Fieller intervals
match the production Python calculation within 1e-12. SVG bytes and PNG pixels
match fresh compilation, with no warnings. No further chart change was needed.
Local reading-task records and screenshots are in
`figures/review/actual-expanded-20260922/`.

## Families without current measurements

The first full export exposed empty-extent warnings from each filtered
interval layer when a whole family was unavailable. The shared overhead
specification now derives its display domain from the unchanged valid results
and the 1× reference. Missing rows supply only that reference, never a ratio
or interval. A singleton domain places the reference at the left edge so it
does not cross long safety-deferral notes.

The 96-case regression preserves every case label, rejects invented estimates,
and requires warning-free rendering. All nine figure tests pass. Actual
Luminal and Eggcc exports passed 180-mm inspection, including long deferral
notes; the measured Math, SpEQ, DialEgg, and Churchroad PNGs remain byte-identical
to the prior exports. Evidence is in `figures/review/empty-family-20260922/`.
An unchanged expanded Make invocation leaves all 27 generated data/image
files and the measurement cache unchanged, including file modification times.


## Completed collection and independent redesign — 2026-09-23

The refreshed cache contains 6,373 rows. The expanded corpus now supplies 59
complete Egglog recording/extraction versus off comparisons (30 successful
observations per condition). Failed and unavailable cases remain explicit in
all eight full-family figures and the accompanying coverage gallery. The
compact interval atlas is conditional on validated, complete results; it must
be published with that coverage, not treated as the full source population.

Rechecked all 16 archived CSE 512 deck hashes and revisited their page-indexed
text, with close reading of encoding, perception, uncertainty, color, evaluation,
and deceptive-visualization material, plus the public assignment criteria.
This was not a new visual inspection of every slide or a controlled reader
study. The independent reviewer used concrete named-case lookup and comparison
tasks, not appearance alone.

For Math, compared the prior four panels, proof-setting panels with overlaid
engines, engine panels with overlaid proof settings, and a mean-time scatter.
Selected the proof-setting panels: fixed-cutoff engine comparisons require
less eye movement, and raw run variation remains visible. The scatter crowds
early cutoffs and removes raw spread. Revised the initially pale dot legend
to opaque solid/dashed strokes and replaced the cryptic safety-stop marker
with a complete, data-derived explanation. The native Egg proof condition at
cutoff 11 retains 29 successful dots and its failed observation; no mean is
manufactured. The separate original cutoff-11 figure now says completed runs
and memory stop rather than the contradictory-looking selected-run count.

For overhead, compared the full per-family interval plots, a two-page interval
atlas, and a runtime-versus-ratio scatter with vertical confidence intervals.
Selected the interval atlas with exact numeric bounds. The scatter answers a
secondary absolute-cost question but fails named-case lookup and hides narrow
intervals. Removed filled points, retained thin interval caps, used natural
Math cutoff order, and shared one numerical log domain across pages. Removing
repeated axes/headers and using 17-pixel rows brings both pages within a normal
180-mm-wide manuscript page. Thousands now use readable comma-grouped integers.

The facet prototype initially collapsed its x scale and placed its numeric
column over the data because explicit width/height expressions resolved at the
parent scope. Corrected these positions and the 1x reference geometry; a
regression now checks nonzero scale range, numeric-column clearance, and full
reference height. Vega-Lite emits a conservative compile warning for the
independent facet domains assembled from filtered/folded copies of the same
case field. That specific warning is documented in the test; the source,
resulting rows, scales and geometry are verified rather than treating it as an
unexplained data-source union.

The final independent review passed the Math and both overhead pages at 180 mm
in color, grayscale, protanopia and deuteranopia simulations. Both overhead
pages fit (approximately 240 and 256 mm tall at that width). At 85 mm, labels
and confidence-bound lookup remain unreliable; that size is unsupported.

An independent numerical audit compared 2,060 actual values/null expectations
against the existing Python benchmark statistics: 1,319 Math raw dots, 43 valid
means, 59 ratios with Fieller intervals, and 229 unavailable case/call ratios.
Maximum relative numerical difference was 2.27e-14. The atlas reuses the same
statistical transform prefix, enforced by regression tests. Python adds only
family/page membership and rebases provenance indices; it does not calculate
performance statistics. One atlas spec renders both raw-data page projections.

Guarded `make check` passed. All eleven Vega numerical/rendering tests and
focused projection/Make tests passed, including temporary-cache preservation,
source-index rebasing and selective atlas rebuilds. The measurement cache and
release executable identities remain unchanged. Local artifacts, alternatives,
reading answers, source hashes, guard logs, and the frozen gallery are in
`review/refreshed-20260923/`.
