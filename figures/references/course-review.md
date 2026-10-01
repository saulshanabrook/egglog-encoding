# Course-wide review of the performance figures

Reviewed 21 September 2026 against
[UW CSE 512, Spring 2026](https://courses.cs.washington.edu/courses/cse512/26sp/).
This is a course-grounded inspection by an implementation agent and independent
review agents. It is not a human reader study, a course grade, or evidence that
the design is uniquely optimal.

The objective is the smallest presentation that still supports the intended
reading tasks. Removing an element is an improvement only if the reader keeps
the information needed to interpret and compare the measurements.

## Coverage

All **16 public slide decks, 1,279 PDF pages**, were reread as page-indexed text.
Visual inspection supplemented text extraction: all Introduction and Final
Project pages were viewed in contact sheets; the image-heavy Deceptive
Visualization deck was inspected throughout; representative figures and
image-only examples were checked in the other decks. Embedded demonstrations
and videos were not treated as watched lectures. All 16 archived PDF hashes
were verified against [the manifest](manifest.json).

The following references use one-based PDF pages. The decisions are our
application of the teaching material to this benchmark task, rather than
rules that the course states specifically about these figures.

| Deck | Evidence and implication for these figures |
| --- | --- |
| [Introduction](slides/CSE512-Introduction-26sp.pdf#page=30), 75 pages | Pages 8–10 show why summary statistics can conceal data shape; pages 14–30 compare designs for different questions and advocate iteration. Preserve raw Math observations and judge alternatives against the same tasks. |
| [Tools, Part 1](slides/CSE512-ToolsPart1-26sp.pdf#page=5), 46 pages | Pages 5–12 separate data, transforms, scales, guides, and marks; page 20 illustrates overlap in strip plots. Keep explicit JSON inputs, inspectable Vega-Lite transforms, and a sample-count label. |
| [Visual Encoding](slides/CSE512-VisualEncoding-26sp.pdf#page=24), 90 pages | Pages 11–17 distinguish truthful from effective encoding; pages 24–28 favor aligned position, 78 covers ticks, and 83–90 covers log scales and excessive encoding. Keep shared positional scales; reduce ticks and redundant color. |
| [Deceptive Visualization](slides/CSE512-DeceptiveVisualization.pdf#page=51), 55 pages | Pages 15–19 expose aggregation/denominator choices; pages 43–52 show context-dependent scale failures. Preserve ratio direction and all workloads; do not crop or omit results to support a universal slowdown claim. |
| [Data Transformation](slides/CSE512-DataTransformation.pdf#page=24), 124 pages | Pages 24–29 separate filtering, projection, aggregation, and sorting; page 71 addresses missing data; pages 82–90 compare distributions. Keep failures and expected groups; retain raw dots without adding density estimation. |
| [Interaction](slides/CSE512-Interaction.pdf#page=94), 109 pages | Pages 28, 52, 66, and 94 connect provenance and interaction to tasks. Essential information must work without hovering; these static comparisons need no brushing or filtering controls. |
| [Maps](slides/CSE512-Maps.pdf#page=18), 58 pages | Pages 18 and 34–43 connect abstraction/projection to the relationship being preserved. Preserve runtime position and ratio distance. There is no geographic variable, so no map-related encoding is applicable. |
| [Tools, Part 2](slides/CSE512-ToolsPart2-26sp.pdf#page=61), 79 pages | Pages 56 and 61–64 support limited features and portable declarative specifications. Stay in Vega-Lite; remove unused Math variance computation rather than adding another rendering framework. |
| [Animation](slides/CSE512-Animation-26sp.pdf#page=29), 91 pages | Pages 29–30 discuss distraction and false relations; pages 50–63 address faithful transitions and task-dependent performance. Keep all results simultaneously visible; do not animate or connect unpaired runs. |
| [Color](slides/CSE512-Color.pdf#page=25), 52 pages | Pages 6–8, 25, 29–34, and 52 address accessibility, consistent meaning, and restrained palettes. Direct row labels already identify engines; one data hue avoids an unnecessary, inconsistent mapping across figures. |
| [Graphical Perception](slides/CSE512-Perception-26sp.pdf#page=33), 77 pages | Pages 26–39 distinguish accurate positional reading and useful redundancy; pages 60–69 cover grouping/transparency. Keep mean ticks and the numeric interval column because they support tasks distinct from raw spread and graphical comparison. |
| [Final Project & Perception Exercise](slides/CSE512-FinalProject-26sp.pdf#page=14), 21 pages | Page 14 asks for success criteria, alternatives, and feedback; pages 15–21 demonstrate change blindness. Preserve before/after artifacts and compare actual exports rather than relying on memory. |
| [Networks](slides/CSE512-Networks-26sp.pdf#page=65), 102 pages | Pages 3–4 distinguish relational data; pages 65 and 69–90 discuss overlap, selective encoding, and task-dependent layouts. These are timing observations, not graph edges. No network layout or force simulation is needed. |
| [Uncertainty](slides/CSE512-Uncertainty-26sp.pdf#page=10), 63 pages | Pages 9–17 require named uncertainty and correct interval interpretation; pages 43–59 address distribution displays and inferential failures. Keep 95% intervals visible, label dots as observations, and preserve unavailable results. |
| [Scalability](slides/CSE512-Scalability-26sp.pdf#page=35), 130 pages | Pages 5, 35–37, and 113–124 address visual resolution, lost extremes, and sampling assumptions. These small datasets need neither approximation nor a data service. Preserve every selected Math run and state sampling limits in the methods. |
| [Evaluation](slides/CSE512-Evaluation.pdf#page=25), 107 pages | Pages 4, 14–27, 65–78, and 87–88 distinguish inspection from studies and emphasize task, labels, and size. Test actual reading tasks at the intended width; do not equate preference or fewer marks with better comprehension. |

### Coursework, notebooks, and readings

The public [A1](https://courses.cs.washington.edu/courses/cse512/26sp/a1.html),
[A2](https://courses.cs.washington.edu/courses/cse512/26sp/a2.html),
[A3](https://courses.cs.washington.edu/courses/cse512/26sp/a3.html),
[A2 peer review](https://courses.cs.washington.edu/courses/cse512/26sp/a2-review.html),
and [A3 peer review](https://courses.cs.washington.edu/courses/cse512/26sp/a3-review.html)
pages were read in full, as were the final-project, deliverables, video-guide,
and resources pages. A1's requirement to justify each element directly informs
the table below. A2 motivates checking omissions and implied conclusions;
the peer-review tasks motivate concrete, actionable checks. The interactive
assignment does not require adding interaction to this static-paper task.

All markdown and code in seven course-approved
[Python notebook alternatives](https://github.com/uwdata/visualization-curriculum)
were read: introduction, marks/encodings, scales/axes/legends, view composition,
transformations, interaction, and cartography (**487 cells**). They were not
executed, and not every example output was visually inspected. A later ordinary
public-browser visit also loaded [D3 Part 1](https://observablehq.com/@uwdata/introduction-to-d3-part-1)
and [Part 2](https://observablehq.com/@uwdata/introduction-to-d3-part-2). Their complete instructional
prose, visible code, and example charts were inspected. Long or closed source
cells remain partially reviewed, and the exercises were not performed. The
earlier failed export requests do not imply that these public page bodies
remain unavailable.

All **76 schedule reading entries** were inventoried (34 required, six
encouraged, 36 optional). The complete bibliography was not read. The initial
close reading focused on sources that bear on these figures; the continuation
also covered accessible required readings across the other course topics.
Full main-body coverage below excludes recursively reading cited references
or reproducing the original experiments.

| Reading | Coverage and consequence |
| --- | --- |
| [Card, Mackinlay, and Shneiderman, Information Visualization](https://magrawala.github.io/cs448b-fa17/assets/docs/CardMackinlaySchneid-Chap1.pdf) | All 35 scanned PDF pages, including printed chapter pages 1–34, figures, and tables. Individual facts, comparisons, and patterns can need different representations. Numeric interval labels and graphical marks have distinct purposes; the raw-data-to-view stages should remain inspectable. |
| [Wattenberg and Viégas, Design and Redesign](https://medium.com/@hint_fm/design-and-redesign-4ab77206cf9) | Full main article. A cleaner view can lose information or favor a known conclusion; compare the same data and state the task before choosing a design. |
| [Correll and Gleicher, Error Bars Considered Harmful](https://graphics.cs.wisc.edu/Papers/2014/CG14/Preprint.pdf) | Full main body. Its bar-plus-error studies do not establish that this Fieller interval plot needs a violin or that raw-run spread is inferential uncertainty. Keep interval meaning explicit. |
| [Munzner, A Nested Model](https://www.cs.ubc.ca/labs/imager/tr/2009/NestedModel/NestedModel.pdf) | Full main body. Check the domain question, data/task abstraction, visual encoding, and algorithm separately. Correct calculations do not establish readability. |
| [Cleveland and McGill, Graphical Perception](https://faculty.washington.edu/aragon/classes/hcde511/s12/readings/cleveland84.pdf) | Full main body, journal pages 531–553, including the previously omitted experimental detail and figures. Aligned positions aid comparisons; exact number lookup and pattern recognition are different tasks. The experimental ordering is evidence about particular tasks, not proof that a complete chart is optimal. |
| [Heer and Bostock, Crowdsourcing Graphical Perception](https://idl.cs.washington.edu/files/2010-MTurk-CHI.pdf) | Full main body, PDF pages 1–10. Grid and size effects depend on task/stimulus; test these actual figures instead of importing universal pixel thresholds. Their participant experiments also clarify why this agent inspection must not be reported as measured human reading performance. |
| [Franconeri et al., The Science of Visual Data Communication](https://faculty.sites.iastate.edu/tesfatsi/archive/tesfatsi/ScienceOfVisualDataCommunication.FranconeriEtAl2021.pdf) | Full main body, PDF pages 1–41 (journal pages 110–150), and all 27 numbered figures; the corrigendum was reviewed separately. Encoding rankings, minimalism, and uncertainty displays depend on task and audience. Keep useful context and distinguish estimator uncertainty from individual outcomes. |
| [Muth/Rost, Which Color Scale to Use](https://www.datawrapper.de/blog/which-color-scale-to-use-in-data-vis) | Full main article. The need for hue depends on what the other channels already communicate; directly labeled engine rows can share a color. |
| [Elliott, 39 Studies](https://medium.com/@kennelliott/39-studies-about-human-perception-in-30-minutes-4728f9e31a73) | Main synthesis read, not all cited studies. Its task-specific cautions reinforce using the primary evidence above rather than treating summaries as universal prescriptions. |
| [Stolte et al., Polaris](https://graphics.stanford.edu/papers/polaris_extended/polaris.pdf) | Full main body, PDF pages 1–13 of the extended TVCG article; key layering and transformation figures inspected. Make each layer's grouping and aggregation explicit. No extra interactive view follows. |
| [Heer and Shneiderman, Interactive Dynamics](https://idl.cs.washington.edu/files/2012-InteractiveDynamics-CACM.pdf) | All ten PDF pages and key figures. Sorting serves a task; recorded state supports revisiting and sharing an analysis. Preserve identical measurements across alternatives without adding unnecessary controls. |
| [Bostock et al., D3](https://idl.cs.washington.edu/files/2011-D3-InfoVis.pdf) | Full main body, PDF pages 1–8, and key figures. Inspectable web-standard output is useful; replacing the working declarative specifications with D3 is unnecessary. |
| [Battle and Scheidegger, Structured Review](https://homes.cs.washington.edu/~leibatt/static/papers/battle2020structured.pdf) | Full author-manuscript main body, PDF pages 1–8, and the taxonomy figure. Retain analysis and source provenance. Database acceleration and approximate queries have no demonstrated purpose for these small fixed datasets. |
| [Moritz et al., Falcon](https://idl.cs.washington.edu/files/2019-Falcon-CHI.pdf) | Full main body, PDF pages 1–10, with algorithm/evaluation figures and timing table. Interpolation error, interaction latency, and repeat-run uncertainty are different quantities. Preserve raw observations without progressive approximation. |
| [Dent, The Cartogram](https://magrawala.github.io/cs448b-fa17/assets/docs/Dent-Chap11.pdf) | All 15 scanned pages, including the main body, 12 figures, table, and glossary. Match transformations to the reader's task and keep unplottable cases identifiable. These timings have no geographic relationship requiring an area-based map. |
| [Hullman, The Visual Uncertainty Experience](https://openvisconf.com/2016/#transcripts) | Complete conference-provided transcript read; the video and demonstrations were not watched. Observed values, sampling distributions, and hypothetical outcomes are distinct. Do not relabel the raw runs as simulated ratio uncertainty or add a predictive animation for this static lookup task. |
| [Wattenberg et al., How to Use t-SNE Effectively](https://distill.pub/2016/misread-tsne/) | Entire article and representative interactive diagrams; not every parameter combination. Its nonlinear embedding cautions are algorithm-specific. Here horizontal position is measured time and vertical displacement is layout, with no embedding or inferred pairing. |
| [Robertson et al., Effectiveness of Animation in Trend Visualization](https://www.cc.gatech.edu/~john.stasko/papers/infovis08-anim.pdf) | Full main body, PDF pages 1–8, and key stimuli/results figures. Static comparisons suit these tasks; enjoyment and measured reading accuracy are different criteria. Supplementary videos were not watched. |
| [Easing Functions Cheat Sheet](https://easings.net/) | Complete explanatory text, all 30 curve thumbnails, and one full implementation detail panel. Not every animation or implementation was tested. Easing controls motion; it has no role in transforming these measured times or bounds. |
| [Szafir, Modeling Color Difference](https://www.danielleszafir.com/colordiff_vis2017.pdf) | Full main body, PDF pages 1–9, with key experimental figures. Color discriminability depends on mark geometry and context. Inspect the actual small translucent dots; a named palette alone cannot establish their accessibility. |
| [Bruls et al., Squarified Treemaps](https://diglib.eg.org/server/api/core/bitstreams/c1c7da22-085b-4714-90d8-fe6094b8d886/content) | All ten PDF pages and key layout figures. Runtime ratios do not form a hierarchy of additive sizes. Replacing their shared positional scale with rectangle area would answer a different question. |
| [Holten, Hierarchical Edge Bundles](https://www.cs.jhu.edu/~misha/ReadingSeminar/Papers/Holten06.pdf) | All eight PDF pages and key bundling figures. These samples have no hierarchy-plus-adjacency relationships. Connecting runs would imply unsupported relations. |
| [Lam et al., Seven Scenarios](https://petra.isenberg.cc/publications/papers/Lam_2012_ESI.pdf) | Full main body, PDF pages 1–15, appendix pages 19–20, and summary figure/table. Set communication and lookup goals before choosing evaluation methods. An expert inspection cannot establish population reading speed or comprehension. |

Public author, publisher, and institutional copies closed the required-paper
and chapter gaps despite the original UW reading links requiring login. The
remaining required-reading limits are the four Tufte chapters, which had no
public full-text course link and were not read; partially exposed source cells
in the two D3 notebooks; and the uncertainty talk reviewed by transcript,
without watching its video. Private lecture recordings remained unavailable.
The notebook exercises were not completed. Optional and encouraged readings
were not exhaustively covered, and unread sources were not used as supporting
evidence. These coverage limits qualify the course review, not the numerical
benchmark results.

The continuation's full notes, public source copies, and source checksums are
kept locally under `review/course-continuation/research/`. Their coverage notes
supersede the earlier partial-reading entries in the archived initial review;
the earlier archive remains intact as a record of that stage.

## Element-by-element decisions

| Element | Decision and necessity |
| --- | --- |
| Question titles | Keep, on one line. They identify the task without asserting a result that could become stale after new measurements. |
| Math workload and treatment | Keep the Rational Math description, one-e-graph scope, recording/extraction boundary, and succinct no-backoff context. These prevent materially different interpretations. |
| Raw Math dots | Keep all selected successful runs. Their spread and extremes are part of the requested evidence. |
| Vertical displacement and transparency | Keep small, deterministic offsets and translucent circles to expose overlap; vertical position is not another measured variable. |
| Black mean ticks and mark key | Keep. They support the central-runtime comparison while the dots show individual runs. |
| Engine colors | Replace the two-hue category code with one hue. Directly labeled rows already identify the engines. |
| Math grid and ticks | Remove the grid and use whole-second ticks. Approximate runtime reading still succeeds; the shared zero-based axis remains. |
| Long Math footer | Move timeout, internal limits, verification exclusion, and source details into the supplied caption. Retain one line for requested sample count and mark meaning. |
| Ratio log scale and 1× reference | Keep. Multiplicative distance and the unchanged-runtime reference are necessary; label the reference “equal.” |
| Descending workload order | Keep. It supports finding the largest and smallest change without an extra highlight or callout. |
| Confidence intervals | Keep true bounds with endcaps and no large point covering them. Never widen an interval for visual effect. |
| Numeric ratio/CI column | Keep, rounded to three significant digits. It supplies explicit estimates and precise displayed bounds that the narrow graphical intervals cannot support alone. |
| Repeated explanatory prose | Remove the separate statement that numbers are listed at right and the repeated interval explanation. Column alignment/header and one uncertainty definition suffice. |
| Fieller and detailed source/method notes | Keep in the accompanying caption and methods. Their relocation does not change the statistical procedure or discard provenance. |
| Missing/failure annotations | Keep whenever needed. Minimality must not turn incomplete evidence into a successful comparison. |
| 5× threshold, suite average, animation, extra panels | Keep absent. They do not serve the accepted questions. |

## Iteration and acceptance

The baseline was preserved locally under `review/course-review-before/`.
The first candidate shortened titles, removed Math's redundant color and grid,
reduced its row spacing and footer, and shortened the overhead text and numeric
precision. A second overhead candidate removed the numeric column entirely.
Both candidates used the same input data as the baseline.

The independent reviewer preferred the reduced versions with the numeric
column retained. The table-free candidate failed the required Herbie
estimate/interval lookup and removed the only explicit point-estimate encoding.
It was rejected even though it contained fewer marks. The reviewer also found
that the candidate subtitle named a wall time while displaying a ratio. The
final revision explicitly labels the ratio of mean wall times and groups its
numerator.

The final synthetic-data review exposed one consequence of reducing Math's
row spacing: its lower failure annotation touched the horizontal axis. Moving
the annotation six pixels upward restored clearance. The reviewer checked the
new export and accepted it, with no remaining concrete design objection.

The final gate uses the actual PNG/SVG exports and 85/180 mm screen proxies:
identify Math's faster engine and approximate times; read Herbie's estimate
and both bounds; identify the largest ratio and the runtime decrease; explain
1× and the mark meanings; and recognize missing/failed evidence. Grayscale
and color-vision simulations check that hue is unnecessary. Synthetic examples
are clearly labeled and are never performance evidence.

The independent review passed these tasks on the final exports at 180 mm:
Math was read as approximately 1.85 s for Egglog versus 2.95 s for Egg;
Herbie as 3.34× [3.28, 3.40]; Luminal as the largest ratio; and Churchroad as
the runtime decrease. Missing and failed comparisons remained explicit. The
retained caption preserves the method/source qualifications. Further
preference-only iteration was not required.

The four compiled-Vega tests continue to pass against the existing Python
statistics, including incomplete samples and undefined intervals. Data hashes
are unchanged. No observations were collected for this review. The unnecessary
Math variance aggregate was removed; ratio variances and Fieller calculations
are unchanged.

The supported publication width remains **180 mm**. At 85 mm, the broad pattern
survives but detailed labels and interval lookup do not. These are screen
proxies, not calibrated print tests. The inference remains conditional on the
collected workload/version/machine samples; this inspection adds no performance
evidence and establishes no universal runtime bound.

### Fresh review after acceptance

A new reviewer first read the canonical images without seeing the earlier
verdicts, then checked the source data, compiled marks, timing boundary, and
synthetic failure cases. The reader tasks passed again at 180 mm. All 60 Math
observations, two means, and ten overhead intervals were present. Independently
recomputed ratios and Fieller bounds agreed with the compiled transforms to
less than `6e-14` absolute error; the displayed rounded values also matched.
Fresh SVG compilation matched the existing exports, and the four focused tests
passed. Grayscale and color-vision checks exposed no new ambiguity.

The reviewer found no material defect or unnecessary remaining element. The
accepted figures were therefore retained. This continuation changes the
coverage record, not the measurements or chart specifications. Its detailed
independent audit is archived locally under
`review/course-continuation/research/fresh-review.md`.
