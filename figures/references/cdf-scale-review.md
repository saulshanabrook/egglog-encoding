# Choosing a scale for the proof-overhead distribution

For a talk, prefer a **linear 0–6× detail with a smaller, complete overview**
for each metric. Keep full-range log as the compact alternative when there is
only room for one panel per metric. Full-range linear alone obscures too much
of the distribution in this snapshot.

This recommendation comes from course and primary-source research, actual
render comparisons, and independent agent inspection. It is a design judgment,
not the result of a reader study or a layout prescribed by CSE 512.

The controlled design comparison below uses a frozen preliminary snapshot.
After collection finished, the cached projections were refreshed and the
preferred design was also applied to the
[current recording data](../review/recording-current/proof-recording-cdf.1280.png).
That newer view has 441 complete ten-run comparisons out of 442 selected
replays, with one MISAAL host-memory interruption. Its approximate 50%/90%
coverage thresholds are 3.62×/3.97× runtime and 3.05×/3.34× peak memory. The
change from the preliminary thresholds below is due to completed measurements,
including 39 HardBoiled comparisons, rather than an axis or denominator change.

## Question and data boundary

The reading task is: **How much overhead does proof recording add, and what
share of the selected workloads is at or below a given ratio?** Runtime and
peak memory use separate panels; colors identify workload families within one
pooled ranking. The curves are not separately normalized family distributions.

All alternatives use the same frozen
[`recording-preliminary.data.json`](../review/talk-20260929/recording-preliminary.data.json),
SHA-256 `b66bc5209d9ae58fc4994d89799ae734fa7f4820a38af94e831f1796a9f525f5`.
There are 442 selected replays, each with 10 successful proofs-off observations
and mean off runtime strictly between 0.1 and 30 seconds. Memory does not
select the cohort. There are 402 displayed recording/off comparisons with
5–7 recording observations; 39 HardBoiled comparisons have too few recording
observations and one MISAAL comparison has a host-memory interruption. This
is a preliminary recording-only view, without proof extraction or confidence
intervals. It does not replace the canonical ten-observation requirement.

Every view retains the denominator of 442. Consequently, the measured curve
ends at 402/442 = 90.95%, with 40 outcomes unavailable. The 50% and 90% guides
are **observed coverage of the selected cohort**, not confidence levels or
settled full-cohort percentiles. In particular, the 90% guide uses rank 398 of
402 displayed estimates, rather than the 90th percentile of those 402 alone.
Remaining measurements can change the thresholds.

| Frozen-snapshot statistic | Runtime ratio | Peak-memory ratio |
| --- | ---: | ---: |
| 50% selected-cohort coverage | 3.6921× | 3.0829× |
| 90% selected-cohort coverage | 5.6780× | 3.5930× |
| Largest displayed ratio | 24.0708× | 12.4839× |
| Displayed estimates above 6× | 3 | 2 |

The current full linear runtime view allocates only 14.45% of its width to
1–5×. The 0–6× detail allocates 66.67% to that region. The detail limit is a
viewing choice, not a workload filter or a claim that everything is below 6×.
Six rather than five also keeps the current runtime 90% crossing visible.

## Evidence and implications

Page numbers below are one-based PDF pages. The archived source URLs and
hashes are in [`manifest.json`](manifest.json).

| Primary source | What it supports | Application here |
| --- | --- | --- |
| [CSE 512 Visual Encoding, pp. 79–88](https://courses.cs.washington.edu/courses/cse512/26sp/lectures/CSE512-VisualEncoding-26sp.pdf#page=79) | Scale choices include clipping, breaks, and logarithms; logarithms support multiplicative comparisons and increase resolution for skewed distributions, with audience familiarity a consideration. | Log is a defensible full-range view. Linear detail makes additive threshold readings simpler for a talk. |
| [CSE 512 Interaction, p. 109](https://courses.cs.washington.edu/courses/cse512/25sp/lectures/CSE512-Interaction.pdf#page=109) | A concrete overview-and-detail example links the selected region to an enlarged view. | Adapt this to static adjacent views and visibly shade the enlarged region in the overview. |
| [CSE 512 Deceptive Visualization, pp. 43–52](https://courses.cs.washington.edu/courses/cse512/25sp/lectures/CSE512-DeceptiveVisualization.pdf#page=43) | Both exaggerated truncation and overly broad scales can impair interpretation; context matters. | Zoom is acceptable when labeled and accompanied by complete context. Hidden tail removal would be misleading. |
| [CSE 512 Perception, pp. 29–31](https://courses.cs.washington.edu/courses/cse512/26sp/lectures/CSE512-Perception-26sp.pdf#page=29) | Position on common scales supports quantitative comparisons. | Use the same 0–6× detail domains and the same full-range overview domains for runtime and memory. Preserve 0–100% y-scales. |
| [CSE 512 Uncertainty, pp. 44–54](https://courses.cs.washington.edu/courses/cse512/26sp/lectures/CSE512-Uncertainty-26sp.pdf#page=44) | Distribution and uncertainty representations require interpretation appropriate to the question and audience. | A CDF of ratio estimates is not a confidence interval for a ratio. Keep missing data and preliminary status explicit. |
| [CSE 512 Evaluation, pp. 65–88](https://courses.cs.washington.edu/courses/cse512/25sp/lectures/CSE512-Evaluation.pdf#page=65) | Evaluate graphics against concrete tasks, display size, and context. | Inspect rendered slide-size PNGs, not just specifications. Describe this as inspection, not a comprehension experiment. |

The relevant lectures were reread for this decision; this was not another
complete pass through every slide in all sixteen decks. The broader previous
course review is preserved in [`course-review.md`](course-review.md).

Two public implementations illustrate the alternatives. The official
[Vega-Lite overview-and-detail example](https://vega.github.io/vega-lite/examples/interactive_overview_detail.html)
puts a large detail view above a short complete overview and binds the detail
domain to the overview selection. The official
[Matplotlib zoomed-inset example](https://matplotlib.org/stable/gallery/subplots_axes_and_figures/zoom_inset_axes.html)
uses a rectangle to identify which region is enlarged. These support a visible
link between views; our preference for separate static strips over an inset
is an inference based on this figure's dense points and export size.

The foundational [Shneiderman overview/zoom paper](https://www.cs.umd.edu/users/ben/papers/Shneiderman1996eyes.pdf)
also motivates preserving context while examining detail. For implementation,
[Vega-Lite's scale documentation](https://vega.github.io/vega-lite/docs/scale.html#example-clipping-or-removing-unwanted-data-points)
distinguishes clipping marks from filtering data. Our zoom uses a domain and
clipping **after** computing pooled ranks and shares. It does not rerank or
renormalize the visible points.

## Alternatives inspected

| Alternative | Strength | Limitation | Decision |
| --- | --- | --- | --- |
| [Full-range linear](../review/talk-20260929/recording-preliminary.png) | Familiar spacing; all measured extremes visible. | Most runtime differences occupy a narrow strip; the tail consumes most of the width. | Retain as a comparison, not the preferred main view. |
| [Full-range log](../review/talk-20260929/scale-options/full-range-log.1280.png) | Compact, complete, and consistent for multiplicative comparisons. | Equal absolute ratio differences have unequal spacing; requires logarithmic-axis reading. | Strong single-panel alternative. |
| [Linear zoom plus overview](../review/talk-20260929/scale-options/linear-zoom-overview.1280.png) | Enlarges the dense region; preserves visible full context and requested coverage crossings. | Adds axes and panels; needs careful space allocation. | Preferred talk design after compacting the first version. |
| Zoom alone | Simple detail. | Hides known tail observations. | Reject for this figure. |
| Broken axis or nonlinear custom compression | Can fit bulk and tail together. | Adds a scale discontinuity or a less familiar transform to decode. | No advantage over explicit separate views for this task. |
| Inset over the chart | Conventional way to connect detail and overview. | Risks obscuring points and creating small labels in slide exports. | Prefer the separate overview strip here. |

No design advantage is inferred from a change in measurements: every rendered
alternative uses identical observations and calculations.

## Iteration and acceptance checks

The first zoom render was 1280×888. Inspection found clear 50%/90% readings
but unnecessary height, independently scaled overviews, and only approximate
readings of the extremes. A second revision uses a compact slide layout,
common full-range domains, explicit maximum labels, and concise qualifications.
The 0–6× main scale is shared between metrics; the complete overview retains
all tail points, with the main viewing range shaded.
The revised frozen-snapshot PNG is 1280×652, fitting a 1280×720 slide without
scaling down. Root and the rendering agent inspected the local PNG; all four
threshold labels, every main-axis tick, both maximum labels, and the missing
outcome qualification are readable. The independent reviewer identified the
first version's scale and sizing problems; this is an informal review loop.
The independent reviewer accepted the compact frozen-snapshot layout after
revision. Root also inspected the updated 441/442 render at 1280×652: the
HardBoiled points now appear in green, the revised coverage labels are legible,
and the one unavailable result remains explicit. Its
[`audit.json`](../review/recording-current/audit.json) verifies actual rendered
point and label data, identical detail/overview ranks, complete overview bounds,
and exact ten-run eligibility inherited from the canonical specification.
The user subsequently identified clipped tops on the 90% labels, which the
initial visual inspection missed. The corrected render moves the labels down,
disables clipping for annotation text, and checks actual glyph bounding boxes
against the panel boundary. Checking point coordinates and label contents alone
was insufficient to establish that the exported text was intact.

Acceptance tasks for the final render are:

1. Read ratio direction, the 1× reference, and the detail/overview domains.
2. Read the 50% and 90% crossings in both metrics without a legend lookup.
3. Find the tail maxima and counts beyond the zoom.
4. Explain the 90.95% curve endpoint and distinguish unknown outcomes from
   measured tail observations.
5. Recognize that changing the viewing window does not change the cohort.

The quantitative audit checks every ratio against independent means, 402
distinct estimates per metric, the 442 denominator, the coverage endpoint,
and nearest-rank thresholds. Rendering scripts and evidence are beside the
prototype specifications in
[`scale-options/`](../review/talk-20260929/scale-options/).
The palette is unchanged; the neutral curve and direct quantitative labels
carry the distribution independently of color. Individual family identification
still relies on color, so these figures do not promise grayscale identification
of every workload family.

For final complete-sample figures, reuse this design principle with the actual
current cohort and dynamic full-range bounds. Do not hard-code this snapshot's
442 count, 25× upper bound, partial-sample eligibility, or preliminary thresholds
into canonical collection or figure preparation.
