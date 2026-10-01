# Figure review criteria

This rubric applies course principles to these two benchmark questions. Page
numbers below are **1-based PDF pages**, including title and exercise pages.
URLs and hashes are pinned in [manifest.json](manifest.json); the linked PDFs
are restored by `download.py`. The criteria and manuscript dimensions are our
operational choices, not an endorsement by the instructors.

| Criterion | Evidence | Check for these figures |
| --- | --- | --- |
| Give the image a clear question and enough context to stand alone | [Assignment 1](https://courses.cs.washington.edu/courses/cse512/26sp/a1.html) asks for a question or answer in the title, a self-contained graphic, and a rationale for design choices. | Use a question title until an answer is supported by the measurements. Include the workload, units, treatments, and uncertainty meaning in the image itself; explain what each design emphasizes or obscures. |
| Require every element to serve a reading task | [Assignment 1](https://courses.cs.washington.edu/courses/cse512/26sp/a1.html) asks authors to justify each element; [Evaluation, pp. 24–27](slides/CSE512-Evaluation.pdf#page=25) shows that extra information can distract while useful labels improve interpretation. | Ask what becomes harder or ambiguous if an element is removed. Remove redundant encodings and prose; move reproduction details to an accompanying caption. Keep useful redundancy, such as exact interval labels, when a reduced alternative fails the task. |
| Ask an answerable question; iterate | [Introduction, p. 30](slides/CSE512-Introduction-26sp.pdf#page=30) describes graphics/question/refinement cycles; [Evaluation, p. 4](slides/CSE512-Evaluation.pdf#page=4) distinguishes inspection, informal studies, and controlled experiments. | State each figure's workload and timing boundary. Compare alternatives using the same reader tasks; record what changed and why. Call a self-review an inspection, not a user study. |
| Prefer accurate quantitative comparisons | [Visual Encoding, pp. 11-16, 24](slides/CSE512-VisualEncoding-26sp.pdf#page=24) and [Perception, pp. 3-5, 30](slides/CSE512-Perception-26sp.pdf#page=30) cover expressiveness and aligned-position accuracy. | Encode time and ratio as position on a shared axis. Reserve color/shape for categories. Do not imply paired runs, seven separate Math benchmarks, or quantitative significance in jitter position. |
| Match scales to the task | [Visual Encoding, pp. 76, 78, 83-88](slides/CSE512-VisualEncoding-26sp.pdf#page=78) discusses baseline meaning, ticks, and multiplicative log scales. | Label seconds versus multiplicative slowdown. Show a clear 1x baseline for ratios; include the whole visible interval. Use understandable ticks. Explain log scales; never turn an invalid interval into a bounded line by clipping. |
| Keep individual variation and uncertainty distinct | [Uncertainty, pp. 10-16, 43-46, 54](slides/CSE512-Uncertainty-26sp.pdf#page=16) discusses interval interpretation, frequency-based displays, and inferential failures. | Dots are observed process runs, not posterior samples. Label mean and 95% intervals precisely. Readers must distinguish wide run variation from uncertain mean estimates and identify missing results. Avoid a claim of equivalence from overlapping intervals. |
| Make transformations inspectable | [Tools, Part 1, pp. 5, 9-12](slides/CSE512-ToolsPart1-26sp.pdf#page=5) describes data/transforms/scales/marks; [Data Transformation, pp. 24-29, 71](slides/CSE512-DataTransformation.pdf#page=24) covers filtering, grouping, and data-quality hurdles. | Each specification names its source JSON. Inspect treatment filters, group keys, counts, arithmetic means, sample variances, and ratio calculations. Retain failures and input provenance. Label ECDF and boxplot summaries rather than implying they are mean confidence intervals. |
| Preserve meaning without color | [Color, pp. 6-8, 25](slides/CSE512-Color.pdf#page=25) discusses color-vision simulation, distinguishability, and monochrome printing. | Read both figures in grayscale and protanopia/deuteranopia simulations. Endpoint identity must survive through labels, position, or shape. Check interval and point contrast against both background and each other. |
| Avoid persuasive presentation without evidence | [Deceptive Visualization, pp. 20, 27, 32, 51-52](slides/CSE512-DeceptiveVisualization.pdf#page=52) covers invalid encoding, illegibility, and unsupported conclusions. | Do not tune ordering, domain, cropping, or omissions to make a target such as 5x appear satisfied. A threshold line is not a conclusion. Preserve slow workloads and incomplete data in the rendered story. |
| Evaluate the actual publication size | [Evaluation, pp. 65, 67-68, 77, 87-88](slides/CSE512-Evaluation.pdf#page=65) examines chart size, task context, and measures beyond preference; [Visual Encoding, p. 78](slides/CSE512-VisualEncoding-26sp.pdf#page=78) includes label legibility. | Inspect 85 mm and 180 mm exports at intended physical size, not only magnified previews. Check long workload names, tick overlap, interval caps, dense dots, caption independence, and the complete PNG/SVG bounding box. |

The remaining archived decks provide broader course coverage (interaction,
maps, animation, networks, scalability, and project discussion). Their
availability does not require adding interaction, animation, or additional
encodings to these static manuscript figures.

## Reader tasks

Use the same tasks for canonical and alternative designs. Record answers and
specific points of hesitation. At both 85 mm and 180 mm, a reviewer should be
able to:

1. Identify the two engines/treatments, the unit, and the extraction-inclusive
   measurement boundary without relying on tooltips.
2. For Math, identify which endpoint has the lower observed times, describe
   spread and overlap, and explain why the dots are repeated runs of one
   workload. Locate the sample count and distinguish dots from a mean interval.
3. For overhead, locate a named workload, interpret 1x and the numerator,
   identify the largest estimated slowdown, and read its 95% interval without
   confusing point estimate and upper bound.
4. Identify every missing/failed comparison and determine that the chart does
   not establish a cross-workload average or a universal slowdown guarantee.
5. Repeat endpoint identification and interval reading in grayscale and the
   two color-vision simulations. No conclusion should depend only on hue.

Treat inability to answer a task, clipped marks/labels, ambiguous interval
meaning, or failure to show missing data as a defect requiring revision.
Do not invent reader-study scores: record who reviewed, whether this was
self-inspection, and what was actually observed. If only one physical width
is usable, report that limitation and designate the supported width.

## Iteration record

Copy this for each comparison or meaningful revision:

```text
Date / reviewer / inspection or user study:
Data JSON hashes / specification revisions:
Designs compared:
Question each design answers:
Widths inspected: 85 mm / 180 mm
Display checks: color / grayscale / protanopia / deuteranopia
Reader-task observations (correctness, hesitation, ambiguity):
Numerical checks (counts, filter identity, mean and ratio/CI agreement):
Integrity checks (all workloads, failures, unclipped uncertainty, caption):
Defects and changes made:
Reason to retain/reject each alternative:
Follow-up rendering and reader-task result:
Remaining limitations:
```

For the Math chart, compare the raw dot display against ECDF and boxplot
alternatives. ECDFs make cumulative proportions easy to inspect; boxplots
compress the distribution and therefore need clear summary definitions. For
the overhead chart, compare ratio ordering against suite order: ranking
supports finding extremes, while fixed suite order supports locating known
workloads. Record the task tradeoff instead of claiming a universally best
chart.
