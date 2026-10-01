# Parameter-analysis figure

[SVG](parameter-analysis.svg) · [PNG](parameter-analysis.png) ·
[Vega-Lite specification](parameter-analysis.vl.json) ·
[grouped cache snapshot](../.reports-grouped.json)

The six rows compare one fixed logical input: 100,000 equality pairs, 10,000
random disequality pairs, and the paper driver's six fixed numeral disequalities.
Native engines read [`parameter-analysis.in`](../benchmarks/disequality/parameter-analysis.in);
Egglog reads the equivalent [`parameter-analysis.egg`](../benchmarks/disequality/parameter-analysis.egg).
DE uses Disegg; EE, NEE, and OEE use Egg; NE and EE use Egglog. The runner's
`nee` selector names the Egglog **NE** row. All endpoints disable proofs.

Horizontal position is whole-process wall time in seconds on a shared linear
scale starting at zero. Timing includes process launch, input I/O and parsing,
execution, terminal checks, and teardown. Input conversion happens before
collection; original native expression parsing remains inside the measured
executable. Compilation, input conversion, and report analysis are excluded.
These whole-executable times include startup and I/O, unlike the paper's
narrower internal timer boundary.

A dot is one successful finite observation. Small vertical offsets separate
dots and imply no pairing. Each black tick is the arithmetic mean of **all**
observations for the selected exact cache identity, provided every observation
succeeded and has a valid time. A single successful observation permits a mean;
there is no fixed sample-count requirement. The right column gives the mean
and sample count, or the missing/unsuccessful status. Failed samples and timeouts
remain in the snapshot and counts, suppress the mean, and are never plotted as
fast completions. No confidence interval is drawn.

## Reproduce

```sh
make figures-parameter         # collect/reuse, refresh grouped snapshot, render
make figures-parameter-cached  # refresh snapshot and render existing cache only
```

Both produce `figures/parameter-analysis.svg` and a 3× PNG, and print their
absolute paths. To update the grouped snapshot without rendering:

```sh
make reports-grouped
```

The renderer uses `npx` with Vega 6.4.0, Vega-Lite 6.4.3, Vega CLI 6.4.0, and
Canvas 3.2.3 pinned in the root `Makefile`; npm's cache supplies reusable packages.
There is no figure-specific Python projector or repository npm manifest.
Both images depend on the specification, shared snapshot, and render recipe.
The snapshot depends on the JSONL cache and reporting code. It is written only
when its contents change, so refreshing an unchanged cache leaves images alone.

## Inspect the selection

The specification reads `../.reports-grouped.json` once, using the normal
Vega-Lite file loader. The generic snapshot groups every original cache sample
by binary hash, physical input hash, treatment, disequality encoding, timeout,
and fact-directory hash. It retains each record's physical `row_index`.
A group's `labels` list reflects the existing latest persisted label/engine
alias semantics, even when its original samples used other labels.

The chart selects alias `figures`, a 300-second timeout, an empty fact directory,
and the six explicit treatment/encoding combinations. An eligible group must
contain an observation for the corresponding canonical input path above.
Among eligible exact identities for each endpoint, the newest observation's
timestamp and then physical row index select the group. **All** of that group's
samples participate, including records with other original labels or paths.
Different identities are never pooled, and a newer unsuccessful group never
falls back to an older successful group. No filesystem binaries are needed to
render the cached snapshot.

All selection, counting, means, and positioning remain visible in the
Vega-Lite transforms. The outer JSON object lets the specification retain all
six expected rows even when `groups` is empty. Missing observations are never
represented as zero elapsed time.

## Validation

```sh
make figures-parameter-test
```

Tests use temporary synthetic snapshots with the normal file loader. They
check varying sample counts, complete and missing endpoints, failures,
timeouts, invalid timings, newest-identity selection, timestamp ties, input
and alias filtering, and the shared linear scale. Synthetic records never
enter the benchmark cache or shared snapshot. Inspect the actual PNG after
collection for readable labels and unclipped observations at its intended size.
