# Parameter-analysis implementation comparison

The paper figure compares the authors' native DE and EE implementations with
Egglog EE, with proofs off. Native NEE/OEE remain correctness checks.
The author-supplied [native corpus](parameter-analysis.in) is canonical. Its checked-in
[Egglog translation](parameter-analysis.egg) contains the same six fixed numeral
constraints, 100,000 equality pairs, and 10,000 disequality pairs in author order,
followed by a contradiction check. The four native drivers are unchanged.

This is one fixed contradictory workload, not the paper's parameter sweep.
The native drivers read all 400,000 expressions and assert the first 220,000;
Egglog reads the translated assertions. Native EE/OEE stop when their node count
is unchanged; Egglog saturates its private ruleset. Implementations may perform
different amounts of work after a contradiction becomes available.

The author-supplied drivers and corpus are distributed under
[Apache 2.0](LICENSE-APACHE). See [source and dependency provenance](native/README.md).

## Run

From the repository root:

```sh
./bench.py figures disequality-runtime
```

This requests ten runs per configuration through one collection plan, using the
append-only `.reports.jsonl` cache. Compatible cached
observations are reused. Cargo dependency resolution and release builds happen
automatically, outside measurement. Each measured interval spans the complete
engine process, including input reading, expression parsing, and shutdown.
The native CSV timers start after file reading and line-splitting, so the figure
uses external whole-process time for all three timed configurations. The shared
timeout defaults to 500 seconds. Correctness checks run separately from these timings.

Native rows identify the `.in` file and its hash; Egglog rows identify the `.egg`
file and its hash. Each row also identifies the executable that actually ran.
There is no conversion or input preparation during collection. The corpus's
normal native output reports a contradiction; the native programs also permit
consistent inputs to exit successfully.

Outputs are written under `figures/output/eval/`, including the PDF, SVG, PNG,
results JSON, numeric TeX macros, and TeX table. Automatic cache reuse collects
only missing observations, refreshes the grouped snapshot and renders changed
figures. The specification selects the `figures` label and
configured physical inputs. Boxplots show medians and interquartile ranges,
with 1.5-IQR whiskers and outlier points. Exports retain arithmetic means and
95% intervals, including ratios against native DE. Missing or failed conditions
stop export. See the [figure guide](../../figures/README.md) for selection and
provenance details.
