# Parameter-analysis implementation comparison

This comparison runs the authors' DE, EE, NEE, and OEE implementations and the
existing Egglog NE and EE encodings, with proofs off. The author-supplied
[native corpus](parameter-analysis.in) is canonical. Its checked-in
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
make figures-parameter
```

This makes three sequential `./bench.py` comparisons and requests ten runs per
implementation, using the append-only `.reports.jsonl` cache. Compatible cached
observations are reused. Cargo dependency resolution and release builds happen
automatically, outside measurement. Each measured interval spans the complete
engine process, including input reading, expression parsing, and shutdown.
The native CSV timers start after file reading and line-splitting, so the figure
uses external whole-process time for all six implementations. The timeout is
300 seconds. No proofs or proof checks run.

Native rows identify the `.in` file and its hash; Egglog rows identify the `.egg`
file and its hash. Each row also identifies the executable that actually ran.
There is no conversion or input preparation during collection. The corpus's
normal native output reports a contradiction; the native programs also permit
consistent inputs to exit successfully.

To regenerate images using cached observations only:

```sh
make figures-parameter-cached
```

Outputs are `figures/parameter-analysis.png` and `figures/parameter-analysis.svg`.
The Vega-Lite specification reads `.reports-grouped.json` directly and selects
the latest matching group for each condition under the `figures` target alias.
Dots show cached observations; the mean and sample count use those observations.
Missing or failed conditions remain visible. See the
[figure notes](../../figures/parameter-analysis.md) for selection details.
