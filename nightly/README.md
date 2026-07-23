# Nightly benchmarks

`make nightly` benchmarks the suite and writes a single-file, interactive
[eval-live](https://github.com/saulshanabrook/eval-live) report to
`nightly/output/index.html`.

The [egraphs-good nightly service](https://nightly.cs.washington.edu) checks out
this repository, runs `make nightly`, and serves `nightly/output/`, matching the
`report=` entry in the nightly configuration. This mirrors the nightly that
[egglog](https://github.com/egraphs-good/egglog) already runs.

## What it measures

By default the run uses `bench.py`'s representative suite and its default
proof-overhead comparison (`proofs` vs `off` on the current checkout). The page
shows both endpoints' absolute wall time and peak RSS with confidence intervals,
plus their ratios, and loads a pinned Pyodide runtime for cache-only retargeting
within the embedded results.

## Local run

```bash
make nightly            # writes nightly/output/index.html
open nightly/output/index.html
```

## Tuning

`scripts/nightly_bench.py` reads these environment variables:

- `NIGHTLY_ROUNDS` — rows per endpoint/file (default: `bench.py`'s default).
- `NIGHTLY_TIMEOUT_SEC` — per-process timeout in seconds.
- `NIGHTLY_FILES` — shell-split benchmark files; empty selects the
  representative suite.
- `NIGHTLY_FACT_DIRECTORY` — fact directory for explicit `NIGHTLY_FILES`.

Pass an alternate output directory as a single positional argument:

```bash
uv run --locked python scripts/nightly_bench.py /path/to/output
```

The output directory is disposable and git-ignored; each run starts from a clean
report so the page reflects a fresh measurement of the current checkout.
