# Nightly benchmarks

`make nightly` benchmarks the suite and writes a single-file, interactive
[eval-live](https://github.com/saulshanabrook/eval-live) report to
`nightly/output/index.html`, with the raw report cache beside it as
`index.jsonl`.

The [egraphs-good nightly service](https://nightly.cs.washington.edu) checks out
this repository, runs `make nightly`, and serves `nightly/output/`, matching the
`report=` entry in the nightly configuration. This mirrors the nightly that
[egglog](https://github.com/egraphs-good/egglog) already runs.

## What it measures

The run invokes `bench.py` once per available backend/treatment endpoint, on the
current checkout and on the latest `main`, over `bench.py`'s representative
suite, and accumulates every endpoint in the one report cache:

| Backend | Treatments |
| --- | --- |
| `main` | `off`, `term`, `proofs`, `proof-extraction` |
| `dd` | `term`, `proofs` |

eval-live builds its dropdown from every cached endpoint, so the page can compare
any two of them. Each endpoint is labelled by target (`branch` / `main`) and
commit hash, so it is clear which commit each side is; endpoints with identical
binaries collapse to one option, so the branch and `main` diverge only once the
code differs.

The page opens on branch-vs-main proof mode, putting both commit hashes side by
side; when the two checkouts share a binary that comparison is degenerate, so it
falls back to proof overhead (`proofs` vs `off`) on the branch. Either way it
shows both endpoints' absolute wall time and peak RSS with confidence intervals
plus their ratios, and loads a pinned Pyodide runtime for cache-only retargeting
within the embedded results.

Populating every endpoint is intentionally heavy — a full nightly builds both
checkouts and runs each endpoint across the whole suite. Populating the cache is
best effort: an endpoint that fails to build or run drops one dropdown option
rather than failing the whole run.

## Local run

```bash
make nightly                              # writes nightly/output/index.html
python3 -m webbrowser nightly/output/index.html   # or just open the file in a browser
```

## Tuning

Edit the constants at the top of `scripts/nightly_bench.py` — `TARGETS` and
`ENDPOINTS` control which checkouts and backend/treatment combinations are
measured, and `HEADLINE` picks the comparison the page opens on. Everything else
uses `bench.py`'s own defaults (rounds, timeout, and the representative suite).

Pass an alternate output directory as a single positional argument:

```bash
uv run --locked python scripts/nightly_bench.py /path/to/output
```

The output directory is disposable and git-ignored; each run starts from a fresh
report so the page reflects a new measurement of the current checkout.
