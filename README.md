# Egglog encoding

This repository is a workspace for iterating on proof and term encoding changes
across `egglog` and `egglog-experimental`.

The goal is to make proof generation work with a reasonable slowdown before
porting the winning strategy back upstream. The current success target is:

- proof mode is less than `2x` slower than the non-proof baseline; and
- that claim is supported by benchmark reports with confidence intervals, not
  just point estimates.

## Daily workflow

Run the complete Python and Rust validation suite through the root Makefile:

```bash
make check
```

Hygiene checks and tests can be run independently. `nits` never runs tests:

```bash
make nits           # lockfile, formatting checks, linting, and type checking
make test           # Python and Rust tests
make python-check   # complete Python validation
make rust-check     # complete Rust validation
make python-nits    # Python hygiene only
make rust-nits      # rustfmt check and Clippy only
make proof-tests    # proof-focused subset of the workspace tests
make benchmark-smoke
make update-snapshots
make format         # apply Ruff and rustfmt formatting
```

`make benchmark-smoke` uses a one-round comparison and writes its disposable
JSONL report to `/tmp/egglog-encoding-bench-smoke.jsonl`. Override
`BENCHMARK_SMOKE_REPORT` to choose another path. `make update-snapshots` is the
explicit review action for accepting intentional Markdown report changes.

The root workspace includes both `egglog` and `egglog-experimental`.
`egglog-experimental` depends on the workspace `egglog` crate, keeping proof
changes and downstream behavior in one reviewable unit.

Proof-specific file tests use the `proofs/` filter: explicit `(prove ...)`
fixtures under `tests/proofs` plus every proof-compatible file under
proof-testing mode. Use `make proof-tests` for focused iteration and
`make rust-check` or `make check` for the final compatibility gate.

## Benchmarking

The public entrypoint is:

```bash
./bench.py [FILE ...] [OPTIONS]
```

Every invocation compares exactly two endpoints over the same ordered files:
a candidate and a baseline. An endpoint is one target, backend, and treatment.
There are no implicit matrices or multi-way comparisons.

The default command compares proof mode with ordinary mode in the current
checkout:

```bash
./bench.py

# Equivalent endpoint selection:
./bench.py \
  --target . --backend main --treatment proofs \
  --compare-target . --compare-backend main --compare-treatment off
```

The endpoint defaults are:

| Endpoint | Target | Backend | Treatment |
| --- | --- | --- | --- |
| Candidate | `.` | `main` | `proofs` |
| Baseline | candidate target | `main` | `off` |

In particular, `--compare-backend` always defaults to `main`, even when the
candidate uses another backend. `--compare-target` alone inherits the candidate
target. The report begins with the exact endpoint, files, rounds, timeout, and
report path so every ratio is interpretable.

### Common comparisons

Proof overhead in the current checkout is the default:

```bash
./bench.py
```

Compare the current proof implementation with proof mode on `origin/main`:

```bash
./bench.py --compare-target @origin/main --compare-treatment proofs
```

Compare the DD backend with main while holding proof mode fixed:

```bash
./bench.py --backend dd --compare-treatment proofs
```

Compare term encoding with ordinary mode:

```bash
./bench.py --treatment term
```

Compare current proofs with a previously cached, labeled ordinary baseline:

```bash
./bench.py --compare-target old-off=
```

That last form reuses the newest cache identity carrying `old-off` when it has
enough matching rows. First create the label with a concrete source, for
example `--compare-target old-off=@origin/main`. If a command changes more than
one of target, backend, and treatment, the report warns that the ratio is a
joint endpoint change and does not attribute the effect to one cause.

### Targets

Both `--target` and `--compare-target` accept the same syntax:

- `.` for the current checkout;
- `/path/to/repo` for another local checkout;
- `@main`, `@origin/main`, or `@abc123` for a git ref from this repository;
- `'#33'` for the latest head of pull request 33 from `origin`;
- `label=SOURCE` to assign a stable report label to any source; or
- `label=` to reuse the newest cached identity with that explicit label.

Quote `#` targets so the shell does not treat them as comments. Paths are used
directly. Git refs and pull requests use an existing worktree at the resolved
commit when available, otherwise the runner creates or reuses an isolated
temporary worktree. It never stashes the main checkout.

If differently spelled target selectors resolve to the same checkout, the
runner builds that checkout once with the union of their required backend
features, so neither endpoint can overwrite the binary recorded for the other.

A cache-only `label=` target skips materialization and building when every
requested endpoint/file already has enough rows. If more rows are required, a
clean cached git revision can be rebuilt; a label pointing to a dirty checkout
requires a new `label=SOURCE` request.

The baseline and candidate may share a binary, as the default proof-overhead
comparison does, but their complete cache identities—binary SHA-256, backend,
and treatment—must differ.

### Files

Positional paths select benchmark files. Use `--fact-directory` for explicitly
selected workloads containing `(input ...)` commands:

```bash
./bench.py egglog/tests/foo.egg egglog/tests/bar.egg
./bench.py benchmarks/pointer.egg --fact-directory benchmarks/data/pointer
```

Paths are resolved relative to the command invocation directory, not relative
to either target. Both endpoints therefore run the exact same file and fact
directory contents. Their SHA-256 hashes are part of the cache identity.

With no positional files, the representative suite is:

- `egglog/tests/math-microbenchmark.egg`
- `egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg`
- `benchmarks/pointer-analysis-small.egg`, with
  `benchmarks/data/pointer-analysis-small`
- `egglog/tests/hardboiled_conv1d_32.egg`
- `benchmarks/luminal-llama.egg`
- `egglog/tests/web-demo/herbie.egg`

Benchmark files must not contain executable `(prove ...)` commands. Use
`(check ...)` in timed workloads and test proof extraction separately, so
printing or checking a proof does not become part of the timing boundary.

### Detail levels and output

`--detail` is cumulative:

| Value | Added report content |
| --- | --- |
| `summary` | comparison selection and headline summary |
| `files` | per-file wall time and peak RSS estimates |
| `phases` | per-file Search, Apply, Merge, Rebuild, and Other means |
| `rulesets` | the top 10 ruleset timing changes for each file |

The default is `summary`. For example:

```bash
./bench.py --detail files
./bench.py --detail phases
./bench.py --detail rulesets --format markdown > benchmark-report.md
```

The headline summary answers the most common questions with a small fixed set
of rows:

- the fixed-suite wall-time ratio, using the sum of the per-file means;
- the lowest and highest per-file wall-time ratios; and
- the lowest and highest per-file peak-RSS ratios.

For a one-file run, redundant lowest/highest rows collapse to one result. The
ratio is always `candidate / baseline`: below `1x` is faster or uses less RSS,
and above `1x` is slower or uses more RSS. Each statistical estimate includes
its point estimate and, when defined, its 95% confidence interval.

Rich output goes to stderr. It prints detailed tables first and the headline
summary last so the decision remains at the bottom of terminal output.
Detailed Rich tables are designed for terminals at least 120 columns wide; a
narrower terminal receives one warning and still renders best-effort. Markdown
goes to stdout, is independent of terminal width, and keeps the canonical
selection, summary, files, phases, rulesets order.

The remaining collection options are:

- `--report PATH`: append-only report/cache path; default `.reports.jsonl`.
  A filesystem path is required; `-` is not a streaming destination.
- `--rounds N`: selected observations required for every endpoint/file;
  default `6`.
- `--timeout-sec N`: per-process timeout; default `120`.
- `--force-run`: append `N` fresh rows for both endpoints before selecting the
  newest rows.
- `--format rich|markdown`: final human report format.
- `--serve` and `--serve-port PORT`: open the cache-only live report.

Use `./bench.py --help` for the complete option reference.

### Engine timing

Every successful benchmark observation records timing from the same measured
process. Timing collection is always enabled; requesting a detailed report does
not rerun a diagnostic process or change the cache key.

The engine records these components per ruleset and the JSONL stores their raw
nanosecond totals:

- Search: matching and join execution.
- Apply: executing rule-head instructions and staging updates.
- Unattributed: measured pre-merge work that cannot be accurately classified
  as Search or Apply.
- Merge: resolving and installing staged updates.
- Rebuild: rebuilding indexes and e-graph state.

The phase report aggregates all rulesets and displays Search, Apply, Merge, and
Rebuild. `Other` is derived as process wall time minus those four phases, so it
includes Unattributed plus process work outside recorded rulesets. A negative
Other value is prefixed with `!`; it means recorded phase totals exceed wall
time and should be treated as an attribution warning. Phase values are
descriptive arithmetic means and do not claim confidence intervals.

The ruleset report totals all five stored components for each ruleset, aligns
the union of names across the two endpoints, and ranks by the absolute
candidate-minus-baseline difference. It displays at most 10 rulesets per file
and reports how many were available. Timings are aggregated across the selected
observations; iterations are not separate report rows. A ruleset absent from
one endpoint is displayed as `—`, while a measured zero remains `0 ns`.

Benchmarks run single-threaded. This keeps Search and Apply attribution
additive for main egglog's interleaved executor. The DD backend records the same
schema at its natural search, apply, merge, and rebuild boundaries.

### Live report

Add `--serve` to print the ordinary report and then open a loopback-only browser
view:

```bash
./bench.py --detail rulesets --serve
./bench.py --detail files --serve --serve-port 8765
```

The page reuses the exact renderer-neutral tables shown by Rich and Markdown.
It can select a baseline endpoint, candidate endpoint, file subset, and
cumulative detail level, and can swap the endpoints. Its endpoint menus contain
only cache entries complete for the invocation's fixed files, rounds, and
timeout. The JSONL is loaded once when the command starts; applying a selection
recomputes the requested pair from that immutable in-process snapshot. A failed
request leaves the prior report and selectors intact.

The live page never resolves a target, builds a binary, runs a benchmark, or
modifies the JSONL. Stop it with Ctrl-C in the benchmark terminal.

### CPU profiling

Benchmark reports answer whether and where performance changed. Use the
separate Samply command when a particular endpoint needs call-stack diagnosis:

```bash
./bench.py profile FILE
./bench.py profile FILE --target @origin/main --treatment proofs --open
./bench.py profile FILE --backend dd --profile-seconds 20
```

Profiling selects one target, backend, treatment, and file. Artifacts are cached
under `.profiles/` by binary, file, fact-directory, backend, treatment, and
iteration policy. `--open` loads the artifact in Samply; `--force-run` replaces
the cached profile. Profiling is deliberately separate from the repeated-run
benchmark statistics and pair report.

## Reports and cache behavior

`.reports.jsonl` is an append-only, disposable local cache. Each line is one
measured process observation. The runner parses the file once into an indexed
`ReportStore`; appends update both the JSONL and those indexes. No database or
second persisted representation is created.

Cache reuse is keyed by:

- binary SHA-256;
- file SHA-256;
- fact-directory SHA-256;
- backend;
- treatment; and
- timeout.

Target source, path, git revision, dirty state, labels, and display paths are
provenance rather than cache-key dimensions. The runner selects the newest
`--rounds` rows for each exact endpoint/file, ordering first by `started_at` and
then by physical JSONL order. Without `--force-run`, it appends only missing
rows. With `--force-run`, it appends a full fresh set and then selects the
newest rows.

Before any measured row is appended, all targets needing collection are built
and preflighted for the required timing-summary interface. Fresh collection is
serial and uses one untimed executable startup warmup per target. Operational
cache, build, progress, and estimate output always goes to stderr.

The trusted writer schema is defined once as `TypedDict` structures in
`benchmarking/reports/records.py`. The standard-library JSON codec parses and
serializes complete rows. A successful row
contains provenance, cache coordinates, process timing, peak RSS, and this
nested timing shape:

```json
{
  "started_at": "2026-07-17T12:34:56Z",
  "status": "success",
  "target_label": null,
  "target_source": ".",
  "target_path": "/path/to/egglog-encoding",
  "target_git_ref": "HEAD",
  "target_git_sha": "abc123...",
  "target_is_dirty": true,
  "binary_sha256": "sha256:...",
  "file_path": "egglog/tests/foo.egg",
  "file_sha256": "sha256:...",
  "fact_directory_path": null,
  "fact_directory_sha256": "",
  "backend": "main",
  "treatment": "proofs",
  "timeout_sec": 120,
  "wall_sec": 1.23,
  "max_rss_bytes": 123456789,
  "error_exit_code": null,
  "error_signal": null,
  "error_message": null,
  "timing_summary": {
    "schema_version": 2,
    "rulesets": [
      {
        "name": "rules",
        "search_ns": 200,
        "apply_ns": 100,
        "unattributed_ns": 20,
        "merge_ns": 40,
        "rebuild_ns": 50
      }
    ]
  }
}
```

Timed-out rows have null wall time, peak RSS, and timing summary. Failed rows
have no timing summary and retain whatever process measurements the operating
system supplied. Either status makes a dependent statistical comparison
incomplete instead of averaging only successful rows.

This tool is the only supported reader and writer. The codec rejects old timing
schema versions and requires successful rows to contain timing data. It trusts
the tool's typed writer rather than repeating the `TypedDict` as runtime
field-by-field validation. A schema change intentionally invalidates existing
caches: move or remove an incompatible report and recompute it.

### Report-analysis ownership

The pure analysis layer produces five immutable named-row collections with
stable responsibilities:

- endpoints: the exact baseline and candidate;
- summary: suite wall ratio and per-file wall/RSS tails;
- files: per-file estimates and ratios;
- phases: per-file phase means, deltas, and ratios; and
- rulesets: top ruleset totals, deltas, and ratios.

`store.py` owns physical row order and exact cache selection. `analysis.py`
owns latest-observation status policy, statistics, classification, phase
aggregation, ruleset alignment, and ranking. `comparison.py` supplies wording
and maps the named rows to one renderer-neutral catalog. Rich, Markdown, and
the live page serialize that same catalog rather than recomputing report facts.

## Statistics

The benchmark unit is a complete `egglog-experimental` process for one file,
endpoint, and round. Python orchestration is outside the measured child
process. The analysis keeps all selected observations; it does not report
best-of-N timings or discard outliers by folklore.

For one successful endpoint/file result, wall time and peak RSS use the
arithmetic mean. With at least two samples, the report computes the ordinary
95% t confidence interval for that mean using the unbiased sample variance.
With one sample it reports a point estimate and explicitly labels it point-only.

Pair comparisons use the candidate-to-baseline ratio of arithmetic means and a
Fieller-style 95% confidence interval. If the interval is wholly below `1`, the
candidate is faster or uses less RSS; if wholly above `1`, it is slower or uses
more RSS; if it includes `1`, the direction is unclear at this confidence
level. If a valid interval cannot be calculated, the point estimate remains
visible with its availability explanation.

The fixed-suite wall result sums each endpoint's per-file means and divides the
candidate sum by the baseline sum. Its uncertainty propagates the per-file
mean variances through the same ratio method. It answers whether the selected
suite's total runtime changed. The lowest/highest file rows answer whether any
individual workload improved and where the worst relative regression occurred.
Peak RSS has no additive suite total, so only its lowest/highest file ratios are
shown. No median or geometric mean is mixed into this minimal headline.

A timed-out, failed, or otherwise incomplete selected result invalidates the
suite result that depends on it. Valid per-file tail comparisons remain useful
when an unrelated file is incomplete. Phase and ruleset tables are descriptive
diagnostics and do not receive confidence intervals.

The `<2x` proof goal is established only when the upper bound of the suite wall
ratio's 95% confidence interval is below `2x` for a proofs-versus-off
comparison.

Methodology references:

- Kalibera and Jones, “Rigorous Benchmarking in Reasonable Time” (ISMM 2013).
- Kalibera and Jones, “Quantifying Performance Changes with Effect Size
  Confidence Intervals” (University of Kent Technical Report 4-12).
- Fieller, “Some Problems in Interval Estimation” (1954).
- Chen and Revels, “Robust Benchmarking in Noisy Environments” (2016).
- Georges, Buytaert, and Eeckhout, “Statistically Rigorous Java Performance
  Evaluation” (OOPSLA 2007).

## Repository layout

Top-level ownership:

- `egglog/`: subtree of `https://github.com/egraphs-good/egglog`.
- `egglog-experimental/`: subtree of
  `https://github.com/egraphs-good/egglog-experimental`.
- `Cargo.toml`: root Cargo workspace integrating both subtrees.
- `bench.py`: executable uv entrypoint.
- `benchmarking/`: Python collection, reporting, live-view, and profiling code.
- `tests/`: domain-focused pytest and Syrupy snapshot coverage.
- `Makefile`: canonical validation and maintenance commands.
- `pyproject.toml` and `uv.lock`: Python configuration and locked environment.
- `.reports.jsonl`: ignored, disposable benchmark cache.
- `.profiles/`: ignored Samply artifact cache.

Python module boundaries:

- `benchmarking/cli.py` performs lazy top-level dispatch.
- `benchmarking/benchmark.py` parses and composes the pair benchmark command.
- `benchmarking/workloads.py` owns default workloads, path/content resolution,
  fact directories, and timed-input validation.
- `benchmarking/models.py` owns dependency-free endpoint, comparison, file,
  cache-key, and backend contracts.
- `benchmarking/targets.py` parses and materializes target sources, builds
  binaries, hashes inputs, and constructs child commands.
- `benchmarking/collection.py` resolves cache-aware targets, plans missing
  observations, captures same-process timing summaries, and writes records.
- `benchmarking/processes.py` measures child processes; `output.py` owns only
  operational stderr presentation.
- `benchmarking/profile.py` owns profile requests and Samply artifact caching;
  `samply_analysis.py` reads and presents profile artifacts.
- `benchmarking/reports/records.py` defines the sole trusted JSONL `TypedDict`
  schema and its standard-library JSON codec.
- `benchmarking/reports/store.py` loads and appends JSONL, preserves physical
  order, indexes exact cache keys and labels, and discovers cached endpoints.
- `benchmarking/reports/analysis.py` defines and computes one pair's immutable
  statistics, summaries, phases, and rulesets without presentation concerns.
- `benchmarking/reports/comparison.py` supplies report wording and maps those
  analysis rows to the fixed catalog.
- `benchmarking/reports/catalog.py` defines renderer-neutral sections, tables,
  rows, cells, and messages.
- `benchmarking/reports/render.py` alone owns Rich/Markdown syntax, ordering,
  styling, and terminal-width behavior.
- `benchmarking/reports/live.py` owns cache-only endpoint discovery, atomic
  retargeting, eval-live adaptation, and the loopback server.

Every module has an ownership docstring. Package `__init__.py` files are
documentation-only. Tests enforce those rules, the data-layer dependency
boundary, and an acyclic static import graph.

## Upstream subtrees

`egglog/` and `egglog-experimental/` are git subtrees, not submodules. The root
workspace owns integration, CI, benchmarking, and local documentation, while
subtree-local changes can be synchronized with their upstream repositories.

To pull upstream changes:

```bash
git remote add upstream-egglog https://github.com/egraphs-good/egglog.git
git fetch upstream-egglog main
git subtree pull --prefix=egglog upstream-egglog main --squash

git remote add upstream-egglog-experimental \
  https://github.com/egraphs-good/egglog-experimental.git
git fetch upstream-egglog-experimental main
git subtree pull --prefix=egglog-experimental \
  upstream-egglog-experimental main --squash
```

If the remotes already exist, skip `git remote add`. Commit or stash local
subtree edits before pulling, then run the root workspace checks.

To create an upstreamable branch containing only one subtree:

```bash
git subtree split --prefix=egglog -b split/egglog
git push https://github.com/<you>/egglog.git split/egglog:<branch-name>

git subtree split --prefix=egglog-experimental -b split/egglog-experimental
git push https://github.com/<you>/egglog-experimental.git \
  split/egglog-experimental:<branch-name>
```

Root-only files such as `bench.py`, this README, and CI configuration are not
included in the split branch.

## Cargo profiles

- `dev`: `opt-level = 3`, with `line-tables-only` debug information.
- `test`: Cargo's built-in test profile, inheriting the optimized development
  configuration.
- `release`: the optimized benchmark build.
- `profiling`: release optimization plus symbols for profilers and samplers.

Each report row records the exact benchmark binary hash.

## CI

CI runs on pull requests, manual dispatches, and pushes to `main`:

- `python`: `make python-nits`, then `make python-test`.
- `rust`: `make rust-nits`, then `make rust-test`.
- `benchmark-smoke`: a one-round pair comparison on
  `egglog/tests/integer_math.egg` through `make benchmark-smoke`.
- `codspeed`: an in-process, proofs-only benchmark over a smaller workload set.
  CodSpeed includes phase-clock execution but does not persist phase reports;
  `./bench.py` remains the source for off/proofs, commit, and backend
  comparisons with stored observations.

Ruff and Mypy discover all repository-owned Python files from project
configuration, so new modules under `benchmarking/` or `tests/` require no
Makefile edits.
