# Egglog encoding

This repository is a workspace for iterating on proof and term encoding changes
across `egglog` and `egglog-experimental`.

The goal is to make proof generation work with a reasonable slowdown before
porting the winning strategy back upstream. The current success target is:

- proof-mode wall time is under `2x` the non-proof baseline; and
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
make rust-nits      # rustfmt check, Clippy, and doc-link check only
make proof-tests    # proof-focused subset of the workspace tests
make benchmark-smoke
make nightly        # benchmark the nightly endpoints and publish nightly/output/
make nightly-local  # the same run at one round, for trying it out
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
proof-testing mode. Proof testing turns checks into proof queries and snapshots
the generated proofs. Use `make proof-tests` for focused iteration and
`make rust-check` or `make check` for the final compatibility gate.

## Benchmarking

The public entrypoint is:

```bash
./bench.py [FILE ...] [OPTIONS]
```

Every benchmark invocation compares exactly two endpoints over the same ordered
files: a candidate and a baseline. An endpoint is one target and treatment.
There are no implicit matrices or multi-way comparisons.

The default command compares proof mode with ordinary mode in the current
checkout:

```bash
./bench.py

# Equivalent endpoint selection:
./bench.py \
  --target . --treatment proofs \
  --compare-target . --compare-treatment off
```

The endpoint defaults are:

| Endpoint | Target | Treatment |
| --- | --- | --- |
| Candidate | `.` | `proofs` |
| Baseline | candidate target | `off` |

`--compare-target` defaults to the candidate target. Every rendered report
states the exact endpoints, files, rounds, timeout, and report path so every
ratio is interpretable.

Treatments map directly to engine modes:

| Treatment | Executable and behavior |
| --- | --- |
| `off` | egglog without term or proof encoding |
| `term` | egglog with `--term-encoding` |
| `proofs` | egglog with `--proofs` |
| `proof-extraction` | egglog with `--proof-extraction`; rewrite checks, then extract, materialize, clean, and simplify proofs without verifying them |
| `proof-testing` | egglog with `--proof-testing`; extract and verify proofs for checks |
| `egg` | current egg without explanation recording |
| `egg-proofs` | current egg with explanation recording enabled |
| `egg-proof-extraction` | current egg with explanation recording and extraction |
| `egg-proof-testing` | current egg with extraction and explanation checking |

The five egglog treatments run `egglog-experimental`. The four `egg*`
treatments run the separate `egg-math-benchmark` executable and currently
support only `egglog-experimental/tests/math-microbenchmark-rational.egg`.
Results from either proof-extraction treatment are performance evidence only;
the corresponding proof-testing treatment provides the strict validity check.

### Common comparisons

Proof overhead in the current checkout is the default:

```bash
./bench.py
```

Measure non-validating proof-extraction overhead explicitly:

```bash
./bench.py --treatment proof-extraction
```

Compare the current proof implementation with proof mode on `origin/main`:

```bash
./bench.py --compare-target @origin/main --compare-treatment proofs
```

Compare term encoding with ordinary mode:

```bash
./bench.py --treatment term
```

For the fixed Math workload, compare proof overhead within each engine and then
compare the engines with proof recording consistently disabled or enabled:

```shell
# Proof overhead in egg.
./bench.py egglog-experimental/tests/math-microbenchmark-rational.egg \
  --compare-treatment egg --treatment egg-proofs

# Proof overhead in egglog.
./bench.py egglog-experimental/tests/math-microbenchmark-rational.egg \
  --compare-treatment off --treatment proofs

# egglog versus egg without proofs.
./bench.py egglog-experimental/tests/math-microbenchmark-rational.egg \
  --compare-treatment egg --treatment off

# egglog versus egg with proofs.
./bench.py egglog-experimental/tests/math-microbenchmark-rational.egg \
  --compare-treatment egg-proofs --treatment proofs
```

Compare current proofs with a previously cached, labeled ordinary baseline:

```bash
./bench.py --compare-target old-off=
```

That last form reuses the newest cache identity carrying `old-off` when it has
enough matching rows. First create the label with a concrete source, for
example `--compare-target old-off=@origin/main`. Newest means the greatest
`started_at`, with later JSONL order breaking ties. If a command changes both
target and treatment, the report warns that the ratio is a joint endpoint
change and does not attribute the effect to one cause.

### Targets

Both `--target` and `--compare-target` accept the same syntax:

- `.` for the current checkout;
- `/path/to/repo` for another local checkout;
- `@main`, `@origin/main`, or `@abc123` for a git ref from this repository;
- `'#33'` for the latest head of pull request 33 from `origin`;
- `label=SOURCE` to assign a stable report label to any source; or
- `label=` to reuse the newest cached identity with that explicit label.

Quote `#` targets so the shell does not treat them as comments. Paths are used
directly. Git refs and pull requests use an existing clean worktree at the
resolved commit when available, otherwise the runner creates or reuses an
isolated temporary worktree. It never stashes the main checkout.

If differently spelled target selectors resolve to the same checkout, the
runner materializes it once and builds each executable required by the selected
treatments. Each cache row records the SHA-256 of the executable that actually
ran.

A cache-only `label=` target skips materialization and building when every
requested endpoint/file already has enough rows. If more rows are required, a
clean cached git revision can be rebuilt; a label pointing to a dirty checkout
requires a new `label=SOURCE` request.

The baseline and candidate may share a binary, as the default proof-overhead
comparison does, but their complete cache identities—binary SHA-256 and
treatment—must differ.

### Files

Positional paths select benchmark files. Use `--fact-directory` for explicitly
selected workloads containing `(input ...)` commands:

```bash
./bench.py egglog/tests/foo.egg egglog/tests/bar.egg
./bench.py egglog/tests/pointer-analysis-initdb.egg \
  --fact-directory egglog/tests/pointer-analysis-initdb
```

Paths are resolved relative to the command invocation directory, not relative
to either target. Both endpoints therefore run the exact same file and fact
directory contents. Their SHA-256 hashes are part of the cache identity.

With no positional files, the representative suite is:

- `egglog-experimental/tests/math-microbenchmark-rational.egg`
- `egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg`
- `egglog/tests/pointer-analysis-initdb.egg`, with
  `egglog/tests/pointer-analysis-initdb`
- `egglog/tests/hardboiled_conv1d_32.egg`
- `egglog/tests/luminal-llama.egg`
- `egglog/tests/web-demo/herbie.egg`
- `egglog/tests/papers/misaal-hvx-dot-product.egg`
- `egglog/tests/papers/churchroad-wide-multiply.egg`
- `egglog-experimental/tests/papers/dialegg-nmm40.egg`
- `egglog/tests/papers/speq-preserved-reference-suite.egg`

The workloads are intentionally bounded proxies rather than an undifferentiated
corpus:

| Workload | Adaptation or scope | Correctness signal |
| --- | --- | --- |
| Math | The paper artifact's Rational language, 24 rewrites, and seven seeds, run for eleven iterations through current egg or egglog without backoff | An equality first established on iteration eleven is checked; tests require it to fail after iteration ten in both engines |
| eggcc 2mm | Bounded pass-one fixture with ordinary constructor-valued merges | Generated `main` function type is checked |
| Pointer analysis | All 73,864 rows from the 23 `initdb.bc` relations consumed by the adapted program; three legacy lookup-or-create functions are constructors under current egglog, and the run uses ordinary seminaive scheduling | Known `constant_points_to` row is derived and both reported output-table sizes are available for artifact comparison |
| Hardboiled | Dormant canonicalization rules using unsupported unstable helpers are omitted | Extracted WMMA store result is checked |
| Luminal | Static Llama graph from [`egglog_repro` commit `7fb0194`](https://github.com/saulshanabrook/egglog_repro/blob/7fb0194812b5b11e41a286d8b55e48e3b0bfcd66/llama.egg) | `t712` is checked after kernel lowering |
| Herbie | Static engine proxy without Racket orchestration or an FPCore corpus | All 14 checks exercise the selected treatment |
| MISAAL | Complete generated HVX dot-product workload with current global syntax | The source expression is checked equivalent to the synthesized HVX result |
| Churchroad | The paper's 16-by-32-bit wide multiply with its prelude and driver mapping rules materialized; the saturating schedule is bounded to 17 cycles, calibrated as a roughly one-second normal-mode workload | The multiply expansion and its two-input and three-input DSP proposals are checked |
| DialEgg | Generated NMM-40 scaling workload with `base.egg` materialized | An alternative matrix-chain association is checked |
| SpEQ | Four artifact-preserved programs that still match the artifact's GEMV/histogram reference rules, recorded using egglog-python's native command log | Each input is checked equal to its extracted reference call (or enclosing expression) |

The Math language, rewrites, and seeds come from
`micro-benchmarks/src/math.rs` and `micro-benchmarks/src/eqlog/math_full.egg`
in the [PLDI 2023 artifact](https://doi.org/10.5281/zenodo.7709794). The fixture
preserves its Rational constants but uses current egg and egglog's ordinary
simple/seminaive schedulers without the artifact's backoff scheduler or match
cap, so this is a controlled current-engine comparison rather than an exact
reproduction of the paper's historical scheduler results.

The pointer input is the complete `initdb.bc` input for the 23 relations read by
this adaptation, not the artifact's full 30-program pointer-analysis matrix.
See `egglog/tests/pointer-analysis-initdb.PROVENANCE.md` for the source
details and archive SHA-256. Herbie remains a bounded static proxy in the
ordinary benchmark suite; reproducing the historical Racket/FPCore
orchestration remains outside the ordinary runner.

Benchmark files must not contain executable `(prove ...)` commands. Use
`(check ...)` in timed workloads so the selected treatment controls whether
proof extraction is included in the timing boundary.

Reports normally identify a selected file by filename. If names collide, they
use the shortest distinguishing path suffix; persisted rows retain the invoked
path.

### Detail levels and output

`--detail` is cumulative:

| Value | Added report content |
| --- | --- |
| `summary` | comparison selection and headline summary |
| `files` | per-file wall time and peak RSS estimates |
| `phases` | additive suite and per-file slowdown decomposition |
| `rulesets` | Program/Equality driver groups and changed rulesets per file |

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
and above `1x` is slower or uses more RSS. Each statistical estimate shows its
95% confidence interval when defined and otherwise shows its point estimate.

Rich output goes to stderr. From top to bottom it prints rulesets, phases,
files, the compact comparison definition, and the headline summary, omitting
sections above the requested detail level. The most specific diagnostics are
therefore above their broader context, while the decision remains at the
bottom of terminal output.
Detailed Rich tables are designed for terminals at least 120 columns wide; a
narrower terminal receives one warning and still renders best-effort without
hiding file names. Markdown goes to stdout, is independent of terminal width,
and keeps the canonical comparison, summary, files, phases, rulesets order.

The remaining collection options are:

- `--report PATH`: append-only report/cache path; default `.reports.jsonl`.
  A filesystem path is required; `-` is not a streaming destination.
- `--rounds N`: selected observations required for every endpoint/file;
  default `6`.
- `--timeout-sec N`: per-process timeout; default `120`.
- `--force-run`: append `N` fresh rows for both endpoints before selecting the
  newest rows.
- `--format rich|markdown`: final human report format.
- `--open`: write the complete cache snapshot to an interactive HTML file and
  open it. For the default cache, the output is `.reports.html`.

Use `./bench.py --help` for the complete option reference.

### Engine timing

Every successful benchmark observation records timing from the same measured
process. Timing collection is always enabled; requesting a detailed report does
not rerun a diagnostic process or change the cache key.

The versioned timing summary stores eleven fixed process counters, one typed
row per named ruleset with its Program or Equality role and five exclusive
own-work phases, and one global native-Rebuild counter. Four generated-frontend
counters separate typed producer construction, signature-catalog operations,
sort/call resolution, and remaining batch materialization. Each is an exclusive
leaf; `frontend_other` is the residual source-lowering work outside them. Parent
mechanisms, shares, and Residual are derived rather than stored; the same
canonical per-file breakdown feeds both the decomposition and ruleset-driver
views, so their parent totals match by construction.

Checks are charged to the command counters in both modes. One known boundary is
that a rebuild triggered by a top-level action such as `(union ...)` remains in
Commands/Actions. The captions printed next to `--detail phases` and
`--detail rulesets` are the source of truth for grouping and display rules.

Benchmarks run single-threaded. This keeps Search and Apply attribution
additive for egglog's interleaved executor.

### Interactive report

Add `--open` to print the ordinary report, write one single-file HTML
snapshot next to the JSONL cache, open it, and exit normally:

```bash
./bench.py --open
./bench.py --report results.jsonl --open  # writes results.html
```

The HTML embeds the complete loaded cache snapshot and the same Python analysis
and catalog code used by the CLI. It immediately displays the invocation's full
ruleset-detail report, then loads a pinned Pyodide runtime and SciPy over HTTPS
to enable retargeting. The initial report preserves the invocation's endpoint
provenance and file order; after Apply, retargeted endpoints and files use the
latest cached provenance for each cache identity within that immutable snapshot.
The page can select any two cached endpoints, any nonempty file subset, a cached
timeout, and an available round count; it always shows all report sections.
Combinations without enough matching observations remain selectable and produce
explicit missing-result states. A failed request leaves the prior report and
selectors intact.

The snapshot never resolves a target, builds a binary, runs a benchmark,
modifies the JSONL, or observes rows appended after it was created. If the
network runtime cannot load, the initial static report remains readable and
only retargeting is unavailable. The HTML contains the full cache, including
machine-local paths and provenance, so treat it as potentially sensitive when
sharing it.

### Nightly

`make nightly` benchmarks each treatment in `TREATMENTS` — `term`, `proofs`,
and `proof-extraction` — on the current checkout and on the latest `main`,
writing `nightly/output/index.jsonl` and the interactive page beside it:

```bash
make nightly
uv run --locked python scripts/nightly_bench.py /path/to/output  # alternate output directory
```

Endpoints are labelled by target (`branch` / `main`) and commit hash, so the
page's dropdown can compare any two of them and it is clear which commit each
side is; endpoints with identical binaries collapse to one option. The page
opens on proof overhead of the current checkout. Populating is best effort: an
endpoint that fails to build or run drops one dropdown option rather than
failing the run. Edit `TARGETS` and `TREATMENTS` in `scripts/nightly_bench.py`
to change what is measured.

Each run replaces both published files, so `index.jsonl` is the cache that run
measured into and a failed run publishes no page.

`make nightly-local` is the same run at `--rounds 1`, for trying the whole
pipeline out without waiting for a full nightly.

The [egraphs-good nightly service](https://nightly.cs.washington.edu) checks out
this repository, runs `make nightly`, and serves `nightly/output/`, matching the
`report=` entry in the nightly configuration. Two things that runner does not
provide, `make nightly` arranges itself: it installs a pinned uv into `.uv/`
when uv is missing from `PATH` (uv then downloads its own CPython; bump
`UV_VERSION` in the `Makefile` to move that pin), and it installs rustup when
the box has none. The runner also leaves rustup's `~/.cargo/bin` off `PATH`,
which would leave cargo resolving to Ubuntu's — too old for
`rust-toolchain.toml`'s pin — so `nightly_bench.py` puts those shims first.

Both installers run `curl … | sh`, so on a developer box prefer installing uv
and rustup yourself: `make nightly` and `make nightly-local` skip each one that
is already there. Only a bare CI runner needs them.

### CPU profiling

Benchmark reports answer whether and where performance changed. Use the
separate Samply command when a particular endpoint needs call-stack diagnosis:

```bash
./bench.py profile FILE
./bench.py profile FILE --target @origin/main --treatment proofs --open
./bench.py profile FILE --profile-seconds 20
```

Profiling selects one target, treatment, and file. Artifacts are cached under
`.profiles/` by binary, file, fact-directory, treatment, and
iteration policy. `--open` loads the artifact in Samply; `--force-run` replaces
the cached profile. Profiling is deliberately separate from the repeated-run
benchmark statistics and pair report.

On macOS, the default summary uses Samply leaf-sample CPU deltas to split
observed CPU into application, other-library, and unattributed CPU, report
application-symbol coverage, and rank top functions by self CPU. Profile
Unattributed means a leaf sample could not be mapped to a library; it is not the
benchmark's pre-merge Unattributed/Execution overhead. These are sampled CPU
totals and shares, not wall time, engine phases, or confidence intervals. Other
platforms still record and cache the artifact and print its viewer handoff
without a CPU breakdown. `--top` limits functions, `--format` selects Rich or
Markdown, and `--no-summary` prints only the artifact path.

## Reports and cache behavior

`.reports.jsonl` is an append-only, disposable local cache. Each line is one
measured process observation. The runner parses the file once into an indexed
`ReportStore`; appends update both the JSONL and those indexes. Normal
collection creates no database or second cache representation; `--open`
separately exports an HTML snapshot.

Cache reuse is keyed by:

- binary SHA-256;
- file SHA-256;
- fact-directory SHA-256;
- treatment; and
- timeout.

Target source, path, git revision, dirty state, labels, and display paths are
provenance rather than cache-key dimensions. The runner selects the newest
`--rounds` rows for each exact endpoint/file, ordering first by `started_at` and
then by physical JSONL order. Without `--force-run`, it appends only missing
rows. With `--force-run`, it appends a full fresh set and then selects the
newest rows.

Before any measured row is appended, all targets needing collection are built.
Fresh collection is serial; one untimed `<binary> --help` capability preflight
per target verifies the required timing-summary interface. Each target prints
one compact cached/required line and either `nothing to collect` or the fresh-run
count; cached failures and timeouts are explicit. Fresh TTY runs use transient
progress with elapsed time, redirected output logs each completed run, and both
end with status counts. All operational output goes to stderr.

`benchmarking/reports/store.py` defines the sole trusted `TypedDict` schema,
standard-library JSON codec, cache key, and append/index/select operations.
Each observation contains target and workload
provenance, exact cache coordinates, status, wall time, peak RSS, and failure
details. A top-level report schema version covers both the persisted shape and
measurement semantics, so methodology changes cannot silently reuse stale
measurements. Successful observations also contain the version-5 timing
summary: fixed process counters, a typed list of named ruleset timings, and one
global native-Rebuild counter. Changes to timing coverage or meaning require a
schema-version change so stale measurements cannot be reused silently.
The experimental custom-scheduler API times its backend query and action
invocations as ruleset work; lazy rule compilation and its intermediate update
flush remain surrounding work and are charged to an enclosing command when one
exists.

Timed-out rows have null wall time, peak RSS, and timing summary. Failed rows
have no timing summary and retain whatever process measurements the operating
system supplied. Either status makes a dependent statistical comparison
incomplete instead of averaging only successful rows.

This tool is the only supported reader and writer. The codec rejects old report
and timing-summary schema versions and requires successful rows to contain
timing data. It trusts the tool's typed writer rather than repeating the
`TypedDict` as runtime field-by-field validation. A schema change intentionally
invalidates existing caches: move or remove an incompatible report and
recompute it.

### Report-analysis ownership

`ComparisonSpec` owns the exact endpoints, files, rounds, and timeout;
`store.py` owns physical row order and cache selection. `analysis.py` computes
immutable summary and file comparisons plus one canonical timing breakdown per
file. `presentation.py` projects that breakdown into mechanism and ruleset
tables; Rich, Markdown, and the interactive page serialize the catalog without
recomputing report facts.

## Statistics

The benchmark unit is a complete `egglog-experimental` process for one file,
endpoint, and round. Python orchestration is outside the measured child
process. The analysis keeps all selected observations; it does not report
best-of-N timings or discard outliers by folklore.

The JSONL does not retain round-pair identities. Fresh and cached reports both
analyze the selected baseline and candidate observations as independent,
unpaired samples.

For one successful endpoint/file result, wall time and peak RSS use the
arithmetic mean. With at least two samples, the report computes the ordinary
95% t confidence interval for that mean using the unbiased sample variance.
With one sample it reports a point estimate labeled `point only`.

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
when an unrelated file is incomplete. Mechanism contributions and ruleset
totals or component deltas are descriptive diagnostics; only endpoint
estimates and ratios receive confidence intervals.

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
- `benchmarking/`: Python collection, reporting, interactive-view, and
  profiling code.
- `tests/`: domain-focused pytest and Syrupy snapshot coverage.
- `Makefile`: canonical validation and maintenance commands.
- `pyproject.toml` and `uv.lock`: Python configuration and locked environment.
- `.reports.jsonl`: ignored, disposable benchmark cache.
- `.profiles/`: ignored Samply artifact cache.

Python ownership is layered so new code has one clear home:

- Commands: `bench.py` dispatches lazily; `benchmark.py` composes pair benchmark
  requests; `profile.py` owns profile requests and Samply artifact caching.
- Inputs and execution: `models.py` defines dependency-free identities and
  invariants; `workloads.py` resolves and validates inputs; `targets.py`
  materializes and builds targets and constructs commands; `collection.py`
  plans and records observations; `processes.py` measures children. Commands
  share one Rich stderr console directly.
- Profile analysis: `samply_analysis.py` reads and presents Samply artifacts.
- Report data: `reports/store.py` owns the JSONL schema, codec, cache key, and
  append/index/select operations; `reports/analysis.py` computes
  renderer-independent statistics.
- Report presentation: `reports/catalog.py` defines the document model;
  `reports/presentation.py` supplies wording and maps analysis into that model;
  `reports/render.py` owns Rich and Markdown; `reports/interactive_runtime.py`
  owns cache-only retargeting; `reports/interactive.py` embeds the cache,
  Python modules, and adjacent browser assets into the HTML artifact, then
  writes and opens it.

Every module has a more precise ownership docstring. Package `__init__.py`
files are documentation-only; tests enforce that rule, the data-layer boundary,
and an acyclic static import graph.

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

Cargo's profile behavior is documented in the
[Cargo profile reference](https://doc.rust-lang.org/cargo/reference/profiles.html).

Each report row records the exact benchmark binary hash.

## CI

CI runs on pull requests, manual dispatches, and pushes to `main`:

- `python`: `make python-nits`, then `make python-test`.
- `rust`: `make rust-nits`, then `make rust-test`.
- `benchmark-smoke`: a one-round `off`/`proofs` pair comparison across the
  default six-file suite through `make benchmark-smoke`.
- `codspeed`: an in-process, proofs-only benchmark over a smaller workload set
  in simulation and memory modes. CodSpeed includes phase-clock execution but
  does not persist phase reports; `./bench.py` remains the source for
  off/proofs and commit comparisons with stored observations.

Ruff and Mypy discover all repository-owned Python files from project
configuration, so new modules under `benchmarking/` or `tests/` require no
Makefile edits.
