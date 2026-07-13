# Egglog encoding

This repository is a workspace for iterating on proof and term encoding changes
across `egglog` and `egglog-experimental`.

The goal is to make proof generation work with a reasonable slowdown before
porting the winning strategy back upstream. The current success target is:

- proof mode is less than `2x` slower than the non-proof baseline; and
- that claim is supported by benchmark reports with confidence intervals, not
  just point estimates.

## Daily workflow

The development loop is:

```bash
# Run all egglog and egglog-experimental tests.
cargo test --workspace

# Run proof-focused tests while iterating.
cargo test --workspace --test files 'proofs/'

# Run lint checks across the workspace.
cargo clippy --workspace --all-targets

# Build release binaries for benchmark comparisons.
cargo build --release --workspace

# Run or reuse the default benchmark report.
./bench.py
```

The root workspace includes both `egglog` and `egglog-experimental`.
`egglog-experimental` depends on the workspace `egglog` crate, which keeps proof
changes and downstream experimental behavior in the same reviewable unit.

Proof-specific file tests use one filter prefix:

- `proofs/`: explicit `(prove ...)` fixtures under `tests/proofs` plus every
  proof-compatible file under proof-testing mode. Checks are treated as prove
  commands and generated proofs are saved as snapshots.

This filter is a subset of the full workspace test run. Use it for fast proof
iteration and reserve `cargo test --workspace` for the final compatibility gate.

## Benchmarking

The public benchmark entrypoint is an executable Python script:

```bash
./bench.py [FILE ...] [OPTIONS]
```

Python dependencies and tool configuration live in `pyproject.toml`; `uv.lock`
pins the environment used by CI and local checks.

The default command is equivalent to:

```bash
./bench.py --target .
```

It builds the current checkout, runs the default representative benchmark
files, appends any missing observations to `.reports.jsonl`, and prints a
Rich terminal report to stderr. Use `--report -` to stream newly measured
report rows to stdout while keeping progress, summaries, build diagnostics, and
errors on stderr.

### Targets

Targets describe the builds being compared. Use one `--target` per build:

```bash
./bench.py --target @origin/main --target .
./bench.py --target @origin/main --target '#33'
./bench.py --target main=@origin/main --target mine=.
./bench.py --target before=@abc123 --target after=@HEAD
./bench.py --target old=/tmp/egglog-old --target new=/tmp/egglog-new
./bench.py --target prev-run=
```

Target syntax:

- `--target .` uses the current checkout.
- `--target /path/to/repo` uses another local checkout.
- `--target @main`, `--target @origin/main`, or `--target @abc123` uses a git
  ref, branch, tag, or commit from this repo.
- `--target '#33'` fetches PR 33 from `origin` and uses the latest PR head
  commit. Quote or escape the `#` so your shell does not treat it as a comment.
- `--target label=SOURCE` gives the target an explicit report label.
- `--target label=` reuses the latest cached target identity with that label
  from `--report`.

Behavior:

- Git refs use the `@` prefix. PR targets use the `#` prefix. Paths do not.
- If no target is provided, the only target is `.`.
- If any target is provided, the target list is exactly what was specified.
- The first target is the comparison baseline.
- Explicit labels are display names. Cache identity is derived from the
  persisted report fields described below.
- PR targets get labels like `#33` by default. Use `--target label='#33'` to
  choose a different display/report label.
- `label=` lookup only considers rows that were written with explicit
  `target.label`. If the same label appears for multiple binary hashes, the
  row with the latest `started_at` timestamp for that label is the definitive
  label pointer, with ties broken by later JSONL file order. When that pointer
  refers to a clean git SHA, the runner rebuilds that SHA in an isolated
  worktree to collect more samples. When it points to a dirty checkout, it is
  report-only unless the user supplies a new `label=SOURCE`.
- Targets are built and measured sequentially. Path targets use the provided
  checkout directly. Git-ref and PR targets use an existing worktree at the
  resolved commit when one exists; otherwise the runner creates or reuses an
  isolated temporary worktree instead of stashing local changes in the main
  checkout.

### Files

Positional arguments are benchmark files:

```bash
./bench.py egglog/tests/foo.egg egglog/tests/bar.egg
```

If no files are provided, the default target benchmark suite is:

- `egglog/tests/math-microbenchmark.egg`
- `egglog/tests/web-demo/rw-analysis.egg`
- `egglog/tests/integer_math.egg`
- `egglog/tests/web-demo/resolution.egg`
- `egglog-experimental/tests/fixtures/eggcc-2mm-pass1-merge-old.egg`

These five files are proof-compatible representative examples under the current
`egglog-experimental` CLI and run under the default `off`, `term`, and `proofs`
treatment matrix. The eggcc fixture is the heavy container/proof benchmark in
the default suite.
Relative file paths are resolved relative to the directory where `./bench.py`
was invoked, not relative to each target checkout. The same file contents are
used for every target, and `file.sha256` records the exact benchmark input.

### Options

The benchmark CLI exposes the routine collection and reporting options:

- `--report <path|->`: JSONL report/cache path. Default:
  `.reports.jsonl`. Use `--report -` to stream measured report rows to stdout;
  in that mode no cache file is loaded.
- `--rounds <n>`: fresh collection rounds per file and target, and matching
  report rows required per cache cell. Default: `6`.
- `--timeout-sec <n>`: per-process timeout. Default: `120`.
- `--treatments <list>`: comma-separated treatments. Default:
  `off,term,proofs`.
- `--force-run`: append new observations even when enough matching rows already
  exist.

### Treatments

The default treatment matrix is:

- `off`: run without proof or term flags.
- `term`: run with `--term-encoding`.
- `proofs`: run with `--proofs`.

`--proof-testing` is a correctness mode, not a benchmark treatment, and does not
appear in performance headlines.
Use `--treatments proofs` when iterating on proof performance across two or more
targets and you only need same-treatment proof-mode comparisons.

The measured command shape is:

```bash
RUST_LOG=error <build-dir>/target/release/egglog-experimental \
  --mode no-messages \
  -j 1 \
  [--term-encoding | --proofs] \
  <file.egg>
```

Benchmarking is single-threaded by default.

## Reports

`.reports.jsonl` is the canonical benchmark artifact and is ignored by git.
Use `--report <path>` to choose a different report file. Use `--report -` to
write newly measured report rows to stdout instead of a file. All progress,
summary, and diagnostic output always goes to stderr, so stdout can be
piped as report JSONL whenever `--report -` is used.

The report file is append-only JSONL. Each line records one process execution
and is a measured timing observation, not a derived summary. The row contains
the flat fields needed to recompute cache identity. The report does not store
`row_index`; the runner derives row order from the JSONL file order when it
loads the report.

Row fields:

- `started_at`: ISO timestamp for the measured child process start.
- `status`: `success`, `timed-out`, or `failure`.
- `binary_sha256`: SHA-256 of the built `target/release/egglog-experimental`
  binary.
- `treatment`: `off`, `term`, or `proofs`.
- `timeout_sec`: per-process timeout.

Target fields:

- `target_label`: explicit display label, present only when the target was
  passed as `label=SOURCE`; otherwise `null`.
- `target_source`: original `--target` source string, such as `.`,
  `/path/to/repo`, `@main`, or `#33`.
- `target_path`: absolute checkout path used for the build.
- `target_git_ref`: git ref used for the checkout, or `HEAD` for path targets.
- `target_git_sha`: resolved HEAD commit used for the build.
- `target_is_dirty`: whether the checkout had relevant local changes when
  built.

File fields:

- `file_path`: benchmark file path as invoked.
- `file_sha256`: SHA-256 of the file contents.

Timing fields:

- `wall_sec`: measured child-process wall time.
- `user_sec`: child-process user CPU time when available, otherwise `null`.
- `system_sec`: child-process system CPU time when available, otherwise `null`.
- `cpu_wall_ratio`: `(user_sec + system_sec) / wall_sec` when available,
  otherwise `null`.
- `max_rss_bytes`: child-process max resident set size in bytes when available,
  otherwise `null`.

For `status: timed-out`, `wall_sec`, `user_sec`, `system_sec`,
`cpu_wall_ratio`, and `max_rss_bytes` are `null`. The row records only that the
run did not complete before `timeout_sec`, so the true runtime is greater than
the timeout.

Rows with `status: timed-out` or `status: failure` can include:

- `error_exit_code`: process exit code when available.
- `error_signal`: terminating signal when available.
- `error_message`: short runner-generated error message.

Example row:

```json
{
  "started_at": "2026-07-04T12:34:56Z",
  "status": "success",
  "target_label": null,
  "target_source": ".",
  "target_path": "/Users/saul/p/egglog-encoding",
  "target_git_ref": "HEAD",
  "target_git_sha": "abc123...",
  "target_is_dirty": true,
  "binary_sha256": "sha256:...",
  "file_path": "egglog/tests/foo.egg",
  "file_sha256": "sha256:...",
  "treatment": "proofs",
  "timeout_sec": 120,
  "wall_sec": 1.23,
  "user_sec": 1.18,
  "system_sec": 0.04,
  "cpu_wall_ratio": 0.99,
  "max_rss_bytes": 123456789,
  "error_exit_code": null,
  "error_signal": null,
  "error_message": null
}
```

Running `./bench.py` always prints the report. For each target/file/treatment
cell, cache sufficiency is at least `--rounds` matching rows of any status. If
enough matching rows exist, the script takes the `--rounds` most recent rows by
`started_at`, breaking timestamp ties by later JSONL file order, analyzes them,
and prints. If observations are missing, it collects only the missing rows,
appends them, then prints. With `--force-run`, the script always appends new
rows first and then analyzes the `--rounds` most recent matching rows by
`started_at` and JSONL file order.

The stderr output shows the cache plan and final selected observations.
The cache plan reports cached rows, missing rows, selected cached statuses,
exact-cell duration estimates, and estimated fresh collection time. Estimates
use only successful rows with the same binary SHA-256, file SHA-256, treatment,
and timeout; if no exact successful rows exist, the estimate is reported as
unknown rather than borrowing data from another target or binary.
During fresh collection, `observations` are measured report rows and
`subprocesses` are child process launches, including the one target startup
warmup when fresh rows are needed. Peak RSS is collected from the measured child
process resource usage and rendered separately from wall-time ratios.

The printed report is ordered so the final decision summary comes last. It
starts with report metadata and a target tree showing source, git revision,
binary hash, and checkout path. Multi-target reports then print per-file
wall-time changes and per-file peak RSS changes before per-target diagnostics.
The final `Benchmark summary` section contains the suite-level wall-time result
plus peak-RSS summaries. Multi-target wall-time ratios are `target / baseline`:
values below `1x` are faster than the baseline, and values above `1x` are
slower. The adjacent wall-time change column is derived from the same ratio:
negative percentages are faster and positive percentages are slower. Peak RSS
changes are rendered separately with less/more wording so memory is not mixed
into wall-time interpretation. Within-target overhead ratios are printed before
raw wall-time and peak-RSS tables. Result cells are labeled `faster`, `slower`,
`less`, `more`, `unclear`, `point only`, or `invalid`.

## Statistics

The benchmark unit is a full process execution of `egglog-experimental` on one
`.egg` file under one treatment. Python orchestration overhead is outside the
measured child process.

Collection and analysis behavior:

- Fresh complete collection uses paired execution rounds: each round runs the
  same target/file across all selected treatments in a balanced order.
  Cached analysis uses the selected rows as unpaired independent samples rather
  than recovering persisted round groups.
- When fresh rows are needed for a target, the runner starts with one untimed
  executable startup warmup. It does not use best-of-N or discard runs by
  folklore.
- The runner builds each target with `cargo build --release` before deciding
  whether cached timing rows can be reused.
- Cache identity comes from persisted fields: binary SHA-256, file SHA-256,
  treatment, and timeout. Target source, path, git ref, git SHA, and dirty flag
  are provenance/display fields; they do not prevent reuse when the binary
  SHA-256 matches.
- Timeouts are incomplete cells. The report shows where timeouts happened, but
  does not compute percent improvement, ratio confidence intervals, suite-pass
  overhead, or geometric-mean overhead for comparisons that include timed-out
  cells.
- Failures are invalid cells. Any target/file/treatment failure invalidates
  comparisons that depend on that cell until replacement observations are
  appended, for example with `--force-run`, and the selected latest rows for the
  cell are successful.

For a successful one-system target/file/treatment cell, the analysis computes
the arithmetic mean and the one-system t interval from "Quantifying Performance
Changes with Effect Size Confidence Intervals", Section 6.2. With `n` selected
successful `wall_sec` samples, sample mean `m`, unbiased sample variance `s^2`,
and 95% t critical value `t` with `n - 1` degrees of freedom:

```text
ci = [m - t * sqrt(s^2 / n), m + t * sqrt(s^2 / n)]
```

If `n < 2`, the printed report shows the mean because the interval is
undefined. When a confidence interval is defined, the printed report shows the
range, such as `[0.0183s, 0.0251s]`.

For a successful pairwise comparison, the analysis uses the one-level
Kalibera/Jones ratio-of-means confidence interval from "Quantifying Performance
Changes with Effect Size Confidence Intervals", Section
6.2.[^benchmark-provenance]

For baseline samples `B` and candidate samples `C`, with sample means `b` and
`c`, unbiased sample variances `s_b^2` and `s_c^2`, equal sample count `n`, and
95% t critical value `t` with `n - 1` degrees of freedom, the point ratio is:

```text
ratio = c / b
```

The Fieller-style interval is:

```text
a = b^2 - t^2 * s_b^2 / n
d = c^2 - t^2 * s_c^2 / n
center = b * c / a
half_width = sqrt((b * c)^2 - a * d) / a
ci = [center - half_width, center + half_width]
```

If `a <= 0` or the radicand is negative, the interval is undefined and the
comparison is inconclusive rather than using a different interval method. The
runner does not use arithmetic averages of percentages.

The benchmark files are the workload suite under evaluation. This follows the
Kalibera/Jones experiment-design framing: define the systems, workload set,
treatments, and repetition policy, then quantify uncertainty in the measured
means for that experiment. For `suite-pass` overhead, the runner sums the
per-file means for the candidate treatment and divides by the summed per-file
baseline means. Its confidence interval applies the same Fieller-style ratio
interval to the summed means, propagating run-to-run timing variance for the
specified suite.

For multi-target wall-time comparisons, the runner uses the same ratio-of-means
method with the first target as the baseline. It compares the same treatment
between targets, for example `candidate proofs / baseline proofs`, and prints
the fixed-suite wall-time change for each treatment, an equal-file geometric
mean ratio, and per-file ratios for diagnostics. This is separate from proof
overhead, which remains a within-target ratio such as `proofs / off`.

The report includes:

- per-file wall-time estimates for each treatment;
- per-file peak RSS estimates for each treatment when memory samples are
  available;
- `term / off` overhead;
- `proofs / off` total proof overhead;
- `proofs / term` marginal proof-generation overhead;
- total suite time ratio (`proofs/off`): summed mean proof time divided by
  summed mean baseline time, with a fixed-suite confidence interval;
- equal-file geometric mean ratio (`proofs/off`), which gives each benchmark
  file equal weight in the summary;
- for multiple targets, suite and per-file same-treatment wall-time changes
  relative to the first target, plus peak RSS changes with confidence intervals
  relative to the first target.

When a confidence interval is defined, printed estimate cells show the interval
range. When it is undefined, they show the point estimate.

The `<2x` goal is established only when the suite-pass proof overhead has a 95%
confidence interval upper bound below `2x`. This gate matches the project goal:
proof mode keeps total execution time for the specified benchmark suite below
`2x` the non-proof baseline, with uncertainty from repeated executions
accounted for. The printed suite summary has no separate status column; the gate
comes from the suite-pass confidence interval upper bound.

Methodology references:

- Kalibera and Jones, "Rigorous Benchmarking in Reasonable Time" (ISMM 2013):
  use an explicit experiment design, repeated benchmark units, and confidence
  intervals.
- Kalibera and Jones, "Quantifying Performance Changes with Effect Size
  Confidence Intervals" (University of Kent Technical Report 4-12): report
  effect sizes as ratios of mean execution times with confidence intervals.
- Fieller, "Some Problems in Interval Estimation" (1954), and Franz, "Ratios:
  A Short Guide to Confidence Limits and Proper Use" (2007): compute confidence
  intervals for ratios directly.
- Chen and Revels, "Robust Benchmarking in Noisy Environments" (2016): keep raw
  observations and avoid best-of-N summaries because timing data can be noisy
  and non-normal.
- Georges, Buytaert, and Eeckhout, "Statistically Rigorous Java Performance
  Evaluation" (OOPSLA 2007): report repeated-run means with uncertainty, not
  informal best/average/worst tables.
- Barrett, Bolz-Tereick, Killick, Mount, and Tratt, "Virtual Machine Warmup
  Blows Hot and Cold" (OOPSLA 2017): make the startup warmup policy explicit.
- Oleksenko, Kuvaiskii, Bhatotia, and Fetzer, "FEX: A Software Systems
  Evaluator" (DSN 2017): make the build-run-collect-report pipeline
  reproducible.

[^benchmark-provenance]: Earlier scripts in
    [`saulshanabrook/egglog_repro`](https://github.com/saulshanabrook/egglog_repro)
    and
    [discussion #15](https://github.com/saulshanabrook/saulshanabrook/discussions/15)
    helped identify this method, but they are provenance only. The statistics
    implementation comes from the cited papers.

## Repository layout

Layout:

- `egglog/`: subtree of `https://github.com/egraphs-good/egglog`.
- `egglog-experimental/`: subtree of
  `https://github.com/egraphs-good/egglog-experimental`.
- `Cargo.toml`: root workspace that includes both subtrees and any benchmark
  helper crates.
- `bench.py`: executable uv entrypoint for benchmark collection and reporting.
- `test_bench.py`: top-level pytest coverage for benchmark-runner logic.
- `pyproject.toml`: Python dependencies plus mypy, pytest, and ruff config.
- `uv.lock`: locked Python environment for benchmark-runner dependencies and
  developer tools.
- `.reports.jsonl`: ignored local benchmark report/cache.
- `AGENTS.md`: guidance for authors and LLMs on test order, benchmark
  expectations, and upstream/subtree hygiene.
- `.github/`: CI workflows.

The root README is the orientation and workflow reference.

## Upstream subtrees

`egglog/` and `egglog-experimental/` are git subtrees, not submodules. The root
workspace owns integration, CI, benchmarking, and local documentation, while
subtree-local source changes can be synced with or proposed back to the
upstream repositories.

To pull new upstream `egglog` changes into this repo:

```bash
git remote add upstream-egglog https://github.com/egraphs-good/egglog.git
git fetch upstream-egglog main
git subtree pull --prefix=egglog upstream-egglog main --squash
```

To pull new upstream `egglog-experimental` changes:

```bash
git remote add upstream-egglog-experimental \
  https://github.com/egraphs-good/egglog-experimental.git
git fetch upstream-egglog-experimental main
git subtree pull --prefix=egglog-experimental upstream-egglog-experimental main --squash
```

If the remotes already exist, skip the `git remote add` command. Commit or
stash local subtree edits before pulling, then run the root workspace checks
after resolving any conflicts.

To propose subtree-local changes upstream, split the subtree history into a
normal branch and push that branch to a fork or upstream branch:

```bash
git subtree split --prefix=egglog -b split/egglog
git push https://github.com/<you>/egglog.git split/egglog:<branch-name>
```

For `egglog-experimental`:

```bash
git subtree split --prefix=egglog-experimental -b split/egglog-experimental
git push https://github.com/<you>/egglog-experimental.git \
  split/egglog-experimental:<branch-name>
```

Open the upstream PR from the pushed branch. Root-only files such as
`bench.py`, this README, and `.github/workflows/build.yml` are not included in
the split branch.

## Profiles

Configured profiles:

- `dev`: `opt-level = 3`, which Cargo defines as all optimizations, with
  `line-tables-only` debug info for tracebacks.
- `test`: Cargo's built-in test profile inherits `dev`, so `cargo test` uses
  the same optimized build settings.
- `release`: Cargo's built-in optimized release profile for benchmark binaries.
- `profiling`: inherits `release` and adds debug symbols for profilers and
  samplers.

Cargo's profile behavior is documented in the
[Cargo profile reference](https://doc.rust-lang.org/cargo/reference/profiles.html).

Each benchmark report row records the binary hash used for that observation.

## CI

CI runs on pull requests, manual dispatch, and pushes to `main`. It runs these
job groups:

- `python`: `uv lock --check`, ruff/mypy checks for the top-level benchmark
  runner files, and pytest.
- `rust`: workspace tests, proof-focused tests, and clippy.
- `benchmark-smoke`: a one-round `./bench.py` run on
  `egglog/tests/integer_math.egg`.
- `codspeed`: an in-process, proofs-only `egglog-experimental` benchmark
  harness over a smaller representative file set, run through CodSpeed in both
  simulation and memory modes. CodSpeed tracks proof-mode movement without
  invoking `./bench.py`; the CLI benchmark report remains the source for the
  full off/term/proofs comparison.

Python checks are run as separate commands:

```bash
uv lock --check
uv run --locked ruff format --check bench.py cli.py models.py report_frame.py tables.py web.py web_registry.py test_bench.py
uv run --locked ruff check bench.py cli.py models.py report_frame.py tables.py web.py web_registry.py test_bench.py
uv run --locked mypy bench.py cli.py models.py report_frame.py tables.py web.py web_registry.py test_bench.py
uv run --locked pytest -q
```

Use `uv run ruff format bench.py cli.py models.py report_frame.py tables.py web.py web_registry.py test_bench.py` to apply formatting locally.
