# Egglog encoding

This repository is the target workspace for iterating on proof and term
encoding changes across `egglog` and `egglog-experimental`.

The goal is to make proof generation work with a reasonable slowdown before
porting the winning strategy back upstream. The current success target is:

- proof mode is less than `2x` slower than the non-proof baseline; and
- that claim is supported by benchmark reports with confidence intervals, not
  just point estimates.

## Daily workflow

The target development loop is:

```bash
# Run all egglog and egglog-experimental tests.
cargo test --workspace

# Run proof-focused tests while iterating.
cargo test --workspace proof

# Run lint checks across the workspace.
cargo clippy --workspace --all-targets

# Build release binaries for benchmark comparisons.
cargo build --release --workspace

# Run or reuse the default benchmark report.
./bench.py
```

The root workspace should include both `egglog` and `egglog-experimental`, and
`egglog-experimental` should depend on the local `egglog` path while developing
this repo. That keeps proof changes and downstream experimental behavior in the
same reviewable unit.

## Benchmarking

The public benchmark entrypoint is an executable Python script:

```bash
./bench.py [FILE ...] [OPTIONS]
```

`./bench.py` must use a uv script shebang so users can run it directly:

```python
#!/usr/bin/env -S uv run --script
```

The default command:

```bash
./bench.py
```

is equivalent to:

```bash
./bench.py --target .
```

It builds the current checkout, runs the default representative benchmark
files, appends any missing observations to `.reports.jsonl`, and prints a
Markdown report to stdout.

### Targets

Targets describe the builds being compared. Use one `--target` per build:

```bash
./bench.py --target @origin/main --target .
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
- `--target label=SOURCE` gives the target an explicit report label.
- `--target label=` reuses the latest cached target identity with that label
  from `--report`.

Rules:

- Git refs must use the `@` prefix. Paths must not.
- If no target is provided, the only target is `.`.
- If any target is provided, the target list is exactly what was specified.
- The first target is the comparison baseline.
- Explicit labels are display names. Cache identity is derived from the
  persisted report fields described below.
- `label=` lookup only considers rows that were written with explicit
  `target.label`. If the same label appears for multiple binary hashes, the
  row with the latest `started_at` timestamp for that label is the definitive
  label pointer, with ties broken by later JSONL file order. If that pointer
  refers to a clean git SHA, the runner may rebuild that SHA in an isolated
  worktree to collect more samples. If it points to a dirty checkout, it is
  report-only unless the user supplies a new `label=SOURCE`.
- Targets are built and measured sequentially. Path targets use the provided
  checkout directly. Git-ref targets should use an existing worktree at the
  resolved commit when one exists, otherwise the runner should create or reuse
  an isolated temporary worktree instead of stashing local changes in the main
  checkout.

### Files

Positional arguments are benchmark files:

```bash
./bench.py egglog/tests/foo.egg egglog/tests/bar.egg
```

If no files are provided, the default target benchmark suite is:

- `egglog/tests/web-demo/unification-points-to.egg`
- `egglog/tests/web-demo/rw-analysis.egg`
- `egglog/tests/integer_math.egg`
- `egglog/tests/proof-extract-cost.egg`

These four files are proof-compatible representative examples. The runner should
validate default files against `off`, `term`, and `proofs` before timing them.
Relative file paths are resolved relative to the directory where `./bench.py`
was invoked, not relative to each target checkout. The same file contents are
used for every target, and `file.sha256` records the exact benchmark input.

### Options

The benchmark CLI should expose only the options users need routinely:

- `--report <path>`: JSONL report/cache path. Default: `.reports.jsonl`.
- `--rounds <n>`: fresh collection rounds per file and target, and matching
  report rows required per cache cell. Default: `6`.
- `--warmup <n>`: untimed warmup runs per target, file, and treatment. Default:
  `1`.
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

`--proof-testing` is a correctness mode, not a benchmark treatment, and should
not appear in performance headlines.

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

`.reports.jsonl` is the canonical benchmark artifact and must be ignored by git.
Use `--report <path>` to choose a different report file.

The report file is append-only JSONL. Each line records one process execution
and is a measured timing observation, not a derived summary. The row should
contain the fields needed to recompute cache identity.

Required row fields:

- `started_at`: ISO timestamp for the measured child process start.
- `status`: `success`, `timed-out`, or `failure`.
- `target`: object describing the benchmarked source tree.
- `binary_sha256`: SHA-256 of the built `target/release/egglog-experimental`
  binary.
- `file`: object describing the `.egg` input.
- `treatment`: `off`, `term`, or `proofs`.
- `warmup_rounds`: number of untimed warmup runs used for this
  target/file/treatment.
- `timeout_sec`: per-process timeout.
- `timing`: measured child-process timing and resource data.

Required `target` fields:

- `source`: original `--target` source string, such as `.`, `/path/to/repo`, or
  `@main`.
- `path`: absolute checkout path used for the build.
- `git_ref`: git ref used for the checkout, or `HEAD` for path targets.
- `git_sha`: resolved HEAD commit used for the build.
- `is_dirty`: whether the checkout had relevant local changes when built.

Optional `target` fields:

- `label`: explicit display label, present only when the target was passed as
  `label=SOURCE`. If absent, report output should infer a label from `git_ref`,
  `git_sha`, or `path`.

Required `file` fields:

- `path`: benchmark file path as invoked.
- `sha256`: SHA-256 of the file contents.

Required `timing` fields:

- `wall_sec`: measured child-process wall time.
- `user_sec`: child-process user CPU time when available, otherwise `null`.
- `system_sec`: child-process system CPU time when available, otherwise `null`.
- `cpu_wall_ratio`: `(user_sec + system_sec) / wall_sec` when available,
  otherwise `null`.
- `max_rss_bytes`: max resident set size when available, otherwise `null`.

For `status: timed-out`, `wall_sec`, `user_sec`, `system_sec`,
`cpu_wall_ratio`, and `max_rss_bytes` are `null`. The row records only that the
run did not complete before `timeout_sec`, so the true runtime is greater than
the timeout.

Rows with `status: timed-out` or `status: failure` may include:

- `error.exit_code`: process exit code when available.
- `error.signal`: terminating signal when available.
- `error.message`: short runner-generated error message.

Example row:

```json
{
  "started_at": "2026-07-04T12:34:56Z",
  "status": "success",
  "target": {
    "source": ".",
    "path": "/Users/saul/p/egglog-encoding",
    "git_ref": "HEAD",
    "git_sha": "abc123...",
    "is_dirty": true
  },
  "binary_sha256": "sha256:...",
  "file": {
    "path": "egglog/tests/foo.egg",
    "sha256": "sha256:..."
  },
  "treatment": "proofs",
  "warmup_rounds": 1,
  "timeout_sec": 120,
  "timing": {
    "wall_sec": 1.23,
    "user_sec": 1.18,
    "system_sec": 0.04,
    "cpu_wall_ratio": 0.99,
    "max_rss_bytes": 123456789
  }
}
```

Running `./bench.py` should always print the report. For each
target/file/treatment cell, cache sufficiency is at least `--rounds` matching
rows of any status. If enough matching rows exist, the script should take the
`--rounds` most recent rows by `started_at`, breaking timestamp ties by later
JSONL file order, analyze them, and print. If observations are missing, it
should collect only the missing rows, append them, then print. With
`--force-run`, the script always appends new rows first and then analyzes the
`--rounds` most recent matching rows by `started_at` and JSONL file order.

## Statistics

The benchmark unit is a full process execution of `egglog-experimental` on one
`.egg` file under one treatment. Python orchestration overhead is outside the
measured child process.

Required defaults:

- When collecting a fresh complete set, use paired execution rounds: each round
  runs the same target/file across all selected treatments in a balanced order.
  Cached analysis does not require recovering persisted round groups; it may use
  the selected rows as unpaired independent samples.
- Use a small fixed warmup. Do not use best-of-N or discard runs by folklore.
- Run `cargo build --release` for each target before deciding whether cached
  timing rows can be reused.
- Derive cache identity from persisted fields: binary SHA-256, file SHA-256,
  treatment, warmup count, and timeout. Target source, path, git ref, git SHA,
  and dirty flag are provenance/display fields; they do not prevent reuse when
  the binary SHA-256 matches.
- Treat timeouts as incomplete cells. The report should show where timeouts
  happened, but should not compute percent improvement, ratio confidence
  intervals, suite-pass overhead, or geometric-mean overhead for comparisons
  that include timed-out cells.
- Treat failures as invalid cells. Any target/file/treatment failure invalidates
  comparisons that depend on that cell until replacement observations are
  appended, for example with `--force-run`, and the selected latest rows for the
  cell are successful.

For a successful one-system target/file/treatment cell, report the arithmetic
mean and the one-system t interval from "Quantifying Performance Changes with
Effect Size Confidence Intervals", Section 6.2. With `n` selected successful
`wall_sec` samples, sample mean `m`, unbiased sample variance `s^2`, and 95% t
critical value `t` with `n - 1` degrees of freedom:

```text
ci = [m - t * sqrt(s^2 / n), m + t * sqrt(s^2 / n)]
```

If `n < 2`, report the mean and mark the interval as undefined.

For a successful pairwise comparison, use the one-level Kalibera/Jones
ratio-of-means confidence interval from "Quantifying Performance Changes with
Effect Size Confidence Intervals", Section 6.2.[^benchmark-provenance]

For baseline samples `B` and candidate samples `C`, with sample means `b` and
`c`, unbiased sample variances `s_b^2` and `s_c^2`, equal sample count `n`, and
95% t critical value `t` with `n - 1` degrees of freedom, report the point
overhead as:

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

If `a <= 0` or the radicand is negative, mark the interval as undefined and the
comparison as inconclusive rather than substituting a different interval method.
Do not use arithmetic averages of percentages.

Treat the benchmark files as the workload suite under evaluation. This follows
the Kalibera/Jones experiment-design framing: define the systems, workload set,
treatments, and repetition policy, then quantify uncertainty in the measured
means for that experiment. For `suite-pass` overhead, sum the per-file means for
the candidate treatment and divide by the summed per-file baseline means. For
its confidence interval, apply the same Fieller-style ratio interval to the
summed means, propagating run-to-run timing variance for the specified suite.

The report should include:

- per-file means and confidence intervals for each treatment;
- `term / off` overhead;
- `proofs / off` total proof overhead;
- `proofs / term` marginal proof-generation overhead;
- suite-pass proof overhead: summed mean proof time divided by summed mean
  baseline time, with a fixed-suite confidence interval;
- equal-file geometric-mean proof overhead, which gives each benchmark file
  equal weight in the summary;
- for multiple targets, commit deltas within each treatment and a
  ratio-of-ratios for proof overhead changes.

The `<2x` target passes only when the suite-pass proof overhead has a 95%
confidence interval upper bound below `2x`. This gate matches the stated goal:
proof mode should keep total execution time for the specified benchmark suite
below `2x` the non-proof baseline, with uncertainty from repeated executions
accounted for.

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
  Blows Hot and Cold" (OOPSLA 2017): make warmup policy explicit and fixed.
- Oleksenko, Kuvaiskii, Bhatotia, and Fetzer, "FEX: A Software Systems
  Evaluator" (DSN 2017): make the build-run-collect-report pipeline
  reproducible.

[^benchmark-provenance]: Earlier scripts in
    [`saulshanabrook/egglog_repro`](https://github.com/saulshanabrook/egglog_repro)
    and
    [discussion #15](https://github.com/saulshanabrook/saulshanabrook/discussions/15)
    helped identify this method, but they are provenance only. The statistics
    specification above should be implemented from the cited papers.

## Repository layout

Target layout:

- `egglog/`: subtree of `https://github.com/egraphs-good/egglog`.
- `egglog-experimental/`: subtree of
  `https://github.com/egraphs-good/egglog-experimental`.
- `Cargo.toml`: root workspace that includes both subtrees and any benchmark
  helper crates.
- `bench.py`: executable uv script for benchmark collection and reporting.
- `.reports.jsonl`: ignored local benchmark report/cache.
- `AGENTS.md`: guidance for authors and LLMs on test order, benchmark
  expectations, and upstream/subtree hygiene.
- `.github/`: CI workflows.

The root README is the orientation and workflow contract. Detailed design notes
belong in focused docs or ADRs once implementation decisions stabilize.

## Profiles

Target profiles:

- `dev`: optimized enough for realistic local testing, with useful debug info.
- `test`: same optimization expectations as `dev`.
- `release`: full optimization for benchmark binaries.
- `bench`: same codegen expectations as `release`.
- `profile`: release-like optimization with debug symbols for profilers and
  samplers.

Benchmark reports must record the binary hash used for each observation.

## CI

Target CI should run:

- workspace tests;
- proof-focused tests;
- clippy;
- benchmark script smoke tests;
- statistical fixture tests for the reporter;
- advisory performance checks on PRs;
- CodSpeed timing and memory benchmarks on the default benchmark files. These
  should use an in-process benchmark harness, such as a `benches/files.rs`
  equivalent of the CLI file runner, so CodSpeed measures the same workloads
  even though it does not invoke `./bench.py`.
