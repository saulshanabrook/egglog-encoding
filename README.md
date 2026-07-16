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

`make benchmark-smoke` writes its machine-readable report to
`/tmp/egglog-encoding-bench-smoke.jsonl`, so it neither reads nor appends to the
default benchmark cache. Override `BENCHMARK_SMOKE_REPORT` to choose another
temporary output path.

`make update-snapshots` is the explicit review action for accepting intentional
changes to deterministic Markdown report snapshots.

Run or reuse the default benchmark suite separately when you want performance
results rather than validation:

```bash
./bench.py
```

The root workspace includes both `egglog` and `egglog-experimental`.
`egglog-experimental` depends on the workspace `egglog` crate, which keeps proof
changes and downstream experimental behavior in the same reviewable unit.

Proof-specific file tests use one filter prefix:

- `proofs/`: explicit `(prove ...)` fixtures under `tests/proofs` plus every
  proof-compatible file under proof-testing mode. Checks are treated as prove
  commands and generated proofs are saved as snapshots.

The proof filter is a subset of the full workspace test run. Use
`make proof-tests` for fast proof iteration and `make rust-check` or `make check`
for the final compatibility gate.

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
Rich terminal report to stderr. Use `--report PATH` to read and append another
report file without touching the default cache.

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
- Targets that produce the same binary SHA-256 are rejected because they would
  select the same cached observations rather than independent comparison data.
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

Positional arguments are benchmark files. Use `--fact-directory` for workloads
containing `(input ...)` commands:

```bash
./bench.py egglog/tests/foo.egg egglog/tests/bar.egg
./bench.py benchmarks/pointer.egg --fact-directory benchmarks/data/pointer
```

If no files are provided, the default target benchmark suite is:

- `egglog/tests/math-microbenchmark.egg`
- `egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg`
- `benchmarks/pointer-analysis-small.egg`, with its checked-in sample data in
  `benchmarks/data/pointer-analysis-small`
- `egglog/tests/hardboiled_conv1d_32.egg`
- `benchmarks/luminal-llama.egg`
- `egglog/tests/web-demo/herbie.egg`

These six files are proof-compatible representative examples under the current
`egglog-experimental` CLI and run under the default `off`, `term`, and `proofs`
treatment matrix. The eggcc fixture is the heavy container/proof benchmark in
the default suite. The pointer-analysis workload uses the first 100 rows from
each input relation of the artifact's smallest `initdb.bc` dataset so all three
treatments complete within the standard timeout.

| Workload | Compatibility adaptation | Correctness signal |
| --- | --- | --- |
| Math | Existing synthetic stress fixture | Existing checks and proof snapshots |
| eggcc 2mm | Existing bounded container fixture | Existing checks and proof snapshots |
| Pointer analysis | 100-row samples for 23 input relations; three legacy function declarations become constructors because current egglog requires merge modes and disallows rule-body lookup on `:no-merge` functions | Known `constant_points_to` row is derived |
| Hardboiled | Dormant canonicalization rules using unsupported unstable helpers are omitted | Extracted WMMA store result is checked |
| Luminal | Static Llama graph imported from [`egglog_repro` commit `7fb0194`](https://github.com/saulshanabrook/egglog_repro/blob/7fb0194812b5b11e41a286d8b55e48e3b0bfcd66/llama.egg) | `t712` is checked after kernel lowering |
| Herbie | Static engine proxy; no end-to-end Racket orchestration or FPCore corpus | All 14 existing checks run through the proof checker |

Relative file paths are resolved relative to the directory where `./bench.py`
was invoked, not relative to each target checkout. The same file contents are
used for every target, and `file.sha256` records the exact benchmark input. The
default workload table also owns any per-file fact-directory configuration.
Two selected files with the same file and fact-directory hashes are rejected;
they would otherwise address the same cached observations as two suite members.
Final report tables normally show only each filename. If selected files share a
filename, the report uses the shortest path suffix that distinguishes them. The
initial collection plan and machine-readable report rows retain full paths.

### Options

The benchmark CLI exposes the routine collection and reporting options:

Positional files together with `--target`, `--backend`, and `--treatments`
define the selected benchmark results. Display options do not select a
different subset: every enabled report view covers every selected result.

- `--report <path>`: append-only JSONL report/cache path. Default:
  `.reports.jsonl`. Literal `-` is rejected; use a disposable path under
  `/tmp` when the default cache should remain untouched.
- `--format <rich|markdown>`: human-readable report format. Rich output goes to
  stderr; Markdown goes to stdout. Default: `rich`.
- `--rounds <n>`: fresh collection rounds per target, file, backend, and
  treatment result, and matching report rows required for cache reuse.
  Default: `6`.
- `--timeout-sec <n>`: per-process timeout. Default: `120`.
- `--fact-directory <path>`: fact directory used by explicitly selected
  benchmark files. The default suite supplies its fixture-specific fact
  directory internally.
- `--backend <list>`: comma-separated backends. Default: `main`.
- `--treatments <list>`: comma-separated treatments. Default:
  `off,term,proofs`.
- `--phase-timings`: display a compact engine-timing breakdown for every
  selected result.
- `--detailed-timing`: display the compact timing breakdown followed by every
  recorded ruleset for every selected result.
- `--duckdb-ui`: after rendering the report, open DuckDB's official local UI
  on the same transient in-memory database. The selected report scope and
  analysis views are available for interactive SQL. This requires interactive
  stdin; press Enter or Ctrl-C in the benchmark terminal to close the session.
  DuckDB installs and loads its `ui` extension on first use and the UI frontend
  may fetch remote assets, so opening it can require network access.
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
  --timing-summary <temporary-path> \
  --mode no-messages \
  -j 1 \
  [--fact-directory <path>] \
  [--term-encoding | --proofs] \
  <file.egg>
```

Benchmarking runs single-threaded. Direct egglog CLI use likewise requires
`-j 1` whenever `--timing-summary` is requested; the CLI exits before running
when a larger thread count would make overlapping Search and Apply times
non-additive. Ordinary runs without `--timing-summary` may still use multiple
threads.

### Engine timing breakdown

Every successful benchmark observation records the engine time attributed to
each ruleset: Search, Apply, Merge, and Rebuild. The runner reads the
summary produced by the measured child process and stores it in the same
`.reports.jsonl` row as wall time and peak RSS. It does not run a separate
diagnostic process, and a timing view does not request observations beyond
those required by the ordinary benchmark and cache policy.

The ordinary human-readable benchmark summary remains unchanged unless a
timing view is requested. Show a compact breakdown for every selected result
with:

```bash
./bench.py --phase-timings
```

For a result whose selected `--rounds` observations are all successful, the
compact view reports their arithmetic means for Search, Apply, Merge, Rebuild,
Other, and Wall. Other is mean Wall minus the four unrounded mean phase totals
summed across every ruleset. It includes all process time not charged to those
timers, such as process setup and reporting, and is not an engine phase.

If Other is negative, the timing view prefixes the negative value
with `!` and explains that attributed time exceeds wall time. This is a
display-only attribution warning computed before rounding: the requested timing
view is still shown, ordinary wall-time and peak-RSS results remain valid, and
the command does not fail. An incomplete or invalid result instead shows its
ordinary status and no aggregate phase values; the renderer never averages only
the successful subset of a mixed-status result.

The complete compact overview appears before any per-ruleset detail. Results
are grouped by file and backend/treatment, with compared targets adjacent and
the baseline first. Rich output uses one numeric table layout designed for
terminals at least 120 columns wide. Below 120 columns it prints one warning and
renders the same table best-effort: identity fields may fold while numeric
values remain on one line. Widen the terminal or use Markdown when wrapping
makes a narrow report difficult to read. Widths below 80 have no readability
guarantee. Markdown uses the same values in a width-independent table and
preserves full result names and values.

The ordinary selectors determine which results appear. For example:

```bash
# Compare the same proof workload between two commits.
./bench.py FILE --target main=@origin/main --target mine=. \
  --treatments proofs --phase-timings

# Compare the main and DD backends on one proof workload.
./bench.py FILE --backend main,dd --treatments proofs --phase-timings
```

Add a complete per-ruleset breakdown beneath every selected result with:

```bash
./bench.py egglog/tests/integer_math.egg \
  --treatments proofs --detailed-timing
```

`--detailed-timing` implies `--phase-timings`. It shows every recorded ruleset;
there is no timing-specific result selector or top-N storage/display limit.
Narrow a verbose report with the ordinary selectors:

```bash
./bench.py FILE --target main=@origin/main --target mine=. \
  --backend main --treatments proofs --detailed-timing
```

Running `--detailed-timing` without explicit narrowing selectors is
intentionally exhaustive. For a long report, use Markdown rather than relying
on terminal history:

```bash
./bench.py --detailed-timing --format markdown > timing-report.md
```

For each file and backend/treatment comparison group, the DuckDB timing view
takes the union of ruleset names across the fully successful results and all of
their selected observations. Each fully successful target receives its own
aligned ruleset rows, and all target tables use the same ruleset order. A
ruleset that never appears for one target is represented by SQL `NULL` and
displayed as `—` for every phase, Total, and Share; a ruleset explicitly
recorded with zero duration remains `0 ns`. Once a ruleset appears in at least
one selected observation for a target, observations where it did not run
contribute zero so its mean still covers every selected observation rather than
only the runs where it was active. An incomplete or invalid result contributes
no names or values to this union and receives a status block instead of a
ruleset table.

For a ruleset, Total is its unrounded mean Search + Apply + Merge + Rebuild.
Share is Total divided by the sum of every present ruleset Total for that same
target, file, backend, and treatment result. Share is displayed as `—` for an
absent ruleset or whenever that denominator is zero, including an empty summary
or a nonempty summary whose rulesets all report zero time. Rulesets are ordered
by the largest unrounded mean Total they reach in any target in the comparison
group, then by the exact ruleset name as a lexical tie-breaker. The empty name
is displayed as `<default ruleset>`.

Rich output at 120 columns or more uses `Ruleset`, `Total`, `Share`,
`Search`, `Apply`, `Merge`, and `Rebuild` columns. Below 120 columns the same
table renders best-effort after the command's single width warning; ruleset
names may fold, but numeric values remain on one line. Markdown preserves every
full name.
Across compact and detailed views, each duration independently chooses a unit
from its absolute magnitude: `ns` below 1 us, `us` below 1 ms, `ms` below 1 s,
and `s` otherwise. Values retain three significant digits and include the unit.
Shares use one decimal place; a nonzero share below the displayed precision is
written as `<0.1%` rather than zero.

The phase boundaries are:

- Search: matching and join execution.
- Apply: executing rule-head instructions and staging updates.
- Merge: resolving and installing staged updates.
- Rebuild: rebuilding indexes and e-graph state.

Main egglog interleaves Search and Apply. Each inline `run_instrs` action batch
is timed and subtracted from its enclosing plan-execution span. The final flush
is also timed as Apply; because it occurs after plan execution, it needs no
subtraction. Batches contain at most 128 matches, so this adds stopwatch calls
per batch rather than per match. DD times
materializing `fused_bindings` as Search, its `apply_head` loop as Apply, and
installation of collected writes as Merge. DD has no separate union-find
rebuild phase, so it reports Rebuild as zero. The exact mechanisms remain
backend-specific, but both backends use the same semantic boundaries above.

The engine enables these split-phase stopwatches only for serial
`--timing-summary` execution. Ordinary programmatic runs retain the existing
combined Search+Apply report without the new per-batch clocks; in particular,
the in-process CodSpeed harness does not enable them.

These measurements are aggregated by ruleset across engine iterations within
one process; they are not per-rule or per-iteration profiles. The stored
summary contains only the ruleset name and the four primitive phase totals.
Search+Apply and Other are derived by DuckDB rather than persisted.

A failed or timed-out observation has no timing summary and remains invalid or
incomplete under the ordinary report rules rather than being treated as zero.
Phase values are descriptive attribution; the existing wall-time and peak-RSS
comparisons and confidence intervals, where defined, remain the
regression-decision surface. Phase means and shares do not receive confidence
intervals or faster/slower labels.

Every selected target must support `--timing-summary`, even when no timing view
is displayed, because every successful benchmark row stores the summary. A
revision from before this interface was added must first receive the compact
timing-summary support; it is not run through a legacy fallback.

Use the separate `profile` command below for call-stack-level investigation.
CodSpeed uses its own in-process harness and does not request or store timing
summaries.

### CPU profiling

Use the same entrypoint with the `profile` subcommand to record or reuse a
Samply CPU profile for one workload:

```bash
./bench.py profile egglog/tests/integer_math.egg
./bench.py profile egglog/tests/integer_math.egg --target @origin/main --open
```

Profiling defaults to the `proofs` treatment and automatically calibrates an
iteration count for a roughly ten-second recording. Profiles are cached under
`.profiles`; use `--force-run` to replace a cached recording,
`--profile-seconds` or `--iterations` to control its duration, and `--open` to
load it in Samply. Run `./bench.py profile --help` for the complete option list.

## Reports

`.reports.jsonl` is a disposable local benchmark cache and is ignored by git.
The benchmark runner is its only supported reader and writer. Use
`--report <path>` to choose a different cache file. The option always requires
a filesystem path; literal `-` is rejected. Runner progress, build information,
and errors go to stderr. The final Rich report also goes to stderr; the final
Markdown report goes to stdout.

The report file is append-only JSONL. Each line records one process execution
and is a measured timing observation, not a derived summary. The row contains
the identity and timing fields needed for cache selection plus the nested raw
engine-timing summary from that execution. The report does not store
`row_index`; the runner derives row order from the JSONL file order when it
loads the report. Each observation is appended as soon as its subprocess
finishes, so an interrupted long-running benchmark retains every completed
observation instead of waiting for a whole-file rewrite or end-of-run flush.

The runner opens a private in-memory DuckDB catalog and reads this JSONL file
directly through a concrete nested record schema. The catalog owns only types,
selected-scope tables, analysis views, and output-facing views: report rows are
not copied into another table, and no `.duckdb` database or WAL file is created.
Cache selection and report analysis use bulk, set-oriented operations rather
than scanning once per target/file/backend/treatment result. Appending remains
a direct, one-line JSONL filesystem write.

Use `./bench.py --duckdb-ui` to inspect that in-memory database interactively
after the ordinary report is rendered. The browser UI runs locally and queries
the same in-memory DuckDB instance, so closing the benchmark process also
closes the UI and discards its transient catalog. The report JSONL remains the
only benchmark cache on disk. Query execution and report data remain local by
default, while the UI frontend may load assets from DuckDB's configured remote
UI host.

The UI exposes selector metadata in `presentation_targets`,
`presentation_files`, and `presentation_cells`; typed report datasets in
`presentation_cell_estimates`, `presentation_file_ratios`, and
`presentation_comparison_rollups`; and timing datasets in
`presentation_compact_timings` and `presentation_ruleset_timings`. For example:

```sql
SELECT * FROM presentation_comparison_rollups;
SELECT * FROM presentation_compact_timings;
SELECT * FROM presentation_ruleset_timings;
```

These views contain numeric values, coordinates, result classifications, and
issues rather than preformatted terminal strings. Python only selects report
sections, arranges their columns, formats units and wording, and serializes the
result as Rich or Markdown.

The persisted Python and SQL schemas deliberately mirror one another:
`ReportRecord` matches `report_record_t`, `TimingSummaryRecord` matches
`timing_summary_record_t`, and `RulesetTimingRecord` matches
`ruleset_timing_record_t`, including field names and order. A shape edit must
update both definitions. There are no report migrations: DuckDB strictly casts
every existing row when the cache is opened, so move or remove an incompatible
cache and rerun the benchmark.

Row fields:

- `started_at`: ISO timestamp for the measured child process start.
- `status`: `success`, `timed-out`, or `failure`.
- `binary_sha256`: SHA-256 of the built `target/release/egglog-experimental`
  binary.
- `backend`: `main` or `dd`.
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
- `fact_directory_path`: absolute fact-directory path, or `null` when the
  workload has no external facts.
- `fact_directory_sha256`: deterministic SHA-256 of relative file names and
  contents under the fact directory, or the empty string when absent.

Timing fields:

- `wall_sec`: measured child-process wall time.
- `max_rss_bytes`: child-process max resident set size in bytes when available,
  otherwise `null`.
- `timing_summary`: the compact ruleset timing produced by the same child
  process. It is required for `status: success` and `null` for failed or
  timed-out observations.

`timing_summary.schema_version` is `1`. Its `rulesets` array contains every
ruleset name present in the engine report, without a producer-side cap. Each
ruleset has nonnegative integer nanosecond fields `search_ns`, `apply_ns`,
`merge_ns`, and `rebuild_ns`. The empty string is the engine's default-ruleset
name. The transport sorts names lexically. Search and Apply are required for
every included ruleset; absent Merge and Rebuild entries are zero-filled.
DuckDB's analysis and output views derive
Search+Apply, Other, the comparison-oriented order, totals, and shares described
above when a report is queried; those values are not stored in each observation.

For `status: timed-out`, `wall_sec`, `max_rss_bytes`, and `timing_summary` are
`null`. The row records only that the run did not complete before
`timeout_sec`, so the true runtime is greater than the timeout. Failed rows
also store `timing_summary: null`; their ordinary process timing remains
available when the operating system reported it.

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
    "schema_version": 1,
    "rulesets": [
      {
        "name": "rules",
        "search_ns": 200,
        "apply_ns": 100,
        "merge_ns": 40,
        "rebuild_ns": 50
      }
    ]
  }
}
```

Report loading trusts files written by this tool. DuckDB's ordinary
JSON-to-STRUCT conversion owns shape and type conversion; the runner does not
add field-by-field validation or reject values that DuckDB can coerce. It
eagerly casts the complete cache to the current record shape when it opens. A
structurally incompatible or otherwise unreadable cache produces one generic
error asking the user to move or remove it and recompute the benchmarks, before
targets are built or observations are collected. There is no root report
version, migration, legacy phase fallback, or partial old-format rendering.
The nested timing-summary version remains a separate engine interface and is
checked before a successful observation is appended. A selected target that
does not support `--timing-summary` likewise fails preflight before timed
collection begins.

Running `./bench.py` always prints the report. For each target, file, backend,
and treatment result, cache sufficiency is at least `--rounds` matching rows of
any status. If enough matching rows exist, the script takes the `--rounds` most
recent rows by `started_at`, breaking timestamp ties by later JSONL file order,
analyzes them, and prints. If observations are missing, it collects only the
missing rows, appends them, then prints. With `--force-run`, the script always
appends new rows first and then analyzes the `--rounds` most recent matching
rows by `started_at` and JSONL file order.

The stderr output shows the cache plan and final selected observations.
The cache plan reports cached rows, missing rows, selected cached statuses,
exact-result duration estimates, and estimated fresh collection time. Estimates
use only successful rows with the same binary SHA-256, file SHA-256,
fact-directory SHA-256, backend, treatment, and timeout; if no exact successful
rows exist, the estimate is reported as unknown rather than borrowing data from
another target, binary, or input dataset.
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
raw wall-time and peak-RSS tables. Comparisons are labeled `faster`, `slower`,
`less`, `more`, `unclear`, `point only`, or `invalid`.

## Statistics

The benchmark unit is a full process execution of `egglog-experimental` on one
`.egg` file with one backend and treatment. Python orchestration overhead is
outside the measured child process.

Collection and analysis behavior:

- Fresh complete collection uses paired execution rounds: each round runs the
  same target/file across all selected backend/treatment combinations in a
  stable order. Cached analysis uses the selected rows as unpaired
  independent samples rather than recovering persisted round groups.
- When fresh rows are needed for a target, the runner starts with one untimed
  executable startup warmup. It does not use best-of-N or discard runs by
  folklore.
- For source targets, the runner builds with `cargo build --release` before
  deciding whether cached timing rows can be reused. A cache-only `label=`
  target skips the build when every requested row is already present.
- Cache identity comes from persisted fields: binary SHA-256, file SHA-256,
  fact-directory SHA-256, backend, treatment, and timeout. Target source, path,
  git ref, git SHA, dirty flag, and fact-directory path are provenance/display
  fields; they do not prevent reuse when the content hashes match. A single
  request therefore requires unique binary hashes and unique file/fact hashes.
- Timeouts are incomplete results. The report shows where timeouts happened, but
  does not compute percent improvement, ratio confidence intervals, suite-pass
  overhead, or geometric-mean overhead for comparisons that include timed-out
  results.
- Failures are invalid results. Any target/file/backend/treatment failure
  invalidates comparisons that depend on that result until replacement
  observations are appended, for example with `--force-run`, and the selected
  latest rows for the result are successful.

For a successful one-system target/file/backend/treatment result, the analysis
computes the arithmetic mean and the one-system t interval from "Quantifying
Performance Changes with Effect Size Confidence Intervals", Section 6.2. With
`n` selected successful `wall_sec` samples, sample mean `m`, unbiased sample
variance `s^2`, and 95% t critical value `t` with `n - 1` degrees of freedom:

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

When a confidence interval is defined, printed estimates show the interval
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
- `bench.py`: executable uv entrypoint for benchmark collection and profiling.
- `benchmarking/`: benchmark selection and collection, report persistence and
  rendering, engine-timing summaries, target resolution, and profiling.
- `tests/`: domain-focused pytest coverage for the benchmark tooling.
- `Makefile`: canonical validation, formatting, proof-test, and benchmark-smoke
  interface.
- `pyproject.toml`: Python dependencies plus mypy, pytest, and ruff config.
- `uv.lock`: locked Python environment for benchmark-runner dependencies and
  developer tools.
- `.reports.jsonl`: ignored, disposable local benchmark cache.

Python package boundaries:

- `benchmarking/cli.py` performs top-level command dispatch;
  `benchmark.py` composes an ordinary benchmark run, and
  `benchmark_config.py` owns ordinary CLI parsing, workload selection, and
  validation.
- `benchmarking/collection.py` performs report-aware target resolution, plans
  cache-aware runs, and constructs report records; `processes.py` measures child
  processes and owns their result types. `targets.py` parses and materializes
  generic target sources, builds them, and constructs child commands.
- `benchmarking/models.py` contains dependency-free shared identities, backend
  metadata and display/comparison helpers, and canonical benchmark-cell
  ordering; `output.py` contains operational stderr output only.
- `benchmarking/profile.py` owns profile requests and records and caches Samply
  profiles; `samply_analysis.py` reads, summarizes, and renders those artifacts.
- `benchmarking/reports/records.py` defines the trusted JSONL `TypedDict`
  writer contract. `database.py` owns the transient DuckDB catalog, selected
  scope, append/query boundary, and typed conversion of output-view rows.
- `benchmarking/reports/sql/schema.sql` defines the JSONL projection and scope;
  `analysis.sql` owns statistics and timing aggregation; `presentation.sql`
  exposes the semantic datasets consumed by both Python and the DuckDB UI.
- `benchmarking/reports/results.py` mirrors those output-view schemas as named
  tuples and contains renderer-neutral table values. `summary.py` selects
  comparisons and lays out ordinary tables without recomputing report facts.
- `benchmarking/reports/timing.py` lays out timing tables and formats their
  SQL-derived values; `render.py` is the only owner of Rich/Markdown syntax and
  terminal width behavior.
- Package `__init__.py` files are documentation-only. Tests enforce ownership
  docstrings, this no-side-effect initializer rule, the data-layer dependency
  boundary, and an acyclic static import graph.
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

## Cargo profiles

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

- `python`: `make python-nits`, then `make python-test` (lockfile, Ruff, and
  Mypy are reported separately from Pytest).
- `rust`: `make rust-nits`, then `make rust-test` (rustfmt and Clippy are
  reported separately from workspace tests).
- `benchmark-smoke`: a one-round `./bench.py` run on
  `egglog/tests/integer_math.egg` through `make benchmark-smoke`.
- `codspeed`: an in-process, proofs-only `egglog-experimental` benchmark
  harness over a smaller representative file set, run through CodSpeed in both
  simulation and memory modes. CodSpeed tracks proof-mode movement without
  invoking `./bench.py` or requesting timing-summary serialization, so the
  split-phase stopwatches remain disabled there. The CLI benchmark report
  remains the source for the full off/term/proofs comparison.

The same entrypoints used by CI are available locally:

```bash
make check
make benchmark-smoke
```

Use `make nits` for non-test hygiene, `make test` for tests alone, and
`make python-check` or `make rust-check` for complete language-specific
validation. `make format` applies Python and Rust formatting locally. Ruff and
Mypy discover the repo-owned Python files from `pyproject.toml`, so new modules
under `benchmarking/` or `tests/` are checked without editing Make recipes.
