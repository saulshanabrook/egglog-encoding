# Agent Guidance

## Sub-Agent Defaults

When spawning sub-agents of any type (`default`, `explorer`, or `worker`), use
`reasoning_effort: "ultra"` by default. If the selected model does not support
`ultra`, use its highest supported reasoning effort. If a full-history fork is
required and the spawn tool requires inherited fields to be omitted, rely on
the parent session's `ultra` reasoning effort instead.

## Workspace

- Treat this repository root as the source of truth. The root Cargo workspace
  owns the local `egglog` and `egglog-experimental` checkout integration.
- Keep subtree-local changes narrowly scoped and compatible with upstream
  history. Do not rewrite subtree metadata or vendored history unless asked.
- Prefer current local APIs over reviving old downstream-only helper methods.

## Tests

Run the complete Python and Rust validation suite through the root Makefile:

```bash
make check
```

`make nits` runs formatting checks, linting, type checking, and lockfile
validation without tests. `make test` runs the Python and Rust tests. Use
`make python-check` or `make rust-check` for complete language-specific
validation; their `*-nits` and `*-test` dependencies can be run separately
while iterating. These targets discover files from project configuration rather
than naming individual files in this document.

For proof-focused changes, the filtered proof snapshot test is useful while
iterating or when you want a focused proof rerun:

```bash
make proof-tests
```

`proofs/` runs explicit `(prove ...)` fixtures under `tests/proofs` and every
proof-compatible file under proof-testing mode, snapshotting generated proofs.
It is a name-filtered subset of `cargo test --workspace`, so do not run it after
a full workspace test unless you want a focused proof rerun. The Make target
owns the exact Cargo filter.

For benchmark-runner changes, smoke the public CLI entrypoint with a temporary,
machine-readable report path so the run does not read or append to the default
benchmark cache; runner status and build diagnostics stay on stderr.

```bash
make benchmark-smoke
```

The Make target writes the one-round machine-readable report to
`/tmp/egglog-encoding-bench-smoke.jsonl` by default and verifies that it is
nonempty. Override `BENCHMARK_SMOKE_REPORT` to use another temporary path.

For benchmark-report UI changes, inspect both a focused one-file report and the
default six-file report in Rich and Markdown form. Exercise terminal widths 80,
119, 120, and 160 using copies of the report cache under `/tmp`; do not read
from or append to the repository cache during UI validation. Confirm that the
cumulative `--detail` levels add files, phases, and top rulesets in that order,
Rich output at 120 columns is readable, widths below 120 produce exactly one
warning for detailed output and still render without error, and Markdown
preserves full names and values independent of terminal width. Widths below 80
have no readability guarantee.

For live-report changes, manually run `--serve` against a report under `/tmp`
with both an OS-selected port and one fixed `--serve-port`. In the browser,
verify complete cached endpoint selection, endpoint swapping, file subsets,
cumulative detail, an invalid Apply that preserves the prior selectors and
report, and clean Ctrl-C shutdown. Scope changes must never build a target or
collect a new row.

## Benchmarking

- Use `./bench.py` as the public benchmark entrypoint.
- Keep `.reports.jsonl` append-only and ignored by git.
- `--report` requires a filesystem path; literal `-` is rejected rather than
  treated as a streaming destination.
- Runner status output always goes to stderr, including Rich progress and
  summary tables.
- Treat report JSONL as a disposable cache written and read only by this tool.
  Schema shape changes invalidate the cache and require recomputation; do not
  add migrations or field-by-field malformed-input validation.
- The runner queries report JSONL directly through an explicitly typed DuckDB
  view; it must not copy rows into a persistent or in-memory DuckDB table.
- Benchmark inputs should not contain executable `(prove ...)` commands; use
  `(check ...)` in benchmark fixtures and cover proof extraction in proof tests.
- Benchmark files are resolved relative to the command invocation directory,
  not relative to comparison targets.
- Cache reuse is decided by binary SHA-256, file SHA-256, fact-directory
  SHA-256, backend, treatment, and timeout.
- The baseline and candidate must have different endpoint cache identities
  (binary SHA-256, backend, and treatment). They may use the same binary when
  backend or treatment differs.
- A request must not contain duplicate file/fact-directory hash pairs; those
  selectors would address the same cached workload observations twice.
