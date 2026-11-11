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
validation without tests. Use `uv run --locked pytest` or `cargo test` directly
for focused reruns. `check` combines `nits`, `test-python`, `test-rust`, and
`test-figures`; CI runs those four parts in parallel. `nightly` is the externally
required entrypoint.

The catalog-driven Rust paper target and frozen slotted differential pairs run
in the normal Cargo workspace suite. `make check` prepares unchanged native
parameter-analysis drivers first and includes Vega tests. No separate Python
slotted orchestration or live fixture generation belongs in routine validation.
The Make recipe runs the workspace suite without `paper-tests`, then
selects the `benchmarks/paper-tests` package alone. This prevents workspace feature merging
from enabling the reference's expensive internal checks on the large paper cases;
all paper oracles and the ordinary Rust debug assertions remain active.
CI sets the explicitly partial `RUST_TEST_ARGS="--skip paper/"` filter for
`make test-rust`. Local `make check` runs all enabled paper cases. The paper target honors
the normal `--test-threads` option and `RUST_TEST_THREADS` environment variable.
The Make invocation defaults to one worker per Rust test binary, including
custom test harnesses. Set `RUST_TEST_THREADS=N` to change the default; an explicit
`--test-threads` in `RUST_TEST_ARGS` takes precedence. This controls concurrent
test cases, not each e-graph's worker settings, and is not an individual memory
cap. The paper allocator limit remains per child.
The paper target
uses the allocator/address-space cap from `benchmarking/config.py` by default;
`PAPER_TEST_MEMORY_LIMIT_BYTES=none` runs it uncapped. Apply the shared ignore
policy against that selected profile, and print excluded configuration counts.

For proof-focused changes, the filtered proof snapshot test is useful while
iterating or when you want a focused proof rerun:

```bash
cargo test --locked --workspace --test files proofs/ --
```

`proofs/` runs explicit `(prove ...)` fixtures under `tests/proofs` and every
proof-compatible file under proof-testing mode, snapshotting generated proofs.
It is a name-filtered subset of `cargo test --workspace`, so do not run it after
a full workspace test unless you want a focused proof rerun.

For benchmark-runner changes, smoke the public CLI entrypoint with a temporary,
machine-readable report path so the run does not read or append to the default
benchmark cache; runner status and build diagnostics stay on stderr.

```bash
uv run --locked pytest -q benchmarking/tests/test_benchmark.py::test_public_cli_collects_real_observations
```

This integration test is included in `make check`. It builds through the public
CLI and checks four successful observations with wall/RSS measurements, using
small Math and disequality fixtures and pytest's temporary report directory.
It requires the Git checkout and Rust toolchain used by the normal workflow.

For benchmark-report UI changes, inspect both a focused one-file report and the
default ten-file report in Rich and Markdown form. Exercise terminal widths 80,
119, 120, 160, and 200 using copies of the report cache under `/tmp`; do not read
from or append to the repository cache during UI validation. Confirm that the
cumulative `--detail` levels add files, phases, and top rulesets in that order,
Rich output at 120 columns is readable, widths below 120 produce exactly one
warning for detailed output and still render without error, and Markdown
preserves full names and values independent of terminal width. Widths below 80
have no readability guarantee.

For collection-status UI changes, exercise fully cached, partially cached, and
fully fresh plans. Keep operational output compact, make reused and missing work
clear, and do not duplicate the final report or the progress display.

For interactive-report changes, manually run `--open` against a report under
`/tmp` and inspect the generated `file://` page. Verify that the complete
initial report appears before the Python runtime is ready and preserves the
invocation's endpoint provenance and file order. After Apply, selector
provenance must come from the latest cached row for each identity. Verify that
endpoint swapping, file subsets, timeout, and rounds retarget the report;
incomplete combinations show explicit missing results; and invalid selector
requests preserve the prior selectors and report. The command must exit after
opening the page, and scope changes must never build a target, collect a row,
or modify the JSONL.

## Benchmarking

- Use `./bench.py` as the public benchmark entrypoint.
- Keep `data-cache/reports.jsonl` append-only and ignored by git.
- `--report` requires a filesystem path; literal `-` is rejected rather than
  treated as a streaming destination.
- Operational status, build diagnostics, and progress always go to stderr. The
  final Rich report also uses stderr; the final Markdown report uses stdout.
- Treat report JSONL as a disposable cache written and read only by this tool.
  Schema shape changes invalidate the cache and require recomputation; do not
  add migrations or field-by-field malformed-input validation.
- The runner loads report JSONL once through the shared JSON codec into an
  indexed `ReportStore`; an interactive artifact embeds that complete snapshot
  and retargets only within it.
- `proofs` is generation-only. The `proof-extraction` treatment uses
  `--proof-extraction` to rewrite checks and extract, materialize, clean, and
  simplify proofs without verifying them. Treat its results as performance
  evidence only; `--proof-testing` remains the strict correctness mode.
- Bare `./bench.py` compares `proof-testing` with `off`, including proof
  extraction and checking. Recording-only `proofs` and unchecked
  `proof-extraction` remain explicit choices.
- `slotted-proof-testing` runs `--slotted --proofs`, translating and checking ground
  source equality claims. This differs from ordinary recording-only `proofs`.
- The five core egglog treatments and three slotted encoding treatments run
  `egglog-experimental`. Native slotted treatments run `slotted-reference` with
  explicit matcher/substitution flags. The `egg` treatment and
  its three proof variants run `egg-math-benchmark` on the fixed Rational Math
  workload at registered cutoffs, including the frozen twelve-round witness.
  Native workload selection derives from the complete input identity.
  `egg-de`, `egg-ee`, `egg-nee`, and `egg-oee` run the original native
  parameter-analysis drivers on `.in` inputs without proofs. Mixed-engine
  comparisons build each required executable, and every cache row identifies
  the executable that actually ran.
- Benchmark inputs should not contain executable `(prove ...)` or
  `(prove-extract ...)` commands. Use `(check ...)` and `(extract ...)` so the
  selected treatment controls proof extraction, and cover strict proof validity
  in proof tests.
- Benchmark files are resolved relative to the command invocation directory,
  not relative to comparison targets. Require self-contained files without
  `(include ...)` or `(input ...)`; expand external inputs before benchmarking.
- Cache identity includes binary SHA-256, physical file SHA-256, and treatment.
  Reuse completed successes independently of time/memory
  guards. `select_records` centrally retries timeouts only after raising the
  timeout, and memory-limited outcomes only after raising/removing the memory
  guard. Ordinary failures require force-run. Classify outcomes once at launch;
  readers use status rather than exit codes or diagnostic parsing.
  Historical rows remain append-only; runtime-contract/schema changes require
  a new cache. Controlled launches keep one allocator environment in both modes.
- Shared exclusions live only in `benchmarks/ignore.json`, with reason/evidence.
  A cap-specific resource exclusion applies only to a set cap no larger than the
  recorded bound, never to uncapped runs. Unsupported entries apply across profiles.
  Preserve exclusions in grouped/interactive snapshots. Figure timing inputs
  omit only expected-failure table-size rules; Rust correctness checks retain
  their exact expectations. Complete successful samples bypass cap-specific
  resource deferrals; unsupported configurations remain excluded.
- The baseline and candidate must have different endpoint cache identities
  (binary SHA-256 and treatment). They may use the same binary when treatment
  differs.
- A request must not contain duplicate file hashes; those
  selectors would address the same cached workload observations twice.

## Paper figures

- `./bench.py figures` collects and renders the seven paper PDFs through the shared
  benchmark phases. `--config` selects a flat JSON catalog with global `rounds`
  and optional `timeout_sec` override, and direct per-figure `spec`, `files`, `treatments`, and optional correctness-only `checks`.
  File selectors are ordered catalog-relative globs: `!pattern` removes current
  matches, and later positives can re-add them. Both forms must match files;
  final selections must be nonempty. Count resolved workloads, not selector tokens.
- Resource defaults for all entrypoints come from `benchmarking/config.py`.
  The Rust paper parent reads them once through stdlib-only `python3`; execution
  and worker scheduling stay in Rust. The catalog requests ten observations.
  Correctness watchdogs retain a 3x allowance per mode for their additional
  extraction, proof, and native-reference work.
  Use `--rounds 3 --memory-limit` with temporary reports/previews for verification;
  ordinary benchmark defaults are unchanged. `figures --reuse-from DIR --no-runs`
  renders compatible exports without builds, measurements or measurement-cache writes.
- Reuse compatible observations automatically, merge repeated runtime/memory
  requests, and refresh current label bindings even with zero fresh runs.
  Keep raw observations append-only. Scope plots by label and selected physical
  input/facts/treatment identities; select the newest N rows including failures.
- Figure collection never acquires sources, regenerates corpus inputs or runs
  separate validators. Retain selected published input hashes/aliases, strict
  failures and source blockers. Source blockers are not saved replay counts.
- The outputs are `disequality-runtime`, `math-runtime`, `slotted-runtime`,
  `slotted-multipattern-runtime`,
  `corpus-congruence-cdf`, `corpus-proof-recording-cdf`, and `corpus-proofs-cdf`.
  Each has PDF/SVG/PNG, bound specification, results JSON, numeric TeX macros,
  and a TeX table under `figures/output/eval/` by default. Authored specifications
  stay in `figures/eval/`. `--output-dir` overrides the common generated folder.
  Copy the generated `eval` folder into the manuscript's `figures/` directory;
  PDF/TeX need no JSON runtime. Results JSON and bound specs retain selected data
  and settings for `--reuse-from DIR` without the original cache. Subset invocations
  update selected filenames only; obsolete renamed
  or removed outputs are not cleaned automatically. Render through temporary
  files and replace the requested bundle only after every condition is complete
  and every format succeeds. Failed/missing measurements stop publication.
  Observation provenance remains in the raw JSONL, grouped JSON and results JSON.
- `make check` includes the Vega tests; inspect all seven exported figures at manuscript width
  and verify PDF font embedding. Tests must cover latest-N selection, N=1 without
  intervals, independent Fieller intervals, incomplete-bundle rejection, and
  the shared baseline-runtime corpus cohort (>=0.2 seconds, no upper cutoff).

- The shared runner owns whole-process wall time and peak RSS for every engine.
  Native slotted is a workload driver with no self-timing or phase-summary path.
- Local allocation protection uses the existing allocator/address-space cap only.
  Do not add host-reserve, host-pressure, or RSS-ceiling supervisors. Use
  `--no-memory-limit` explicitly for uncapped final collection; peak RSS is
  measured independently.
- Resource failures require explicit evidence and review before an ignore entry;
  known table-size bugs instead require an issue and an explicitly reviewed
  `expected-failure` with exact `[ordinary, candidate]` counts. Rust must execute
  that case, fail unexpected passes or any different failure, and keep all other
  checks active. Figure timings still include these known table-size cases.
  semantic/proof failures are failures, never automatic exclusions. Do not use a
  smaller input to certify an excluded actual paper workload.
