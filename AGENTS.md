# Agent Guidance

## Sub-Agent Defaults

When spawning sub-agents of any type (`default`, `explorer`, or `worker`), use
`reasoning_effort: "xhigh"` by default. If a full-history fork is required and
the spawn tool requires inherited fields to be omitted, rely on the parent
session's `xhigh` reasoning effort instead.

## Workspace

- Treat this repository root as the source of truth. The root Cargo workspace
  owns the local `egglog` and `egglog-experimental` checkout integration.
- Keep subtree-local changes narrowly scoped and compatible with upstream
  history. Do not rewrite subtree metadata or vendored history unless asked.
- Prefer current local APIs over reviving old downstream-only helper methods.

## Tests

Use this order for normal full validation:

```bash
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
uv lock --check
uv run --locked ruff format --check bench.py test_bench.py
uv run --locked ruff check bench.py test_bench.py
uv run --locked mypy bench.py test_bench.py
uv run --locked pytest -q
```

For proof-focused changes, the filtered proof test is useful while iterating or
when you want a focused proof rerun:

```bash
cargo test --workspace proof
```

This is a name-filtered subset of `cargo test --workspace`, so running both as a
final gate intentionally repeats those tests.

For benchmark-runner changes, smoke the public CLI entrypoint with a temporary,
machine-readable report. Use stdout report mode so the run does not read or
append to the default benchmark cache; runner status and build diagnostics stay
on stderr.

```bash
./bench.py --rounds 1 --treatments off --report - \
  egglog/tests/integer_math.egg > /tmp/egglog-encoding-bench-smoke.jsonl
```

## Benchmarking

- Use `./bench.py` as the public benchmark entrypoint.
- Keep `.reports.jsonl` append-only and ignored by git.
- Use `--report -` when report rows should be streamed to stdout instead of
  appended to a cache file.
- Runner status output always goes to stderr, including Rich progress and
  summary tables.
- Benchmark files are resolved relative to the command invocation directory,
  not relative to comparison targets.
- Cache reuse is decided by binary SHA-256, file SHA-256, treatment, and
  timeout.
