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

Use this order for normal changes:

```bash
cargo test --workspace
cargo test --workspace proof
cargo clippy --workspace --all-targets -- -D warnings
uv lock --check
uv run --locked ruff format --check bench.py test_bench.py
uv run --locked ruff check bench.py test_bench.py
uv run --locked mypy bench.py test_bench.py
uv run --locked pytest -q
```

For benchmark-runner changes, also smoke the CLI with a temporary report:

```bash
uv run --locked ./bench.py --rounds 1 --warmup 0 --treatments off --report .reports.smoke.jsonl \
  egglog/tests/integer_math.egg
```

For agent-readable benchmark smoke output, pipe report rows from stdout and keep
runner status and build diagnostics on stderr:

```bash
uv run --locked ./bench.py --rounds 1 --warmup 0 --treatments off --report - \
  egglog/tests/integer_math.egg > /tmp/egglog-encoding-bench-smoke.jsonl
```

## Benchmarking

- Use `./bench.py` as the public benchmark entrypoint.
- Do not pass egglog's `--save-report` during timed benchmark collection; it
  changes the measured work.
- Keep `.reports.jsonl` append-only and ignored by git.
- Use `--report -` when report rows should be streamed to stdout instead of
  appended to a cache file.
- Runner status output always goes to stderr, including Rich progress and
  summary tables.
- Benchmark files are resolved relative to the command invocation directory,
  not relative to comparison targets.
- Cache reuse is decided by binary SHA-256, file SHA-256, treatment, warmup
  count, and timeout.
