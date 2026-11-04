# Engine-only compiler retarget

Status: first compatibility slice passed. No compiler/API source adaptation was needed. B changes only the two manifests and their lockfiles; its reviewable patch is [engine-only.patch](engine-only.patch) (also retained as `compiler-retarget.patch`), with hashes in `engine-only-checkpoint.json`. No new encoding behavior, analysis or optimization has been added.

A is the untouched compiler baseline at `/Users/saul/p/wt/eggcc/encoding-study-baseline`; B is `/Users/saul/p/wt/eggcc/encoding-study-retarget`. Both start at eggcc `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`. Both B aliases retain `package = "egglog-experimental"` and point at `/Users/saul/p/wt/egglog-encoding/eggcc-study/egglog-experimental`. Native Tiger extraction, fresh-graph reconstruction, schedules, passes and optimization rules have no source changes. `final-provenance.json` confirms A is clean and B has exactly those four modified files.

## Hypothesis and result

H1 predicted that ordinary-mode host APIs and native compiler round trips remain compatible. The confirming prediction was matching non-null original/optimized interpreter outputs on both small inputs through the complete host pipeline. The disconfirming prediction was a reduced parse, API, serialization or extraction failure. The two selected cases confirm H1 within this narrow scope; they establish no general engine equivalence, compiler benefit, encoding coverage or performance result.

| Evidence | Result | Raw source of truth |
| --- | --- | --- |
| Dependency-only host APIs | Passed execution, evaluation, extraction, complete serialization and Function-to-DAG output | `api-probe-independent-workspace.{json,stdout,stderr}`, `api-probe/` |
| Root test compilation | Passed `cargo +1.91.0 check --locked --tests` | `candidate-root-check.*` |
| Standalone DAG test compilation | Passed equivalent command with `--manifest-path dag_in_context/Cargo.toml` | `candidate-dag-check.*` |
| A/B release compiler builds | Both passed Rust 1.91.0 | `{baseline,candidate}-release-build.*` |
| A/B constant CLI | Original and optimized both `1\n`; full passes 0, 1, 2 | `A-frozen-constant_fold_simple.*`, `B-constant_fold_simple.*` |
| A/B memory CLI | Original and optimized both `10\n`; full passes 0, 1, 2 | `A-frozen-mem_simple_store_forwarding.*`, `B-mem_simple_store_forwarding.*` |
| Optimized Bril comparison | A/B byte-identical for each case | `{A,B}-*-optimized-bril.stdout` |
| Root constant fixture filter | 4 passed, 0 failed | `B-files-constant_fold_simple.*` |
| Root memory fixture filter | 4 passed, 0 failed | `B-files-mem_simple_store_forwarding.*` |
| Standalone DAG arithmetic | 1 passed, 0 failed | `B-dag-arithmetic.*` |
| Standalone DAG optional-memory canary | 1 passed, 0 failed | `B-dag-memory.*` |
| Standalone DAG constant folding | 1 passed, 0 failed | `B-dag-constant.*` |
| Automated receipt audit | 2 A/B cases and 11 selected tests passed; rejects null/mismatched outputs, incomplete passes or wrong counts | `verify-canaries.py`, `correctness.json`, `verify-canaries.*` |

CLI correctness commands preserve `--with-context --run-mode optimize --interp`, all default parallel passes, default greedy Tiger extraction, and `non_weakly_linear=true`. No cutoff, schedule, rule ablation or extraction replacement was used. Both source inputs lack `# ARGS:`, so each uses its ordinary empty argument list; durable exact copies are in `inputs/`. Info logs retain all three pass boundaries and reconstruction runs. Correctness receipts explicitly assert both interpreter fields are non-null and equal to the expected output; the CLI alone does not assert equality.

The harness differs from the CLI: its `non_weakly_linear=false`, and sequential/no-context trials do not themselves compare interpreter outputs. Each root filter selected direct-jump, interpreted optimize, no-context optimize and sequential optimize snapshots. The CLI A/B comparison above is a separate, fixed configuration. The optional memory DAG canary explicitly enables its optional analysis only inside that pre-existing test; default compiler analysis was unchanged.

## Dependency and binary provenance

Both complete resolved dependency graphs are retained under `{baseline,candidate}-{root,dag}-metadata.stdout`. A's root experimental/core pins remain `19ed8666` / `9b5ce111`; its standalone DAG pins remain `6b37b6b3` / `07650bed`. B's root and DAG both use the same local experimental 3.0.0 / core 2.0.0 and the integrated workspace crates. Manifest/lock hashes and source revisions are in `source-hashes.json` and `final-provenance.json`.

Release binaries are frozen independently at `bin/A/{eggcc,tiger}` and `bin/B/{eggcc,tiger}`. Runtime lookup chooses the existing sibling of `current_exe` first (`find_tiger_binary`), so the canaries do not depend on subsequently overwritten shared target outputs. Both Tiger artifacts hash to `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`. A compiler hashes to `e062c92bbcb9a8f05caed3cc10ec013c126a1d1f528e57f3b797bf6c3004912d`; B to `6c30c8cb28768f3c461666b0370ff5c249fe6ba1f8f58a1a1d6c78e2df3e638f`. See `binary-hashes-{A,B}.json` and per-case `correctness.json` entries.

## Failed probes and resolved setup issues

1. The first raw API-probe launch exited before compilation because it sat beneath the encoding root workspace but was not a member. An empty `[workspace]` only in the disposable raw probe resolved this. `api-probe.{json,stderr}` retains the failure. This was probe packaging, not an engine incompatibility.
2. The initial A canaries failed with `tiger binary not found` because reusing the Cargo target directory did not materialize the baseline build script's external `target/release/tiger` side effect. Those failed `A-constant_fold_simple.*` and `A-mem_simple_store_forwarding.*` receipts remain. The unchanged compiled build script was then invoked with baseline `CARGO_MANIFEST_DIR` and `PROFILE=release`; `baseline-native-tiger-build.*` plus `baseline-native-build-env.json` retain the exact command/environment and source hash. It created an identical native Tiger. The successful frozen-sibling reruns use the distinct `A-frozen-*` names. No source change was made to address this output-cache issue.

## Reproduction

`run-command.py NAME TIMEOUT_SECONDS CWD ARGV...` captures exact argv, cwd, selected environment, wall time, exit/timeout status, stdout and stderr. It uses a separate process group and kills that group on timeout. Build/check commands used `CARGO_BUILD_JOBS=4`, `RAYON_NUM_THREADS=1`, and compatible shared Cargo output under B's `target/`. `environment.json` records Rust 1.91.0, C++ and LLVM/CBC environment. LLVM 18 remains required even with default features disabled. No Gurobi invocation was needed in greedy mode.

For example, from B, the successful constant CLI command was:

```sh
RAYON_NUM_THREADS=1 RUST_LOG=info /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/retarget/bin/B/eggcc --with-context --run-mode optimize --interp --run-data-out /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/retarget/B-constant_fold_simple.run-data.json tests/passing/small/constant_fold_simple.bril
```

Replay the exact argv/cwd/environment in the corresponding JSON receipt for other commands. `python3 verify-canaries.py` rechecks both fixed A/B cases, complete pass logs, emitted Bril equality, artifact/input hashes and exact nonzero focused-test counts, then rewrites `correctness.json`. Instrumented receipt times include logging/interpretation and some overlap with builds; they are setup/correctness evidence, not optimizer performance measurements.

No compiler process remains active (`final-provenance.json` records an empty active receipt list). No commits or pushes were made. The parent owns the final broad validation gates and any subsequent encoding prototype decision.
