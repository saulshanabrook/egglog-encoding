# Rerun the structural type case

This guide uses the isolated local checkouts created for this study. The [explanation](report.md) describes the inference; the [reference](reference.md) describes modes and boundaries. Focused checks pass. Official test/lint gates retain the baseline failures described below.

## Source and environment

The compiler is `/Users/saul/p/wt/eggcc/combined-encoding`; the encoding dependency is `/Users/saul/p/wt/egglog-encoding/eggcc-combined-encoding`. Both compiler Cargo manifests point to that encoding checkout. The [baseline receipt](findings/baseline.md) binds the exact commits, patches, dependency graphs and unchanged engine source. New raw evidence is under ignored `benchmarks/local/eggcc-combined-encoding/` in the main encoding workspace.

Use the pinned build environment:

```sh
export CC_COMBINED=/Users/saul/p/wt/eggcc/combined-encoding
export ENC_COMBINED=/Users/saul/p/wt/egglog-encoding/eggcc-combined-encoding
export RUSTUP_TOOLCHAIN=1.91.0
export CARGO_BUILD_JOBS=4
export LLVM_SYS_180_PREFIX=/opt/homebrew/opt/llvm@18
export LIBRARY_PATH=/opt/homebrew/lib
export CARGO_TARGET_DIR="$CC_COMBINED/target"
unset RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER RUSTFLAGS CARGO_ENCODED_RUSTFLAGS
unset CARGO_INCREMENTAL INSTA_UPDATE INSTA_FORCE_PASS MAKEFLAGS
unset EGGLOG_BENCH_MEMORY_GUARD
```

The user requested no memory-pressure blocking. The retained experiment commands use timeouts; the commands below are correctness checks, not a performance protocol.

Tiger must exist at `target/release/tiger` and be executable. The study's Tiger SHA-256 is `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`. A cached Cargo buildscript result did not initially recreate this external output. Its explicit materialization and retry are retained under `consumer/attempt-03/tiger-materialize.*`; buildscript success alone is insufficient evidence that the binary exists. Official LLVM-related tests also require the separately pinned runtime assets described in [the gate receipt](findings/gates.md).

## Focused registered tests

```sh
cd "$ENC_COMBINED"
CARGO_TARGET_DIR="$ENC_COMBINED/target" cargo test --locked -p egglog-experimental --test injectivity_disequality

cd "$CC_COMBINED"
cargo test --locked --release --manifest-path dag_in_context/Cargo.toml structural_type -- --nocapture
cargo test --locked --release --lib structural_type -- --nocapture
cargo test --locked --release --bin eggcc structural_type -- --nocapture
```

Require nonzero selected tests: **18 engine, 9 DAG, 1 host and 1 CLI-parser test**. Compiler tests exercise the actual internal producer/consumer, both-feature controls, equal/helper-normalized inputs, shape differences, unsupported/missing coverage and tag corruption. The host test checks a valid pointer/call program in all five modes through the three production passes. The ninth DAG test independently compares derived Rust Type equality with all three complete checker modes on nine ground cases under the not-equal relation (`nee`) and equality embedding (`ee`) [representations](reference.md#assertion-representations), producing 54 matching oracle rows.

The exact source is `consumer/oracle-final/source.json` (SHA `8165c4521d16ea4f5d1cffe66a08092962b55b8976f37c2b6a2553bfc5352738`); its [checkpoint](../../benchmarks/local/eggcc-combined-encoding/consumer/oracle-final/checkpoint.json) binds the source archive, patches, witness/consumer JSON, oracle rows and every focused command receipt. The host/CLI production closure is unchanged by the final oracle test-only delta; the checkpoint states that receipt reuse explicitly.

The intentionally malformed internal fixture is constructed in [the DAG tests](/Users/saul/p/wt/eggcc/combined-encoding/dag_in_context/src/structural_types/tests.rs). It cannot be supplied as an ill-typed Bril program without first hitting the existing source type checker.

## Actual CLI correctness control

Build the executable, then use a fresh temporary directory for outputs:

```sh
cd "$CC_COMBINED"
cargo build --locked --release --bin eggcc
export RUN_COMBINED="$(mktemp -d /tmp/eggcc-combined-rerun.XXXXXX)"
python3 - <<'PY'
import json
import os
from pathlib import Path
import subprocess

root = Path(os.environ['CC_COMBINED'])
out = Path(os.environ['RUN_COMBINED'])
binary = root / 'target/release/eggcc'
fixture = root / 'tests/encoding_combined/structural-types.bril'
rows = []
for mode in ['off', 'manual', 'combined', 'annotations-off', 'query-off']:
    data = out / f'{mode}.json'
    argv = [str(binary), '--with-context', '--structural-types', mode,
            '--run-mode', 'optimize', '--run-data-out', str(data),
            '--interp', str(fixture)]
    result = subprocess.run(argv, cwd=root, capture_output=True, text=True, timeout=60)
    (out / f'{mode}.stdout').write_text(result.stdout)
    (out / f'{mode}.stderr').write_text(result.stderr)
    assert result.returncode == 0, (mode, result.returncode, result.stderr)
    values = json.loads(data.read_text())
    assert values['original_interpreted'] == '7\n', mode
    assert values['result_interpreted'] == '7\n', mode
    rows.append({'mode': mode, 'exit_code': result.returncode,
                 'original': values['original_interpreted'],
                 'optimized': values['result_interpreted']})
(out / 'summary.json').write_text(json.dumps(rows, indent=2) + '\n')
print(out)
PY
```

`--interp` records both outputs; the Python assertions perform the comparison. The retained original CLI matrix also ran un-interpreted optimize/emit commands and recorded all native passes. Those emit rows have null interpreter fields by design and are not correctness substitutes for the interpreted rows.

Do not count printed-output reparse as unmodified success: the initial emitted file failed because its empty `# ARGS:` comment was read as one empty argument. Five reparses of explicitly comment-normalized copies are separate diagnostics; their transformation and both file hashes are retained. No printer/reader fix or new baseline-bug claim is part of this study.

## Official gates and evidence

From the compiler root, run `make test` and `make nits`. [gates.md](findings/gates.md) specifies the remaining strict DAG sub-gates when an aggregate stops early, the fresh pre-integration control and exact failure-attribution requirements. Never accept snapshots or suppress warnings to make the comparison pass.

Observed outcomes: candidate root tests pass 37 library, one CLI and 2,421 integration tests; control passes 36 library and the same 2,421 integration tests. Both official `make test` commands then fail review of 13 pending snapshots. Twenty-six selected trials each run exactly one corresponding test; actual snapshot bodies match the official captures and each other. Candidate/control full DAG suites pass 83/74 tests. Prettier and root/DAG formatting pass; strict root/DAG Clippy retain three exact common source-site failures. Official `make nits` and strict DAG Clippy remain failed. The default-Off prologue bytes match exactly; the existing observer canaries are covered by the full suites and were not redundantly rerun.

The evidence includes command argv/cwd/environment, return status, stdout/stderr, source/patch/archive identities, binaries, witnesses and consumer outcomes. Ordinary command durations are diagnostic metadata; this study does not claim a speedup. The prior study and its frozen evidence remain separate.
