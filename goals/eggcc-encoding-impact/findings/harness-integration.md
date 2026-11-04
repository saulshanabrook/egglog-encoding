# Collector and guard integration checkpoint

The narrow reuse is ready for independent review in `/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding`, HEAD `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`. No compiler command, study workload, timing cohort, Cargo build, public benchmark smoke, commit or push ran in this slice. Final complete `make check` and public smoke remain coordinated gates after review and the shared build-slot handoff.

Raw evidence is under `benchmarks/local/eggcc-encoding-impact/harness-integration/`. `checkpoint.json` binds the seven owned files, their frozen copies in `checkpoint/`, the E1 preservation checks and command receipts. `harness.patch` SHA-256 is `16b8517274903b9a6c6ef6786f8ce160b62ddccd280c9e6aa1cd5fa593f35294` (79,025 bytes). `git diff --check` and the patch's reverse apply check both pass. The patch includes untracked additions and excludes the encoding owner's five-file patch.

## Scope and source identity

The collector Python file is byte-identical to the previous frozen collector, SHA-256 `79c4147dbe5b74d1d9138e170643a7c09205f55a6d49d355f1fc201c3a811380`. Its documentation and tests start from the same old three-file checkpoint. The only collector-specific additions are documentation and meaningful integration/scheduling tests; its successful-exit, non-null equal interpreted-output, separate untimed correctness, nonempty measured-row and verification contracts are unchanged. Expected detector aborts remain separate diagnostic evidence.

`benchmarking/processes.py` is the exact inventoried guarded source (`21f1184ba33fa8a45a7bcfcae32e9b4568c15c93cfa04f47a0b77deddea8e073`); `benchmarking/memory_guard.py` is likewise exact (`5384d741dccbe32701b1d77f6f13f9b3119f59f3d5efe80b27b75c0571b52a68`). `tests/test_processes.py` is the retained current source basis (`f301f6ee0849b4d9b73bbfb182032cb710d81c3094badc433223d507b33c9ddc`). The guard tests are a standalone selection/adaptation of the inventoried guard/process tests, without admission, pilot or campaign dependencies. All copied origins and hashes are retained in `copied-files.json` and the earlier `harness-prep/file-plan.json`.

The existing selected `models`/`engines` interfaces satisfy these imports dynamically in the pinned environment; no models, engines, Math, admission, pilot or native adapter modules were transplanted. Makefile already has the public smoke target and is unchanged. Its two tiny fixtures exercise the public runner, not the study compiler. Makefile, project manifests/locks, models and engines are byte-identical to their before-integration inventory. All five reviewed E1 Rust/test/docs/example files are byte-identical to the source handoff; exact before/after hashes are in `before.json` and `checkpoint.json`. An untracked `.DS_Store` is outside this patch and was left untouched.

## Actual checks

The fresh environment remains `benchmarks/local/eggcc-encoding-impact/harness-prep/.venv`: CPython 3.13.11, pytest 8.4.2, Matplotlib 3.10.7, with all 15 distributions pinned and hash-locked in `harness-prep/requirements.lock` (`7c2a9fb7b401b8762e4e4033970e8c395fc35d65d84194283fe7433fcb74d2af`). This environment does not need the project's optional/reporting dependencies for the focused suite.

All commands below used the selected worktree cwd. Exact argv, environment overrides, exits and complete outputs are in the named JSON receipts:

- Before copying the runner, `HARNES_PY -m pytest -q tests/test_memory_guard.py --basetemp=RAW/harness-integration/recorded-red-tmp` produced **two expected failures** (`red-tests.json`). One proves guard refusal must happen before Popen; the other proves the runner must read parent policy before child overrides. The red test source is retained separately.
- After integration, `HARNES_PY -m pytest -q tests/test_eggcc_encoding_case_study.py tests/test_processes.py tests/test_memory_guard.py --basetemp=RAW/harness-integration/focused-tmp` passed **67 tests**, including actual Matplotlib export/regeneration (`focused-1.json`, SHA-256 `8658b75a3a847c0f858fc99796dd63e3eb0be17732e15a9488fc984fc6efddf9`). `MPLBACKEND=Agg` and `MPLCONFIGDIR=RAW/harness-integration/matplotlib` were explicit. Test-only compiler stand-ins are protocol fixtures, never study measurements.
- `make python-nits` passed lockfile validation, formatting, lint and mypy for **50 source files** (`python-nits-3.json`, SHA-256 `537983b57dc538dd0173242a45120b244d728e6be5f6b3bfcca663cf187505bd`). The first two nits receipts retain a formatting and import-order failure, both corrected in owned tests only.

`HARNES_PY` above is the absolute prepared environment's `bin/python`; `RAW` is `/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact`. These abbreviations are explanatory; each receipt contains actual absolute arguments.

## Boundaries for later collection

Activate the guard in the **common outer environment**:

```sh
EGGLOG_BENCH_MEMORY_GUARD=1 HARNES_PY scripts/eggcc_encoding_case_study.py collect STUDY.json RESULTS.json
```

Substitute the explicit prepared interpreter path for `HARNES_PY`. The runner reads `MemoryGuard.from_environment()` before arm environment overrides; an arm-only setting cannot enable the parent guard. Do not use per-arm overrides as policy. Retain this outer invocation/environment in provenance; the unchanged collector hashes the effective child environment but does not independently attest a parent policy overridden by a child setting. Tests preserve that distinction and prove unsafe outer policy retains a single explicit failed correctness row, launches no process and prevents all later invocations.

The guard samples process-group RSS and host state for operational stopping; reported figure/row RSS remains normalized `wait4` child rusage. It does not become simultaneous group RSS or combined host/Tiger bytes. Existing process tests cover timeout/interrupt cleanup, permission races, exit/signal accounting and bounded stdout/stderr reads. Guard tests cover exact cap boundaries, pressure/headroom and monitor launch refusal, descendant cleanup on live stops, discarded invalid timing, missed-sample post-exit peaks, successful timing and unexpected SIGKILL with unknown cause.

The added actual synthetic collection check uses three arms and twelve observations, verifies all 42 invocations (3 correctness, 3 warmups, 36 measured), each arm's twelve observations and four visits to every position. The default remains ten. Later successful Off/Manual/Injective cost controls need externally supplied frozen inputs, common seed/flags and coverage evidence, with `observations: 12`; expected aborts and failing time-to-detection stay outside these successful-control figures. No speedup or unique-power claim follows from this integration.

The next gates are independent read-only review, then coordinated final `make check` and `make benchmark-smoke BENCHMARK_SMOKE_REPORT=/tmp/eggcc-impact-harness-smoke.jsonl` when root releases the shared build slot. These have not been run after this integration checkpoint.

## Final combined gate, 2026-10-17

The combined encoding/harness gate and public smoke are now **passed**, and the shared slot is released. This section supersedes the pending-gate status above. Raw `harness-final-gate/final-summary.json` binds the actual commands, final source checkpoint, counts, logs and retained smoke report. The original seven-file checkpoint and its independent review remain preserved; one narrowly reviewed test-only correction produces the final checkpoint described below.

The first full `make check` genuinely failed in Python: 281 passed, nine failed, one skipped and two snapshots passed. All nine failures were synthetic collector invocations reaching their configured one-second timeout, including one intended mismatch failure masked by timeout. No host cause is established. Hygiene passed, but Rust workspace tests were not reached. `check-attempt-1.{json,stdout,stderr}` and `check-attempt-1-summary.json` retain that attempt and its unchanged-source hashes.

Root directly reviewed and consented to exactly one test-file change: the normal synthetic fixture timeout becomes ten seconds, while the deliberate timeout mode explicitly keeps one second against its sixty-second sleeper. Collector implementation, guard/process implementation, Rust source and snapshots are unchanged. The delta is retained in `timeout-fixture-delta.{patch,json}`. The new test hash is `6a6b52ac9e20060c6dad1b43cf6d17d4aed97e25b20404132200bd2a5c671e33`; the final seven-file `harness-2.patch` hash is `7489f1043a8b1ab322d44ecc8cee85011eb953b1e6acfd7cf8fee2707937f3f3`. Use `harness-final-gate/checkpoint-2.json` (SHA-256 `f9d9dc5c6b2d9c6c9910b4702fad5e8ba539649505aad96e30aecc88352b1d01`) and its `checkpoint-2/` frozen copies for final bindings. The other six harness files, five E1 files and seven boundary files retain their previous hashes.

After that change, the pinned Python environment passed all **26 collector tests**, including real Matplotlib export/regeneration, and `make python-nits` passed for 50 files. Receipts are `focused-after-timeout.json` and `python-nits-after-timeout.json`. The exact full `make check` retry then passed: **290 Python tests, two snapshots, one optional Matplotlib skip; 1,804 Rust tests passed, zero failed and six ignored across 60 summaries**, with zero measured or filtered Rust tests. The optional figure test is skipped because Matplotlib is absent from the normal project environment; `optional-figure-dependency.json` records the availability probe, and that same test passed in the pinned focused run. No proof subset was rerun.

Both full attempts used `/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding` as cwd, Rust/Cargo 1.91.0, `CARGO_BUILD_JOBS=4`, `CARGO_TARGET_DIR=/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/target`, and explicit `UV_PYTHON=/Users/saul/.local/share/uv/python/cpython-3.13-macos-aarch64-none/bin/python3.13` (Python 3.13.11). Build wrappers, inherited Rust flags, incremental override, snapshot-update mode and MAKEFLAGS were unset explicitly, matching the prior E1 gate. `check-attempt-2.{json,stdout,stderr}` retains full command/environment/version identities and terminal exit 0; its elapsed 234.8 seconds is gate duration, not study performance evidence. All nine Makefile stages passed, including workspace Clippy/rustdoc and full workspace tests.

The subsequent public command was:

```sh
make benchmark-smoke BENCHMARK_SMOKE_REPORT=/tmp/eggcc-impact-harness-final-smoke-20261017.jsonl
```

It used the same cwd/toolchain/jobs/target/Python settings and **common outer `EGGLOG_BENCH_MEMORY_GUARD=1`**, completed exit 0 and wrote four fresh successful rows: rational-math and congruence fixtures under Off and Proofs, ordinary NEE. Every row has positive time/RSS, no error fields and the expected input and actual release-binary hashes. This public target's existing timeout is 1,800 seconds, retained in its rows; it is not the prospective study's 300-second configuration. The report remains at the requested fresh `/tmp` path and is archived byte-for-byte as `harness-final-gate/smoke-report.jsonl`, SHA-256 `dd7ae23c0b8972bc7da7388007a4f3e1bcec9dcdc3b2632edad30fb9112829ca`. The actual built release `egglog-experimental` hash is `1a7d6ddcf1e59000a9499bf9e4950e03a1934ee3be130769549040a47c4d43b7`. Smoke commands/environment/logs/exit are in `smoke.{json,stdout,stderr}`. Its rows are functional public-runner smoke evidence, not observer study measurements.

Before/after checks bind all twenty files: five E1, seven harness, seven declared source/configuration boundary files and `rust-toolchain.toml`. They are unchanged throughout the final retry and smoke. Source snapshots were not accepted or updated, and no unrelated source fix was made. No observer cost cohort or new compiler workload ran. Final observer source/CLI/control bindings and the reserved host timing window remain separate requirements before any measured block.
