# Reproduction instructions

The frozen compiler/control packages, fresh correctness reproduction and repeated descriptive cost captures are complete. Official EggCC gates have attributed baseline failures. Cost figures are generated and independently regenerated; the selected data have a disclosed host-protocol deviation with known background upload and unmeasured I/O. No speedup or controlled-host inference is claimed.

## Paths and frozen identities

These are machine-local instructions. Start in `/Users/saul/p/egglog-encoding` and use fresh output directories. Keep each frozen compiler beside its exact sibling `tiger`; the compiler looks there first. No replay requires rebuilding or modifying a frozen endpoint.

```sh
export RAW=/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact
export ENC=/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding
export EGGCC_SOURCE=/Users/saul/p/wt/eggcc/encoding-impact
export OBS="$RAW/compiler/observations"
export CONTROL="$OBS/corrected-control-1"
export PY=/Users/saul/.local/share/uv/python/cpython-3.13-macos-aarch64-none/bin/python3.13
```

| Binding | Original observer | Two-rule-deleted diagnostic control |
| --- | --- | --- |
| Endpoint directory under `$CONTROL` | `final-release` | `corrected-release` |
| eggcc SHA256 | `5d980389feec6270146db9a2cfe4e1775974102ab6c50cdf7bad029471907af1` | `f44edb3cb9c4b9660524335a29bea536571fe2ddbd1bcc68ba589decbd9bcc15` |
| Sibling Tiger SHA256, both endpoints | `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a` | Same |
| Full `source.json` SHA256 | `5cddb863fa1a242fd028051400fb9a58c54ff33c876fe74a678e29fee020c6a3` | `8748805409bdc89ae7d529521140aacadb85483ffb421b957d82b3a8de0fbc22` |
| Full `source.patch` SHA256 | `db5eec0373d8a77a06356d3d064a17b449e83208baed3f416e463ea0970b66e6` | `9ea4a5a1fb8597ba498abb6ccbe80ce60944e20a31e15d8e36dbdd9aa518a61a` |
| `manifest.json` SHA256 | `ff017790bf298fd56213f56759b8372cd6d74bb12457a747f088c03670f9fef2` | `860add623480776002f680501c1077ea7c2cd8e268545ce4c028c0e90aab20e2` |

Check these bytes before reuse:

```sh
shasum -a 256 "$CONTROL/final-release/manifest.json" "$CONTROL/final-release/source.json" "$CONTROL/final-release/source.patch" "$CONTROL/final-release/bin/eggcc" "$CONTROL/final-release/bin/tiger"
shasum -a 256 "$CONTROL/corrected-release/manifest.json" "$CONTROL/corrected-release/source.json" "$CONTROL/corrected-release/source.patch" "$CONTROL/corrected-release/bin/eggcc" "$CONTROL/corrected-release/bin/tiger"
```

The [compiler summary](../../benchmarks/local/eggcc-encoding-impact/compiler/observations/corrected-control-1/summary.md) and `final-summary.json` bind the complete command/log index and final source audit. The latter has SHA256 `a9a32c2d100c406fcb148ea9226c726b2d9d37e180f207f1f8ecdc85c76fa5ce`.

## Reconstruct the uncommitted source

HEAD alone cannot reproduce this experiment. Both compiler packages are uncommitted patches against EggCC `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`. E1 and the harness are separate patches against the encoding workspace base `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`:

- `encoding/reviewable-1.patch`, SHA256 `b21d12ce1fd58453275d001609d12583439a295c8899d4ed058bd1ba070c1ee0`: all five E1 files, including the new independent oracle. `encoding/final-source-checkpoint.json` binds their hashes and successful full gate. The development four-tracked-file engine diff is incomplete and is not this authority.
- `harness-final-gate/harness-2.patch`, SHA256 `7489f1043a8b1ab322d44ecc8cee85011eb953b1e6acfd7cf8fee2707937f3f3`: the reviewed seven-file harness package; use `checkpoint-2.json` and `final-summary.json` beside it.
- The two compiler patches in the table include new files, both root/DAG manifests and lockfiles, observer code, fixtures and helpers. Do not layer the corrected patch over the original patch: each is complete against the same base.

For a fresh source reconstruction, choose an absent directory outside another Cargo workspace; do not reapply patches to the existing dirty trees:

```sh
SOURCE_COPY=/tmp/eggcc-impact-source-01
mkdir "$SOURCE_COPY"
git -C "$ENC" worktree add --detach "$SOURCE_COPY/encoding" 392b6d6b48b5bc307a5b9c981c957fc0a09e23e5
git -C "$SOURCE_COPY/encoding" apply "$RAW/encoding/reviewable-1.patch"
git -C "$SOURCE_COPY/encoding" apply "$RAW/harness-final-gate/harness-2.patch"
git -C "$EGGCC_SOURCE" worktree add --detach "$SOURCE_COPY/compiler" 15ee7cbabe70d3b2e72d796bcf81cc2604626e7b
git -C "$SOURCE_COPY/compiler" apply "$CONTROL/final-release/source.patch"
git -C "$EGGCC_SOURCE" worktree add --detach "$SOURCE_COPY/corrected" 15ee7cbabe70d3b2e72d796bcf81cc2604626e7b
git -C "$SOURCE_COPY/corrected" apply "$CONTROL/corrected-release/source.patch"
```

Verify the reconstructed compiler's entire file map, not just the patch hash; this stdlib-only check does not build anything:

```sh
"$PY" - "$CONTROL/final-release/source.json" "$SOURCE_COPY/compiler" <<'PY'
import hashlib, json, pathlib, sys
manifest = json.loads(pathlib.Path(sys.argv[1]).read_text())
root = pathlib.Path(sys.argv[2])
for name, expected in manifest['source_sha256'].items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == expected, name
print('all', len(manifest['source_sha256']), 'compiler source hashes match')
PY
```

Repeat with `corrected-release/source.json` and `$SOURCE_COPY/corrected` for that variant; verify E1's five file hashes using its checkpoint. The compiler Cargo graphs intentionally pin the recorded absolute E1 path `$ENC/egglog-experimental`. A copied compiler still uses that path. To build against a relocated encoding tree, retarget **both** graphs and resolve/record both lockfiles as a new source package; it is not the frozen byte identity. Rebuilt or relocated endpoints need new binary/Tiger hashes and relevant correctness gates before study use.

The final original package differs from the pre-repair original control only by the cfg(test) borrow `&[input.clone()]` → `std::slice::from_ref(&input)`. Its production binary/Tiger bytes are identical. The corrected package intentionally retains its pre-repair test bytes and deletes exactly the two overlapping multiplication-sign rules; it is a specificity control, not a general integer fix. Original interval SHA256 is `ff363e2c10c57c2f3f79005d1f883f98091b3a32d023f43265b2ccbb89ce2647`; corrected SHA256 is `ef5ff6ca63884d2c2588babb624971b76f464c15e92849c0c6a95c3cfce33037`. The saved recovery, actual mutation/restoration receipts and `controller-provenance.json` remain under `$CONTROL`. Do not rerun its already-used controller output paths. Its old preparation metadata is not evidence that the correction was absent; actual variant/source maps and control receipts bind the executed state.

The actual build command was `cargo build --locked --release --bin eggcc`. Use a new target for reconstruction; never activate or clean an old frozen target. The final tested environment was:

```sh
export RUSTUP_TOOLCHAIN=1.91.0 CARGO_BUILD_JOBS=4 RUST_TEST_THREADS=4 RAYON_NUM_THREADS=1
export LLVM_SYS_180_PREFIX=/opt/homebrew/opt/llvm@18 LIBRARY_PATH=/opt/homebrew/lib
export CARGO_TARGET_DIR="$EGGCC_SOURCE/target"
```

For a fresh source copy, change `CARGO_TARGET_DIR` to that copy's own target before building there. LLVM18, CBC and g++ are required on this host; greedy Tiger needs no Gurobi. Compatible release cache was copied on write into the new target, with the old target read-only. Runtime `rt.bc`/`rt.o` were copied only after all six runtime source/build inputs and pinned nightly were verified compatible; see `$CONTROL/runtime-compatibility.json` and `runtime-reuse.json`. Their hashes are `c24564b983852848320eed8cd19cc02678ad781a821e6dff133489994c644f91` and `07123ecfab57014f9f227953c277fa53edca38c7c1e362ebf02ee5a44be62b84`. A clean source reconstruction also needs these compatible outputs or a separately recorded runtime build. The historical install linker failure is retained; no new successful `make runtime` is claimed.

## Frozen release correctness and specificity

The independent final reproducer uses no peer validator imports. It verifies manifest/patch/binary/Tiger/input hashes before and after two fresh full CLI calls, derives expected values by signed reduction modulo 2^64, checks actual feasible observations and all three native extraction/reconstruction passes, and archives evidence. Its SHA256 is `559513b996633415431bb865dd3d4767233908b2a4fd41332765a1b7081d8c72`.

From `/Users/saul/p/egglog-encoding`, use an absent output path:

```sh
"$PY" -I -B "$RAW/fresh-final-reproduction/reproduce.py" --out "$RAW/fresh-final-reproduction/run-02"
```

The actual completed `run-01/results.json` has two passes: final original x=1 source/result `false\n`, corrected MAX source/result `true\n`. Both use `--observations injective`. Each has three accepted audits, six seeds per pass, non-null outputs and three serialized native graphs. These are correctness diagnostics, not cost observations.

The reproducer's actual compiler argv shape is shown below; `ENDPOINT` is `final-release` for x=1 or `corrected-release` for MAX, `INPUT` is a hash-matched copied fixture, and `OUT` must be a new directory. Cwd is `$EGGCC_SOURCE`, with `RUST_LOG=info RAYON_NUM_THREADS=1`; the script supplies a 120-second process-group timeout and retains full stdout/stderr/PID:

```sh
RUST_LOG=info RAYON_NUM_THREADS=1 "$CONTROL/$ENDPOINT/bin/eggcc" --with-context --run-mode optimize --interp \
  --run-data-out "$OUT/run-data.json" --egraph-out-dir "$OUT/egraphs" \
  --observations injective --observation-evidence-dir "$OUT/evidence-root" "$INPUT"
```

For the fixed four-mode MAX oracle, use the live, byte-matched driver in the fully bound compiler tree. Its `__file__` determines fixture/cwd routing; the Python-only frozen snapshot is not a runnable substitute. Use fresh parent/output paths and the recorded capture runner:

```sh
CAPTURE=/tmp/eggcc-impact-specificity-01
mkdir "$CAPTURE"
RUST_LOG=info "$PY" "$OBS/run-command.py" "$CAPTURE/original-driver" 540 "$EGGCC_SOURCE" \
  "$PY" "$EGGCC_SOURCE/tests/encoding_impact/observations/check_corrected_specificity.py" \
  --binary "$CONTROL/final-release/bin/eggcc" --source-package "$CONTROL/final-release/manifest.json" \
  --capture-runner "$OBS/run-command.py" --out "$CAPTURE/original"
RUST_LOG=info "$PY" "$OBS/run-command.py" "$CAPTURE/corrected-driver" 540 "$EGGCC_SOURCE" \
  "$PY" "$EGGCC_SOURCE/tests/encoding_impact/observations/check_corrected_specificity.py" \
  --binary "$CONTROL/corrected-release/bin/eggcc" --source-package "$CONTROL/corrected-release/manifest.json" \
  --capture-runner "$OBS/run-command.py" --out "$CAPTURE/corrected"
```

The original driver intentionally exits1: require all four assertions and `capture_complete=true`, `valid_original_red=true`. Off/Common must give true→false through three native passes; Manual/Injective must report exactly `(ObservationConflict 5 2 1 true false)` before serialization/Tiger. A timeout, malformed receipt, domain error or other panic is not valid red. The corrected driver must exit0 with four passes and `all_corrected_green=true`. Its same-byte oracle independently requires true→true for Off/Common too. Ordinary original-source bug-witness tests remain enabled and deliberately have incompatible expectations under the corrected variant; no full corrected-variant production gate is claimed.

The completed release controls are `$CONTROL/original-release-red/`, `corrected-release-green/` and `corrected-controls/` (24 nearby calls). Final original CLI matrix/repeats are `final-release/results.json` (37 expected outcomes) and `final-release-repeated/results.json` (ten calls/five identical-argv pairs with distinct children and historical-receipt revalidation). Exact per-call argv/cwd/env/log hashes are in `final-command-index.json`; no ignored test or zero-selected filter substitutes for these results.

## Final gates and attributed failures

Run one command at a time from `$EGGCC_SOURCE` with the build environment above and a fresh capture directory. These are the actual gate argv, bounded by the recorded runner; expected nonzero official outcomes must remain visible:

```sh
GATES=/tmp/eggcc-impact-gates-01
mkdir "$GATES"
unset INSTA_UPDATE INSTA_FORCE_PASS
"$PY" "$OBS/run-command.py" "$GATES/root-test" 1800 "$EGGCC_SOURCE" make test
"$PY" "$OBS/run-command.py" "$GATES/dag-test" 1200 "$EGGCC_SOURCE" bash -c 'cd dag_in_context && cargo insta test --release --unreferenced=reject'
"$PY" "$OBS/run-command.py" "$GATES/nits" 1200 "$EGGCC_SOURCE" make nits
"$PY" "$OBS/run-command.py" "$GATES/dag-strict-clippy" 1200 "$EGGCC_SOURCE" cargo clippy --tests --manifest-path dag_in_context/Cargo.toml -- -D warnings
"$PY" "$OBS/run-command.py" "$GATES/root-format" 120 "$EGGCC_SOURCE" cargo fmt --check
"$PY" "$OBS/run-command.py" "$GATES/dag-format" 120 "$EGGCC_SOURCE" cargo fmt --manifest-path dag_in_context/Cargo.toml --check
```

Recorded official `make test` exits 2: 36 root library and 2421 integration executions report pass, two doctests are ignored, but cargo-insta rejects 13 pending snapshot differences. No snapshots were accepted. Because this stops the Make target before its DAG command, the exact remaining standalone DAG release suite ran separately and passed 74/74. The accepted one-line cfg(test) borrow repair followed; focused DAG10, full DAG74 and formatting were rerun. The earlier 16-minute root result was retained across that test-only edit with explicit authorization, not relabeled as a new full root pass.

Official post-repair `make nits` exits 2 on root `clippy::unnecessary_unwrap` at `src/rvsdg/optimize_direct_jumps.rs:236`. Standalone strict DAG Clippy exits 101 on `unnecessary_unwrap` at `extractiongymfastergreedydag.rs:134` and `cloned_ref_to_slice_refs` at `fastercbcextractor.rs:991`; the owned test warning is fixed. Diagnostic root/DAG Clippy pass with only these lint names allowed:

```sh
cargo clippy --tests -- -D warnings -A clippy::unnecessary_unwrap
cargo clippy --tests --manifest-path dag_in_context/Cargo.toml -- -D warnings -A clippy::unnecessary_unwrap -A clippy::cloned_ref_to_slice_refs
```

Those altered commands are not a passing official nits result. Fresh matched base15ee7cba/E1 controls use the same dependency/lock graphs, Rust1.91, environment, inputs, harness, expectations and native Tiger, with only dependency/workspace bookkeeping changes from the base. All 13 exact trials selected one test and produced identical actual snapshot bodies; strict root/DAG lint reproduced all three warnings with identical owning-source hashes. See `$CONTROL/fresh-engine-control/attempt-2/results.json`; its initial missing-native-fallback setup failure is retained separately. Historical pre-E1 matches alone were not used for final attribution. The integration/native `Run::new` tests use non_weakly_linear=false; the separately captured frozen CLI matrix and final reproducer use the CLI true default.

Encoding/harness combined validation passed separately. From `$ENC`, the actual complete gate and public smoke commands are:

```sh
RUSTUP_TOOLCHAIN=1.91.0 CARGO_BUILD_JOBS=4 CARGO_TARGET_DIR="$ENC/target" UV_PYTHON="$PY" make check
RUSTUP_TOOLCHAIN=1.91.0 CARGO_BUILD_JOBS=4 CARGO_TARGET_DIR="$ENC/target" UV_PYTHON="$PY" make benchmark-smoke BENCHMARK_SMOKE_REPORT=/tmp/eggcc-impact-public-smoke-fresh.jsonl
```

Use `harness-final-gate/final-summary.json` for the successful combined 290-Python/1804-Rust checkpoint and public smoke; the earlier E1-only retry is in `encoding/full-check/`. Retain earlier disk-full and timeout-fixture failures. Do not run a redundant proof subset after the complete gate.

The frozen E1 ordinary CLI can also run the mathematical example without rebuilding. From `$ENC`:

```sh
"$RAW/encoding/bin/known-disequal-debug" --disequality-encoding nee egglog-experimental/tests/injectivity/injectivity-disequality.egg
"$RAW/encoding/bin/known-disequal-debug" --disequality-encoding ee egglog-experimental/tests/injectivity/injectivity-disequality.egg
```

Both completed with exit0; CLI SHA256 is `c5d2b867415eb5d68cb0e84898bd596c68f255238a05b433fdc4d339b0bb1d4a`. This canary is separate from the cost studies.

## Earlier independent baseline bug and E1 query contrast

The original independent baseline checker remains runnable with a fresh output directory:

```sh
"$PY" -I -B "$RAW/independent-bug-reproduction/reproduce.py" --output "$RAW/independent-bug-reproduction/capture-fresh"
```

It verifies retained A/B/prototype-off binaries and fixtures, derives signed wrapping expectations independently, and runs six bounded full compiler calls. MAX must have non-null source true / optimized false on all three endpoints; x=1 must be false/false. All finish three native passes. These intentionally wrong optimized MAX outputs establish the baseline bug; they are not compiler-cost or generated-machine-code measurements.

`$OBS/initialized-replay/max.egg` is an actual initialized observation graph with a closed pre-pass query, SHA256 `e3cdcebb142d0f16aa7714a82b6c8e742b69e71e737d396e8e21969b820e3337`. Identical old/E1 ordinary CLI runs give query-unknown (specific check failure, exit1) versus known (exit0); x=1 is unknown on both. The separate witness-free different-point algebra fixture passes both engines with fail-wrapped unknown checks. These are labeled replay/algebra contrasts, not full old-query compiler endpoints. Exact commands/stderr are retained with the replay receipts and [fresh-evidence review](findings/observation-fresh-evidence-review.md). Disable the separate E1 prepass probe for every cost arm.

## Selected descriptive cost captures and figure regeneration

This section supersedes the earlier block-02 planning status. The selected pair is `original-one/block-05` and `corrected-max/block-03`. Each complete 42-call collector, explicit verifier and frozen-helper postcapture step exits 0 without timeout. Strict clean-host consent remains withheld. The pre-numeric descriptive-scope resolution admits only absolute observations with the known upload/unmeasured-I/O limitation. Primary and regenerated figures now exist; final independent numeric review is recorded separately.

| Case | Directory under `$RAW/observations-cost` | Frozen `study.json` SHA256 |
| --- | --- | --- |
| `original-one` | `original-one/block-05` | `4f48459fa9b6e6bcfa16b249d88bb79ba877bf69821febc90921102fe54ce6a6` |
| `corrected-max` | `corrected-max/block-03` | `cf2c25be89354255201b6d847672b8aa8ea1219119b7d3791613a3ae0023874a` |

Each selected directory retains `collect-command.json`, `verify-command.json`, `postcapture-command.json`, their logs, `results.json`, `results.receipts/` and `postcapture/`. Do not overwrite them. The exact frozen endpoints and case inputs are unchanged from the source/correctness packages above. The unchanged static source-package artifacts still have block-01 paths; this is source-artifact reuse, not reuse of any earlier measurement or correctness row.

### User-amended memory policy and host evidence

The original measurement protocol used outer `EGGLOG_BENCH_MEMORY_GUARD=1`, with normal-pressure, 10 GiB sampled process-group RSS and 2 GiB reserve checks. That is historical protocol, not the selected pair's execution environment. The user explicitly waived memory-pressure blocking for these minimized cases. [The correction](../../benchmarks/local/eggcc-encoding-impact/observations-cost/user-memory-policy-correction.json), SHA256 `2df138b8fd4393be4a63d1507d55d32656017ee6c9b018aa2e61d7564f3f0991`, binds the actual common prefix:

```sh
/usr/bin/env -u EGGLOG_BENCH_MEMORY_GUARD RAYON_NUM_THREADS=1 RUST_LOG=error
```

Unset disables the entire optional guard; it does not merely relax its pressure check. It is the frozen guard's disabling API. `EGGLOG_BENCH_MEMORY_GUARD=0` is invalid and is not an equivalent setting. This amendment does not waive the approved plan's exclusion of active build/test/collector work or permit pausing unrelated processes. No CPU-policy waiver is assumed. Normal desktop/UI activity and memory/power context remain disclosed; active build/test/collector interference still invalidates the whole affected block, and unresolved external activity must be classified under the retained host rules. Compiler nonzero/timeout/OOM, missing receipt, provenance drift or correctness failure also remain failures.

Root captured a full `host-before.json`, two `host-during-*.json` records and immediate `host-after.json` for each selected case, with automated five-second monitoring recorded in `monitor-record.json`. The before-launch `host-admission.json` records no active known build/test/collector job; the new pair's observations found none. These sampled records include a coincident low-CPU artifact-upload process whose I/O rate is unmeasured. Its prelaunch attribution was omitted. Strict clean-host consent is withheld; the [descriptive resolution](../../benchmarks/local/eggcc-encoding-impact/observations-cost/descriptive-observations-resolution.json) preserves that deviation and admits only absolute recorded-host observations, not uninterrupted exclusivity or causal feature effects. The collector commands had a 14000-second outer capture bound and each declared compiler invocation retains its 300-second timeout. No unrelated process was paused or killed.

### Actual collection, verification and archival commands

The following variables select existing data. Choose the first pair or the second pair explicitly; cwd for every actual command is `$ENC`:

```sh
CASE=original-one
BLOCK_NAME=block-05
# Alternatively: CASE=corrected-max; BLOCK_NAME=block-03
BLOCK="$RAW/observations-cost/$CASE/$BLOCK_NAME"
STUDY="$BLOCK/study.json"
RESULTS="$BLOCK/results.json"
COST_PY="$RAW/harness-prep/.venv/bin/python"
COLLECTOR=scripts/eggcc_encoding_case_study.py
HELPER="$OBS/fresh-evidence-python-2-final/source/tests/encoding_impact/observations/observation_evidence.py"
# Discard the build-only exports if using the same shell as the gates above.
unset RUSTUP_TOOLCHAIN CARGO_TARGET_DIR CARGO_BUILD_JOBS RUST_TEST_THREADS
cd "$ENC"
```

These are the **recorded completed invocation forms**, shown for reproduction provenance. Do not repeat collection into the existing `RESULTS` or archival into the existing `postcapture` directory:

```sh
/usr/bin/env -u EGGLOG_BENCH_MEMORY_GUARD RAYON_NUM_THREADS=1 RUST_LOG=error "$COST_PY" "$COLLECTOR" collect "$STUDY" "$RESULTS"
/usr/bin/env -u EGGLOG_BENCH_MEMORY_GUARD RAYON_NUM_THREADS=1 RUST_LOG=error "$COST_PY" "$COLLECTOR" verify "$STUDY" "$RESULTS"
/usr/bin/env -u EGGLOG_BENCH_MEMORY_GUARD RAYON_NUM_THREADS=1 RUST_LOG=error "$COST_PY" "$HELPER" collector \
  --study "$STUDY" --results "$RESULTS" --collector "$ENC/$COLLECTOR" \
  --source-artifact "cost-$CASE-source-package" --reference-artifact "expected-$CASE-reference" \
  --archive "$BLOCK/postcapture"
```

Verification reads the selected data and may be rerun without collecting. A repeated archival check must choose an absent archive directory. For a genuinely new collection, first declare a new study ID and fresh per-arm evidence roots, then use a fresh result/receipt directory; changing only the results path would keep writing into the selected evidence roots. Preserve existing manifests and every previous row. After separate host-window admission, the collection form is:

```sh
# Prospective only: both paths belong to a newly declared, separate block.
NEW_STUDY=/absolute/path/to/new-declared-study.json
NEW_RESULTS=/absolute/path/to/fresh-block/results.json
/usr/bin/env -u EGGLOG_BENCH_MEMORY_GUARD RAYON_NUM_THREADS=1 RUST_LOG=error "$COST_PY" "$COLLECTOR" collect "$NEW_STUDY" "$NEW_RESULTS"
```

The pinned cost environment is CPython3.13.11/Matplotlib3.10.7 with `harness-prep/requirements.lock`. Each case uses Off/Manual/Injective, one warmup and 12 measured observations per arm, 300-second compiler timeout and balanced rotating order: 42 calls, 36 measured. Common-seed remains an untimed correctness control. Contexts, full three passes, CLI nwl=true, greedy native extraction and probe/profile/dump exclusion remain common. The collector owns interpreted correctness flags; warmup/measurement interpreter fields are null and the frozen helper links them to exact verified same-arm correctness rows and references.

The named postcapture step validates/copies the normal receipts and enabled evidence trees outside compiler wall time. The unchanged collector itself does not recursively archive those trees or independently record successful compiler PID/full stderr. The stronger diagnostic drivers do retain full stderr and independent PID.

### Excluded attempts

Keep all excluded attempts and their explanations; none contributes rows to the selected pair:

- Both block-01 cohorts are host-invalid; passing collector verification did not cure the unrelated active development workload. See `observations-cost/invalid-block-01.json`.
- Original block-02 ended with guard refusal. Original block-03 used the invalid disabling value 0 and failed before EggCC Popen. The corrected unset policy supersedes that setup attempt.
- Original block-04 and corrected block-02 were invalidated before statistics review because of unknown external activity/tar. See `observations-cost/invalid-retry-cohorts.json` and retained host/attribution records. Any separately labeled diagnostic statistics are not accepted performance data.

No earlier observation, warmup or correctness receipt is pooled into the selected pair; no outlier trimming, selective retry or silent cohort expansion is allowed. Expected original-MAX observer aborts remain separate correctness diagnostics.

### Generated figures and independent regeneration

Captured exports exist at each selected block's `figures/` and `figures-regenerated/`; all four JSON/Markdown/SVG/PDF artifacts match byte-for-byte. Both primary PDF renders were visually inspected, with pixel-identical regenerated renders. The following commands reproduce exports to **new** temporary paths; those particular temporary paths were not used in the captured commands. They read existing data without collecting. Choose absent names:

```sh
FIGURES="/tmp/eggcc-impact-$CASE-figures-01"
REGENERATED="/tmp/eggcc-impact-$CASE-figures-regenerated-01"
/usr/bin/env -u EGGLOG_BENCH_MEMORY_GUARD RAYON_NUM_THREADS=1 RUST_LOG=error MPLBACKEND=Agg "$COST_PY" "$COLLECTOR" figures "$STUDY" "$RESULTS" "$FIGURES"
/usr/bin/env -u EGGLOG_BENCH_MEMORY_GUARD RAYON_NUM_THREADS=1 RUST_LOG=error MPLBACKEND=Agg "$COST_PY" "$COLLECTOR" figures "$STUDY" "$RESULTS" "$REGENERATED"
```

Compare `figure-data.json`, `table.md` and each case SVG between exports, inspect both PDF exports, and independently recompute all 12 raw values' median/min/max/sample SD per arm. Preserve/account for PDF metadata differences. Report each case separately, retain neutral/regressive outcomes, and provide no overall aggregate. Wall time is the public process-runner boundary; memory is platform-normalized wait4 child peak RSS, not simultaneous process-group peak or per-pair storage. These are descriptive costs on two minimized fixtures, with no isolated component-cost, cross-source treatment comparison, statistical-significance, production benefit or generated-runtime claim. The [historical measurement protocol](findings/measurement-protocol.md), explicit user memory override and [descriptive-scope resolution](../../benchmarks/local/eggcc-encoding-impact/observations-cost/descriptive-observations-resolution.json) define this limited use. Always accompany either exported figure with the report's interactive-host/upload/unmeasured-I/O caption. Exact byte/pixel comparisons are in `observations-cost/figures-qa/regeneration-and-render.json`; visual review is beside it. No prior withheld host admission or excluded cohort is rehabilitated.
