# Reproduce the EggCC injectivity/disequality study

This guide separates read-only evidence review, correctness/native replay, and
performance collection. Do not write into a retained result directory. The
drivers deliberately refuse many existing labels, and performance reruns must
not mix with the frozen evidence.

All paths below are relative to the repository root
`/Users/saul/p/egglog-encoding` unless a command changes directory.

## 1. Review the retained result

Start with the connected [explanation](report.md) and compact
[reference](reference.md). QR7's primary authorities are:

```text
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/source-identities-r1.json
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/final-r1/inspection.json
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/actual-binary-inspection-r1.json
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/prospective-timing-design-r1.json
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/timing-r1/independent-verification.json
```

Read the result fields without writing into the retained tree:

```bash
python3 - <<'PY'
import json
from pathlib import Path
root = Path('benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration')
for name in ['final-r1/inspection.json', 'actual-binary-inspection-r1.json',
             'timing-r1/independent-verification.json']:
    data = json.loads((root / name).read_text())
    print(name, json.dumps(data.get('gates', data.get('groups')), indent=2))
PY
```

The causal inspection predates timing: its `timing_collected` and
`performance_acceptance` fields are false. The separate independent timing
verification has `status: passed` and `overall_speedup_acceptance: true`.
`transport-off` is an export-gate placebo, and the actual process-entry code
comparison is 91 instructions/two backward branches versus 55/zero. The
baseline executed LLVM entry already has zero i64 loads. See the
[QR7 reference](reference.md#qr7-authorities-and-records) for exact identities,
executed coverage, tables, and claim boundaries.

The Parts32 and same-mask experiment reports are:

```text
benchmarks/local/eggcc-nontrivial-encoding-payoff/candidate-same-mask/report.md
benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/report.md
```

The bounded negative Pack32 and same-region `NoAlias` attempts are documented
separately:

```text
benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/report.md
benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-integration/actual-r0/report.md
```

They are fail-closed search evidence. Neither changed the compiler endpoint or
entered performance measurement.

The same-mask timing authority is:

```text
benchmarks/local/eggcc-nontrivial-encoding-payoff/candidate-same-mask/confirmation-design.json
benchmarks/local/eggcc-nontrivial-encoding-payoff/candidate-same-mask/confirmation-samples.jsonl
benchmarks/local/eggcc-nontrivial-encoding-payoff/candidate-same-mask/confirmation-cycles.json
benchmarks/local/eggcc-nontrivial-encoding-payoff/candidate-same-mask/confirmation-summary.json
```

The Parts32 correctness/native authority is under:

```text
benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/final-reviewed/
```

The Parts32 inspector writes derived function extracts, diffs, and an inspection
JSON. Run it from a temporary copy so the retained capture stays unchanged; it
does not execute EggCC or a native program:

```bash
export PARTS32_REVIEW_ROOT=$(mktemp -d /tmp/parts32-review.XXXXXX)
cp benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/inspect-final.py \
  "$PARTS32_REVIEW_ROOT/"
cp -R benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/final-reviewed \
  "$PARTS32_REVIEW_ROOT/"
python3 -B "$PARTS32_REVIEW_ROOT/inspect-final.py"
```

It must report 200 positive/negative/context native checks, U0/B1/SeedOnly
parity, Manual/Encoding parity, all theory knockouts returning to U0, the exact
high-child rescue returning to Encoding, and a null primitive-only treatment.

The same-mask audit also writes a derived `final-evidence-audit.json`. Copy its
evidence tree before running it:

```bash
export SAME_MASK_REVIEW_ROOT=$(mktemp -d /tmp/same-mask-review.XXXXXX)
cp -R benchmarks/local/eggcc-nontrivial-encoding-payoff/candidate-same-mask/. \
  "$SAME_MASK_REVIEW_ROOT/"
python3 -B "$SAME_MASK_REVIEW_ROOT/verify-final.py"
```

This audit also checks live reconstructed source paths. Run it only after
reconstructing the exact candidate and engine roots named by the copied
`source-admission.json`, or on the retained machine state where those roots
still exist. This guide does not claim the command as a cold-checkout replay.
When its source prerequisites are present, it must report
`runtime_microbenchmark_gate_passed: true`, 32 complete cycles, and
`full_eggcc_integration_gates_green: false` because the known
retarget/format/lint limitations remain visible.

## 2. Verify immutable identities

The key hashes are:

```bash
shasum -a 256 \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/candidate-same-mask/confirmation-design.json \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/prospective-timing-design-frozen.json \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/final-source.tar \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/bin-reviewed-final/eggcc
```

Expected values, in order:

```text
a8eca05eaf0455536d737ea9064adff54573022e26ea68a1073323f3848c6a0e
c646d77e41334fd252a4e951245068f771afbbb41e44cd828e30edd58b0f6367
ba2f65df7091573a594b7c51ec68a8b3665b5c85f279fe4415ca0f6e08565873
d712e8347bf6eea231de829174a9436f411a3cedfd210daf8e7c4614c2371d2f
```

Verify QR7's corrected source freeze, immutable compiler, timing design, and
independent result:

```bash
shasum -a 256 \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/source-identities-r1.json \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/corrected-source-r1.tar \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/bin-r1/eggcc \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/prospective-timing-design-r1.json \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/timing-r1/independent-verification.json
```

Expected values, in order:

```text
22c37674b4f8617b90cceadddb2daa0992b501b9f627029ebc48dbda6515723c
17d40620cb9c621ff493cb4edfd5099a487ce0f68ee054184b75381386a7e30e
ab1185cd3e24d1ed1698bc004ed3cc70f16c89202e3cc36a910b8308221df251
490ca1cea524edfd8e0bc6d2652a87bc1dcddf2989b38be12d54feff7d88b601
d23cda45901736c2c02721f7c456bf591526fc72e262f84de1a0c27c68276b56
```

Pinned EggCC U0 is
`a0bbec127f83249074a46af3fd6f6126c90fe0fb`. Its deterministic Git archive is
SHA-256
`7a886debd758e78d0e859a05bbac75084e7da9c4f4bd0d73321dcf6f5ad25c2a`.
It can be recreated without network access:

```bash
export EGGCC_U0_REPLAY_ROOT=$(mktemp -d /tmp/eggcc-u0.XXXXXX)
git -C /Users/saul/p/eggcc archive --format=tar \
  --output="$EGGCC_U0_REPLAY_ROOT/eggcc-u0.tar" \
  a0bbec127f83249074a46af3fd6f6126c90fe0fb
mkdir "$EGGCC_U0_REPLAY_ROOT/source"
tar -xf "$EGGCC_U0_REPLAY_ROOT/eggcc-u0.tar" \
  -C "$EGGCC_U0_REPLAY_ROOT/source"
```

## 3. Replay the QR7 matrix and independently recompute runtime results

The correctness driver uses the retained immutable candidate and admitted U0
compiler, the retained oracle, and LLVM 18 at
`/opt/homebrew/opt/llvm@18/bin`. It is an immutable-binary replay, not a
cold-source reconstruction. Choose a new output root:

```bash
export QR7_BINARY=/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/bin-r1/eggcc
export QR7_OUTPUT_ROOT=$(mktemp -d /tmp/qr7-replay.XXXXXX)
python3 -B benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/matrix.py positive
python3 -B benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/matrix.py negative
python3 -B benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/matrix.py loop-negative
python3 -B benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/matrix.py context-negative
python3 -B benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/inspect.py
```

Expect 37 compiler cases, 177 exact native outputs, interpreter parity, Manual
and rescue parity, baseline knockouts, a null primitive treatment, a surviving
consumer-off relation without a store-forward event, and loop elimination in
the executed entry. This is the executed coverage; the integration plan's
larger proposed rejection matrix is not a completed test inventory. These
command durations are correctness diagnostics, not timing samples.

The runtime verifier reads retained samples and does not execute native
programs. It exclusively creates its result. Recompute it in a small temporary
copy that omits the retained result:

```bash
export QR7_VERIFY_ROOT=$(mktemp -d /tmp/qr7-verify.XXXXXX)
python3 - "$QR7_VERIFY_ROOT" <<'PY'
from pathlib import Path
import shutil
import sys
source = Path('benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration')
target = Path(sys.argv[1])
for name in ['verify-timing-r1.py', 'prospective-timing-design-r1.json',
             'timing-preflight-r1.json', 'timing-r1.py',
             'prepare-timing-r1.py', 'freeze-timing-r1.py']:
    shutil.copy2(source / name, target / name)
shutil.copytree(source / 'timing-r1', target / 'timing-r1',
                ignore=shutil.ignore_patterns('independent-verification.json'))
PY
python3 -B "$QR7_VERIFY_ROOT/verify-timing-r1.py"
```

Expect `status: passed`, all gates true, and the primary confirmation ratios in
the reference. The verifier checks frozen script/design/preflight identities,
exact row order and outputs, complete-block bootstrap intervals, both sessions,
and the instruction-group placebo gate. It does not independently reconstruct
source or re-disassemble binaries.

A fresh collection needs a separate temporary script/configuration directory.
The frozen design's absolute paths must still resolve to the hash-matched
retained compiler, native binaries, emitted programs, assembly, source, patch,
and archive. This procedure does not relocate or rebuild those artifacts:

```bash
export QR7_TIMING_ROOT=$(mktemp -d /tmp/qr7-timing.XXXXXX)
python3 - "$QR7_TIMING_ROOT" <<'PY'
from pathlib import Path
import shutil
import sys
source = Path('benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration')
target = Path(sys.argv[1])
for name in ['prospective-timing-design-r1.json', 'source-identities-r1.json',
             'actual-binary-inspection-r1.json', 'prepare-timing-r1.py',
             'timing-r1.py', 'verify-timing-r1.py', 'freeze-timing-r1.py',
             'freeze-source-r1.py', 'inspect-binaries.py']:
    shutil.copy2(source / name, target / name)
PY
unset EGGLOG_BENCH_MEMORY_GUARD
python3 -B "$QR7_TIMING_ROOT/prepare-timing-r1.py"
python3 -B "$QR7_TIMING_ROOT/timing-r1.py" screen
python3 -B "$QR7_TIMING_ROOT/timing-r1.py" confirmation
python3 -B "$QR7_TIMING_ROOT/verify-timing-r1.py"
```

The preflight checks identities and schedule balance before sampling. Each
observation includes ten serial fresh process launches and excludes compiler
and lowering time. The screen has 392 measured rows; confirmation has 3,136.
Every session has 28 warmups. Preserve partial failure output; do not overwrite
or combine sessions, discard outliers, or retry based on elapsed values. Process
and memory snapshots are descriptive; they never block or discard samples.
Report the hot and neutral workloads separately. No speedup is required for the
zero-trip control. The result supports only this fixed generated-runtime
workload, with no compiler-time, general-workload, proof, or disequality claim.

## 4. Replay the Parts32 correctness and native matrix

The immutable compiler is
`parts32-integration/bin-reviewed-final/eggcc`. Choose a new empty output root:

```bash
export PARTS32_BINARY=/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/bin-reviewed-final/eggcc
export PARTS32_OUTPUT_ROOT=$(mktemp -d /tmp/parts32-replay.XXXXXX)

python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/matrix.py positive
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/matrix.py negative
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/matrix.py loop-negative
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/matrix.py context-negative
```

The public driver records exact argv, cwd, input/executable hashes, streams,
exit code, timeout, and diagnostic elapsed time for each compiler and native
invocation. Compiler invocations have a 180-second bound and native checks a
30-second bound. These command durations are correctness diagnostics, not
performance samples.

The modes are:

```text
off, seed-only, primitive-only, forward-off, reverse-off, identity-off,
high-rescue, query-off, manual, encoding, bridge-off, consumer-off,
if-consumer-off
```

`EGGCC_SCOPED_MODE` selects a mode and `EGGCC_SCOPED_EVIDENCE` selects a new
receipt directory. The final inspector documents the expected witness/code
state for each mode.

## 5. Validate an already reconstructed selected encoding engine

The retained `final-source.tar` is an overlay whose members are bound by
`final-source-identities.json`, not a standalone source tree. This dossier does
not contain a complete cold-source reconstruction driver for the selected
encoding checkout. This section applies only after the exact base revision and
retained overlay listed in `parts32-integration/source-admission.json` and
`final-source-identities.json` have already been reconstructed. Sections 1-4
review retained evidence or replay it with immutable compilers; those steps do
not depend on this optional source-validation step.

From the reconstructed isolated encoding root run:

```bash
cargo test --locked -p egglog-experimental --test injectivity_disequality
make check
```

Confirm that the focused filter selects tests. The captured final run selected
18 injectivity/disequality tests and the complete selected-engine `make check`
passed. Do not accept or rewrite snapshots while reproducing the host checks.

## 6. Review or repeat the Parts32 runtime confirmation

The accepted campaign is already retained under
`parts32-integration/timing/`. Review
`timing/independent-verification.json` first; its SHA-256 is
`9b26a8c4a1176979d555ff0c054ee0c985c8a3faa0e7c4313f225a4cbaaae959`.
It reports `all_sessions_passed`, `all_session_speedup_gates_passed`, and
`placebo_validity_passed` as true, with no consistent placebo shifts. The two
session directories hold the raw rows and summaries used by that result.

The verifier deliberately uses exclusive creation. To recompute its result,
copy the complete experiment directory, remove only the copied
`timing/independent-verification.json`, and run `python3 -B verify-timing.py`
inside the copy. This reads retained rows and does not execute native programs.

A fresh collection also belongs in a copied evidence directory. It uses
existing native binaries and does not compile. Keep
`EGGLOG_BENCH_MEMORY_GUARD` unset. The three workloads each execute one million
loop iterations; no raytracing workload is involved. From the copied
experiment directory, remove only the copied current preflight and accepted
`timing/` tree, then run:

```bash
unset EGGLOG_BENCH_MEMORY_GUARD
python3 -B prepare-timing.py
python3 -B timing.py 1
python3 -B timing.py 2
python3 -B verify-timing.py
```

`prepare-timing.py` exclusively creates `timing-preflight.json` after hashing
the design, producer, verifier, source, compiler, all five arm binaries,
emitted programs, and assembly. `timing.py` exclusively creates one complete
session directory and checks the process inventory before warmups, at every
15-cycle block boundary, and after measurement. Preserve a failed session
whole and never combine its partial rows with accepted rows. The retained
`timing-aborted-process-admission-01/` and
`timing-aborted-process-admission-02/` attempts are excluded from the accepted
result.

Each complete session contains:

```text
45 warmup rows
1,350 measured rows (90 cycles x 3 workloads x 5 arms)
8 passing process checks
one summary.json
```

The independent verifier recomputes identities, exact outputs, schedule order,
process checks, paired log ratios, whole-block bootstrap intervals, speed gates,
and placebo validity. Report every workload and session separately. Do not pool
them or select cycles after inspecting elapsed values.

## 7. Review or repeat the compiler-time diagnostic

Compiler timing is diagnostic only. The completed 10-cycle, five-arm result is
`parts32-integration/compile-diagnostic-final/results/summary.json`, SHA-256
`283a6af7bb6a9d69d87510fab681042170f47ff70efa7a95719e37a8d36ad12e`.
Its Encoding/Manual paired median ratio is `0.99919`, with descriptive interval
`[0.99370, 1.00697]`. The reconstruction receipt is
`compile-diagnostic-final/reconstruction.json`, SHA-256
`d898d41033574ab93d315d31f068b15da323875bd1becef79db6a2db0f7f3d2f`.

To repeat the diagnostic, copy its driver and frozen design into a fresh root.
The sibling links keep the immutable command map read-only and use the same
measurement-exclusion lock as generated-runtime collection. The exact
reconstructed working directories in the receipt must still exist. Run only
after any fresh generated-runtime collection so compilation cannot interfere:

```bash
export PARTS32_DIAGNOSTIC_SOURCE="$(pwd)/benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration"
export PARTS32_DIAGNOSTIC_COPY=$(mktemp -d /tmp/parts32-compile-diagnostic.XXXXXX)
mkdir "$PARTS32_DIAGNOSTIC_COPY/compile-diagnostic-final"
cp "$PARTS32_DIAGNOSTIC_SOURCE/compile-diagnostic-final/run.py" \
  "$PARTS32_DIAGNOSTIC_SOURCE/compile-diagnostic-final/prospective-design.json" \
  "$PARTS32_DIAGNOSTIC_COPY/compile-diagnostic-final/"
ln -s "$PARTS32_DIAGNOSTIC_SOURCE/final-reviewed" \
  "$PARTS32_DIAGNOSTIC_COPY/final-reviewed"
ln -s "$PARTS32_DIAGNOSTIC_SOURCE/timing-measurement.lock" \
  "$PARTS32_DIAGNOSTIC_COPY/timing-measurement.lock"
python3 -B "$PARTS32_DIAGNOSTIC_COPY/compile-diagnostic-final/run.py" \
  run --acknowledge-diagnostic-only
```

It includes EggCC invocation and excludes generated-program execution. The
retarget differences make U0 comparisons descriptive integration-cost data,
not a compiler-speed claim.

## 8. Review supporting integrations

The complete reports and retained matrices are:

```text
benchmarks/local/eggcc-nontrivial-encoding-payoff/affine-integration/
benchmarks/local/eggcc-nontrivial-encoding-payoff/route-integration/
benchmarks/local/eggcc-nontrivial-encoding-payoff/sort-integration/
```

Their `inspect.py` scripts check causal receipts and code identities. Route and
Sort also retain independent semantic `verify.py` scripts, which write replay
artifacts; run them only in a copied evidence root or with their documented
output-root override. These integrations are correctness/mechanism evidence and
must not be reported as measured speedups.

## 9. Review final validation and search closure

The final validation authorities are:

```text
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r1/final-validation-summary.md
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r1/final-validation-summary.json
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/root-make-check-r4/receipt.json
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r1/commands/engine-make-check-py314-git-r3/receipt.json
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/final-summary.md
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/final-summary.json
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/nits-r2.patch
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/u0-nits/comparison.json
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/matrix-r2/r1-r2-comparison.json
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/matrix-r2/actual-binary-inspection-r2.json
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/host-tests/comparison.json
benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/host-tests/command/receipt.json
```

Verify the r2 records without executing the compiler:

```bash
shasum -a 256 \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/final-summary.json \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/nits-r2.patch \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/u0-nits/comparison.json \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/matrix-r2/r1-r2-comparison.json \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/matrix-r2/actual-binary-inspection-r2.json \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/host-tests/comparison.json \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/root-make-check-r4/receipt.json
```

Expected values, in order:

```text
051e8a3951265779bba1ddd3b5b0eee79fc8c73dc06c7657d9d4db20f1214d9a
b0802da11e40e6d7fba3eefc8a3639a81153bee445cd90a71000e967d4211e00
92a5f5a568bed5d6ee6db381a8de576cf6b473bc7a713d364bde80a9a21dd374
0b29b24ccfe9b5b7de9d2b5a1a2cd82f095810384fa542aeb935d042dee125f4
1c92c4b9b4407a6cc4a521d7a5f94cbb816edcbd262b0ab8b3426d0d0f57fdf4
12bf6cbaef77011ba8f029537559eb1cf51c4898ea016355cb8e4aeb3cf2edab
4e419fe4e240069a782f8ea3a01dd1fc0e3a396c8f5f6934cb1c203dfec574f2
```

Review both summaries before interpreting an exit code. The repository-root
and isolated-engine `make check` runs exit zero, and the cleaned r2 EggCC DAG
suite passes 70 tests. The four-hunk r2 patch fixes the QR7-local formatting and
two Clippy findings exposed by direct r1 checks. Root and DAG formatting pass;
the one remaining root and two remaining DAG Clippy diagnostics reproduce in a
fresh pinned-U0 control.

The cleaned r2 host root command exits one only after 31 unit and 2,420
file-test bodies pass, because the same 13 dependency-retarget snapshots remain
unaccepted. Its first captured attempt lacked the external Tiger executable;
the final receipt uses the retained hash-verified Tiger without changing source.
The failed host commands remain failures, and no snapshot is accepted.

The r2 matrix replays all 37 cases and 177 native outputs. It establishes
semantic and execution-content equivalence with r1; complete regenerated Mach-O
hashes differ in UUID, temporary linker metadata, and the derived signature.
The performance result remains a direct measurement of the frozen r1 files.
Replaying r2 validates the cleanup and code shape; it does not produce r2 timing
samples.

To repeat the repository-required check from this repository root:

```bash
unset EGGLOG_BENCH_MEMORY_GUARD
make check
```

The retained successful root receipt is the result authority for this study. A
fresh run can differ if unrelated work in the shared dirty checkout changes.
The heavy EggCC `raytracewithscreen` test was excluded from isolated host
validation; the ordinary `raytrace-test-benchmark` fixture ran and passed. No
raytracing workload contributes to any timing result.

The final hypothesis pass is recorded in:

```text
goals/eggcc-nontrivial-encoding-payoff/cycles/06-codex-audit.md
goals/eggcc-nontrivial-encoding-payoff/cycles/06-fable-audit.md
goals/eggcc-nontrivial-encoding-payoff/cycles/06-fable-validation.md
goals/eggcc-nontrivial-encoding-payoff/hypotheses.jsonl
```

The Fable file is retained model output. Use its source-validation companion for
the supported conclusions and corrections; in particular, do not infer a
specific LLVM pass order, an exhaustive equality-consumer census, or a lifetime
proof from `ContextOf`.

## 10. Interpret failures

| Failure | Interpretation |
| --- | --- |
| preflight competitor | Environmental rejection; preserve it and wait or run other nonmeasurement work. |
| process checkpoint competitor | Exclude and preserve the whole session before inspecting timing values. |
| output, exit, or timeout mismatch | Correctness failure; no performance claim. |
| required speed upper bound at or above `0.99` | That primary comparison does not pass its frozen gate; QR7's neutral control has no speedup requirement. |
| consistent placebo shift outside `[0.99,1.01]` | Overall Parts32 timing result is inconclusive. |
| missing witness | Unknown; suppress export. |
| unsupported/container field | Outside the encoding; do not coerce to equality or disequality. |
| 13 known retarget snapshots | Preserve and attribute by exact bytes; do not accept them. |
| new test, lint, snapshot, or source drift | Candidate validation failure until localized. |

No commit, push, pull request, snapshot acceptance, proof integration, or paper
edit belongs to this reproduction.
