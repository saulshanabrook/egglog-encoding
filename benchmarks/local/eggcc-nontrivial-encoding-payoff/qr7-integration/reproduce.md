# Reproduce the QR7 result

Read the [explanation](report.md) for the source-to-consumer argument. This guide
separates retained-data verification, fresh correctness replay, and fresh native
timing. Keep every retained result unchanged; the scripts refuse to overwrite
many existing outputs.

The commands assume this machine's repository and retained absolute paths:

```bash
export QR7_ROOT=/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration
cd "$QR7_ROOT"
```

## Verify the immutable cohort

The [source identity manifest](source-identities-r1.json) binds the corrected
source overlay, compiler delta, admitted base archives, harness, inputs, and
release-build recheck. [Binary identities](binary-identities-r1.json) bind the
evaluated compiler and Tiger. U0 is EggCC
`a0bbec127f83249074a46af3fd6f6126c90fe0fb`; the selected engine base is
`392b6d6b48b5bc307a5b9c981c957fc0a09e23e5` plus the retained encoding delta.

```bash
shasum -a 256 \
  corrected-source-r1.tar \
  eggcc-candidate-r1.patch \
  bin-r1/eggcc \
  prospective-timing-design-r1.json \
  timing-r1/independent-verification.json
```

Expected SHA-256 values, in that order:

```text
17d40620cb9c621ff493cb4edfd5099a487ce0f68ee054184b75381386a7e30e
3242cf2bd7925912fa7902b9fdeee2a98889fe6e1dba5f5d0d93cea31691295f
ab1185cd3e24d1ed1698bc004ed3cc70f16c89202e3cc36a910b8308221df251
490ca1cea524edfd8e0bc6d2652a87bc1dcddf2989b38be12d54feff7d88b601
d23cda45901736c2c02721f7c456bf591526fc72e262f84de1a0c27c68276b56
```

`corrected-source-r1.tar` is an overlay, not a standalone checkout. Its
`MANIFEST.json` identifies `eggcc/`, `encoding/`, and `evidence/` members. The
admitted full base archives and earlier dependency/runtime overlays are named
by [source-admission.json](source-admission.json). Do not substitute the initial
`eggcc-candidate.patch` or rerun `write-candidate.py` as a reconstruction of the
corrected evaluated source.

## Recompute the retained-data inspections

These commands execute no compiler or benchmark process. They copy captured
data, remove only copied result files, and write new inspection outputs under
a fresh `/tmp` directory:

```bash
QR7_REVIEW=$(mktemp -d /tmp/qr7-review.XXXXXX)
cp -R final-r1 "$QR7_REVIEW/final-r1"
cp -R timing-r1 "$QR7_REVIEW/timing-r1"
cp inspect-binaries.py verify-timing-r1.py timing-r1.py \
  prepare-timing-r1.py freeze-timing-r1.py \
  prospective-timing-design-r1.json timing-preflight-r1.json "$QR7_REVIEW/"
rm "$QR7_REVIEW/final-r1/inspection.json" \
  "$QR7_REVIEW/timing-r1/independent-verification.json"

QR7_OUTPUT_ROOT="$QR7_REVIEW/final-r1" python3 -B "$QR7_ROOT/inspect.py"
python3 -B "$QR7_REVIEW/inspect-binaries.py"
python3 -B "$QR7_REVIEW/verify-timing-r1.py"
```

Expected results:

- The causal inspector passes output, Manual parity, primitive-null,
  downstream-consumer, and actual-entry-loop gates. Its historical
  `timing_collected:false` does not inspect the later runtime campaign.
- The actual-binary inspector reports one baseline instruction group
  (91 instructions, two internal backward branches) and one winning group
  (55 instructions, zero internal backward branches).
- The independent timing verifier reports `status: passed` and every gate
  true, including the primary confirmation upper bounds below `0.99` and
  same-code medians within 2%.

The timing verifier recomputes order, row counts, recorded output hashes,
paired ratios, and complete-block intervals from retained rows. Running it in
the copy changes output paths, so its new JSON need not have the retained
verifier result's whole-file hash. It does not re-execute native programs.

## Replay correctness and native code

The [matrix driver](matrix.py) uses the immutable compiler selected below and
untouched [admitted U0](../admission/bin/eggcc) to lower every emitted arm with
LLVM 18 `O3_O3`, `optimize-egglog=false`, and the same runtime. It also needs
the retained `/private/tmp/eggcc-qr7-candidate` working directory/runtime and
the installed LLVM 18 tools. These are retained-machine replay commands, not
an automated cold-source reconstruction. Reconstruct and verify those exact
source/runtime prerequisites from the manifests before using them elsewhere;
never overwrite an existing candidate root.

```bash
export QR7_BINARY="$QR7_ROOT/bin-r1/eggcc"
export QR7_OUTPUT_ROOT=$(mktemp -d /tmp/qr7-native.XXXXXX)
python3 -B matrix.py positive
python3 -B matrix.py negative
python3 -B matrix.py loop-negative
python3 -B matrix.py context-negative
python3 -B inspect.py
```

The four phases produce 154 positive/boundary/control native outputs, 18
semantic-negative outputs, four changed-pointer outputs, and one absent-context
output: **177 exact outputs** in total. The driver compares optimized and
original interpreter output, and checks native output against the
[independent oracle](../qr7-screen/oracle.py). Each compiler invocation has a
180-second timeout and native invocation a 30-second timeout. Captured command
durations are diagnostics, not performance samples.

The positive phase covers all 14 treatments. `cancellation-off`, `identity-off`,
`query-off`, `bridge-off`, and `consumer-off` restore baseline code; `x-rescue`
and `key-rescue` restore winning code. `transport-off` is an export-gate
placebo, not a direct transport-computation knockout. Missing quotient,
missing remainder, and mixed-divisor witnesses must remain `-24\n`, not
`28\n`; changed pointers and absent contexts must export nothing.

The captured [mechanism test receipt](revision-01/commands/mechanism-tests/receipt.json)
and [output](revision-01/commands/mechanism-tests/stdout) show six selected
tests passing. Focused checks, replay, and retained timing do not replace the
host and repository's required full validation. Preserve and attribute pending
snapshots; do not accept them while reproducing.

## Collect a fresh runtime campaign

Use a new copy for every campaign. The frozen design stores absolute native
binary paths; the existing immutable arm binaries must remain at those paths.
Copying the scripts redirects newly written timing artifacts, not those binary
inputs. This is a replay of the retained cohort on the retained machine.

```bash
cd "$QR7_ROOT"
QR7_TIMING=$(mktemp -d /tmp/qr7-timing.XXXXXX)
cp prepare-timing-r1.py timing-r1.py verify-timing-r1.py \
  freeze-timing-r1.py freeze-source-r1.py inspect-binaries.py \
  prospective-timing-design-r1.json source-identities-r1.json \
  actual-binary-inspection-r1.json "$QR7_TIMING/"
unset EGGLOG_BENCH_MEMORY_GUARD
python3 -B "$QR7_TIMING/prepare-timing-r1.py"
python3 -B "$QR7_TIMING/timing-r1.py" screen
python3 -B "$QR7_TIMING/timing-r1.py" confirmation
python3 -B "$QR7_TIMING/verify-timing-r1.py"
```

The preparer verifies source, compiler/backend, arm binaries, emitted code,
assembly, and balanced order before writing a new preflight. Each observation
times ten fresh serial processes. Keep compilation and correctness replay
outside timing. The 14-cycle screen has 392 measured rows; the independent
112-cycle confirmation has 3,136. Each session has 28 warmup invocations. The
hot workload is `(12,12,10000000)` with exact output `49999995000000\n`;
zero-trip `(12,12,0)` must print `0\n` and has no speedup requirement.

Retain every completed observation and any partial failed campaign. Timeout,
signal, nonzero exit, stderr, or wrong stdout stops collection. Memory/process
pressure is recorded descriptively and never blocks or discards samples;
the memory-guard environment variable must be absent. Report each workload
and session separately. The frozen same-code gate permits each hot median to
be within 2% of its instruction-identical reference; it does not require its
interval to contain one.

This campaign measures generated-program process runtime, including startup,
argument parsing, allocation, computation, and printing. It excludes compiler
and lowering time, disequality contribution, proof work, and raytracing. The
baseline executed entry already has no i64 load: the claimed endpoint is the
phase-ordering change from a cyclic reduction to acyclic arithmetic. No suite-wide
estimate, compiler bug, or compiler-speed claim follows from these commands.
