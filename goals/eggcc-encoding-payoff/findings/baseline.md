# Independent untouched-main reproduction

**U0 produces wrong results on both new endpoints.** AddMAX and SubMIN each print `true\n` under source interpretation and optimization-free native O3_O3 lowering, but `false\n` after the complete EggCC optimizer. Interpreting and lowering the exact retained optimized Bril independently reproduce `false\n`. These are successful wrong-output executions on untouched pinned main, not conclusions inferred from B1's encoding abort.

The complete12-case matrix finished96/96 commands with exit0 and no timeouts. The other10 nearby/skipped controls agree with the independent oracle. Both optimizer invocations per case completed actual passes0,1,2, for24 complete pass logs. No timing claim is made.

## Frozen authorities and chronology

Raw evidence: [baseline-newcase](../../../benchmarks/local/eggcc-encoding-payoff/baseline-newcase/).

| Authority | SHA-256 |
|---|---|
| Encoding-first checkpoint, `compiler/first-detection/checkpoint.json` | `0d438df08ca55653d6fdd0eecfe448f45918eea0b0688f87fa5ee35996714eee` |
| Independent oracle, `oracle/run-01/expected-matrix.json` | `0bd80e89973c34b067cf014501dd2b0efb7397bdeafce4bfa609ce09710b5a6f` |
| Prospective U0 matrix manifest | `d84f522ccf84e07ade96a1509a2bdbbd63c2380037cc6240cc6c6bd08f555c79` |
| Complete matrix, `results.json` | `67f2f41322496d734cefb77492995cc0cac6c1e27dab94d601bb31c0fd71d25b` |
| Terminal consistency audit, `audit.json` | `7b2a6703d4cd8ed82a4ddbd7fad68cc8afcade0685824fcc3f30f3d9a6f8d8ee` |

The driver checked these first two authority hashes before launching, copied/hash-checked all12 oracle fixtures, and froze its manifest before any U0 case. The independent audit checked the encoding checkpoint timestamp precedes the U0 manifest and that every command began after that manifest. Case order was declared as AddMAX, SubMIN, then the remaining oracle rows; first endpoint outcomes were reported before the controls finished. The first checkpoint records pass0 Injective conflicts; this U0 matrix supplies independent downstream output evidence after that checkpoint.

U0 is main `a0bbec127f83249074a46af3fd6f6126c90fe0fb`, cwd `/Users/saul/p/wt/eggcc/encoding-payoff-upstream-control`, with original declared engine dependencies. It used only the admitted frozen pair:

- Compiler SHA `d86869982413d4561cf713cc769c96eb1c9bfefe46fa459a2692c53a7aa93cf0`.
- Current-main Tiger SHA `130eaba8bb575e196b8e18898826356269efe6e28a56b9d3690ef42647d3b201`.
- Admission manifest SHA `6f1b81ec383a88a15abff05152a66d6e826db24817d6f021b9670ed3889296fa`.

That manifest links original locked root/DAG graphs, source map, build receipt and runtime provenance. This matrix checked all771 U0 source hashes, compiler/Tiger/runtime binaries and six runtime source inputs before/after; none changed. B1 and E1 source were not accessed or modified. No new build was needed.

## Exact semantics and commands

The independent exact-integer calculation reduces Add/Sub modulo2^64 and compares signed i64 values. On AddMAX, `9223372036854775807 + 1` wraps to `-9223372036854775808`, so the selected `shifted < 0` prints true. On SubMIN, `-9223372036854775808 - 1` wraps to `9223372036854775807`, so selected `0 < shifted` prints true. The U0 DAG interpreter source uses `wrapping_add`/`wrapping_sub` (`dag_in_context/src/interpreter.rs:239–244`); independently executed source Bril/native programs agree. Both fixtures use only Add or Sub, strict LessThan, a guarded branch and print; neither contains Mul or the known non-strict endpoint comparisons.

The stdlib-only independent driver is `baseline-newcase/reproduce.py`; it does not import the compiler worker's driver, observer evaluator, collector, or project Python code. For each fixture, it ran these eight calls from cwd U0, with absolute paths retained per command:

```sh
"$BIN" --with-context --run-mode parse --interp --run-data-out "$CASE/source-parse.json" "$SOURCE"
"$BIN" --with-context --run-mode optimize --interp --run-data-out "$CASE/optimize-correctness.json" "$SOURCE"
"$BIN" --with-context --run-mode optimize --run-data-out "$CASE/optimize-emit.json" "$SOURCE"
"$BIN" --with-context --run-mode parse --interp --run-data-out "$CASE/emitted-parse.json" "$CASE/optimized.bril"
"$BIN" --with-context --run-mode llvm --optimize-egglog false --optimize-bril-llvm O3_O3 -o "$CASE/source-program" --llvm-output-dir "$CASE/source.ll" --run-data-out "$CASE/source-lowering.json" "$SOURCE"
"$CASE/source-program" "$INPUT_I64"
"$BIN" --with-context --run-mode llvm --optimize-egglog false --optimize-bril-llvm O3_O3 -o "$CASE/emitted-program" --llvm-output-dir "$CASE/emitted.ll" --run-data-out "$CASE/emitted-lowering.json" "$CASE/optimized.bril"
"$CASE/emitted-program" "$INPUT_I64"
```

`optimized.bril` is the exact successful emission command's stdout bytes, not a reimplementation or assumed repeat result. Normal RunResult JSON skips visualizations, so separate interpreted/emit calls are necessary. Reinterpreting the emitted artifact ties its output to the correctness receipt; both artifact parses and native paths agree. The emitted programs replace the selected inner result with `const false`. Both original and emitted lowering use `optimize_egglog=false`, the same O3_O3 backend/runtime and numeric native argument. No extra optimizer is silently inserted during lowering. Both `# ARGS:` values and generated executable `-args` files were checked; unused trailing compiler positional arguments were not used to supply input.

All compiler/parse/lowering calls had180-second bounds (emitted parse60); actual native execution had30-second bounds. Every command retains argv, cwd, PID, full stdout/stderr, start/end, exit/timeout, source manifest and complete effective-environment hashes. Common environment explicitly sets `EGGCC_ROOT=U0`, private U0 target, Rust1.91, Rayon1, LLVM18 prefix/library path and `RUST_LOG=info`; memory guard is uniformly **UNSET**. LLVM18 `opt`/`clang-18` executable paths and hashes are pinned in the manifest. No profiling, `--add-timing`, source mutation, or source/snapshot acceptance occurred. Captured elapsed values are diagnostic timeout provenance only.

## Results

Values below are the program outputs in RunResult/direct native stdout. `empty` means the exact empty string, with no print executed; it is not null, absent output evidence, or the CLI's extra formatting newline.

| Case | Oracle, source interpreter/native | Full optimizer, emitted interpreter/native | Outcome |
|---|---|---|---|
| add-max | `true\n` | `false\n` | Wrong output |
| sub-min | `true\n` | `false\n` | Wrong output |
| add-max-minus-one | `false\n` | `false\n` | Matches |
| add-two | `false\n` | `false\n` | Matches |
| add-one | `false\n` | `false\n` | Matches |
| add-zero-skipped | empty | empty | Matches |
| add-negative-one-skipped | empty | empty | Matches |
| sub-min-plus-one | `false\n` | `false\n` | Matches |
| sub-negative-two | `false\n` | `false\n` | Matches |
| sub-negative-one | `false\n` | `false\n` | Matches |
| sub-zero-skipped | empty | empty | Matches |
| sub-one-skipped | empty | empty | Matches |

All36 interpreted JSON receipts have both original/result fields present and non-null strings. In optimize correctness receipts, original output matches the oracle even on the two failing endpoints. All36 intentionally uninterpreted emit/lowering receipts have both fields present and null; those fields were never used as agreement. All24 native executions have independently checked exit0 and exact stdout, with full stderr retained. The audit checks all recorded artifact/output hashes, actual pass logs, manifest/command environment equality, expected output linkage, and all96 child PIDs absent at terminal.

## Scope

These successful U0 executions establish two pre-existing wrong-output cases on the selected main revision, independently of E1 integration and observer rejection. They support the approved Add/Sub lead and are distinct fixture/operator families from the excluded old Mul and non-strict-comparison findings. This slice does not itself localize the first unsound rule, demonstrate a conservative repair, audit the encoding witness's semantic domain, establish unique detector power, or show performance benefit. Those remain separate root/owner evidence and review gates; this reproduction alone does not declare the goal complete.
