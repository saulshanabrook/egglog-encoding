# MISAAL completed-native packaging recovery

The original blur3x3 parent has now passed packaging recovery and independent ordinary replay. Evidence is retained under `benchmarks/local/reproduction/misaal-blur3x3-materialization-attempt-0001/`: packaging took 0.408 seconds, ordinary replay 0.552 seconds, and the native output contract passed. The replay SHA-256 is `8a66eeb28625418f8fc7d5cf0ddfb72dc8471eb1f281b4d60d00108f900af570`. No native compiler, original backend, or LLVM verifier was rerun for recovery. Strict proof validation was not part of this source-reproduction gate.

## Native lowering blocker found after replay

The source audit found that pinned Hydride initializes its legalizer with
`bitsimd = true`, but the selected x86 SIMD pass never clears that flag. Its
BitSIMD branch replaces legalized calls with `UndefValue`; the retained canary
contains `ret <32 x i16> undef`. LLVM verification and the successful standalone
Egglog output checks do not establish meaningful native lowering. This canary
therefore remains **outside completed corpus admission** pending a narrow pass-mode
repair, a fresh native parent run, and validation of the actual lowered functions.
The original outputs and successful replay remain diagnostic evidence.

## Original evidence

Source stage: `/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/1b8cc1e5cd28697cf8c6f79535959b73feda97457d61e5c8306a6af8bc365cd2/attempt-0001/stage.json`.

The sealed capture has generator return code 0, source_capture_complete true, source_completion success, five nonempty final outputs (`blur3x3.a`, `.stmt`, `.h`, `.ll`, `.s`), successful final LLVM verification, one successful generated Python child, one successful compiler backend invocation and one completed LLVM legalization. The wrapper then failed importing `rich` from the former native_check_contract module. That wrapper return code 1 is retained as historical failure; it is never rewritten as native execution success.

The archived capture hook is `benchmarks/local/reproduction/misaal-packaging-dependency-repair/misaal_reproduction.py`, SHA-256 `dc5721226b9d5547e432f3780d012438188822fa4ecab5ec11312b1170fd1a92`, matching the original stage input. Read-only AST comparison confirms both native hooks and the old inline packaging body match the repaired implementation, allowing only extraction into a helper and packaging imports. Recovery enforces this comparison.

## Interface and admission

`materialize_complete_capture(source_stage: Path, output: Path, *, native_implementation: Path) -> dict` in `scripts/misaal_reproduction.py` verifies the original stage's artifact membership/hashes, archived hook, current request source files/executables/native library/legalizer, exact final output set, exact child and invocation sets, raw input/stdout/result receipts, retained legalizer input/tool identities, and saved LLVM verifier/feedback linkage. It uses the same pure packaging helper as a fresh capture. No native tool is executed. An existing destination or a destination inside the old attempt is refused.

The fresh `capture.json` records old stage/evidence hashes, old implementation identities, new materializer/helper hashes, original process failure, and `native_execution_repeated: false`. Its admitted status is only `ordinary-validation-pending`. Ordinary replay is still required before reproduction success. Recovery failures retain a fresh failure receipt and expose no workloads. The original stage and all original files remain untouched.

When integrating with `run_stage`, include both new output files and `recovery.verified_evidence` paths in the stage's `artifacts`; otherwise later reuse would bind only the new packaging files rather than the native evidence they reference. Bind source-stage SHA and current materializer hashes in the recovery stage identity. This patch exposes the callable and public CLI; it does not edit the shared coordinator or source settings.

## Invocation accounting boundary

Source review by the HardBoiled/MISAAL worker establishes the current canary's coverage: process.stdout.log line2591 reports creation of new pattern files and line3173 reports one unique expression to compile. Cold x86 pattern creation/deduplication does not call Egglog. The compiler's reached optimization paths all use the observed execute_egglog_file hook; repeated nodes reuse the compiled unique expression. The low-level script and inspected LLVM generator/legalizer code use only llvm-link, llvm-dis and opt, all three recorded successful tools.

A separate future gap remains: warm-cache PatternAbstractor -> PatternUtils.is_pattern_valid_egg directly invokes a backend subprocess outside the compiler hook; EggLogCompiler.is_pattern_valid also has a direct subprocess path. This patch does not intercept or invent workloads for those helper calls. Recovery is deliberately restricted to one generated child under the archived frontend's fresh-cache precondition. Multi-child recovery is rejected pending complete helper-call accounting.

## Guarded recovery command

The actual combined driver is retained as `benchmarks/local/reproduction/misaal-blur3x3-materialization-attempt-0001/run.py`; it executes the following packaging step, then ordinary validation. For another attempt use a fresh enclosing directory and the exclusive heavy slot; never overwrite the source stage.

```python
from dataclasses import asdict
from pathlib import Path
from benchmarking.pilot import run_bounded_command
from scripts.misaal_reproduction import save_receipt
from scripts.reproduction_process import exclusive_job

root = Path('/Users/saul/p/egglog-encoding')
source_stage = root / 'benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/1b8cc1e5cd28697cf8c6f79535959b73feda97457d61e5c8306a6af8bc365cd2/attempt-0001/stage.json'
archive = root / 'benchmarks/local/reproduction/misaal-packaging-dependency-repair/misaal_reproduction.py'
attempt = root / 'benchmarks/local/reproduction/misaal-blur3x3-materialization-attempt-0001'
with exclusive_job(root / 'benchmarks/local/reproduction/stages/.heavy-job.lock'):
    attempt.mkdir(exist_ok=False)
    process = run_bounded_command(
        [str(root / '.venv/bin/python'), '-m', 'scripts.misaal_reproduction',
         'materialize', '--source-stage', str(source_stage),
         '--native-implementation', str(archive), '--output', str(attempt / 'capture')],
        root, attempt / 'materialize', timeout_sec=120,
        memory_limit_bytes=5 * 1024**3, require_guard=True,
        disk_reserve_bytes=10 * 1024**3, allow_warning_pressure=True,
    )
    save_receipt(attempt / 'process.json', asdict(process))
```

After a successful process and `capture.json` reporting ordinary-validation-pending, root can run its usual separately guarded `validate_capture` admission. No original compiler command is rerun.

## Patch and validation

Owned files: `scripts/misaal_reproduction.py`, `tests/test_misaal_reproduction.py`. Fresh live snapshots are in `.baseline/misaal-materialization-recovery/`; patch is `MISAAL-MATERIALIZATION-RECOVERY.patch`. Read-only dependency copies used by mirror imports are not integration files.

Targeted tests exercise successful packaging without any native subprocess, duplicate/root preservation, old evidence immutability, reused output refusal, changed final output/child/raw/stdout/source/executable, omitted/additional invocations/children, sealed failed native parent/child/backend/LLVM feedback, and archived implementation mismatch. Ruff/format and focused mypy are separate static gates. These protocol fixtures do not claim a successful native reproduction.

Validation completed: 26 targeted tests passed; Ruff lint/format and focused two-file mypy with --follow-imports=silent passed. Root reviewed the patch, integrated it, and ran 95 combined recovery/validation tests before the successful real replay.
