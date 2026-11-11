# DialEgg / SpEQ complete capture implementation handoff

This mirror implements the approved complete-parent path. **No native build, generator, container, download, device execution, or performance campaign was run in this slice.** Tests below use synthetic process/graph doubles and establish adapter contracts only.

## Owned integration files

- `scripts/suite_capture_dialegg_speq.py` (public complete/case-selection CLI; legacy diagnostics retained)
- `scripts/paper_benchmarks/record_speq.py` (all original-C regions, native extraction reports, outcomes)
- `scripts/dialegg_speq_complete.py` (new native patch, delegate, guards, orchestration and receipts)
- `tests/test_dialegg_speq_complete.py` (new focused synthetic tests)

`tests/test_suite_capture_dialegg_speq.py` is unchanged. `.baseline` retains original owned sources. Root supplied the newer shared `benchmarking/pilot.py`; do not integrate it as this agent's change. No edits were made through `benchmarks/local` or `goals` symlinks, to source checkouts, catalog, or benchmark cache.

## Implemented boundary

DialEgg's complete patch retains both engine invocation and MLIR reconstruction. Every actual block gets a unique raw program, context, stdout/stderr and JSON receipt. Its delegate invokes the explicitly selected historical native engine with the unmodified raw input; nonzero exits, missing/extra/multiline responses, and malformed output terms fail before reconstruction. A completed native parent must produce nonempty MLIR, pass the host `mlir-opt` verifier, and have every standalone replay agree with its actual native output sequence. Helpers with zero extracts retain a zero-output contract. No `DIALEGG_SHAPE_QUERIES` are added. Constructor/dynamic costs and source schedules/extraction order are retained in modernization; the source CLI does not expose costs as output, so no cost-number comparison is claimed.

Population is 15 `bench/` runtime configurations (five kernels × three pass orders) plus nine actual `test/` timer parents. `dialegg-extra-nmm-160` requires explicit selection and is labelled `artifact-extra`. All 25 configured input/template paths exist in the current pinned checkout. The exact native patch is a deterministic string transformation saved as the copied `frontend/src/EqualitySaturationPass.cpp`, with original/patched hashes. Original source files are untouched.

SpEQ complete mode uses each of the eight available original C files (not REVTest or reference substitutes), including verified PolyBench headers. It runs the actual LLVM/REV frontend and retains every ordered FIR region. Only exceptions from the original `foldFromStr` parse/SMT boundary are legitimate skips. Parsed regions execute the original 5 transform / 1 expand / 3 transform schedule inside independent pushed scopes inheriting the reference graph. The pinned egglog-python 13.2.0 `_run_extract` response is observed without adding a command, recording the actual term and cost. Driver kernel selection/CSR/CSC formatting and runtime-condition text are retained. The parent requires its intended application kernel in at least one region after the entire sequence completes; other parsed regions may be unmatched. Engine failures abort the parent. Native session, region outcomes, parser logs, and failed-parent receipts remain diagnostic evidence. TPAL and TSVC2 remain explicit missing-input cases, pending exact-source/setup recovery.

Receipts separate `source_complete`/`source_completion`, `ordinary_compatible`, `workloads`, and `proof_validation: not-run`. Ordinary admission compares all native output terms with the current standalone CLI; process exit alone is insufficient. Source failure admits no partial workloads. Immutable attempts/resume and broader input locks belong to the root coordinator.

All top-level native builds/parents/verifiers/replays use the shared guarded runner with `require_guard=True`, a 10 GiB disk reserve, 10 GiB process-group RSS default, and `allow_warning_pressure=True` for these diagnostics. Guard preflight refusals become durable `resource-stopped` receipts. Native child processes do not start separate sessions. The coordinator must invoke the function in-process; it must not wrap the entire adapter in another session guard.

## Callable interface and proposed first canary

`scripts.dialegg_speq_complete.complete_capture(args: argparse.Namespace) -> int` accepts the fields shown below. It writes `<output>/manifest.json` plus per-family/per-case receipts. Return 0 means every selected case reproduced, 1 means an ordinary blocked case, 2 means a safety/deadline stop. `output` must not already exist. `case=None` selects the exact paper population for the family; duplicate/unknown IDs fail closed. Required family-specific paths are explicit; there is no download fallback.

**Proposed, not executed**, for root's guarded stage-lock owner to call in-process:

```python
from argparse import Namespace
from pathlib import Path
from scripts.dialegg_speq_complete import complete_capture

root = Path('/Users/saul/p/egglog-encoding')
status = complete_capture(Namespace(
    family='speq', case=['speq-spmv_npb'],
    output=root / 'benchmarks/local/complete-reproduction-canaries/speq-spmv-npb-01',
    egglog=root / 'target/release/egglog-experimental',
    speq_artifact=root / 'benchmarks/local/sources/speq/artifact',
    speq_lleq=root / 'benchmarks/local/sources/speq/lleq',
    speq_python=Path('/Users/saul/.cache/uv/archive-v0/0-NSo2ksd2fjStFc/bin/python'),
    llvm17_config=Path('/opt/homebrew/opt/llvm@17/bin/llvm-config'),
    speq_rev_plugin=None, timeout_sec=300,
))
```

The cached Python environment's metadata identifies egglog 13.2.0, lark 1.3.1, and z3-solver 4.15.3.0. LLVM17 config, the pinned LLEQ REV/MemorySSA source files, original artifact files, and current replay binary exist. No retained REV plugin was found; `speq_rev_plugin=None` builds the small plugin inside the guarded native parent. These prerequisites were inspected, not executed, in this slice. A second multi-region canary is `speq-polybench_gemm`; prior diagnostics predict a genuine unmatched application kernel, which must stay blocked, not be replaced by `gemm_ref`.

Equivalent public invocation (also proposed, not executed):

```bash
.venv/bin/python scripts/suite_capture_dialegg_speq.py --complete --family speq \
  --case speq-spmv_npb --output benchmarks/local/complete-reproduction-canaries/speq-spmv-npb-01 \
  --egglog /Users/saul/p/egglog-encoding/target/release/egglog-experimental \
  --speq-artifact /Users/saul/p/egglog-encoding/benchmarks/local/sources/speq/artifact \
  --speq-lleq /Users/saul/p/egglog-encoding/benchmarks/local/sources/speq/lleq \
  --speq-python /Users/saul/.cache/uv/archive-v0/0-NSo2ksd2fjStFc/bin/python \
  --llvm17-config /opt/homebrew/opt/llvm@17/bin/llvm-config --timeout-sec 300
```

For DialEgg, set `family='dialegg'`, `case=['dialegg-runtime-vector_norm-eqsat']`, `dialegg_source=root/'benchmarks/local/sources/dialegg'`, `llvm18_prefix=Path('/opt/homebrew/opt/llvm@18')`, and `native_egglog=<built historical cost-action executable>`. Keep `egglog` as the current standalone replay binary. LLVM18 and source paths exist; no historical cost-action executable was found. The backend must be prepared from artifact-pinned `saulshanabrook/egg-smol` commit `b6e1c96ed7335366e90056ea0a24ef425dfbb8fb` before this canary. Never substitute current Egglog for that native slot without documenting a separate semantics/compatibility lane. The public flags are `--dialegg-source`, `--llvm18-prefix`, and `--native-egglog`.

## Validation actually run

- Focused Python tests: **55 passed**, `tests/test_suite_capture_dialegg_speq.py tests/test_dialegg_speq_complete.py`.
- Ruff check/format on the three changed/new Python modules and new test module: passed.
- Mypy on those four modules: passed.
- Public `--family dialegg --list-cases`: returned all 24 required parent IDs without builds/downloads.
- Applied `patch_dialegg_pass` in memory to the actual pinned C++ source and checked all configuration paths: matched its expected source fragments; no source written or compilation performed.

Next gates are root review/integration, the real SpEQ canaries, historical DialEgg backend preparation plus MLIR canary, and instrumented/uninstrumented compile-only output comparison. Exact API/output contracts and frontend compatibility can still fail at those gates. Then complete source repairs and missing-input recovery remain required before the full population run; this implementation and synthetic tests do not complete the reproduction goal. Full `make check` is root-coordinated and has not run in this slice.
