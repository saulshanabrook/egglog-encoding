# Retained MISAAL x86 SIMD-mode continuation

New files only: `scripts/reproduction_continue_misaal_simd.py`, `tests/test_reproduction_continue_misaal_simd.py`. No existing module is edited by this patch. Imported preparer/audit files in this mirror were refreshed from live root for tests and are not integration files.

The 32 archived x86 requests currently match their recorded source hashes. Their old selector source is still the exact previously repaired wide-literal version (`37063c9e74625eb3568c1befb3373c1fc792cc3f6e5e9213b64b624cfd0823a5`), and their plugin is still the old `2546d4239f78028ecfbd3a4c63916e83910b577de57f7c632ed108279824c48b` library. Thus no already-repaired source conflict was found. The continuation refuses a changed/already-mode-repaired source instead of silently rebasing archived provenance.

The function verifies all 32 request hashes, their source/generator/backend/Python/LLVM/library identities, compiler dependencies and retained successful builds. It records the exact previous CMake target and only allows the existing suffix/wide-literal changes in pinned Hydride. PatternUtils is newly pinned against the original MISAAL Git blob before its hash is added to requests. Original selector, plugin, Halide library and every request are copied into fresh `before/` evidence. Only the canonical x86 `L->bitsimd = false;` replacement is applied; the existing x86 plugin target is rebuilt serially. Halide and generators are not rebuilt or run. A fresh plugin copy under `native/` becomes the new requests' legalizer and LEGALIZERS_DIR.

The diagnostic copies the exact sealed linked LLVM, required functions, old output and native opt command from the retained 1b8cc stage. It requires the known old undefined-result failure, applies the actual rebuilt pass with the original optimization flags, runs the canonical selected-function audit, then llvm-as. Every subprocess uses Preparation's 5 GiB process-group ceiling, 10 GiB disk reserve and required guard; the CLI holds the shared heavy-job lock. All original receipts/requests stay untouched. A failed attempt retains evidence and publishes no settings. The acquired selector and build plugin intentionally remain changed if rebuilding fails; a repeat requires reviewing the saved failure, not blind automatic replay or rollback.

Success produces 32 fresh requests, their hashes, separate settings, old/new source and library hashes, exact diff, immutable step receipts, diagnostic audit and evidence manifest. This means native prerequisites are ready. It is **not** a complete parent compiler run or corpus admission. The earlier undefined native outputs remain quarantined.

Validation: 10 fake-process protocol tests pass; Ruff and focused mypy pass. No native jobs, actual compilation or lowering were executed by this agent.

## Proposed guarded command (not executed)

Run from `/Users/saul/p/egglog-encoding`, after integration and the heavy slot is free:

```bash
.venv/bin/python -m scripts.reproduction_continue_misaal_simd \
  --generators benchmarks/local/reproduction/prerequisites/misaal-44ff/x86-generators-attempt-0001 \
  --diagnostic-stage benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/1b8cc1e5cd28697cf8c6f79535959b73feda97457d61e5c8306a6af8bc365cd2/attempt-0001/stage.json \
  --output benchmarks/local/reproduction/prerequisites/misaal-44ff/x86-simd-mode-attempt-0001 \
  --timeout-sec 600
```

Only after its settings are published and diagnostic succeeds:

```bash
.venv/bin/python -m scripts.suite_reproduction --family misaal --case misaal-x86-blur3x3 --stage all \
  --settings benchmarks/local/reproduction/prerequisites/misaal-44ff/x86-simd-mode-attempt-0001/settings.json
```

Do not add an outer subprocess guard around these CLI entrypoints; they already acquire the lock/use monitored native commands. No settings file in the existing preparation or main configuration is overwritten.

## New file hashes

- `scripts/reproduction_continue_misaal_simd.py`: `90519aa8b39f33feab5837007ef6ce1ea0e84112285858f0cd77bf087d440138`
- `tests/test_reproduction_continue_misaal_simd.py`: `e7ac5677f4307671e5b79cb019f2535ef4f76369894679b83446bb2735ffd9a3`
