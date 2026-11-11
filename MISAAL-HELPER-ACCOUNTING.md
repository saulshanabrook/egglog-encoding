# MISAAL direct helper accounting and native feedback gate

Ready for review/integration; no native programs, generators or builds were run for this patch. Only the two files listed below are owned changes. `scripts/reproduction_misaal_legalizer.py` and its tests were copied unchanged from live root solely as test dependencies; do not overwrite them from this mirror.

## Scope and retained behavior

The pinned MISAAL source directly invokes Egglog in module-level `patterns.PatternUtils.is_pattern_valid_egg` (lines 1167, 1226 and cleanup 1230) and `compiler.EggLogCompiler.is_pattern_valid_egg` (482, 521). These do not pass through the optimizer class's `execute_egglog_file`. Source evidence is the retained `benchmarks/local/reproduction/prerequisites/misaal-44ff/attempt-20260925T051740Z-ef4010cc/sources/MISAAL/lib/` tree.

The observer verifies both module source hashes, then temporarily replaces only their `sb` aliases. Imported references to those functions still use the observed globals. Standard `subprocess` and the existing optimizer hook remain separate, preventing recursive or duplicate capture. Each accepted call must have the exact recognized source caller, two literal shell arguments naming its local compiler/backend and an `.egg` input, and only the source's known subprocess options. Unknown callers, shell syntax, subprocess operations or recursive installation fail completion, even if source code catches the immediate exception.

Actual pinned backend execution retains raw input, full stdout/stderr and their SHA-256 values, actual returncode, source command/backend, and the executed command before an observed source deletion can occur. A completed backend returning nonzero remains `accepted: false`; the real CompletedProcess returncode reaches the original source Boolean check. Helper records have `admitted_as_workload: false`. Parent `helper_accounting` reports accepted/rejected counts separately; optimizer invocations, source queries and workload counts are unchanged. A timeout or other execution exception retains partial streams and marks observation failed. The two source modules' original aliases are restored on every exit. Inherited helper output is forwarded after the real subprocess completes; log interleaving/timing is not preserved as a performance measurement.

The canonical stdlib-only `audit_simd_lowering` now gates each requested legalizer function before the produced LLVM is returned to Halide. It checks function presence, direct undef/poison return and remaining `llvm.hydride` calls; the complete audit JSON is retained. Generated LLVM is copied to durable legalization evidence before the gate, including failures. Final generator LLVM with no selected function set still receives ordinary llvm-as verification. This gate catches the observed mode-selection defect; it is not general LLVM semantic equivalence validation.

Old recovered blur3x3 output is not made correct by this patch. Its ordinary Egglog replay passed, but sibling's source audit found undefined native results. The pass-mode repair, dependency rebuild and fresh full native reproduction are still required. The native observer AST changes here also deliberately prevent claiming the old pre-observer capture was produced by this implementation. Its completed historical recovery/evidence is untouched.

## Validation

- `.venv/bin/python -m pytest -q tests/test_misaal_reproduction.py tests/test_reproduction_misaal_legalizer.py`: **48 passed in 29.59s**, fake tools/protocol fixtures only.
- Ruff format/check and focused mypy: passed for both owned files.
- Independent read-only helper review: no concrete blocker found.
- New coverage includes both helper entrypoints, accepted and rejected outputs, exact raw/hash preservation after deletion, inherited/suppressed streams, module restoration, unexpected shell/caller/operations/recursive observation, interruption receipts, helper/optimizer accounting separation, and failed SIMD feedback never consumed by the fake native parent.

## Integration and next guarded native gate

Apply `MISAAL-HELPER-ACCOUNTING.patch` or copy only the two owned files. Live versions still matched the saved baselines when this handoff was written. Root already pins `lib/patterns/PatternUtils.py` in new requests and binds the canonical audit module in coordinator identities.

After the recorded SIMD-mode repair/rebuild produces a **fresh settings file and request with new legalizer/source hashes**, the proposed coordinator command is:

```bash
.venv/bin/python -m scripts.suite_reproduction --family misaal --case misaal-x86-blur3x3 --stage all --settings /absolute/path/to/new-simd-mode-settings.json
```

The settings path is intentionally a prerequisite placeholder; no repaired source build is claimed here. Use the coordinator's existing exclusive heavy-job lock and adapter process guard; do not wrap it in a second process-session guard. Require source completion, successful per-legalization audit, separate helper accounting, and subsequent ordinary contracts. A cold single-child run may legitimately report zero helper calls; exercise a naturally reached warm/later child before claiming real helper-path coverage. Never admit helpers as extra paper workloads or add queries to force them.

## Independent source review

Read-only review of the new pinned backend build and MISAAL coordinator preparation found no concrete blocker: archive/lock digests, pinned Rust version, serial guarded build, and produced binary identity are recorded; prepared subsets have case-specific blockers; safety stop propagation remains explicit. Read-only Churchroad borrow-continuation review likewise found no concrete blocker. These are source-review findings, not runtime validation.

## File identities

| Owned file | Baseline SHA-256 | Proposed SHA-256 |
| --- | --- | --- |
| `scripts/misaal_reproduction.py` | `f0811821716234ff343fc9fe115b15ae283f81153090cbdbeb9b1f9ca8aae0cd` | `1e619534391002950f082e866cb75237009434e903409c61721bbc9f168ace5c` |
| `tests/test_misaal_reproduction.py` | `e27ed837bcaf33ac3562f7f48ef49ba3e2bf033e32c3566f1753861a70eca2c5` | `d05cdd108b3da8f23dfdf5665dec41afde9543c7ab073e80ce096687031a5f62` |
