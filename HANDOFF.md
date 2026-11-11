# Durable fresh MISAAL ABI gate

Reviewed worker patch: `review/abi-gate.patch` SHA-256 `2373bc38acd7c7fcd549ce9bcf71cfa91650ab2296491a980b0aadd274ee0622`. Root has already integrated this patch. Exact original baselines, new paths and worker result identities are in `review/handoff.json`; do not apply it twice.

The public worker API is `run_gates(runtime_path, checkout, output, *, lock_owned=False)`, returning `abi_gate`/`captured_gate` references accepted by `seal_runtime`. Standalone owns the shared lock; the coordinator passes `lock_owned=True`. `CAPTURED_FIXTURE` and `CAPTURED_SHA256` are exported for preparation. `prepare_programs(checkout, output)` is offline-only. Terminal `output/result.json` retains `active_gate` and the exact last returned process receipt for parent safety-stop scanning.

Validation: 66 focused tests passed in the isolated mirror; 18 gate tests passed again after safety-summary propagation. Ruff/check+format and mypy passed. Final worker-identity actual-source offline reconstruction verified 21 class methods and reproduced all four earlier native-passed program hashes. Independent read-only review found no concrete blocker. Live-root apply check passed before integration. No native job, root source edit or commit was performed by this worker.

Root-owned integration corrections (do not make competing mirror edits):

- Change the test import to `tests.test_reproduction_misaal_patterns`, matching root's test package. The mirror omitted tests/__init__.py, so its successful local collection did not expose this mismatch.
- Add optional `preparer_path` to `_runtime`/`run_gates`, default current source, and explicitly record the archived executed preparer hash without executing it. This extends the original fresh-only contract to the approved historical archive, matching `seal_runtime`.
- Preserve the failed preflight0001; root reports no native job was launched. Root owns subsequent tests/native gates.

The captured ki4k2nlc fixture is exact diagnostic evidence, not a benchmark or complete reproduction success. Only its separate executed copy loses the one unsupported argument. The recipe does not itself seal/publish a runtime or admit workloads/proofs. Root owns final integration identities and native execution.
