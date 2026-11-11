# Durable ABI gate recipe

Write only new gate runner/test, small exact captured/oracle fixtures with provenance, and a narrow MISAAL documentation addition. Build all four programs from actual pinned full-module method code, compare adapted programs byte-for-byte to tracked c098-generated oracles, preserve the exact captured ki4k2nlc.rkt fixture, and run five sequential guarded diagnostics only when called by root. Default standalone execution owns the shared heavy lock; `lock_owned=True` is reserved for the coordinator. Emit the existing runtime sealer contracts unchanged. No acquisitions, builds, source edits or native runs in this worker.

Checks: focused mocked process/pin/failure/lock tests, real-source offline reconstruction, Ruff/mypy, independent review when available. Stop at sealed handoff; root integrates prepare_family and executes native gates.
