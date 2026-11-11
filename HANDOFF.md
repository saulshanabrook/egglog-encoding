# MISAAL parameter ABI restoration

Sealed three-file patch: `review/parameter-abi.patch`. SHA-256: `b9d3728d3a4dc6255b3411e601716493968e4aebb5759c1cd2f8af0774953e84`. Exact root baselines and result hashes are in `review/handoff.json`; all root baselines remained intact at sealing.

The opt-in `parameter_abi="c098-four-argument-v1"` contract restores precisely the original paper emitter and general-call ABI, leaving other 44ff behavior and checkout bytes unchanged. It verifies request/file pins plus every loaded class method's code, globals and defaults, compiles the narrow virtual source change, and restores original method objects on normal, exceptional and interrupted exit. No ignored reg_only flag remains.

48 focused tests, Ruff check/format, and mypy pass. Independent read-only review by prove_extract_design_review found no concrete blocker and independently compared both adapted methods against local Git c098. Offline actual-source reconstruction passed all 21 method pins and produced exactly the c098 ordinary-depth2 and general-depth1 scripts.

`diagnostics/misaal-parameter-abi-gate-0001/` contains those genuine scripts, unadapted five-argument arity controls, immutable preparation manifest, fixed preparation code and root-only guarded run recipe. Nothing native was run. Root owns integration into `misaal_reproduction.py`, acquisition/request identity and completed package readiness, then actual script gates and a fresh source canary.

This is a mixed-revision restoration of executable paper behavior. Depth1 remains arithmetic-capable; undocumented register-only intent, universal semantic correctness and native/proof admission are not established. Source/header bytes, guards, caches, newer validation and simplification were not changed.
