# MISAAL parameter ABI restoration

Implement only the opt-in `parameter_abi="c098-four-argument-v1"` adaptation in the existing patterns helper, its focused tests, and the MISAAL reproduction document. This restores the executable c098 paper ABI while retaining newer 44ff validation/simplification; it does not claim equivalence to undocumented register-only behavior.

Pin original checkout bytes, request pins, and loaded PatternAbstractor methods; compile an in-memory two-site source repair without executing module imports; install only the restored emitter/general method and restore them on every exit. Leave checkout bytes unchanged. Root owns capture/request integration.

Checks: genuine ordinary depth-2 and general depth-1 generation against verbatim paper methods, strict pin/code/default rejection, exclusions, short-circuits, exception restoration, newer behavior retention, Ruff, mypy, and existing focused pattern tests. Optionally prepare retained actual-source emitted scripts for root execution. No native jobs/builds. Stop after sealed three-file patch and handoff.
