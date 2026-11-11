# Prepared parameter ABI gate — no native execution yet

These four programs come from the retained actual 44ff `PatternAbstractor` method code objects, compiled from the complete original module. Only launch was intercepted. The original `HYDRIDE_HEADER` and `emit_racket_cond` are used verbatim; no import of source populations occurred. The two repaired programs exactly match programs independently generated from the retained complete c098 source. All 21 original class methods passed the adapter's checks; only two were replaced and all original objects were restored.

`manifest.json` pins source files, helper implementation, preparation code, program bytes and the complete preparation receipt. This is diagnostic evidence only: `admitted:false`, `proof_admitted:false`. Checkout bytes were never changed. The fixed preparation script already ran and refuses to overwrite its manifest.

Programs:

- `ordinary-depth2.rkt`: actual `generate_param_expr`, source `[1,2,3]`, target `[2,4,6]`, additional destination `[5,7,11]`, exclusion `[1]`, depth 2. Require exit 0 and fresh nonempty `ordinary-depth2.temp`.
- `general-depth1.rkt`: actual `generate_param_expr_general` with the same maps/exclusion, depth 1. Require exit 0 and fresh nonempty `general-depth1.temp`. No available input directly aliases the output; arithmetic must remain possible under the paper ABI.
- Corresponding `*-unadapted.rkt`: exact original five-argument emitted programs. Require nonzero exit with the specific `synthesize-param-expression` arity error (expected 4, given 5). Missing packages/solver, generic failure, timeout or a different error do not pass this control.

Root execution recipe:

1. Wait for the shared heavy slot. Verify every manifest source/program pin; verify the integrated root helper byte hash equals the prepared mirror helper hash. Also pin completed Racket runtime executable, package receipt, exact environment and actual resolved Hydride/MISAAL/Rosette module identities; the runtime package's `param_abstract.rkt` must match the manifest hash. Do not use partially prepared packages.
2. Acquire the existing shared `exclusive_job` lock. Run each program as `[absolute_racket, absolute_program]` through existing `run_bounded_command`, using a separate fresh empty directory per run and the completed runtime environment. Use timeout <=60 s, aggregate process-group RSS <=5 GiB, >=2 GiB host reserve, >=10 GiB disk, and existing allowed-warning policy. The direct Racket process remains in the guarded root group; do not invoke the source detached Python launcher for this script gate.
3. Save exact argv, environment identity, command receipt, stdout/stderr, return code, memory observation and result-file bytes/hashes. Check the explicit expectations above; stop on a resource/containment failure. Do not rewrite these prepared receipts or any prior evidence.
4. Keep source-canary readiness separate: this gate only establishes executable emitted-script behavior under the restored paper ABI. A fresh complete guarded source parent at the final request identity is still required.

No additional runtime framework is supplied. The root already owns guarded execution and request integration.
