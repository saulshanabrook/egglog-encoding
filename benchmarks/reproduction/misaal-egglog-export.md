# MISAAL Egglog-only export

The `egglog-only-v1` request contract captures the complete original Egglog work
while skipping downstream LLVM generation. Captures identify their source as
`misaal-egglog-export` and record `native_codegen: not_requested`. They do not
claim successful native compilation or manufacture LLVM feedback.

The source frontend must be prepared by `scripts.reproduction_misaal_export`.
Its `verify_export_request(request)` binds the exact frontend source changes,
frontend library and generator linked to that library. The adapter requires
`egglog_export: egglog-only-v1`, `export_preparation` receipts and an empty
`expected_generator_outputs` list. Old acquisition-tail, terminal-empty and HVX
link policies cannot be combined with this request. Selector, wrapper and LLVM
verifier artifacts are not prerequisites for export.

The adapter supplies `MISAAL_EXPORT_MODE=egglog-only-v1` and the fresh absolute
`MISAAL_EXPORT_EVENTS` path. Those fields cannot be injected through the request
or inherited environment. The normal guarded capture entrypoint remains:

```sh
python -m scripts.misaal_reproduction capture --request REQUEST.json --output FRESH_DIRECTORY
```

It retains the existing resource and registered Racket-process-group guards.
The public reproduction pipeline owns source preparation and ordinary replay.
This command alone does not certify standalone replay success.

## Complete source enumeration

The pinned source branch emits `misaal-export-v1` JSONL with globally sequential
row, module, function and child identities. Modules begin before their
submodules; submodules finish before source-order functions. Functions enclose
their generated children. The adapter checks matching begin/end records,
declared module/function counts, child return codes and exact child receipts.
Each root needs its final `export_complete` record with cumulative counts.
Multiple roots and zero-function modules, including shared runtime modules,
remain explicit. Exit zero without the complete ledger does not suffice.

The source branch bypasses native output generation. An existing
`HALIDE_COMPILE_LLVM` variable retains its original presence semantics, including
value `0`: if no optimizer work is reached, the result is a source helper with
no admitted workload. The adapter does not fabricate source synthesis.

## Original Python compilation

The adapter recognizes the exact target-specific generated Python structure and
literal input specifications. It retains imports, patterns, source expressions,
rules, costs, schedules and every original recursive or swizzle call. The
execution copy removes only the original `run_llvm_legalizer()` statement; the
original generated file remains unchanged. A legalizer call through another
path fails before a native tool starts.

The original `compile_hydride` must return normally. Its original named-result
serialization is observed, and every input name must complete in source order.
The selected-expression file must equal the complete original joined results;
it is copied immediately before another child can overwrite it. Failed backend
calls remain failures even if the original parallel compiler swallows an
exception. Every captured optimizer invocation, including repeated identical
inputs, is materialized separately with its original extracts and actual
selected-term checks. Ordinary replay remains required for admission.

## Empty source children

An empty child before any real compilation executes the original imports and
exact empty-tests exit. Once a real child completes, a terminal empty suffix can
move that same exit guard before pattern imports. This binds the preceding real
child's successful compilation receipt and retained selected-expression file,
plus every allowed cache file and its bytes. ARM, x86 and HVX retain their own
cache names; frontend Halide and target HVX caches have independent states.

The boundary is durable before the first deferred child executes. Any later
nonempty child fails, including after an ignored empty-child failure. The whole
suffix must exit at the exact source guard without optimizer/helper work or
cache/selection changes. Empty children are source helpers, never workloads.
This export boundary requires no LLVM output and does not reuse the historical
ARM native-feedback policy.

Historical native captures and failures keep their original meaning. An old
successful backend prefix cannot establish the new complete export boundary.
