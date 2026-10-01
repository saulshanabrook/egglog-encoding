# MISAAL Egglog-only frontend

`egglog_export: "egglog-only-v1"` enumerates the original source graphs and
retains all original Egglog recursion and swizzle work. It returns before
native LLVM body emission, legalization, optimization, linking, or output
serialization. It does not claim native LLVM success and creates no placeholder
LLVM files. Ordinary standalone replay remains required for every captured
optimizer invocation; helper children and zero-work traversals are not workloads.

This source component supports the pinned 44ff frontend and the existing
single-target x86, ARM, and Hexagon generator commands. It preserves virtual
`compile_func` dispatch, `run_with_large_stack`, source function order, and
child-first traversal of all nested modules, including zero-function runtime
modules. HVX retains its original preprocessing before synthesis. The
presence-based `HALIDE_COMPILE_LLVM` branch retains its zero-synthesis behavior.
The original Python generated script remains intact; the capture adapter owns
its separately verified cut after `compile_hydride` returns normally.

## Prepare from retained prerequisites

These public commands create fresh immutable destinations from an explicitly
verified retained graph/runtime template. They never rebuild Egglog, Python/Racket, selectors,
or wrappers, and never execute a generator. A missing retained template is a
blocker; this component does not silently acquire native legalization tools.
The coordinator owns source/runtime acquisition and request selection.

From the repository root, build the shared export frontend once:

```sh
.venv/bin/python -B -m scripts.reproduction_misaal_export frontend \
  --template benchmarks/local/reproduction/diagnostics/misaal-arm-terminal-policy-0001/requests/misaal-arm-blur5x5.json \
  --output benchmarks/local/reproduction/prerequisites/misaal-export-frontend-0001
```

Then compile the small original generator/support sources and link that library:

```sh
.venv/bin/python -B -m scripts.reproduction_misaal_export generator \
  --template benchmarks/local/reproduction/diagnostics/misaal-arm-terminal-policy-0001/requests/misaal-arm-blur5x5.json \
  --frontend benchmarks/local/reproduction/prerequisites/misaal-export-frontend-0001/frontend.json \
  --output benchmarks/local/reproduction/prerequisites/misaal-export-arm-blur5x5-0001
```

`verified_export_template` checks source, backend, Python, and Racket identities.
It does not require the old generator, library, LLVM assembler, selector, or
wrapper files, and replaces obsolete build identities with graph/runtime inputs.

The second command emits `capture-request.json`. It removes the earlier native
acquisition-tail, terminal-empty, and HVX link policies: the export adapter owns
the new completion boundary. It retains unused constructor path strings without
requiring the corresponding selector, wrapper, or LLVM assembler files.

Both commands acquire `stages/.heavy-job.lock` and use the existing guarded
serial preparation steps: 5 GiB process ceiling, host reserve, 10 GiB disk floor,
and two frontend build jobs (one aggregate process guard). Their APIs use the caller's job slot. Default timeouts are
1800 seconds for the frontend and 120 seconds per generator step. The retained
source measured 662 MiB including excluded Git metadata; the prior Halide build
measured 227 MiB. Allow roughly 1 GiB for the copied source plus frontend build,
then additional small generator objects and logs. This is a planning estimate,
not an upper bound; the existing disk guard remains authoritative.

`frontend.json` binds source inputs, exact patch hashes, implementation and guard
sources, build tools, command/result evidence, public header, and actual library.
`generator.json` binds original input dependencies, actual objects, successful
compile/link evidence, the linked library, binary, and resulting request.
`verify_export_request(request)` verifies both through `export_preparation`
(`frontend`, `frontend_sha256`, `generator`, `generator_sha256`). Existing backend
receipts and their preparer hashes are unchanged. New source/library/generator
and request identities distinguish export acquisition from old native attempts.

## Parent completion protocol

Only a verified request enables `MISAAL_EXPORT_MODE=egglog-only-v1`. The adapter
sets an absolute fresh `MISAAL_EXPORT_EVENTS` path, normally
`<attempt>/parent-export.jsonl`. Ambient activation is not authorization.

Each JSONL row has `schema: "misaal-export-v1"`, a global zero-based `seq`, and
one `event`. IDs are global, zero-based integers. Strings use lowercase UTF-8
byte hex to avoid ambiguous escaping. C++17 inline state is shared across all
patched translation units in the same process.

| Event | Additional fields |
| --- | --- |
| `module_begin` | `module_id`, `parent_module_id` (null for root), `name_hex`, `target_hex`, `function_count`, `submodule_count` |
| `function_begin` | `module_id`, `function_id`, `name_hex` |
| `child_begin` | `module_id`, `function_id`, `child_id`, `script_hex` |
| `child_end` | `module_id`, `function_id`, `child_id`, `returncode: 0` |
| `function_end` | `module_id`, `function_id` |
| `module_end` | `module_id` |
| `export_complete` | `root_module_id`, cumulative `module_count`, `function_count`, `child_count` |

Order is module begin, each original submodule recursively, each original
function, module end. A child's begin/end encloses the original `system` call;
nonzero status throws even when release assertions are disabled. Completion is
emitted only after each top-level module returns normally. Multiple roots are
permitted, with cumulative counters and uninterrupted sequence numbers.

The adapter must verify exhaustive nesting, counts, unique IDs, every reached
child receipt, and parent exit zero. A source-empty child remains a helper with
its exact permitted source exit; a real child needs normal source compilation
completion and successful backend calls. No unfinished recursion, failed parallel
call, missing child, or missing marker is converted into success.

Before admission, root must compile this frontend and compare existing completed
canaries' full source-test multisets and raw Egglog session multisets (including
multiplicities). Their ordinals can differ because original compilation uses a
set and thread pool. Include ARM real-plus-empty suffix, x86, HVX, and nested
module coverage. This component's mocked/static checks establish no native run
or successful canary by themselves.
