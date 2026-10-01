# Original MISAAL x86 generator request preparation

Status: all **32 original x86 generators compiled and linked successfully** in
`benchmarks/local/reproduction/prerequisites/misaal-44ff/x86-generators-attempt-0001`.
The 66 serial guarded compiler/link steps completed without a resource stop.
This preparation ran no optimizer parent or target program; complete source
optimization and standalone validation remain separate gates.

## Reusable prepared environment

The current verified seed, after the SIMD pass-mode repair, is:

```
benchmarks/local/reproduction/prerequisites/misaal-44ff/x86-simd-mode-attempt-0001/requests/misaal-x86-blur3x3.json
```

It records MISAAL `44ff893445d664cd87f52b08a138260ed2015ba8`, Hydride
`beb825327fc946d65032e96f7cde9acf3d24c13e`, and Egglog
`6b6938bc0088163f61240482cd34a1579715b804`, with the real native LLVM12,
Python/Rose environment and repaired Halide/legalizer dependencies. The new
preparer verifies the seed's source/backend/Python/verifier/generator hashes,
plus the Halide and legalizer hashes, before compiling anything. This reuse
requires that the preparation inputs still exist; it does not acquire missing
prerequisites or infer success from a historical path.

`prepare_misaal_cases(output, template_request, case_ids=None,
compiler=Path('/usr/bin/clang++'), timeout_sec=120)` is callable in process under
the coordinator's existing heavy slot. The CLI alone takes the shared lock:

```sh
.venv/bin/python -m scripts.reproduction_prepare_misaal_cases \
  --template-request benchmarks/local/reproduction/prerequisites/misaal-44ff/x86-simd-mode-attempt-0001/requests/misaal-x86-blur3x3.json \
  --output benchmarks/local/reproduction/prerequisites/misaal-44ff/x86-generators-attempt-0001
```

The output must be a new directory. For a bounded first preparation use
`--case misaal-x86-gaussian3x3`; repeat `--case` for an explicit subset. This
command shape was used for the recorded full 32-generator preparation with the
earlier environment seed. The SIMD continuation subsequently rebound all 32
requests to the corrected legalizer. Use a fresh output directory for another
attempt; the earlier seed no longer matches the repaired selector bytes.

## Coverage and exact build recipe

The current inventory contains **32 x86 generator entries: 31 required and one
artifact extra, tensor_shr**. They match the pinned source's active Makefile
list. The preparer derives them from `expected_cases` and preserves catalog ID,
source directory, target configuration, paper aliases and scope. It does not
edit the catalog. The Makefile bytes are pinned to SHA-256
`6a6e3d1e5fd77e462ca1541e5fa07bb8494b0764a9df8cc4d689391468d8855e`.

For each entry it compiles the exact `$name/src/${name}_generator.cpp` named by
the [original Makefile](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/benchmarks/x86/halide/Makefile)
and verifies its matching `HALIDE_REGISTER_GENERATOR`. Alternative suffixed
source files are not substituted. It preserves C++17, `-fno-rtti -O3 -g`, and
`-DLOG2VLEN=7`. `GenGen.cpp` and `hannk/common_halide.cpp` are compiled once with
the same flags; each generator links these objects and the exact prepared
Halide dylib. Native Apple Clang and the prepared header/tool/dylib locations
are the same build-location adaptation used for the earlier native blur3x3
preparation. This is not a claim to have run the Linux Makefile verbatim.

Each translation unit gets its own compiler-produced dependency file. Requests
bind those included local headers, original generator source, compiler, shared
library/legalizer, and source environment. Shared support failures stop all
cases; ordinary per-generator compiler failures are retained while subsequent
cases can be prepared. Resource-limit or launch refusals stop further jobs.
Every actual compiler/link process uses `Preparation.step`: required memory
guard, 5 GiB process-group cap, warning pressure allowed diagnostically, 10 GiB
disk floor, and a 120-second default limit per step. There is no parallel build.

All emitted generation commands preserve the Makefile's original `-t 0`,
`-g/-f name`, `static_library,stmt,h,llvm_assembly,assembly` outputs and
`target=host-x86-64-no_bounds_query-no_asserts`. Graph settings remain depth2,
synthesis width16, enabled MISAAL/Hydride, `empty_hash`, and disabled frontend
patterns. No GeneratorParam overrides are invented. In particular the
[batched matmul source](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/benchmarks/x86/halide/batched_matmul_256_32bit/src/batched_matmul_256_32bit_generator.cpp)
uses runtime batch variable `b` over 3D buffers and default matrix size256; the
paper aliases `matmul[b=1]`, `matmul[b=2]`, `matmul[b=4]` stay three aliases of
one original generator request. Runtime sizes do not become new graph flags.

The recipe does not include the Makefile's later runtime-object generation,
AVX benchmark-harness compilation or 1920x1080 execution. Separate ARM and HVX
preparation recipes now generate their original target selectors and host
generators. Their actual native builds and complete-parent runs remain pending;
existing x86 success does not establish either target. See
[HVX recovery](misaal-hvx-preparation.md) for the source-defined lowering and
explicit absent-wrapper contract.

## Immutable results and coordinator handoff

- `identity.json`: seed, source Makefile, compiler, inventory, shared inputs and
  implementation hashes.
- `steps/`: numbered exact compiler commands, raw logs, exit/status/resource
  evidence owned by the shared guard.
- `case-<id>.json` and `preparation.json.cases[<id>]`: **every selected ID**, with
  status, reason, compiler result-receipt paths, and request path or null.
- `requests/<id>.json`: emitted only after real nonempty executable and dependency
  checks and the same `verified_request` used by capture. Candidate requests are
  retained separately if verification fails.
- `settings.json`: the `misaal.paths.requests` directory, emitted when at least
  one case is prepared. Overall status is success only if every selected case
  is prepared; partial failures remain visible in the indexed summary.

A prepared generator is not a completed source optimizer, valid LLVM result,
complete .egg capture, successful ordinary replay, or strict proof validation.

## Why the pattern caches stay fresh

The prepared `lib/patterns/x86.py` preserves the original branch behavior with
only the optional cache-directory path patch. Its
[upstream source](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/lib/patterns/x86.py)
implements these states:

1. **Cold:** load ten ordered target-pattern JSON files, construct and deduplicate
   patterns, use the raw list, then write `x86.pickle`.
2. **Raw cache present:** deserialize the raw list, run `PatternAbstractor`, write
   `x86_abstract.pickle`. Although the exported variable is not explicitly
   reassigned to the abstracted list here, the abstractor can mutate existing
   objects through `pat_j.swap()` while forming buckets. This import cannot be
   assumed equivalent to the cold branch.
3. **Abstract cache present:** load the abstracted list directly.

The mutation is visible in
[`PatternUtils.py`, `PatternAbstractor.abstract_patterns`](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/lib/patterns/PatternUtils.py).
Therefore an immutable byte hash plus source/settings hashes is insufficient to
justify pre-seeding a new parent: it changes the branch, work and potentially
rules presented to the optimizer. No cache reuse is implemented or recommended
as an equivalent optimization without a separate source-behavior argument.

Within one complete parent, `run_frontend` creates one fresh attempt cache and
exports its directory to every Python child. The
[generated Python import](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/frontends/halide/src/misaal.cpp)
imports `patterns.x86` in each new child process. If that parent invokes multiple
children, successive successful imports naturally observe cold → raw → abstract
states. A single Python process instead keeps its normal module-import cache.
The current graph setting disables the separate `patterns.Halide` import.
The original Makefile does not create or remove these pickle files directly;
its `clean` removes benchmark binaries and temporary generated files, not
`lib/patterns/*.pickle`. Thus unmodified upstream repeated parents can also
observe persistent warm state. The current adapter deliberately starts each
parent cold and retains the within-parent progression.

A future cache proposal must first specify which state each child is meant to
observe, bind the full pattern-generation inputs and Python class/dependency
identities, and compare actual per-child emitted rules and complete results
against cold behavior. Copying raw or abstract pickles blindly is not that
validation. No pickle was deserialized during this audit.

## Validation of this implementation

Eleven focused tests pass, with all native compiler calls replaced by controlled
fixtures. They cover exact source/default/alias preservation; per-translation-unit
header dependency binding; missing executable outputs; compiler-failure evidence;
resource-stop and shared-support accounting; explicit selection; identity drift;
immutable attempts; and no nested API lock. Ruff, Mypy and CLI help also pass.
The separate native receipt establishes that all 32 original generators compile;
these tests and compilation do not establish successful source optimization.

The coordinator can also acquire and build the original Egglog backend from
its pinned archive and locked dependencies, using native Rust 1.91.0. This closes
the previous dependency on a pre-existing local binary. The complete fresh
recipe is implemented and unit-tested; its new backend build has not yet run.
The existing successful preparation still records its actual original backend
identity.
