# HardBoiled native preparation handoff

Status: **native prerequisite preparation succeeded; complete source canaries remain pending.** The successful guarded attempt is
`benchmarks/local/reproduction/stages/hardboiled-prerequisites/prepare/34d7fb28e7be3b9e434103f3d409367704a0e678955fd6b8a40b8b00e9da51fb/attempt-0001`.
The original sidecar built in 78.9 seconds and full Halide in 250.6 seconds.
These are build diagnostics, not performance observations or complete workloads.

## Entry point after the coordinator grants the heavy slot

From the integrated repository root:

```sh
.venv/bin/python -m scripts.reproduction_prepare_hardboiled
```

The command takes the shared `benchmarks/local/reproduction/stages/.heavy-job.lock`
and creates an exclusive attempt under
`benchmarks/local/reproduction/prerequisites/hardboiled-b99cf0c/`. It reuses the
immutable receipt/guard implementation in `reproduction_prepare_misaal.py`.
Every subprocess has a required native memory guard, diagnostic warning pressure
allowance, 5 GiB process-group RSS cap, 10 GiB free-disk floor, and a bounded wall
limit. Builds use one job. The sidecar and Halide each have an 1800-second ceiling;
acquisition/configuration steps have 600 seconds. Neither successful preparation
nor those ceilings promise that the source will compile.

The preparer acquires the complete artifact repository at
`b99cf0c6400e954a278f697bf3a0596ac3fa4f25`, sidecar at
`aa2beffdca1043e0468a03be8c316f934abdd7d9`, and verifies its exact Egglog gitlink
`03859dba7c602f07158b87a63b25c143388fbbac`. It rewrites the sidecar submodule's SSH
transport to HTTPS for that one Git command. It does not substitute MISAAL's
Egglog backend. Cargo uses the checked-in lockfile, Rust 1.92.0, and a fresh
attempt-owned target directory. The manifest-only workspace isolation repair is
recorded below; package dependencies and lockfile remain unchanged.
The [sidecar gitmodule](https://github.com/yihozhang/egglog-halide-sidecar/blob/aa2beffdca1043e0468a03be8c316f934abdd7d9/.gitmodules)
and [Cargo manifest](https://github.com/yihozhang/egglog-halide-sidecar/blob/aa2beffdca1043e0468a03be8c316f934abdd7d9/Cargo.toml)
define that separate backend relationship.

## Compiler scope and current local evidence

Read-only inspection found `/opt/homebrew/opt/llvm@18` resolving to
`/opt/homebrew/Cellar/llvm@18/18.1.8`. Matching LLVM, Clang and LLD CMake configs,
`libLLVM.dylib`, `libclang-cpp.dylib`, `liblldWasm.a`, `liblldCommon.a`, `ld.lld`
and `wasm-ld` exist. LLVMConfig lists WebAssembly, X86 and NVPTX, among other
targets. These are local presence/config observations, not a HardBoiled build.
At execution, the preparer rechecks the exact version, native architecture and
compiled target list, hashes tools/libraries/CMake configs, and verifies all
three codegen definitions in Halide's generated compile command.

LLVM **18.1.8 is a source-supported diagnostic variance**, not the README's
LLVM19.1.5 environment. The source
[requires LLVM18+ and WebAssembly/X86](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/CMakeLists.txt#L204).
Its [LLVM finder](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/cmake/FindHalide_LLVM.cmake)
links matching Clang/LLD and shared LLVM; the recipe pins those config paths.

Halide's unneeded tests, tutorials, Python bindings, serialization, packaging,
autoschedulers and utilities are disabled. `Halide_WASM_BACKEND=OFF` disables
only the WASM **execution testing** dependency; the WebAssembly codegen target
remains required. This avoids fetching WABT. `Halide_USE_FETCHCONTENT=OFF`
prevents implicit dependency acquisition. SPIR-V and Vulkan headers are supplied
by the full pinned artifact tree. These boundaries come from
[src/CMakeLists.txt](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/src/CMakeLists.txt#L564)
and [runtime/CMakeLists.txt](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/src/runtime/CMakeLists.txt).

## Settings and first two canaries

After successful builds only, `settings.json` has the coordinator's actual
`hardboiled.revision`, `paths.checkout`, `paths.build`, `paths.sidecar`,
`paths.library`, `paths.compiler`, and additional immutable identity paths.
`build-products.json`, `toolchain.json`, `rust-toolchain.json` and numbered step
receipts bind actual files to hashes. `canaries.json` binds source hashes,
unchanged catalog configurations, explicit `prepared-not-run` status and exact
capture commands. A missing binary/header/library or changed source/configuration
prevents settings publication.

Run each separately from the live repository after reviewing preparation:

```sh
.venv/bin/python -m scripts.suite_reproduction --family hardboiled \
  --case hardboiled-matmul_vnni_1x1 --stage capture --settings "$ATTEMPT/settings.json"
.venv/bin/python -m scripts.suite_reproduction --family hardboiled \
  --case hardboiled-matmul --stage capture --settings "$ATTEMPT/settings.json"
```

Here `$ATTEMPT` means the real successful preparation directory. The preparer
writes that absolute path into each machine-readable command; it never launches
either command itself.

| Case | Exact source configuration | Native compiler target |
|---|---|---|
| `hardboiled-matmul_vnni_1x1` | `instrsel-benchmarks/matmul_vnni_1x1.cpp`; no generator parameters | `x86-64-linux-avx512_sapphirerapids`, retained by the original source |
| `hardboiled-matmul` | `apps/tensorcore_benchmarks/matmul_generator.cpp`; `gpu_schedule=tensorcore M=1024 N=1024 K=1024` | `x86-64-linux-cuda-cuda_capability_80`, existing adapter |

AMX adaptation replaces only recognized `result.realize(out, target)` calls in
an attempt-owned copy with LLVM AOT emission and retains other compilation
calls. GPU uses original generator+GenGen compilation and emits
`.a`, `.stmt`, `.h`, `.ll`, `.s`. These actions compile for the target without
executing target code. No SDE, CUDA device run, numerical benchmark or performance
campaign is requested. Compiler completion, complete sidecar/root accounting,
ordinary replay and strict proof validation remain separate gates.

## Concrete existing adapter limitations

Read-only review of live `capture_hardboiled` confirms that the GPU branch is
already wired through the coordinator, includes `GenGen.cpp`, forwards catalog
parameters, wraps every actual sidecar call and requires all five fresh output
files. No missing generic GPU dispatch was found.

Native evidence and remaining limits:

* The fresh GPU `matmul` and AMX `matmul_vnni_1x1` canaries completed source
  optimization and ordinary replay. An [independent native audit](hardboiled-native-audit.md)
  verified their retained artifacts and instruction payloads. All 34 required
  artifact programs subsequently passed; changed shared adapter identities still
  require a current-identity refresh before publication.
* GPU completion currently checks nonempty native output files and hashes. It
  does not separately verify the embedded PTX payload/instruction content.
* Complete-mode compilation and generation use the coordinator timeout (300
  seconds by default), a 5 GiB process-group cap, a 10 GiB disk reserve, and
  guarded warning-pressure diagnostic operation. Legacy capture defaults remain
  120 seconds and 2 GiB.
* The seven supported AMX paper cells still do not map one-to-one to the five
  supplied mains. [The mapping audit](hardboiled-amx-mapping.md) preserves exact gaps; this canary cannot close
  that inventory issue.

Validation in this slice: the five new preparer tests and seven MISAAL preparer
tests pass (12 total); Ruff lint/format and Mypy pass for both preparers/tests.
Those tests mock subprocesses; the subsequent real build evidence is recorded above.

## Native preparation attempts

The first guarded preparation reached the real sidecar build and exposed Cargo
workspace discovery through the surrounding benchmark repository. The next
attempt exposed the sidecar dependency’s own nested workspace. The recipe now
adds a local `[workspace]` with `exclude = ["egglog"]` to the acquired sidecar
manifest, leaving package dependencies and the lockfile intact. Exact source
before/after hashes and the patch are retained per attempt. Both failed attempts
remain diagnostic evidence; preparation is reported successful only after the
sidecar and full Halide builds pass.
