# HardBoiled and MISAAL prerequisite recipes

2026-09-24. This is a source/read-only environment inspection and a proposed
execution recipe, **not a completed build receipt**. No compiler build, source
generator, container, package install or large download ran in this slice.
Only this note was added. Existing adapters are unchanged.

Start with **MISAAL x86 blur3x3**, then **HardBoiled VNNI 1x1 AOT**. The earlier
HVX-add canary suggestion in the adapter handoff is superseded: current HVX
pattern dependencies are repaired upstream, but its native legalizer still has
separate missing/ambiguous prerequisites described below. Do not use an empty
wrapper or fabricated legalizer result to bypass them.

## 1. Exact source identities and acquisition

| Component | Repository and required revision | Role |
|---|---|---|
| MISAAL | [RafaeNoor/MISAAL](https://github.com/RafaeNoor/MISAAL/tree/44ff893445d664cd87f52b08a138260ed2015ba8), `44ff893445d664cd87f52b08a138260ed2015ba8` | Contains the **full modified Halide** at `frontends/halide`, generator sources and online Python optimizer |
| MISAAL Hydride | [akothen/Hydride](https://github.com/akothen/Hydride/tree/beb825327fc946d65032e96f7cde9acf3d24c13e), `beb825327fc946d65032e96f7cde9acf3d24c13e` | Pinned gitlink; Rose Python IR/lowering, supplied LLVM wrappers and native legalizers |
| MISAAL Egglog | [egraphs-good/egglog](https://github.com/egraphs-good/egglog/tree/6b6938bc0088163f61240482cd34a1579715b804), `6b6938bc0088163f61240482cd34a1579715b804` | Pinned gitlink, Egglog 0.4.0 CLI |
| HardBoiled | [yihozhang/cgo2026-hardboiled-artifact](https://github.com/yihozhang/cgo2026-hardboiled-artifact/tree/b99cf0c6400e954a278f697bf3a0596ac3fa4f25), `b99cf0c6400e954a278f697bf3a0596ac3fa4f25` | **The repository itself is full modified Halide**; no submodules at this revision |
| HardBoiled sidecar | [yihozhang/egglog-halide-sidecar](https://github.com/yihozhang/egglog-halide-sidecar/tree/aa2beffdca1043e0468a03be8c316f934abdd7d9), `aa2beffdca1043e0468a03be8c316f934abdd7d9` | Real source-specific backend; not the current ordinary/proof engine |
| Sidecar's Egglog | [egraphs-good/egglog](https://github.com/egraphs-good/egglog/tree/03859dba7c602f07158b87a63b25c143388fbbac), `03859dba7c602f07158b87a63b25c143388fbbac` | Sidecar gitlink, Egglog 0.3.0 library; distinct from MISAAL's backend |

MISAAL's [gitlinks](https://api.github.com/repos/RafaeNoor/MISAAL/git/trees/44ff893445d664cd87f52b08a138260ed2015ba8),
[submodule URLs](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/.gitmodules),
and the [sidecar gitlink](https://api.github.com/repos/yihozhang/egglog-halide-sidecar/git/trees/aa2beffdca1043e0468a03be8c316f934abdd7d9)
were checked directly. Do not follow Hydride's moving `bitserial` branch.

Proposed fresh root: `/Users/saul/p/egglog-encoding/benchmarks/local/reproduction-prereqs-20260924/native`.
The coordinator should choose an immutable attempt directory if this exists.
The following shell blocks are commands for that future guarded preparation;
they were not executed here. Substitute `/work/prereqs` inside a Linux runner.

```sh
TASK_PREP=/Users/saul/p/egglog-encoding/benchmarks/local/reproduction-prereqs-20260924/native
MISAAL="$TASK_PREP/MISAAL"
HARDBOILED="$TASK_PREP/HardBoiled"
SIDECAR="$TASK_PREP/egglog-halide-sidecar"
mkdir -p "$TASK_PREP"
git clone --depth 1 --filter=blob:none --no-checkout https://github.com/RafaeNoor/MISAAL.git "$MISAAL"
git -C "$MISAAL" fetch --depth 1 origin 44ff893445d664cd87f52b08a138260ed2015ba8
git -C "$MISAAL" checkout --detach 44ff893445d664cd87f52b08a138260ed2015ba8
git clone --depth 1 --filter=blob:none --no-checkout https://github.com/akothen/Hydride.git "$MISAAL/Hydride"
git -C "$MISAAL/Hydride" fetch --depth 1 origin beb825327fc946d65032e96f7cde9acf3d24c13e
git -C "$MISAAL/Hydride" sparse-checkout set codegen-generator code-synthesizer/dsl-ir
git -C "$MISAAL/Hydride" checkout --detach beb825327fc946d65032e96f7cde9acf3d24c13e
git -C "$MISAAL" submodule update --init --depth 1 egglog
git clone --depth 1 --filter=blob:none --no-checkout https://github.com/yihozhang/cgo2026-hardboiled-artifact.git "$HARDBOILED"
git -C "$HARDBOILED" fetch --depth 1 origin b99cf0c6400e954a278f697bf3a0596ac3fa4f25
git -C "$HARDBOILED" checkout --detach b99cf0c6400e954a278f697bf3a0596ac3fa4f25
git clone --depth 1 --no-checkout https://github.com/yihozhang/egglog-halide-sidecar.git "$SIDECAR"
git -C "$SIDECAR" fetch --depth 1 origin aa2beffdca1043e0468a03be8c316f934abdd7d9
git -C "$SIDECAR" checkout --detach aa2beffdca1043e0468a03be8c316f934abdd7d9
git -C "$SIDECAR" -c url.https://github.com/.insteadOf=git@github.com: submodule update --init --depth 1
```

Hydride's sparse checkout deliberately excludes its **other** Halide/LLVM trees;
MISAAL's own `frontends/halide` remains complete. Its online dependency subtree
has 2,646 entries / 236,689,521 raw file bytes in the nontruncated GitHub tree.
MISAAL's main tree has 316,519,142 file bytes, HardBoiled 57,201,922. These are
source payload totals, not estimates of Git history or allocated disk. Save
repository heads, exact submodule heads, all patches and file hashes. An archive
without `.git` requires its archive receipt; `git -C archive rev-parse HEAD`
can silently return the enclosing egglog-encoding repository's head.

## 2. Reusable local assets, checked now

All executable/library assets below are **Mach-O arm64**, not Linux binaries.

| Asset | Absolute path | SHA-256 / qualification |
|---|---|---|
| MISAAL real Egglog CLI | `/Users/saul/p/egglog-encoding/benchmarks/local/artifact-audit-20260924/misaal/egglog-pinned/target/debug/egglog` | `6bbb9c3fa064b300590ce059ec25eb9cbe10b5572e1e2ed2d80ea1fa332eb0c7` |
| Old MISAAL Halide library | `/Users/saul/p/egglog-encoding/benchmarks/local/family-followup-20260923/issues/misaal-prerequisites/build-llvm12/src/libHalide.14.0.0.dylib` | `a29dff6ba5a8641d0efa1fefa38b8286f8105558b13dc299bde41432a96890b9`; built from **c098f0f**, not current 44ff |
| Old HVX-add generator | `/Users/saul/p/egglog-encoding/benchmarks/local/artifact-audit-20260924/misaal/cases/misaal-hexagon-add/add_generator` | `f9251b250937fa9042ae3e05a0cd8f7127cea89ed9f73f0297d22df2c1175b01`; old frontend, diagnostic reference only |
| LLVM 12 syntax verifier | `/opt/homebrew/opt/llvm@12/bin/llvm-as` | `d3ce8f42b62f30982057526f63e40f776f52e5cf318fab4061a9db11cbf5adc5` |
| LLVM 12 optimizer | `/opt/homebrew/opt/llvm@12/bin/opt` | `9a83899f15afc76a576afe16b6d7d9ac94eb2466f1b54dba9b849dfd379e4fa9` |
| Prior Python interpreter | `/Users/saul/.cache/uv/environments-v2/0b69a57d38d1c0f5/012b67368557f409/bin/python` | `656e56062f3b201d783f70ae07b1ec613309fc95abbbd9e7d0c0b7bcbe0c9527`; CPython 3.13.11, incomplete Rose environment |

The Egglog archive receipt is
`/Users/saul/p/egglog-encoding/benchmarks/local/artifact-audit-20260924/misaal/egglog-source.json`:
gitlink `6b6938bc…`, archive SHA-256
`2ad90a57a4b940dc02476121b1d09d19ddb0025957ef4562dbf08cff9227959c`.
Pinned upstream `Cargo.toml`, `Cargo.lock`, `src/lib.rs` and `src/main.rs` match
the retained source bytes. The adjacent `backend-build-20260924T122531/` records
successful `cargo build --locked --jobs 1 --bin egglog`, 81.3 seconds and 474 MB
sampled group RSS. This is a legitimate native reuse candidate; it does not
validate the new end-to-end capture path.

Installed LLVM CMake configs resolve to 12.0.1 (`llvm@12/12.0.1_1`), 17.0.6,
18.1.8 and 23.1.2. **LLVM 19.1.5 is not installed under these Homebrew prefixes.**
LLVM 12 lists X86, ARM, AArch64, Hexagon and NVPTX among its built targets.
Current Rust/Cargo are 1.92.0. No retained native legalizer library or HardBoiled
library/sidecar was found in the inspected artifact-audit and family-followup
trees. The retained HardBoiled recovery directory is selected source, not a
complete rebuildable Halide checkout.

## 3. MISAAL: smallest native complete canary

### Toolchain and source repairs

The [installer](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/frontends/halide/install.sh)
selects LLVM **14.0.5** and 32 parallel build threads. The separate
[legalizer CMake file](https://github.com/akothen/Hydride/blob/beb825327fc946d65032e96f7cde9acf3d24c13e/codegen-generator/tools/low-level-codegen/CMakeLists.txt)
requires LLVM **12**. Do not run the broad installer as the canary recipe.
Use installed 12.0.1 for both current Halide and `llvm-link`/`llvm-dis`/`opt`/
`llvm-as`; this reuses the **locally demonstrated frontend build configuration**,
not the installer's exact LLVM selection. A later LLVM14 frontend/LLVM12
legalizer comparison remains separate.

Rebuild 44ff's Halide: its `Rosette.cpp` changed since c098, so the old library
cannot certify current source. Apply the existing narrow build patch to the
**fresh checkout only**, after checking its context:

```sh
FRONTEND_PATCH=/Users/saul/p/egglog-encoding/benchmarks/local/family-followup-20260923/issues/misaal-prerequisites/frontend-cmake-build-only.patch
git -C "$MISAAL" apply --check "$FRONTEND_PATCH"
git -C "$MISAAL" apply "$FRONTEND_PATCH"
MISAAL_BUILD="$TASK_PREP/misaal-halide-llvm12"
LLVM12=/opt/homebrew/opt/llvm@12
uv tool run --from cmake==3.31.10 cmake -S "$MISAAL/frontends/halide" -B "$MISAAL_BUILD" -G 'Unix Makefiles' \
  -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER=/usr/bin/clang -DCMAKE_CXX_COMPILER=/usr/bin/clang++ \
  -DLLVM_DIR="$LLVM12/lib/cmake/llvm" -DClang_DIR="$LLVM12/lib/cmake/clang" \
  -DHalide_SHARED_LLVM=ON -DTARGET_WEBASSEMBLY=OFF -DTARGET_NVPTX=OFF \
  -DWITH_TESTS=OFF -DWITH_PYTHON_BINDINGS=OFF -DWITH_TUTORIALS=OFF -DWITH_DOCS=OFF -DWITH_UTILS=OFF
uv tool run --from cmake==3.31.10 cmake --build "$MISAAL_BUILD" --target Halide --parallel 1
```

The patch adds existing `misaal.cpp` to CMake and honors explicitly disabled LLVM
backends with shared LLVM. The old equivalent native build completed in 147.5s
with 595 MB sampled group RSS. That is sizing evidence, not a prediction for
44ff or an emulated Linux build.

The current x86 legalizer target is `x86LegalizerAllArgs`. It requires Boost's
header-only multiprecision code. `/opt/homebrew/include/boost/version.hpp` is
absent. The pinned CMake hardcodes an old Homebrew include directory. A concrete
native acquisition is Boost 1.81.0's official archive:

```sh
curl --fail --location https://archives.boost.io/release/1.81.0/source/boost_1_81_0.tar.bz2 -o "$TASK_PREP/boost_1_81_0.tar.bz2"
printf '%s  %s\n' 71feeed900fbccca04a3b4f2f84a7c217186f28a940ed8b7ed4725986baf99fa "$TASK_PREP/boost_1_81_0.tar.bz2" | shasum -a 256 -c -
tar -xjf "$TASK_PREP/boost_1_81_0.tar.bz2" -C "$TASK_PREP" boost_1_81_0/boost
```

The hash comes from [Boost's release receipt](https://archives.boost.io/release/1.81.0/source/boost_1_81_0.tar.bz2.json).
For the prepared Hydride copy, a tiny recorded CMake patch should set
`set_target_properties(x86LegalizerAllArgs PROPERTIES SUFFIX ".so")` under
`if(APPLE)`. MISAAL's [`misaal.cpp`](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/frontends/halide/src/misaal.cpp#L157)
requests `libx86LegalizerAllArgs.so` on every host, while CMake otherwise creates
a `.dylib` on macOS. This output-name adaptation preserves the generated command;
the library is still Mach-O. It is proposed, not build-tested here.

```sh
LEGALIZERS="$TASK_PREP/misaal-legalizers-llvm12"
uv tool run --from cmake==3.31.10 cmake \
  -S "$MISAAL/Hydride/codegen-generator/tools/low-level-codegen" -B "$LEGALIZERS" \
  -DLLVM_DIR="$LLVM12/lib/cmake/llvm" -DCMAKE_CXX_COMPILER=/usr/bin/clang++ \
  -DCMAKE_CXX_FLAGS="-I$TASK_PREP/boost_1_81_0"
uv tool run --from cmake==3.31.10 cmake --build "$LEGALIZERS" --target x86LegalizerAllArgs --parallel 1
```

### Python and Rose

The prior environment contains numpy 2.5.1, psutil 7.2.2, pyparsing 3.3.3 and
z3-solver 5.1.0.0; **it lacks sympy**, imported by `RoseUtilities.py`. Prepare a
new environment rather than mutating it. Proposed explicit dependency selection
(the additions are not author-pinned requirements):

```sh
uv venv --python 3.13.11 "$TASK_PREP/misaal-python"
uv pip install --python "$TASK_PREP/misaal-python/bin/python" \
  numpy==2.5.1 psutil==7.2.2 pyparsing==3.3.3 z3-solver==5.1.0.0 \
  sympy==1.14.0 mpmath==1.3.0 ply==3.11
```

Use the pinned Hydride **vendored llvmlite Python IR package** through its
`setup.sh` path, not a recent pip llvmlite substitution. The online path inspected
imports `llvmlite.ir`; the vendored optional FFI builder expects LLVM11, which is
a third dependency and must not accidentally be invoked by a generic pip install.
Do not claim FFI is supported unless a reached operation requires it and its
build is separately validated. Racket/Rosette installation belongs to offline
rule synthesis; the inspected online route parses Rosette text with Python,
then runs native LLVM tools. A small **future** import probe of `RosetteLifter`
and `RoseLowLevelCodeGen` should precede any pattern imports. It should assert
`llvmlite.__file__` lies under the pinned Hydride checkout and record imports.

### Original generator, environment and request

The actual retained source recipe is
`/Users/saul/p/egglog-encoding/benchmarks/local/artifact-audit-20260924/misaal/cases/misaal-x86-blur3x3/request.json`.
The source's recorded SHA-256 is
`a7446e7bb7b9ae48d9b1d593ea0df0ce5ab82322f25790653e41a8162e739582`.
Rehash the acquired 44ff file and retain any difference; compile from that
checkout, never from the old recovered source plus a claimed new revision.

```sh
MISAAL_GEN="$TASK_PREP/blur3x3_generator"
/usr/bin/clang++ --std=c++17 -fno-rtti -O3 -g -DLOG2VLEN=7 \
  -I "$MISAAL_BUILD/include" -I "$MISAAL/frontends/halide/tools" \
  "$MISAAL/benchmarks/x86/halide/blur3x3/src/blur3x3_generator.cpp" \
  "$MISAAL/frontends/halide/tools/GenGen.cpp" \
  "$MISAAL/benchmarks/x86/halide/hannk/common_halide.cpp" \
  -o "$MISAAL_GEN" -L "$MISAAL_BUILD/src" -lHalide -Wl,-rpath,"$MISAAL_BUILD/src"
```

Source `MISAAL/setup.sh` **from its own root**, then override its stale inferred
LLVM locations with the actual LLVM12 prefix. Capture this environment in the
request, including `PYTHONPATH`, `PATH`, `MISAAL_SRC`, `MISAAL_ROOT_DIR`,
`HYDRIDE_DIR`, `HYDRIDE_ROOT`, `LEGALIZERS_DIR`, `LLVM_ROOT`, `LLVM_DIS_ROOT`,
`LLVM_CONFIG`. Prepend the new Python environment and LLVM12 `bin` directories.
The source setup builds the Rose/DSL import paths; setting only MISAAL `lib/`
is insufficient. Set `HALIDE_SRC`, `HALIDE_DIR`, `HALIDE_DISTRIB` consistently
with the fresh source/build if retaining them in the receipt.

For this **artifact source configuration**, preserve these flags exactly:

```json
{
  "HL_EXPR_DEPTH": "2",
  "HYDRIDE_BENCHMARK": "blur3x3_x86_depth2_misaal",
  "HL_ENABLE_MISAAL": "1",
  "HL_ENABLE_HYDRIDE": "1",
  "HL_SYNTH_BW": "16",
  "HYDRIDE_INITIAL_HASH": "empty_hash",
  "MISAAL_DISABLE_FRONTEND_PATTERNS": "1"
}
```

Leave `MISAAL_EQ_SAT_ITERS` unset here: `misaal.h` defaults to five. The separate
HVX recipe explicitly chooses three; do not copy that setting into this case.
Do not add lookahead, ISA features or remove the frontend-pattern flag silently.
The `host-x86-64` target preserves the recipe but means host-derived features can
differ between the Mac and Linux; record the concrete emitted target.

The complete request uses the [existing schema](benchmarks/reproduction/misaal-hardboiled.md#misaal-request-and-first-canary):
`case_id=misaal-x86-blur3x3`, the 44ff revision, actual source/tool/generator hashes,
and the reused real Egglog executable above. Its command and expected outputs are:

```json
{
  "generator_command": ["ABSOLUTE_MISAAL_GEN", "-t", "0", "-o", "{output}",
    "-g", "blur3x3", "-e", "static_library,stmt,h,llvm_assembly,assembly",
    "-f", "blur3x3", "target=host-x86-64-no_bounds_query-no_asserts"],
  "expected_generator_outputs": ["blur3x3.a", "blur3x3.stmt", "blur3x3.h", "blur3x3.ll", "blur3x3.s"]
}
```

The placeholders are not a submittable request. The coordinator must compute
actual hashes and populate all required fields. Use a fresh pattern-cache-free
checkout copy for the attempt. First validate that the x86 wrapper exists and
the exact LLVM12 `opt` can load the new library and register
`-x86-hydride-legalize`. Then call `capture_misaal(request_path, fresh_attempt)`
directly, or the documented `scripts/misaal_reproduction.py capture` CLI with
no redundant outer native process-group wrapper.

## 4. Ubuntu/OrbStack variant

Root reports only a BusyBox 1.37 arm64 guard canary is acquired. There is **no
Ubuntu image digest or successful Linux prerequisite build yet**. A proposed
image is Ubuntu22.04 `linux/amd64`, with its actual digest recorded by the
coordinator on pull. This aligns the OS/host ISA with the x86 recipes and the
official LLVM19 x64 release, but introduces emulation on Apple Silicon. It does
not repair source assertions, rules, absent wrappers or disabled build targets.

Ubuntu Jammy supplies [LLVM12](https://packages.ubuntu.com/jammy/llvm-12-dev) and
[Clang12](https://packages.ubuntu.com/jammy/clang-12) version
`1:12.0.1-19ubuntu3` for amd64 and arm64. Its
[Boost development package](https://packages.ubuntu.com/jammy/libboost-dev) is
`1.74.0.3ubuntu7`. A future image preparation command is:

```sh
apt-get update
apt-get install -y --no-install-recommends ca-certificates curl git build-essential ninja-build \
  python3 python3-venv python3-pip pkg-config xz-utils \
  llvm-12=1:12.0.1-19ubuntu3 llvm-12-dev=1:12.0.1-19ubuntu3 \
  llvm-12-tools=1:12.0.1-19ubuntu3 clang-12=1:12.0.1-19ubuntu3 \
  libclang-12-dev=1:12.0.1-19ubuntu3 libclang-cpp12-dev=1:12.0.1-19ubuntu3 \
  libboost-dev=1.74.0.3ubuntu7 libffi-dev libtinfo-dev zlib1g-dev
```

Record the resolved package manifest and fail if explicit packages are no
longer available, instead of falling through to an unrecorded LLVM version.
Install/use CMake3.31.10 and Rust1.92.0 in the container, recording installer and
tool hashes. Create the proposed Python3.13.11 environment there as well; Jammy's
default Python3.10 cannot substitute for the specified numpy2.5.1 environment.
Use `LLVM12=/usr/lib/llvm-12`, `/usr/bin/clang-12`, `/usr/bin/clang++-12` in the
same CMake/generator recipes. CMake `.so` output already matches MISAAL on Linux;
the Mac suffix patch and Boost archive are unnecessary. Rebuild Egglog in the
actual Linux checkout with `cargo +1.92.0 build --locked --jobs 1 --bin egglog`.
Never execute a mounted Mac binary as a Linux prerequisite.

The coordinator owns container execution, cgroup/VM guard evidence and cleanup.
Keep children inside its supervised container; mounting source does not convert
native `run_bounded_command` into a container guard. There is no SDE, CUDA
execution, generated target-code execution or performance campaign in this plan.

## 5. HardBoiled: full Halide, real sidecar, AOT only

The [artifact README](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/README.md)
specifies LLVM19.1.5, CMake3.28+ and a separately built sidecar. Its
[CMake constraints](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/CMakeLists.txt#L203)
accept LLVM18+, require **WebAssembly and X86**, and make NVPTX optional. Clang
and LLD development CMake packages must match LLVM. Do not use MISAAL's LLVM12.

Two explicitly labelled routes:

1. **Smallest native diagnostic:** existing `/opt/homebrew/opt/llvm@18` (18.1.8),
   provided its matching Clang/LLD configs are present. This is supported by the
   source's version constraint, not a demonstrated HardBoiled build or the
   README's exact compiler version. Keep this variance in the receipt.
2. **README-version Linux route:** acquire the official
   [LLVM19.1.5 release](https://github.com/llvm/llvm-project/releases/tag/llvmorg-19.1.5).
   `LLVM-19.1.5-Linux-X64.tar.xz` is 1,652,713,376 compressed bytes and has an
   adjacent `.jsonl` provenance asset. An official AArch64 Linux archive also
   exists (1,132,333,340 bytes); no native Apple-arm64 archive was listed.
   Record downloaded bytes/hash/provenance; preflight `llvm-config --version`,
   target set and `lib/cmake/{llvm,clang,lld}` before treating it as a development
   toolchain. No large asset was fetched here. If the binary distribution is
   unsuitable, build `llvmorg-19.1.5` with the README's exact options and one job;
   this is the expensive fallback, not a 30-minute guarantee.

With `HARDBOILED_LLVM` set to the chosen **installation** prefix:

```sh
HARDBOILED_BUILD="$TASK_PREP/hardboiled-halide"
uv tool run --from cmake==3.31.10 cmake -S "$HARDBOILED" -B "$HARDBOILED_BUILD" \
  -DCMAKE_BUILD_TYPE=Release -DHalide_LLVM_ROOT="$HARDBOILED_LLVM" \
  -DWITH_TESTS=OFF -DWITH_PYTHON_BINDINGS=OFF -DWITH_TUTORIALS=OFF \
  -DWITH_DOCS=OFF -DWITH_UTILS=OFF -DWITH_AUTOSCHEDULERS=OFF -DWITH_SERIALIZATION=OFF
uv tool run --from cmake==3.31.10 cmake --build "$HARDBOILED_BUILD" --target Halide --parallel 1
cargo +1.92.0 build --manifest-path "$SIDECAR/Cargo.toml" --locked --jobs 1 --bin egglog-halide-sidecar
```

The explicit minimal build avoids unrelated tests/tutorials/schedulers. The
adapter compiles its fresh AMX source copy itself, so disabling `WITH_TESTS`
(which also disables the artifact's `instrsel-benchmarks` CMake subdirectory)
does not omit the canary. Check the actual generated Halide header and shared
library paths, rather than assuming the old MISAAL output layout.

Use the existing complete adapter with actual checkout/build/library/compiler
and `SIDECAR/target/debug/egglog-halide-sidecar`, selecting only
`hardboiled-matmul_vnni_1x1`, `optimization_only=True`. It replaces the exact
realization with AOT LLVM emission, returns real sidecar choices to native
post-selection lowering and requires fresh final outputs. This avoids target
execution; it does not establish AMX numerical correctness. AOT API/bounds and
later lowering remain canary gates. First GPU expansion additionally requires
the LLVM NVPTX backend and validation of actual generated CUDA/PTX output;
CUDA/PyTorch/cuDNN baseline timing dependencies are not prerequisites to assume
for this first AMX source-optimization canary.

## 6. Explicit unresolved source prerequisites and coverage

At MISAAL44ff, all three previously problematic HVX file paths now exist in
[`targets/hvx`](https://github.com/RafaeNoor/MISAAL/tree/44ff893445d664cd87f52b08a138260ed2015ba8/targets/hvx).
[`lib/patterns/HVX.py`](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/lib/patterns/HVX.py)
also removes the dead import and fixes the machine-local path logic. Fresh
pattern caches are still required; old pickle files can hide those changes.

This does **not** finish native HVX/ARM acquisition:

| Target | Concrete pinned-source gap | Next permissible repair/verification |
|---|---|---|
| HVX | CMake target commented; `InstSelectors/hexagon/**.cpp` selects three files defining the same `HexLegalizationPass`/ID | Select one implementation explicitly, with source evidence and a native legalization canary; merely uncommenting the target is wrong |
| HVX | `misaal.cpp` requests `wrappers/hvx_wrappers.ll`; absent from the complete Hydride `codegen-generator` tree at beb825 and MISAAL44ff tree | Recover a source-backed wrapper or derive and verify necessary LLVM definitions from the actual generated program; do not create an empty success placeholder |
| ARM | Target commented; `ARMLegalizer.cpp` includes absent `ARMLegalizer.h` | Supplied `RoseARMLegalizerGen.py` can emit header/selector files, but its main imports absent `ARMSemantics`; resolve that semantics source first and record generated code |

Inspected sources:
[HVX directory](https://github.com/akothen/Hydride/tree/beb825327fc946d65032e96f7cde9acf3d24c13e/codegen-generator/tools/low-level-codegen/InstSelectors/hexagon),
[ARM generator](https://github.com/akothen/Hydride/blob/beb825327fc946d65032e96f7cde9acf3d24c13e/codegen-generator/tools/low-level-codegen/InstSelectors/arm/RoseARMLegalizerGen.py),
[complete codegen tree](https://api.github.com/repos/akothen/Hydride/git/trees/4dca7f9000f79e1ad5327e501a7a240b10a12b23?recursive=1).
A static name comparison gives `HexLegalizerGeneric.cpp` coverage of 112/114
MISAAL `hexsemantics_new` dictionary instruction names (missing interleave2/4),
versus 63/114 and 65/114 for the other two files. This makes Generic the leading
repair candidate, **not proof of complete/semantically correct legalization**.
No exhaustive history search or author contact was made.

HardBoiled's five current AMX programs still do not establish all seven paper
cells. See [AMX-MAPPING.md](AMX-MAPPING.md): one direct supported feature mapping,
two structural reference candidates, two unresolved loop-order contrasts and
two missing explicit A-preload configurations. Preserve all five original
programs; additional reviewed source variants are still required. Installing
LLVM19 or running Linux does not close this inventory gap.

## 7. Guarded order, resource envelope and admission gates

Proposed stages, each with a separate receipt: source acquisition → tool/env
preflight → one-job frontend build → one-job legalizer build → generator build
→ one complete capture → ordinary replay → strict proof validation. No whole
suite until that chain passes. For native calls use the shared required guard,
10 GiB disk reserve and no simultaneous compiler jobs. Root reports ~7.4 GiB
fresh OrbStack `MemAvailable`; a 5 GiB cap fits only while that remains true.

Suggested initial **limits, not measured forecasts**: 600s per dependency/Rust/
legalizer/generator build, 1,800s per one-job Halide build, 900s MISAAL capture.
The existing HardBoiled adapter has 120s compile/generate limits; any needed
increase must be explicit and recorded. A timeout is evidence, not permission
for an automatic unbounded retry. Full LLVM source compilation can exceed an
1,800s slot substantially.

Measured old native footprints: sparse MISAAL Halide source 76 MiB, old Halide
build 252 MiB, pinned Egglog source+debug build 404 MiB, selected MISAAL/Hydride
recovery 223 MiB, Homebrew LLVM12 1.5 GiB. For planning, reserve **10 GiB additional
working space** for the native dependency-reuse route, or **25 GiB** for a Linux
image plus unpacked LLVM19 binary/toolchains/builds, **in addition** to the
10 GiB free-space floor. These are conservative allowances to check against
actual bytes, not download/build measurements. The largest fallback, full LLVM
source builds, warrants a separate **100 GiB-class disk budget** (the HardBoiled
README itself warns that LLVM builds can reach this size); do not start it on
the binary-route allowance.

Admission requires all actual backend calls and roots, real stdout selections,
fresh LLVM/native files with hashes, legalizer feedback accepted by the live
original parent, and successful final parent exit. Then run every standalone
`.egg` with the ordinary engine against recorded root/check/output order; strict
proof checks are separate. Generated bytes, successful individual calls, whole
source optimization, ordinary compatibility and proof validity remain distinct
statuses. No output is inserted to make its check pass, and no target-device
execution or timing claim follows from these gates.
