# Initial infrastructure inventory

Completed 2026-10-17. This is provenance and setup evidence, not a performance or correctness result. No build, test, compiler workload, timing collection, project-module import, source edit or old-artifact write was performed. The encoding and compiler owners may be changing their authorized source concurrently; these observations are not a final source checkpoint.

Machine-readable evidence is [inventory.json](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/inventory.json), with exact argv/cwd/status and hashed stdout/stderr in [inventory/commands.json](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/inventory/commands.json), selected file identities/copies in `inventory/files.json` and `inventory/selected-files/`, and static Python import evidence in `inventory/import-compatibility.json`. The captured approved plan hash matches `initial-selection.json`. Parent-provided live PR/remote-main observations were retained through that selection receipt, without duplicate remote queries.

## Available environment

| Component | Actual identity |
| --- | --- |
| Host | Apple M4, Mac16,1; arm64; 16 GiB; 10 CPUs; macOS 26.6 build 25G72. LLVM 18 reports `Host CPU: apple-m1`; that is the tool's label, not the physical machine model. |
| Rust compiler | `rustc 1.91.0 (f8297e351 2025-10-28)`, aarch64-apple-darwin, internal LLVM 21.1.2. Cargo 1.91.0 `ea2d97820`. Clippy, rustfmt, llvm-tools and Rust standard components are installed. This Rust LLVM version is separate from the Bril backend. |
| Runtime compiler | Installed `nightly-2024-05-01`: rustc 1.80.0-nightly `f705de596`, LLVM 18.1.4. It was queried for version only. |
| Bril backend | Homebrew LLVM 18.1.8 under `/opt/homebrew/opt/llvm@18`, resolved prefix `/opt/homebrew/Cellar/llvm@18/18.1.8`. `opt`, `clang-18`, `llvm-dis`, `llvm-objdump` and `llvm-config` are available. `opt-18` is absent. Current EggCC lookup therefore selects LLVM 18 `opt` and `clang-18`; plain `/usr/bin/clang` is Apple 21 and is a distinct tool. |
| Python/uv | uv 0.13.0 Homebrew. Explicit managed CPython 3.13.11 exists at `/Users/saul/.local/share/uv/python/cpython-3.13-macos-aarch64-none/bin/python3.13`; ambient `python3` is Homebrew 3.14.8. No package install or environment synchronization occurred. |
| Native link setup | `pkg-config` 3.0.8 resolves CBC 2.10.13 and arm64 Homebrew link flags under `/opt/homebrew`. cargo-insta 1.46.3 is installed. No link was attempted. |

Current relevant inherited settings are `LLVM_SYS_180_PREFIX=/opt/homebrew/opt/llvm@18`, `LIBRARY_PATH=/opt/homebrew/lib`, `PKG_CONFIG_PATH=/usr/local/opt/cbc/lib/pkgconfig`, `LANG=en_US.UTF-8`, `LC_ALL=C.UTF-8`. Despite that inherited `/usr/local` pkg-config entry, actual CBC resolution is the `/opt/homebrew` installation. `RUSTUP_TOOLCHAIN`, `CARGO_TARGET_DIR`, build/test thread counts, `RAYON_NUM_THREADS`, `RUSTFLAGS`, `EGGCC_ROOT` and `EGGLOG_BENCH_MEMORY_GUARD` were unset in this inventory process. Future commands must set and record the intended compiler/thread/guard settings explicitly; these ambient defaults are not a chosen treatment.

All three locked/offline metadata commands succeeded with no code generation and unchanged checked manifests/locks:

```text
cwd /Users/saul/p/wt/eggcc/encoding-impact
  cargo +1.91.0 metadata --locked --offline --format-version 1
cwd /Users/saul/p/wt/eggcc/encoding-impact/dag_in_context
  cargo +1.91.0 metadata --locked --offline --format-version 1
cwd /Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding
  cargo +1.91.0 metadata --locked --offline --format-version 1
```

## Dependency and source endpoints

| Graph | Current resolution |
| --- | --- |
| New EggCC root, base 15ee7cba | 291 packages; experimental 0.1.0 at `19ed86667733c56e4072956ce3b414b6860660bc`; core 2.0.0 at `9b5ce1114ac1cf407be78f1ec9493324fd296920`. Default EggCC features include `llvm`. |
| New standalone DAG | 185 packages; experimental 0.1.0 at `6b37b6b31cf878fd7384e470b216398d9cc006fe`; core 2.0.0 at `07650bedfe246ecaf4490d3074bc30bc5442bfe3`. This is a separate lock/graph, not the root resolution. |
| New encoding workspace, base 392b6d6b | 235 packages; local experimental 3.0.0 and local core 2.0.0. The new worker's encoding source is not yet a dependency of the new compiler manifests. |

Root and standalone DAG dependency identity sets each equal their respective historical A metadata sets. They do not equal one another. Bril is pinned to `06117c089c2d235ff8d040bb3d0cfd1e2a1c4880`, Inkwell to `6c0fb56b3554e939f9ca61b465043d6a84fb7b95`, and llvm-sys resolves 180.0.0. Original compiler ordered-float is 5.1.0; selected encoding resolves 5.3.0. Both Cargo manifests and both lockfiles must be retargeted and captured deliberately if a new engine comparison is selected. Metadata success establishes resolution availability, not build/API compatibility.

The old B/prototype archives use absolute experimental dependency paths into the old `eggcc-study` worktree. Reconstructing a patch without changing and recording both paths would silently keep the old engine. The new compiler baseline is still the original 15ee7cba source; the old feature CLI is not implicitly present there. Root owns any source reconstruction/selection.

## Frozen executable and runtime identities

All existing expected binary, runtime and collector hashes checked here match their historical receipts. Frozen compiler hashes are:

- A: `e062c92bbcb9a8f05caed3cc10ec013c126a1d1f528e57f3b797bf6c3004912d`.
- B: `6c30c8cb28768f3c461666b0370ff5c249fe6ba1f8f58a1a1d6c78e2df3e638f`.
- Final prototype: `d44a89c2f752aff60b2691d9e055f23e54215fc9dfa74a0db8e956afc713162e`.
- All three sibling Tiger files: `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`.

The final full/feature patches match checkpoint hashes `7ab6605cedbdb7e6e44fe7b4a6f1768033b1cb83bb7c4f3ad5aee391f64cb08c` / `243298fbf886be35e9919d54a73bfa4a973e8da62c7a1361fcf455cc8b913183`. These are distinct historical source/binary endpoints, not the new worker's code. `file` reports arm64 Mach-O for each distinct compiler and Tiger. `otool -L` outputs are retained, with all listed non-system absolute library files present and hashed. Availability/static linkage inspection is not a fresh execution or ABI test.

The old retarget tree's generated runtime still matches archived LLVM 18-era artifacts: `rt.bc` SHA256 `c24564b983852848320eed8cd19cc02678ad781a821e6dff133489994c644f91`, `rt.o` `07123ecfab57014f9f227953c277fa53edca38c7c1e362ebf02ee5a44be62b84`. Runtime sources/manifest/lock match the new compiler's corresponding sources. Historical verification/build workaround receipts are retained; bitcode was not reverified or executed here.

Generated `rt.bc` and `rt.o` are absent in both the new compiler tree and the old baseline tree. `src/util.rs:113–117` resolves runtime files through `EGGCC_ROOT`, defaulting to cwd. Native lowering from the new cwd is therefore not ready merely because the old retarget runtime exists. Select a compatible explicit runtime root or new retained runtime location, bind its source/tool/artifact hashes identically across arms, and avoid rewriting old artifacts. `runtime/install.sh` cleans and can hit the historical macOS no_main link failure; no invocation was made.

Tiger lookup checks the compiler executable's sibling first, then the compile-time manifest parent's `target/release` and `target/debug`. Its build script writes to that manifest-parent target independently of a custom Cargo target directory. Reused Cargo cache alone does not guarantee that side-effect artifact exists or selects the intended Tiger; freeze/hash the actual sibling when producing a new compiler endpoint.

## Collector and guarded-runner boundary

The reviewed collector is an uncommitted three-file checkpoint on the old 392b6d6b worktree basis, not part of the selected new 392b6d6b commit:

| File | SHA256 |
| --- | --- |
| `scripts/eggcc_encoding_case_study.py` | `79c4147dbe5b74d1d9138e170643a7c09205f55a6d49d355f1fc201c3a811380` |
| `scripts/eggcc_encoding_case_study.md` | `66b125c2375fc68bff2659a9c3baf0652420e01fd524f80b3cb92965d40017a5` |
| `tests/test_eggcc_encoding_case_study.py` | `90a2fddab01a471fd51155aaebe1be0229a145c6e8174ebcab66235244e70093` |

Old worker, integrated study and frozen provenance copies agree. `harness/harness.patch` SHA256 `632740a1c68eccb4b87ba9bf09b7888fb5ee2e130eede6a6cd7859138a621152` equals its frozen engine-control copy and lists exactly those three paths. The selected new encoding tree lacks all three files; it contains the old unguarded `processes.py` hash `1dc11c5d11551729ec4dc8507773e9edc5cb33d52891837ac2505b5f87f816ce`.

Current primary guarded `processes.py` is `21f1184ba33fa8a45a7bcfcae32e9b4568c15c93cfa04f47a0b77deddea8e073`. Static parsing under isolated Python 3.13.11 shows the minimal current-primary reuse boundary is **that process file plus `benchmarking/memory_guard.py`**. Existing selected `models.Status`, `models.FileSpec` (including sha256/fact-directory/display fields), `engines`, and empty package initializer satisfy the inspected imports. The caller's run_command arguments and timing/error fields remain available; the new result adds defaulted `resource_stopped`. Current models/engines do not need transplantation; copying them wholesale would also introduce the current `math_workloads.py` dependency and unrelated Math support.

This is static source compatibility only. No file was copied into either source tree, and no project module was imported. Once root selects a separate harness basis, import smoke plus focused collector/process/guard tests must establish actual integration behavior. Preserve the guard's explicit failure behavior; its opt-in variable is `EGGLOG_BENCH_MEMORY_GUARD=1`, currently unset. The primary guard's sampled 10 GiB group-RSS cap/normal-pressure/2GiB reserve is operational safety, distinct from the collector's reported normalized `wait4` child `ru_maxrss` metric. Merely adding the module does not enable the guard.

Collector collect/verify use stdlib plus that process import graph; figures lazily require explicit pinned Matplotlib 3.10.7. Python >=3.12 is needed by type-alias syntax in the import graph. A fresh isolated plotting environment was not created or checked. The driver accepts optimizer mode only, performs interpreted checks separately, and defaults to one warmup/ten observations/300s. Four-arm balanced pilots must explicitly set 12 observations; native preparation/execution is not already supported.

## Treatment settings to freeze next

CLI contexts default off unless `--with-context`, unlike the Rust config default true. Production CLI uses `non_weakly_linear=true`; broad file-harness configs use false. Default optimization is parallel/all passes and greedy Tiger, with no ILP/timing instrumentation; retain actual pass receipts rather than relying solely on labels. Original interpreter arguments come from retained `# ARGS:` headers; trailing CLI arguments are parsed but unused. Native backend levels are exactly `O0_O0`, `O1_O0`, `O2_O0`, `O3_O0`, `O3_O3`, with explicit unique output paths needed per arm.

Before a fair new comparison, root must choose the harness source basis/current guard, compiler engine retarget and both dependency graphs, actual new compiler/Tiger checkpoint, matching thread/options/manual/closure arms, and an explicit runtime/backend setup if native execution becomes useful. Fresh collector/guard checks, native exit/output/final-code checks and confirmation precision remain future work. No native adapter or general runner change is justified or implemented by this inventory.
