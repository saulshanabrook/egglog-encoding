"""Prepare pinned native HardBoiled tools; never execute AMX or GPU generators.

Run as ``python -m scripts.reproduction_prepare_hardboiled`` after acquiring the
heavy-job slot through this command. Each fresh attempt retains pins, exact tool
hashes, guarded subprocess logs, and coordinator settings. LLVM 18.1.8 is an
explicit source-supported variance from the README's LLVM 19.1.5 recipe.
"""

from __future__ import annotations

import argparse
import json
import platform
import sys
import traceback
import uuid
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from scripts.reproduction_prepare_misaal import Preparation, sha256_file, write_json
from scripts.reproduction_process import exclusive_job

ROOT = Path(__file__).resolve().parents[1]
HARDBOILED_REVISION = "b99cf0c6400e954a278f697bf3a0596ac3fa4f25"
SIDECAR_REVISION = "aa2beffdca1043e0468a03be8c316f934abdd7d9"
EGGLOG_REVISION = "03859dba7c602f07158b87a63b25c143388fbbac"
LLVM = Path("/opt/homebrew/opt/llvm@18")
REQUIRED_TARGETS = {"WebAssembly", "X86", "NVPTX"}
CMAKE = ["uv", "tool", "run", "--from", "cmake==3.31.10", "cmake"]
CANARIES = {
    "hardboiled-matmul_vnni_1x1": {
        "source": "instrsel-benchmarks/matmul_vnni_1x1.cpp",
        "configuration": {},
        "target": "x86-64-linux-avx512_sapphirerapids",
    },
    "hardboiled-matmul": {
        "source": "apps/tensorcore_benchmarks/matmul_generator.cpp",
        "configuration": {"gpu_schedule": "tensorcore", "M": 1024, "N": 1024, "K": 1024},
        "target": "x86-64-linux-cuda-cuda_capability_80",
    },
}


def inspect_llvm(preparation: Preparation, llvm: Path) -> dict[str, Any]:
    """Require matching development packages and all three canary codegen targets."""
    version = preparation.step("llvm-version", [str(llvm / "bin/llvm-config"), "--version"], timeout=30).strip()
    if version != "18.1.8":
        raise ValueError(f"this native recipe requires the inspected LLVM 18.1.8, found {version}")
    targets = set(
        preparation.step("llvm-targets", [str(llvm / "bin/llvm-config"), "--targets-built"], timeout=30).split()
    )
    if missing := REQUIRED_TARGETS - targets:
        raise ValueError(f"LLVM lacks required codegen targets: {sorted(missing)}")
    paths = [
        llvm / relative
        for relative in (
            "bin/llvm-config",
            "bin/clang",
            "bin/clang++",
            "bin/llvm-as",
            "bin/llvm-dis",
            "bin/llvm-link",
            "bin/llc",
            "bin/ld.lld",
            "bin/wasm-ld",
            "lib/libLLVM.dylib",
            "lib/libclang-cpp.dylib",
            "lib/liblldWasm.a",
            "lib/liblldCommon.a",
            "lib/cmake/llvm/LLVMConfig.cmake",
            "lib/cmake/clang/ClangConfig.cmake",
            "lib/cmake/lld/LLDConfig.cmake",
        )
    ]
    for path in paths:
        if not path.is_file():
            raise ValueError(f"missing LLVM 18 development prerequisite: {path}")
    for package in ("clang/ClangConfig.cmake", "lld/LLDConfig.cmake"):
        if "set(LLVM_VERSION 18.1.8)" not in (llvm / "lib/cmake" / package).read_text():
            raise ValueError(f"LLVM package version mismatch: {package}")
    architectures = preparation.step(
        "native-tools", ["file", "-L", str(llvm / "bin/clang"), str(llvm / "bin/llvm-config")], timeout=30
    ).splitlines()
    if len(architectures) != 2 or any("arm64" not in line for line in architectures):
        raise ValueError("LLVM executables do not match the native arm64 host")
    # Include imported-target declarations, which name the actual linked libraries.
    paths.extend(path for path in (llvm / "lib/cmake").rglob("*.cmake") if path.is_file())
    return {
        "version": version,
        "root": str(llvm.resolve()),
        "targets": sorted(targets),
        "variance": "source permits LLVM18+; artifact README specifies LLVM19.1.5",
        "files": {str(path.resolve()): sha256_file(path) for path in dict.fromkeys(paths)},
    }


def acquire_source(preparation: Preparation, name: str, url: str, revision: str) -> Path:
    """Acquire a fresh source directory and reject any checkout other than its pin."""
    source = preparation.directory / "sources" / name
    preparation.step(
        f"{name}-clone", ["git", "clone", "--filter=blob:none", "--no-checkout", "--depth", "1", url, str(source)]
    )
    preparation.step(f"{name}-fetch", ["git", "fetch", "--depth", "1", "origin", revision], cwd=source)
    preparation.step(f"{name}-checkout", ["git", "checkout", "--detach", revision], cwd=source)
    if preparation.step(f"{name}-head", ["git", "rev-parse", "HEAD"], cwd=source, timeout=30).strip() != revision:
        raise ValueError(f"{name} revision differs from requested pin")
    return source


def write_canary_settings(directory: Path, checkout: Path, build: Path, sidecar: Path, llvm: Path) -> Path:
    """Bind real build products and unchanged catalog configurations to two requests."""
    library = build / "src/libHalide.dylib"
    required = [library, build / "include/Halide.h", sidecar, build / "CMakeCache.txt"]
    for path in required:
        if not path.is_file() or not path.stat().st_size:
            raise ValueError(f"missing nonempty built prerequisite: {path}")
    catalog = json.loads((ROOT / "benchmarks/catalog.json").read_text())
    selected = {case["id"]: case for case in catalog["cases"] if case["id"] in CANARIES}
    if set(selected) != set(CANARIES):
        raise ValueError("the two expected HardBoiled canary identities are not in the catalog")
    requests = []
    for case_id, specification in CANARIES.items():
        case = selected[case_id]
        if case["source"] != specification["source"] or case.get("configuration", {}) != specification["configuration"]:
            raise ValueError(f"catalog source/configuration changed: {case_id}")
        source = checkout / case["source"]
        requests.append(
            {
                "case_id": case_id,
                **specification,
                "source_sha256": sha256_file(source),
                "status": "prepared-not-run",
                "device_execution": False,
                "command": [
                    sys.executable,
                    "-m",
                    "scripts.suite_reproduction",
                    "--family",
                    "hardboiled",
                    "--case",
                    case_id,
                    "--stage",
                    "capture",
                    "--settings",
                    str(directory / "settings.json"),
                ],
            }
        )
    toolchain = json.loads((directory / "toolchain.json").read_text())
    settings = {
        "hardboiled": {
            "revision": HARDBOILED_REVISION,
            "paths": {
                "checkout": str(checkout),
                "build": str(build),
                "sidecar": str(sidecar),
                "library": str(library.resolve()),
                "compiler": str(llvm / "bin/clang++"),
                "egglog": str(ROOT / "target/release/egglog-experimental"),
            },
            "identity_paths": [
                str(build / "include"),
                str(directory / "identity.json"),
                str(directory / "toolchain.json"),
                str(directory / "build-products.json"),
                str(directory / "rust-toolchain.json"),
                *toolchain["files"],
            ],
        }
    }
    write_json(directory / "build-products.json", {str(path.resolve()): sha256_file(path) for path in required})
    write_json(directory / "canaries.json", requests)
    path = directory / "settings.json"
    write_json(path, settings)
    return path


def prepare(directory: Path, llvm: Path) -> Path:
    """Build the real sidecar and Halide compiler with sequential guarded jobs."""
    if (platform.system(), platform.machine()) != ("Darwin", "arm64"):
        raise ValueError("this recipe is explicitly for native Apple Silicon")
    preparation = Preparation(directory)
    with (directory / "preparer.py").open("xb") as snapshot:
        snapshot.write(Path(__file__).read_bytes())
    write_json(
        directory / "identity.json",
        {
            "hardboiled_revision": HARDBOILED_REVISION,
            "sidecar_revision": SIDECAR_REVISION,
            "egglog_revision": EGGLOG_REVISION,
            "rust_toolchain": "1.92.0",
            "cmake_version": "3.31.10",
            "host": {"system": platform.system(), "machine": platform.machine()},
            "scripts": {
                path: sha256_file(ROOT / path)
                for path in (
                    "scripts/reproduction_prepare_hardboiled.py",
                    "scripts/reproduction_prepare_misaal.py",
                    "scripts/reproduction_process.py",
                    "benchmarking/pilot.py",
                    "benchmarking/memory_guard.py",
                )
            },
            "source_patches": ["sidecar-workspace-isolation"],
            "device_execution": False,
        },
    )
    write_json(directory / "toolchain.json", inspect_llvm(preparation, llvm))
    (directory / "sources").mkdir()
    checkout = acquire_source(
        preparation, "HardBoiled", "https://github.com/yihozhang/cgo2026-hardboiled-artifact.git", HARDBOILED_REVISION
    )
    sidecar = acquire_source(
        preparation, "sidecar", "https://github.com/yihozhang/egglog-halide-sidecar.git", SIDECAR_REVISION
    )
    link = preparation.step(
        "sidecar-egglog-gitlink", ["git", "ls-tree", "HEAD", "egglog"], cwd=sidecar, timeout=30
    ).strip()
    if link != f"160000 commit {EGGLOG_REVISION}\tegglog":
        raise ValueError("real sidecar Egglog gitlink differs from inspected pin")
    preparation.step(
        "sidecar-submodule",
        [
            "git",
            "-c",
            "url.https://github.com/.insteadOf=git@github.com:",
            "submodule",
            "update",
            "--init",
            "--depth",
            "1",
        ],
        cwd=sidecar,
    )
    if (
        preparation.step(
            "sidecar-egglog-head", ["git", "rev-parse", "HEAD"], cwd=sidecar / "egglog", timeout=30
        ).strip()
        != EGGLOG_REVISION
    ):
        raise ValueError("sidecar Egglog checkout mismatch")
    manifest = sidecar / "Cargo.toml"
    before = manifest.read_text()
    if "[workspace]" in before:
        raise ValueError("pinned sidecar no longer needs workspace isolation")
    preparation.patch(
        manifest, [(before, before + '\n[workspace]\nexclude = ["egglog"]\n')], "sidecar-workspace-isolation"
    )
    rust_version = preparation.step("rust-version", ["rustc", "+1.92.0", "--version", "--verbose"], timeout=30)
    if "host: aarch64-apple-darwin" not in rust_version:
        raise ValueError("Rust toolchain does not match the native arm64 host")
    rust_files = {}
    for name in ("rustc", "cargo"):
        executable = Path(
            preparation.step(f"{name}-path", ["rustup", "which", "--toolchain", "1.92.0", name], timeout=30).strip()
        )
        rust_files[str(executable.resolve())] = sha256_file(executable)
    write_json(directory / "rust-toolchain.json", {"version": rust_version, "files": rust_files})
    preparation.step("cargo-version", ["cargo", "+1.92.0", "--version", "--verbose"], timeout=30)
    cargo_target = directory / "sidecar-target"
    preparation.step(
        "sidecar-build",
        [
            "cargo",
            "+1.92.0",
            "build",
            "--manifest-path",
            str(sidecar / "Cargo.toml"),
            "--locked",
            "--jobs",
            "1",
            "--target-dir",
            str(cargo_target),
            "--bin",
            "egglog-halide-sidecar",
        ],
        cwd=sidecar,
        timeout=1800,
    )
    build = directory / "halide-build"
    preparation.step(
        "halide-configure",
        [
            *CMAKE,
            "-S",
            str(checkout),
            "-B",
            str(build),
            "-G",
            "Unix Makefiles",
            "-DCMAKE_BUILD_TYPE=Release",
            f"-DHalide_LLVM_ROOT={llvm}",
            f"-DLLVM_DIR={llvm}/lib/cmake/llvm",
            f"-DClang_DIR={llvm}/lib/cmake/clang",
            f"-DLLD_DIR={llvm}/lib/cmake/lld",
            f"-DCMAKE_C_COMPILER={llvm}/bin/clang",
            f"-DCMAKE_CXX_COMPILER={llvm}/bin/clang++",
            "-DCMAKE_EXPORT_COMPILE_COMMANDS=ON",
            "-DHalide_LLVM_SHARED_LIBS=ON",
            "-DBUILD_SHARED_LIBS=ON",
            "-DHalide_USE_FETCHCONTENT=OFF",
            "-DHalide_WASM_BACKEND=OFF",
            "-DWITH_TESTS=OFF",
            "-DWITH_PYTHON_BINDINGS=OFF",
            "-DWITH_TUTORIALS=OFF",
            "-DWITH_DOCS=OFF",
            "-DWITH_UTILS=OFF",
            "-DWITH_AUTOSCHEDULERS=OFF",
            "-DWITH_SERIALIZATION=OFF",
            "-DWITH_PACKAGING=OFF",
        ],
    )
    commands = json.loads((build / "compile_commands.json").read_text())
    selected = [entry for entry in commands if Path(entry["file"]).name == "ExtractTileOperations.cpp"]
    if len(selected) != 1 or any(
        f"-DWITH_{target.upper()}" not in selected[0]["command"] for target in REQUIRED_TARGETS
    ):
        raise ValueError("configured Halide omits a required codegen target")
    preparation.step(
        "halide-build", [*CMAKE, "--build", str(build), "--target", "Halide", "--parallel", "1"], timeout=1800
    )
    return write_canary_settings(directory, checkout, build, cargo_target / "debug/egglog-halide-sidecar", llvm)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--storage", type=Path, default=ROOT / "benchmarks/local/reproduction/prerequisites/hardboiled-b99cf0c"
    )
    parser.add_argument("--lock", type=Path, default=ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock")
    parser.add_argument("--llvm", type=Path, default=LLVM)
    args = parser.parse_args()
    with exclusive_job(args.lock.resolve()):
        directory = args.storage.resolve() / f"attempt-{datetime.now(UTC):%Y%m%dT%H%M%SZ}-{uuid.uuid4().hex[:8]}"
        directory.mkdir(parents=True)
        print(f"HEAVY_START {directory}", flush=True)
        summary: dict[str, Any] = {"attempt": str(directory), "started_at": datetime.now(UTC).isoformat()}
        try:
            settings = prepare(directory, args.llvm.resolve())
            summary.update(status="canary-ready", settings=str(settings), settings_sha256=sha256_file(settings))
        except BaseException as error:
            summary.update(status="failed", reason=str(error))
            with (directory / "failure.txt").open("x") as output:
                output.write(traceback.format_exc())
            raise
        finally:
            summary["finished_at"] = datetime.now(UTC).isoformat()
            write_json(directory / "summary.json", summary)
            print(f"HEAVY_FINISH {directory}: {summary['status']}", flush=True)


if __name__ == "__main__":
    main()
