"""Prepare DialEgg's pinned original cost-action backend and native LLVM18 inputs.

The API uses its caller's heavy-job slot; the CLI alone acquires the shared lock.
The existing capture adapter continues to build and instrument the small frontend
per parent. This preparer performs no optimization, benchmark or target execution.
"""

from __future__ import annotations

import argparse
import json
import platform
import shutil
import tarfile
import tomllib
from pathlib import Path
from typing import Any

from scripts.reproduction_process import exclusive_job
from scripts.source_tools import Preparation, acquire_source, sha256_file, write_json

ROOT = Path(__file__).resolve().parents[1]
DIALEGG_REVISION = "4d0d522e98c15becdc5e7d711348cb0891ff0d44"
BACKEND_REVISION = "b6e1c96ed7335366e90056ea0a24ef425dfbb8fb"
BACKEND_ARCHIVE_SHA256 = "bee6dc3afa05fcbedc4246cf71ef25c6693745f4013abbc4381aa3b909c9e070"
BACKEND_MANIFEST_SHA256 = "285072ca24f3f7cc88c2a022b7451902e41ca80b3ab7cc2ca9131e16af16d2c3"
BACKEND_LOCK_SHA256 = "d40ef351e9bc73acd0b525245acf5a285d084df8763309baf978d0bab8f7286c"
LLVM = Path("/opt/homebrew/opt/llvm@18")


def unpack_backend(archive: Path, checkout: Path) -> dict[str, str]:
    """Keep the original backend workspace and fail on source/archive drift."""
    if sha256_file(archive) != BACKEND_ARCHIVE_SHA256:
        raise ValueError("backend archive differs from the retained cost-action build")
    files: dict[str, str] = {}
    with tarfile.open(archive) as tree:
        members = tree.getmembers()
        if sum(member.size for member in members) > 64 * 1024**2:
            raise ValueError("backend source exceeds the preparation size limit")
        for member in members:
            parts = Path(member.name).parts
            if not parts or parts[0] != f"egg-smol-{BACKEND_REVISION}" or ".." in parts:
                raise ValueError("unexpected backend archive member path")
            if member.isdir():
                continue
            if not member.isfile() or len(parts) < 2:
                raise ValueError("unexpected backend archive member type")
            relative = Path(*parts[1:])
            if relative.as_posix() in files:
                raise ValueError("duplicate backend archive member")
            stream = tree.extractfile(member)
            assert stream is not None
            destination = checkout / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            with destination.open("xb") as output:
                shutil.copyfileobj(stream, output)
            destination.chmod(member.mode & 0o777)
            files[relative.as_posix()] = sha256_file(destination)
    if files.get("Cargo.toml") != BACKEND_MANIFEST_SHA256 or files.get("Cargo.lock") != BACKEND_LOCK_SHA256:
        raise ValueError("backend manifest/lock differs from the successful original-workspace build")
    if "workspace" not in tomllib.loads((checkout / "Cargo.toml").read_text()):
        raise ValueError("original cost-action backend workspace is missing")
    return files


def linked_libraries(preparation: Preparation, artifacts: list[Path], llvm: Path) -> dict[str, Any]:
    """Resolve the native dynamic dependency closure, retaining system install names."""
    pending = list(artifacts)
    visited: set[Path] = set()
    files: dict[str, str] = {}
    system: set[str] = set()
    while pending:
        artifact = pending.pop().resolve()
        if artifact in visited:
            continue
        visited.add(artifact)
        output = preparation.step(f"linked-libraries-{len(visited):03}", ["otool", "-L", str(artifact)], timeout=30)
        for line in output.splitlines()[1:]:
            name = line.strip().split(" (", 1)[0]
            if name.startswith(("/usr/lib/", "/System/Library/")):
                # These may live only in the macOS dyld shared cache.
                system.add(name)
                continue
            if name.startswith("@rpath/"):
                dependency = llvm / "lib" / name.removeprefix("@rpath/")
            elif name.startswith("@loader_path/"):
                dependency = artifact.parent / name.removeprefix("@loader_path/")
            elif name.startswith("@executable_path/"):
                dependency = artifact.parent / name.removeprefix("@executable_path/")
            elif name.startswith("/"):
                dependency = Path(name)
            else:
                raise ValueError(f"unrecognized native dependency in {artifact}: {name}")
            if not dependency.is_file():
                raise ValueError(f"unresolved native dependency: {artifact}: {name}")
            dependency = dependency.resolve()
            files[str(dependency)] = sha256_file(dependency)
            pending.append(dependency)
    return {"files": files, "system_install_names": sorted(system)}


def prepare_dialegg(
    output: Path, engine: Path, *, build_root: Path | None = None, timeout_sec: int = 600
) -> dict[str, Any]:
    """Acquire actual pinned sources/build backend; emit existing-adapter settings."""
    output, engine = output.resolve(), engine.resolve()
    build_root = build_root.resolve() if build_root else output / "cargo-target"
    durable = (ROOT / "benchmarks/local/reproduction").resolve()
    if not output.is_relative_to(durable):
        raise ValueError(f"DialEgg source and evidence must remain below {durable}")
    if output.exists() or build_root.exists():
        raise ValueError("preparation requires fresh output and build directories")
    if not engine.is_file():
        raise ValueError(f"ordinary replay engine is missing: {engine}")
    if (platform.system(), platform.machine()) != ("Darwin", "arm64"):
        raise ValueError("this recipe is for native Apple Silicon with Homebrew LLVM18")
    if timeout_sec <= 0:
        raise ValueError("step timeout must be positive")
    output.mkdir(parents=True)
    preparation = Preparation(output)
    record: dict[str, Any] = {
        "family": "dialegg",
        "revision": DIALEGG_REVISION,
        "backend_revision": BACKEND_REVISION,
        "status": "blocked",
        "reason": None,
        "output": str(output),
        "build_root": str(build_root),
        "device_execution": False,
        "benchmark_execution": False,
        "source_patches": [],
        "rust_version": "1.88.0",
        "frontend_preparation": "existing capture adapter builds frontend per parent",
    }
    try:
        tools = {name: shutil.which(name) for name in ("curl", "git", "rustc", "cargo", "rustup", "otool")}
        if missing := [name for name, path in tools.items() if path is None]:
            raise ValueError(f"missing original native build prerequisites: {missing}")
        identities = {str(Path(path).resolve()): sha256_file(Path(path)) for path in tools.values() if path}
        llvm_files = [
            LLVM / relative
            for relative in (
                "bin/clang++",
                "bin/llvm-config",
                "lib/libMLIROptLib.a",
                "lib/libMLIR.dylib",
                "lib/libLLVM.dylib",
                "include/mlir/IR/MLIRContext.h",
                "lib/cmake/llvm/LLVMConfig.cmake",
                "lib/cmake/mlir/MLIRConfig.cmake",
            )
        ]
        for path in llvm_files:
            if not path.is_file():
                raise ValueError(f"missing LLVM18/MLIR frontend prerequisite: {path}")
            identities[str(path.resolve())] = sha256_file(path)
        if (
            preparation.step("llvm-version", [str(LLVM / "bin/llvm-config"), "--version"], timeout=30).strip()
            != "18.1.8"
        ):
            raise ValueError("LLVM version differs from the demonstrated native 18.1.8 environment")
        rust = preparation.step("rust-version", ["rustc", "+1.88.0", "--version", "--verbose"], timeout=30)
        if "rustc 1.88.0" not in rust or "host: aarch64-apple-darwin" not in rust:
            raise ValueError("Rust differs from native aarch64-apple-darwin 1.88.0")
        for name in ("rustc", "cargo"):
            actual = Path(
                preparation.step(f"{name}-path", ["rustup", "which", "--toolchain", "1.88.0", name], timeout=30).strip()
            )
            identities[str(actual.resolve())] = sha256_file(actual)
        for relative in (
            "scripts/reproduction_prepare_dialegg.py",
            "scripts/source_tools.py",
            "scripts/reproduction_prepare_misaal.py",
            "scripts/reproduction_process.py",
            "scripts/dialegg_capture.py",
            "scripts/dialegg_compat.py",
            "process_guard.py",
        ):
            identities[str(ROOT / relative)] = sha256_file(ROOT / relative)
        identities[str(engine)] = sha256_file(engine)
        write_json(output / "tool-identities.json", identities)
        with (output / "preparer.py").open("xb") as snapshot:
            snapshot.write(Path(__file__).read_bytes())
        (output / "sources").mkdir()
        source = acquire_source(
            preparation, "dialegg", "https://github.com/AzizZayed/dialegg-cgo-artifact.git", DIALEGG_REVISION
        )
        frontend_files = {
            str(path.relative_to(source)): sha256_file(path)
            for path in sorted(source.rglob("*"))
            if path.is_file() and ".git" not in path.relative_to(source).parts
        }
        if not all(
            relative in frontend_files
            for relative in ("src/base.egg", "src/EqualitySaturationPass.cpp", "src/Egglog.cpp")
        ):
            raise ValueError("pinned DialEgg checkout lacks required frontend/rule files")
        write_json(output / "dialegg-source.json", {"revision": DIALEGG_REVISION, "files": frontend_files})
        archive = output / "cost-action-source.tar.gz"
        url = f"https://codeload.github.com/saulshanabrook/egg-smol/tar.gz/{BACKEND_REVISION}"
        preparation.step(
            "backend-download",
            ["curl", "--fail", "--location", "--max-filesize", str(16 * 1024**2), "--output", str(archive), url],
            timeout=timeout_sec,
        )
        backend_source = output / "sources/cost-action-egglog"
        backend_files = unpack_backend(archive, backend_source)
        write_json(
            output / "backend-source.json",
            {
                "url": url,
                "revision": BACKEND_REVISION,
                "archive_sha256": BACKEND_ARCHIVE_SHA256,
                "workspace": "original",
                "files": backend_files,
            },
        )
        command = [
            "env",
            f"CARGO_TARGET_DIR={build_root}",
            "CARGO_PROFILE_DEV_DEBUG=0",
            "CARGO_INCREMENTAL=0",
            "RUSTC_WRAPPER=",
            "cargo",
            "+1.88.0",
            "build",
            "--locked",
            "-j1",
            "--bin",
            "egglog",
        ]
        preparation.step("backend-build", command, cwd=backend_source, timeout=timeout_sec)
        backend = build_root / "debug/egglog"
        if not backend.is_file() or not backend.stat().st_size:
            raise ValueError("successful build omitted the real cost-action Egglog executable")
        if any(
            sha256_file(backend_source / name) != expected
            for name, expected in (("Cargo.toml", BACKEND_MANIFEST_SHA256), ("Cargo.lock", BACKEND_LOCK_SHA256))
        ):
            raise ValueError("build changed the original backend workspace or lockfile")
        libraries = linked_libraries(
            preparation, [backend, LLVM / "bin/clang++", LLVM / "lib/libLLVM.dylib", LLVM / "lib/libMLIR.dylib"], LLVM
        )
        write_json(output / "linked-libraries.json", libraries)
        write_json(output / "build-products.json", {str(backend): sha256_file(backend)})
        settings = {
            "dialegg": {
                "revision": DIALEGG_REVISION,
                "backend_revision": BACKEND_REVISION,
                "paths": {
                    "dialegg_source": str(source),
                    "llvm18_prefix": str(LLVM),
                    "native_egglog": str(backend),
                    "egglog": str(engine),
                },
                "identity_paths": [
                    str(output / name)
                    for name in (
                        "tool-identities.json",
                        "dialegg-source.json",
                        "backend-source.json",
                        "linked-libraries.json",
                        "build-products.json",
                    )
                ]
                + [str(path) for path in llvm_files]
                + list(libraries["files"]),
                "timeout_sec": 300,
            }
        }
        settings_path = output / "settings.json"
        write_json(settings_path, settings)
        record.update(
            status="success",
            settings=str(settings_path),
            settings_sha256=sha256_file(settings_path),
            artifacts={str(backend): sha256_file(backend)},
            reason="Sources/backend ready; capture still builds frontend and runs complete optimization",
        )
    except (OSError, ValueError, RuntimeError, tarfile.TarError) as error:
        record["reason"] = str(error)
        receipts = sorted(preparation.logs.glob("*.result.json"))
        if receipts:
            status = json.loads(receipts[-1].read_text()).get("status")
            if status != "success":
                record["status"] = status
        if "guard refused" in str(error):
            record["status"] = "resource-stopped"
    finally:
        write_json(output / "preparation.json", record)
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path, required=True, help="Fresh directory below benchmarks/local/reproduction"
    )
    parser.add_argument("--egglog", type=Path, default=ROOT / "target/release/egglog-experimental")
    parser.add_argument("--build-root", type=Path, help="Fresh optional disposable backend target directory")
    parser.add_argument("--timeout-sec", type=int, default=600)
    args = parser.parse_args()
    with exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        record = prepare_dialegg(args.output, args.egglog, build_root=args.build_root, timeout_sec=args.timeout_sec)
    print(json.dumps({key: record.get(key) for key in ("status", "reason", "settings")}, indent=2))
    return 0 if record["status"] == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
