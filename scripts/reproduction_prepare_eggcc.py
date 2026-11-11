"""Repeat the proven native Eggcc/Statewalk build with durable source and evidence.

The callable API uses its caller's exclusive job slot. Only the CLI takes the
shared lock. This prepares the real compiler and Tiger; it runs no benchmark,
replaces no extractor, and does not install or invoke Gurobi.
"""

from __future__ import annotations

import argparse
import json
import platform
import shutil
import tarfile
from pathlib import Path
from typing import Any

from scripts.eggcc_churchroad_complete import patched_eggcc_sources
from scripts.reproduction_prepare_misaal import Preparation, sha256_file, write_json
from scripts.reproduction_process import exclusive_job

ROOT = Path(__file__).resolve().parents[1]
REVISION = "16be0063133ef0b8ba21cd75ee377002dc3ecbed"
ARCHIVE_SHA256 = "ced650bba88d7c12ce8091281660a26117ba83c68ad23281289c289ef129558c"
LOCK_SHA256 = "271911b11aa595cb22c9bb55915580a6afa7bec3dc8ccd0bf6e284381c916272"
LLVM = Path("/opt/homebrew/opt/llvm@18")


def unpack_source(archive: Path, checkout: Path) -> dict[str, str]:
    """Reject unexpected archive contents and retain exact original source hashes."""
    if sha256_file(archive) != ARCHIVE_SHA256:
        raise ValueError("Eggcc archive differs from the pinned successful build receipt")
    files: dict[str, str] = {}
    with tarfile.open(archive) as tree:
        members = tree.getmembers()
        if sum(member.size for member in members) > 256 * 1024**2:
            raise ValueError("source archive exceeds the preparation size limit")
        for member in members:
            parts = Path(member.name).parts
            if not parts or parts[0] != f"eggcc-{REVISION}" or ".." in parts:
                raise ValueError("unexpected source archive member path")
            if member.isdir():
                continue
            if not member.isfile() or len(parts) < 2:
                raise ValueError("unexpected non-file source archive member")
            relative = Path(*parts[1:])
            if relative.as_posix() in files:
                raise ValueError("duplicate source archive member")
            stream = tree.extractfile(member)
            assert stream is not None
            destination = checkout / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            with destination.open("xb") as output:
                shutil.copyfileobj(stream, output)
            destination.chmod(member.mode & 0o777)
            files[relative.as_posix()] = sha256_file(destination)
    if files.get("Cargo.lock") != LOCK_SHA256:
        raise ValueError("pinned Eggcc lockfile differs from successful build receipt")
    return files


def prepare_eggcc(
    output: Path, engine: Path, *, build_root: Path | None = None, timeout_sec: int = 600
) -> dict[str, Any]:
    """Prepare one fresh native compiler, leaving configuration blockers explicit.

    Caller owns the heavy slot; there is deliberately no nested lock here.
    Original sources, patches, settings and all receipts stay under benchmarks/local.
    ``build_root`` may point to a fresh disposable Cargo target directory.
    """
    output, engine = output.resolve(), engine.resolve()
    build_root = build_root.resolve() if build_root else output / "cargo-target"
    durable = (ROOT / "benchmarks/local/reproduction").resolve()
    if not output.is_relative_to(durable):
        raise ValueError(f"Eggcc source and evidence must remain below {durable}")
    if output.exists() or build_root.exists():
        raise ValueError("preparation requires fresh output and build directories")
    if not engine.is_file():
        raise ValueError(f"ordinary replay engine is missing: {engine}")
    if (platform.system(), platform.machine()) != ("Darwin", "arm64"):
        raise ValueError("this proven recipe is for native Apple Silicon with Homebrew LLVM18")
    if timeout_sec <= 0:
        raise ValueError("step timeout must be positive")
    output.mkdir(parents=True)
    preparation = Preparation(output)
    blocker = {
        "configuration": {"native_options": ["--tiger-ilp", "--ilp-solver", "gurobi"]},
        "status": "blocked",
        "reason": "The measured Gurobi lane lacks gurobi_cl; user reports no installation or usable license access",
        "evidence": "benchmarks/reproduction/eggcc-gurobi.md",
        "extractor_substitution": False,
    }
    record: dict[str, Any] = {
        "family": "eggcc",
        "revision": REVISION,
        "status": "blocked",
        "reason": None,
        "device_execution": False,
        "benchmark_execution": False,
        "configuration_blockers": [blocker],
        "output": str(output),
        "build_root": str(build_root),
        "rust_version": "1.88.0",
    }
    try:
        tools = {name: shutil.which(name) for name in ("curl", "cargo", "rustc", "rustup", "g++")}
        if missing := [name for name, path in tools.items() if path is None]:
            raise ValueError(f"missing original native build prerequisites: {missing}")
        identities = {str(Path(path).resolve()): sha256_file(Path(path)) for path in tools.values() if path}
        for relative in ("bin/llvm-config", "lib/libLLVM.dylib"):
            path = LLVM / relative
            identities[str(path.resolve())] = sha256_file(path)
        if (
            preparation.step("llvm-version", [str(LLVM / "bin/llvm-config"), "--version"], timeout=30).strip()
            != "18.1.8"
        ):
            raise ValueError("native LLVM version differs from the successful 18.1.8 environment")
        rust_version = preparation.step("rust-version", ["rustc", "+1.88.0", "--version", "--verbose"], timeout=30)
        if not rust_version.startswith("rustc 1.88.0 ") and not rust_version.startswith("rustc 1.88.0\n"):
            raise ValueError("Rust compiler differs from the successful 1.88.0 environment")
        if "host: aarch64-apple-darwin" not in rust_version:
            raise ValueError("Rust toolchain does not match native Apple Silicon")
        for name in ("rustc", "cargo"):
            actual = Path(
                preparation.step(f"{name}-path", ["rustup", "which", "--toolchain", "1.88.0", name], timeout=30).strip()
            )
            identities[str(actual.resolve())] = sha256_file(actual)
        for relative in (
            "scripts/reproduction_prepare_eggcc.py",
            "scripts/reproduction_prepare_misaal.py",
            "scripts/eggcc_churchroad_complete.py",
            "scripts/reproduction_process.py",
            "benchmarking/pilot.py",
            "benchmarking/memory_guard.py",
        ):
            identities[str(ROOT / relative)] = sha256_file(ROOT / relative)
        identities[str(engine)] = sha256_file(engine)
        write_json(output / "tool-identities.json", identities)
        with (output / "preparer.py").open("xb") as snapshot:
            snapshot.write(Path(__file__).read_bytes())
        archive = output / f"eggcc-{REVISION}.tar.gz"
        url = f"https://codeload.github.com/egraphs-good/eggcc/tar.gz/{REVISION}"
        preparation.step(
            "download-source",
            ["curl", "--fail", "--location", "--max-filesize", str(64 * 1024**2), "--output", str(archive), url],
            timeout=timeout_sec,
        )
        checkout = output / "sources/eggcc"
        originals = unpack_source(archive, checkout)
        write_json(output / "original-source.json", {"url": url, "archive_sha256": ARCHIVE_SHA256, "files": originals})
        manifest = checkout / "Cargo.toml"
        before = manifest.read_text()
        if "[workspace]" in before:
            raise ValueError("pinned source no longer needs the isolated-workspace build patch")
        preparation.patch(manifest, [(before, before + "\n[workspace]\n")], "workspace-isolation")
        for relative, content in patched_eggcc_sources(checkout).items():
            source = checkout / relative
            preparation.patch(source, [(source.read_text(), content)], "native-capture-" + relative.replace("/", "-"))
        write_json(
            output / "prepared-source.json", {relative: sha256_file(checkout / relative) for relative in originals}
        )
        with (output / "Cargo.lock").open("xb") as lock:
            lock.write((checkout / "Cargo.lock").read_bytes())
        command = [
            "env",
            f"LLVM_SYS_180_PREFIX={LLVM}",
            "LIBRARY_PATH=/opt/homebrew/lib",
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
            "eggcc",
        ]
        preparation.step("build", command, cwd=checkout, timeout=timeout_sec)
        binary = build_root / "debug/eggcc"
        # Upstream build.rs emits Tiger here, independently of CARGO_TARGET_DIR.
        tiger = checkout / "target/debug/tiger"
        for product in (binary, tiger):
            if not product.is_file() or not product.stat().st_size:
                raise ValueError(f"successful build omitted required native executable: {product}")
        products = {str(path): sha256_file(path) for path in (binary, tiger, checkout / "Cargo.lock")}
        if products[str(checkout / "Cargo.lock")] != LOCK_SHA256:
            raise ValueError("locked build changed the pinned dependency lockfile")
        write_json(output / "build-products.json", products)
        settings = {
            "eggcc": {
                "revision": REVISION,
                "paths": {"checkout": str(checkout), "binary": str(binary), "egglog": str(engine)},
                "identity_paths": [
                    str(LLVM / "lib/libLLVM.dylib"),
                    str(output / "tool-identities.json"),
                    str(output / "prepared-source.json"),
                    str(output / "build-products.json"),
                    str(tiger),
                ],
                "timeout_sec": 300,
                "configuration_blockers": [blocker],
            }
        }
        settings_path = output / "settings.json"
        write_json(settings_path, settings)
        record.update(
            status="success",
            settings=str(settings_path),
            settings_sha256=sha256_file(settings_path),
            checkout=str(checkout),
            binary=str(binary),
            tiger=str(tiger),
            artifacts=products,
            reason="Native compiler prepared; actual optimization/replay remains a separate stage",
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
    parser.add_argument("--build-root", type=Path, help="Fresh optional disposable Cargo target directory")
    parser.add_argument("--timeout-sec", type=int, default=600)
    args = parser.parse_args()
    with exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        record = prepare_eggcc(args.output, args.egglog, build_root=args.build_root, timeout_sec=args.timeout_sec)
    print(json.dumps({key: record.get(key) for key in ("status", "reason", "settings")}, indent=2))
    return 0 if record["status"] == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
