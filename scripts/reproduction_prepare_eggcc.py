"""Repeat the proven native Eggcc/Statewalk build with durable source and evidence.

The callable API uses its caller's exclusive job slot. Only the CLI takes the
shared lock. This prepares the real compiler and Tiger; it runs no benchmark,
replaces no extractor, and does not install or invoke Gurobi.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import shutil
import tarfile
import tomllib
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
CORE_REVISION = "ebba7bb902bdc1b0f377b6bb22c06ac305912674"
CORE_URL = "https://github.com/saulshanabrook/egg-smol.git"
CORE_SOURCE = f"git+{CORE_URL}?branch=codex%2Fsplit-scheduler-can-stop-report#{CORE_REVISION}"
CORE_PACKAGES = {
    "egglog",
    "egglog-ast",
    "egglog-reports",
    "egglog-add-primitive",
    "egglog-bridge",
    "egglog-concurrency",
    "egglog-core-relations",
    "egglog-numeric-id",
    "egglog-union-find",
}
CORE_PINS = {
    "Cargo.lock": "466ad68262801a539f11e04a4537d9347c02019d25c480cefed62e67bc31b080",
    "core-relations/src/hash_index/mod.rs": "78e934b68beb13f9090e9a691f0dfa206f0e8a2535c73b14da7faa21870d7e90",
    "core-relations/src/hash_index/tests.rs": "772edd5daa58c7e1504b38b9b4a46eda0b8c69d4cd98076fe11a6a612cc08444",
}
REPAIR_REVISION = "201579afd2b8b646fa518d3065bd319d1a084eba"
REPAIR_SHA256 = "84e6de41c4d7e4741773f58ed271f80072fb5ead1ed0c3b26ad6b0a591e93495"
REPAIR_FIXTURE = "benchmarks/reproduction/fixtures/eggcc-core-row-order.patch"
REGRESSION = "hash_index::tests::multi_column_column_index_rebuild_orders_each_value_by_row"


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


def repaired_lock(original: str) -> str:
    """Change only the nine pinned core package sources; never resolve new versions."""
    packages = tomllib.loads(original)["package"]
    core = [row for row in packages if row.get("source") == CORE_SOURCE]
    if {row["name"] for row in core} != CORE_PACKAGES or len(core) != len(CORE_PACKAGES):
        raise ValueError("original lock does not contain exactly the nine pinned core packages")
    if any(row["version"] != "2.0.0" or "checksum" in row for row in core):
        raise ValueError("original core package identity changed")
    line = f'source = "{CORE_SOURCE}"\n'
    if original.count(line) != len(CORE_PACKAGES):
        raise ValueError("unexpected core source encoding in original lock")
    derived = original.replace(line, "")
    expected = [
        {key: value for key, value in row.items() if key != "source"} if row in core else row for row in packages
    ]
    if tomllib.loads(derived)["package"] != expected:
        raise ValueError("derived lock changes unrelated dependency identities")
    return derived


def seed_cargo_cache(preparation: Preparation, cache: Path, locks: list[Path], *, timeout_sec: int) -> Path:
    """Copy only immutable locked archives/index entries and independent Git objects.

    Cargo may download missing dependencies into the new home. Original cache
    paths are never passed to Cargo, including for its package-cache locks.
    """
    home = preparation.directory / "cargo-home"
    home.mkdir()
    copied: dict[str, str] = {}
    for lock in locks:
        for package in tomllib.loads(lock.read_text())["package"]:
            if package.get("source") != "registry+https://github.com/rust-lang/crates.io-index":
                continue
            name, version = package["name"], package["version"]
            for source in sorted((cache / "registry/cache").glob(f"*/{name}-{version}.crate")):
                if source.is_symlink() or sha256_file(source) != package["checksum"]:
                    raise ValueError(f"cached crate differs from locked checksum: {source}")
                index = cache / "registry/index" / source.parent.name
                key = name.lower()
                relative = (
                    f"{len(key)}/{key}"
                    if len(key) < 3
                    else (f"3/{key[0]}/{key}" if len(key) == 3 else f"{key[:2]}/{key[2:4]}/{key}")
                )
                for entry in (source, index / "config.json", index / ".cache" / relative):
                    if not entry.exists():
                        continue
                    if entry.is_symlink() or not entry.is_file():
                        raise ValueError(f"cache seed must be an ordinary file: {entry}")
                    destination = home / entry.relative_to(cache)
                    if not destination.exists():
                        destination.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(entry, destination)
                        copied[str(entry)] = sha256_file(destination)
                break
    for name in (
        "egglog-experimental-e48206cd5b150391",
        "bril-36edbe08a8ae21f1",
        "inkwell-511a88971ace534e",
        "egg-smol-65fdca4a5529f39b",
    ):
        source = cache / "git/db" / name
        if not source.exists():
            continue
        if source.is_symlink() or any(path.is_symlink() for path in source.rglob("*")):
            raise ValueError("Git cache seed may not contain symlinks")
        if (source / "objects/info/alternates").exists():
            raise ValueError("Git cache seed may not borrow another object store")
        destination = home / "git/db" / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        preparation.step(f"seed-{name}", ["/bin/cp", "-cR", str(source), str(destination)], timeout=timeout_sec)
    write_json(preparation.directory / "cache-seed.json", {"source": str(cache), "files": copied})
    return home


def verify_continuation(previous: Path) -> dict[str, Any]:
    """Bind reuse to the successful original source/build, without writing to it."""
    record: dict[str, Any] = json.loads((previous / "preparation.json").read_text())
    if record.get("status") != "success" or record.get("revision") != REVISION or record.get("core_repair"):
        raise ValueError("continuation requires a successful original unrepaired Eggcc preparation")
    checkout = Path(record["checkout"]).resolve()
    if checkout != previous / "sources/eggcc":
        raise ValueError("previous checkout does not belong to its preparation")
    pins = json.loads((previous / "prepared-source.json").read_text())
    for relative, digest in pins.items():
        path = checkout / relative
        if not path.resolve().is_relative_to(checkout) or path.is_symlink() or sha256_file(path) != digest:
            raise ValueError(f"previous prepared source changed: {relative}")
    products = json.loads((previous / "build-products.json").read_text())
    if products != record["artifacts"]:
        raise ValueError("previous product manifest differs from receipt")
    for name, digest in products.items():
        path = Path(name)
        if path.is_symlink() or sha256_file(path) != digest:
            raise ValueError(f"previous build product changed: {name}")
    if pins.get("Cargo.lock") != LOCK_SHA256 or sha256_file(previous / f"eggcc-{REVISION}.tar.gz") != ARCHIVE_SHA256:
        raise ValueError("previous original archive/lock identity changed")
    return record


def prepare_core(preparation: Preparation, cache: Path, *, timeout_sec: int) -> tuple[Path, dict[str, Any]]:
    """Acquire the exact Git revision and apply the exact upstream correction/test."""
    core = preparation.directory / "sources/egglog-core"
    cached = cache / "git/db/egg-smol-65fdca4a5529f39b"
    if cached.is_dir():
        if (
            cached.is_symlink()
            or (cached / "objects/info/alternates").exists()
            or any(path.is_symlink() for path in cached.rglob("*"))
        ):
            raise ValueError("core Git cache must be independent, without symlinks or alternates")
        preparation.step(
            "core-clone",
            ["git", "clone", "--no-hardlinks", "--no-checkout", str(cached), str(core)],
            timeout=timeout_sec,
        )
    else:
        core.mkdir(parents=True)
        preparation.step("core-init", ["git", "init", str(core)], timeout=30)
        preparation.step(
            "core-fetch", ["git", "fetch", "--depth", "1", CORE_URL, CORE_REVISION], cwd=core, timeout=timeout_sec
        )
    preparation.step("core-checkout", ["git", "checkout", "--detach", CORE_REVISION], cwd=core, timeout=30)
    if preparation.step("core-revision", ["git", "rev-parse", "HEAD"], cwd=core, timeout=30).strip() != CORE_REVISION:
        raise ValueError("acquired core revision differs from the original dependency")
    for relative, digest in CORE_PINS.items():
        if sha256_file(core / relative) != digest:
            raise ValueError(f"core repair source pin changed: {relative}")
    files = preparation.step(
        "core-files", ["git", "ls-tree", "-r", "--name-only", "HEAD"], cwd=core, timeout=30
    ).splitlines()
    originals = {relative: sha256_file(core / relative) for relative in files}
    fixture = ROOT / REPAIR_FIXTURE
    if sha256_file(fixture) != REPAIR_SHA256:
        raise ValueError("upstream core correction fixture changed")
    patch = preparation.directory / "core-row-order.patch"
    shutil.copy2(fixture, patch)
    preparation.step("core-patch-check", ["git", "apply", "--check", str(patch)], cwd=core, timeout=30)
    preparation.step("core-patch", ["git", "apply", str(patch)], cwd=core, timeout=30)
    modified = {relative: sha256_file(core / relative) for relative in files}
    if {name for name in files if originals[name] != modified[name]} != set(CORE_PINS) - {"Cargo.lock"}:
        raise ValueError("core repair changed an unexpected source file")
    receipt = {
        "repair": "pr914-row-order-v1",
        "base_revision": CORE_REVISION,
        "source_url": CORE_URL,
        "upstream_commit": REPAIR_REVISION,
        "upstream_url": f"https://github.com/egraphs-good/egglog/commit/{REPAIR_REVISION}",
        "patch_sha256": REPAIR_SHA256,
        "original_files": originals,
        "prepared_files": modified,
        "regression": REGRESSION,
        "proof_validation": False,
        "benchmark_execution": False,
    }
    write_json(preparation.directory / "core-repair.json", receipt)
    return core, receipt


def prepare_eggcc(
    output: Path,
    engine: Path,
    *,
    build_root: Path | None = None,
    timeout_sec: int = 600,
    continue_from: Path | None = None,
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
    previous = continue_from.resolve() if continue_from else None
    if previous and (
        not previous.is_relative_to(durable) or output.is_relative_to(previous) or build_root.is_relative_to(previous)
    ):
        raise ValueError("continuation requires a separate retained preparation below reproduction storage")
    saved = verify_continuation(previous) if previous else None
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
        "core_repair": "pr914-row-order-v1",
        "build_profile": {
            "name": "dev",
            "opt_level": 3,
            "debug": 0,
            "debug_assertions": True,
            "overflow_checks": True,
            "incremental": False,
            "cargo_jobs": 1,
        },
    }
    try:
        tools = {name: shutil.which(name) for name in ("curl", "cargo", "rustc", "rustup", "g++", "git")}
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
            REPAIR_FIXTURE,
        ):
            identities[str(ROOT / relative)] = sha256_file(ROOT / relative)
        identities[str(engine)] = sha256_file(engine)
        write_json(output / "tool-identities.json", identities)
        with (output / "preparer.py").open("xb") as snapshot:
            snapshot.write(Path(__file__).read_bytes())
        archive = output / f"eggcc-{REVISION}.tar.gz"
        url = f"https://codeload.github.com/egraphs-good/eggcc/tar.gz/{REVISION}"
        if previous:
            shutil.copy2(previous / archive.name, archive)
            write_json(
                output / "continuation.json",
                {
                    "previous": str(previous),
                    "receipt_sha256": sha256_file(previous / "preparation.json"),
                    "prepared_source_sha256": sha256_file(previous / "prepared-source.json"),
                    "products_sha256": sha256_file(previous / "build-products.json"),
                    "reuse": "pinned original archive and private copy-on-write target clone",
                },
            )
        else:
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
        cache = Path(os.environ.get("CARGO_HOME", Path.home() / ".cargo")).resolve()
        core, repair = prepare_core(preparation, cache, timeout_sec=timeout_sec)
        before = manifest.read_text()
        preparation.patch(
            manifest,
            [
                (
                    before,
                    before + f'\n[patch."{CORE_URL}"]\n'
                    'egglog = { path = "../egglog-core" }\n'
                    'egglog-ast = { path = "../egglog-core/egglog-ast" }\n'
                    'egglog-reports = { path = "../egglog-core/egglog-reports" }\n',
                )
            ],
            "core-dependency-override",
        )
        lock = checkout / "Cargo.lock"
        original_lock = lock.read_text()
        preparation.patch(lock, [(original_lock, repaired_lock(original_lock))], "core-lock-identities")
        derived_lock_sha256 = sha256_file(lock)
        cargo_home = seed_cargo_cache(preparation, cache, [lock, core / "Cargo.lock"], timeout_sec=timeout_sec)
        if saved:
            old_target = Path(saved["build_root"]).resolve()
            if Path(saved["binary"]).resolve() != old_target / "debug/eggcc" or build_root.is_relative_to(old_target):
                raise ValueError("continuation target does not match the retained compiler")
            if any(path.is_symlink() for path in old_target.rglob("*")):
                raise ValueError("continuation target may not contain symlinks")
            build_root.parent.mkdir(parents=True, exist_ok=True)
            preparation.step("clone-target", ["/bin/cp", "-cR", str(old_target), str(build_root)], timeout=timeout_sec)
        prepared_files = {relative: sha256_file(checkout / relative) for relative in originals}
        write_json(output / "prepared-source.json", prepared_files)
        with (output / "Cargo.lock").open("xb") as snapshot:
            snapshot.write((checkout / "Cargo.lock").read_bytes())
        environment = [
            "env",
            f"LLVM_SYS_180_PREFIX={LLVM}",
            "LIBRARY_PATH=/opt/homebrew/lib",
            f"CARGO_TARGET_DIR={build_root}",
            "CARGO_PROFILE_DEV_DEBUG=0",
            "CARGO_PROFILE_DEV_OPT_LEVEL=3",
            "CARGO_PROFILE_DEV_DEBUG_ASSERTIONS=true",
            "CARGO_PROFILE_DEV_OVERFLOW_CHECKS=true",
            "CARGO_INCREMENTAL=0",
            "RUSTC_WRAPPER=",
            f"CARGO_HOME={cargo_home}",
        ]
        regression = environment + [
            "cargo",
            "+1.88.0",
            "test",
            "--profile",
            "dev",
            "--manifest-path",
            str(core / "Cargo.toml"),
            "--locked",
            "-j1",
            "-p",
            "egglog-core-relations",
            "--lib",
            REGRESSION,
            "--",
            "--exact",
        ]
        result = preparation.step("core-regression", regression, cwd=core, timeout=timeout_sec)
        if "test result: ok. 1 passed; 0 failed;" not in result:
            raise ValueError("upstream core regression did not execute exactly one passing test")
        command = environment + [
            "cargo",
            "+1.88.0",
            "build",
            "--profile",
            "dev",
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
        if saved and products[str(binary)] == saved["artifacts"][saved["binary"]]:
            raise ValueError("repair build retained the original uncorrected compiler bytes")
        if (
            products[str(checkout / "Cargo.lock")] != derived_lock_sha256
            or sha256_file(core / "Cargo.lock") != CORE_PINS["Cargo.lock"]
        ):
            raise ValueError("locked native gates changed a pinned dependency lockfile")
        if any(sha256_file(core / relative) != digest for relative, digest in repair["prepared_files"].items()):
            raise ValueError("native build changed the repaired core sources")
        if any(sha256_file(checkout / relative) != digest for relative, digest in prepared_files.items()):
            raise ValueError("native build changed the prepared Eggcc sources")
        if previous:
            verify_continuation(previous)
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
                    str(output / "core-repair.json"),
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
            core_repair_receipt=str(output / "core-repair.json"),
            original_lock_sha256=LOCK_SHA256,
            derived_lock_sha256=derived_lock_sha256,
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
    parser.add_argument("--continue-from", type=Path, help="Verified original preparation; reuse only private copies")
    args = parser.parse_args()
    with exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        record = prepare_eggcc(
            args.output,
            args.egglog,
            build_root=args.build_root,
            timeout_sec=args.timeout_sec,
            continue_from=args.continue_from,
        )
    print(json.dumps({key: record.get(key) for key in ("status", "reason", "settings")}, indent=2))
    return 0 if record["status"] == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
