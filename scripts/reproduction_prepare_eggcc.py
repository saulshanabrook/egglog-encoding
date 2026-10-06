"""Build the pinned Eggcc exporter; native Tiger still supplies later passes."""

from __future__ import annotations

import argparse
import json
import platform
from pathlib import Path
from typing import Any

from scripts.reproduction_process import exclusive_job
from scripts.source_tools import Preparation, acquire_source, sha256_file, write_json

ROOT = Path(__file__).resolve().parents[1]
REVISION = "16be0063133ef0b8ba21cd75ee377002dc3ecbed"
LOCK_SHA256 = "271911b11aa595cb22c9bb55915580a6afa7bec3dc8ccd0bf6e284381c916272"
LLVM = Path("/opt/homebrew/opt/llvm@18")
CORE_REVISION = "ebba7bb902bdc1b0f377b6bb22c06ac305912674"
CORE_URL = "https://github.com/saulshanabrook/egg-smol.git"
CORE_PINS = {
    "Cargo.lock": "466ad68262801a539f11e04a4537d9347c02019d25c480cefed62e67bc31b080",
    "core-relations/src/hash_index/mod.rs": "78e934b68beb13f9090e9a691f0dfa206f0e8a2535c73b14da7faa21870d7e90",
    "core-relations/src/hash_index/tests.rs": "772edd5daa58c7e1504b38b9b4a46eda0b8c69d4cd98076fe11a6a612cc08444",
}
REPAIR_REVISION = "201579afd2b8b646fa518d3065bd319d1a084eba"
REPAIR_FIXTURE = "benchmarks/reproduction/fixtures/eggcc-core-row-order.patch"
REGRESSION = "hash_index::tests::multi_column_column_index_rebuild_orders_each_value_by_row"


def prepare_eggcc(
    output: Path, engine: Path, *, build_root: Path | None = None, timeout_sec: int = 600
) -> dict[str, Any]:
    """Prepare fresh sources, reusing normal Cargo caches and a compatible target directory.

    The caller owns the exclusive heavy slot. No historical preparation receipt,
    private Cargo-cache copy, or benchmark execution is required.
    """
    output, engine = output.resolve(), engine.resolve()
    build_root = build_root.resolve() if build_root else output / "cargo-target"
    durable = (ROOT / "benchmarks/local/reproduction").resolve()
    if not output.is_relative_to(durable):
        raise ValueError(f"Eggcc source and evidence must remain below {durable}")
    if output.exists() or (build_root.exists() and not build_root.is_dir()):
        raise ValueError("preparation requires fresh output and a Cargo target directory")
    if not engine.is_file():
        raise ValueError(f"ordinary replay engine is missing: {engine}")
    if (platform.system(), platform.machine()) != ("Darwin", "arm64"):
        raise ValueError("this recipe uses native Apple Silicon with Homebrew LLVM18")
    if timeout_sec <= 0:
        raise ValueError("step timeout must be positive")
    output.mkdir(parents=True)
    preparation = Preparation(output)
    blocker = {
        "configuration": {"native_options": ["--tiger-ilp", "--ilp-solver", "gurobi"]},
        "status": "blocked",
        "reason": "Gurobi requires gurobi_cl and a usable license; this recipe prepares Statewalk only",
        "extractor_substitution": False,
    }
    record: dict[str, Any] = {
        "family": "eggcc",
        "revision": REVISION,
        "status": "blocked",
        "reason": None,
        "output": str(output),
        "build_root": str(build_root),
        "rust_version": "1.88.0",
        "configuration_blockers": [blocker],
        "benchmark_execution": False,
        "core_revision": CORE_REVISION,
        "core_repair": REPAIR_REVISION,
    }
    try:
        if (
            preparation.step("llvm-version", [str(LLVM / "bin/llvm-config"), "--version"], timeout=30).strip()
            != "18.1.8"
        ):
            raise ValueError("native LLVM version differs from 18.1.8")
        rust = preparation.step("rust-version", ["rustc", "+1.88.0", "--version", "--verbose"], timeout=30)
        if not rust.startswith("rustc 1.88.0") or "host: aarch64-apple-darwin" not in rust:
            raise ValueError("Rust toolchain differs from native Apple Silicon Rust 1.88.0")
        checkout = acquire_source(preparation, "eggcc", "https://github.com/egraphs-good/eggcc", REVISION)
        if sha256_file(checkout / "Cargo.lock") != LOCK_SHA256:
            raise ValueError("pinned Eggcc lockfile changed")
        core = acquire_source(preparation, "egglog-core", CORE_URL, CORE_REVISION)
        if any(sha256_file(core / path) != digest for path, digest in CORE_PINS.items()):
            raise ValueError("pinned core repair source changed")
        patches = [
            ROOT / REPAIR_FIXTURE,
            *(
                ROOT / "benchmarks/reproduction/patches" / name
                for name in (
                    "eggcc-build.diff",
                    "eggcc-capture.diff",
                )
            ),
        ]
        preparation.apply_patch(core, patches[0])
        for patch in patches[1:]:
            preparation.apply_patch(checkout, patch)
        lock_sha256 = sha256_file(checkout / "Cargo.lock")
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
        ]
        result = preparation.step(
            "core-regression",
            environment
            + [
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
            ],
            cwd=core,
            timeout=timeout_sec,
        )
        if "test result: ok. 1 passed; 0 failed;" not in result:
            raise ValueError("upstream core regression did not execute exactly one passing test")
        preparation.step(
            "build",
            environment + ["cargo", "+1.88.0", "build", "--profile", "dev", "--locked", "-j1", "--bin", "eggcc"],
            cwd=checkout,
            timeout=timeout_sec,
        )
        binary = build_root / "debug/eggcc"
        # Upstream build.rs writes Tiger independently of CARGO_TARGET_DIR.
        tiger = checkout / "target/debug/tiger"
        if any(not path.is_file() or not path.stat().st_size for path in (binary, tiger)):
            raise ValueError("successful build omitted the native compiler or Tiger")
        if (
            sha256_file(checkout / "Cargo.lock") != lock_sha256
            or sha256_file(core / "Cargo.lock") != CORE_PINS["Cargo.lock"]
        ):
            raise ValueError("locked native build changed a dependency lockfile")
        record["patches"] = {str(patch.relative_to(ROOT)): sha256_file(patch) for patch in patches}
        products = {str(path): sha256_file(path) for path in (binary, tiger, checkout / "Cargo.lock")}
        write_json(output / "build-products.json", products)
        settings = {
            "eggcc": {
                "revision": REVISION,
                "paths": {"checkout": str(checkout), "binary": str(binary), "egglog": str(engine)},
                "identity_paths": [str(tiger), str(output / "build-products.json"), *(str(patch) for patch in patches)],
                "timeout_sec": 300,
                "configuration_blockers": [blocker],
            }
        }
        settings_path = output / "settings.json"
        write_json(settings_path, settings)
        record.update(
            status="success",
            settings=str(settings_path),
            checkout=str(checkout),
            binary=str(binary),
            tiger=str(tiger),
            artifacts=products,
            lock_sha256=lock_sha256,
        )
    except (OSError, ValueError, RuntimeError) as error:
        record["reason"] = str(error)
        receipts = sorted(preparation.logs.glob("*.result.json"))
        if receipts and (status := json.loads(receipts[-1].read_text()).get("status")) != "success":
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
    parser.add_argument("--build-root", type=Path, help="Reusable compatible Cargo target directory")
    parser.add_argument("--timeout-sec", type=int, default=600)
    args = parser.parse_args()
    with exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        record = prepare_eggcc(args.output, args.egglog, build_root=args.build_root, timeout_sec=args.timeout_sec)
    print(json.dumps({key: record.get(key) for key in ("status", "reason", "settings")}, indent=2))
    return 0 if record["status"] == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
