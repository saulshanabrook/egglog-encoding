"""Prepare Churchroad's Verilog frontend and mapping exporter, without synthesis."""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import shlex
import shutil
from pathlib import Path
from typing import Any

from scripts.reproduction_process import exclusive_job
from scripts.source_tools import Preparation, acquire_source, sha256_file, write_json

ROOT = Path(__file__).resolve().parents[1]
REVISIONS = {
    "churchroad": ("gussmith23/churchroad", "9f82ca23b273a5a500cc6a1ca60b30d3c33c5721"),
    "yosys": ("YosysHQ/yosys", "f8d4d7128cf72456cc03b0738a8651ac5dbe52e1"),
}
RUST_VERSION = "1.88.0"


def prepare_churchroad(
    output: Path, engine: Path, *, build_root: Path | None = None, timeout_sec: int = 1200
) -> dict[str, Any]:
    """Build matching Yosys/plugin sources and stop native capture after mapping.

    The caller owns the exclusive heavy slot. Sources/evidence are fresh; normal
    Cargo caching and an explicitly selected compatible Cargo target are reused.
    """
    output, engine = output.resolve(), engine.resolve()
    build_root = build_root.resolve() if build_root else output / "build"
    durable = (ROOT / "benchmarks/local/reproduction").resolve()
    if not output.is_relative_to(durable):
        raise ValueError(f"Churchroad source and evidence must remain below {durable}")
    if any(re.fullmatch(r"[A-Za-z0-9_./-]+", str(path)) is None for path in (output, build_root)):
        raise ValueError("Churchroad's shell paths require directories without spaces or shell syntax")
    if output.exists() or (build_root.exists() and not build_root.is_dir()):
        raise ValueError("preparation requires fresh output and a Cargo target directory")
    if not engine.is_file():
        raise ValueError(f"ordinary replay engine is missing: {engine}")
    if platform.system() not in {"Darwin", "Linux"}:
        raise ValueError("this preparation recipe supports native macOS and Linux")
    if timeout_sec <= 0:
        raise ValueError("step timeout must be positive")
    output.mkdir(parents=True)
    preparation = Preparation(output)
    record: dict[str, Any] = {
        "family": "churchroad",
        "status": "blocked",
        "reason": None,
        "source_revisions": REVISIONS,
        "rust_version": RUST_VERSION,
        "output": str(output),
        "build_root": str(build_root),
        "benchmark_execution": False,
    }
    try:
        required = ["git", "make", "pkg-config", "bison", "flex", "cargo", "rustup"]
        required += ["clang", "clang++"] if platform.system() == "Darwin" else ["gcc", "g++"]
        if missing := [name for name in required if shutil.which(name) is None]:
            raise ValueError(
                "Missing host prerequisites: " + ", ".join(missing) + "; Yosys also needs readline/libffi/zlib headers"
            )
        preparation.step("rust-version", ["cargo", f"+{RUST_VERSION}", "--version"], timeout=30)
        sources = {
            name: acquire_source(preparation, name, f"https://github.com/{repository}.git", revision)
            for name, (repository, revision) in REVISIONS.items()
        }
        churchroad, yosys = sources["churchroad"], sources["yosys"]
        patch = ROOT / "benchmarks/reproduction/patches/churchroad-capture.diff"
        preparation.apply_patch(churchroad, patch)
        prefix = output / "prefix"
        environment = [
            "env",
            f"PATH={prefix / 'bin'}{os.pathsep}{os.environ.get('PATH', '')}",
            f"CARGO_TARGET_DIR={build_root / 'cargo'}",
            "CARGO_BUILD_JOBS=1",
            "CARGO_PROFILE_DEV_DEBUG=0",
            "CARGO_INCREMENTAL=0",
            "RUSTC_WRAPPER=",
            "MAKEFLAGS=-j1",
        ]
        preparation.step(
            "yosys-configure", ["make", "config-clang" if platform.system() == "Darwin" else "config-gcc"], cwd=yosys
        )
        make = ["make", "-j1", f"PREFIX={prefix}", "ENABLE_ABC=0", "ENABLE_TCL=0"]
        preparation.step("yosys-build", make, cwd=yosys, timeout=timeout_sec)
        preparation.step("yosys-install", [*make, "install"], cwd=yosys, timeout=timeout_sec)
        plugin = churchroad / "yosys-plugin/churchroad.so"
        preparation.step(
            "churchroad-plugin",
            [str(prefix / "bin/yosys-config"), "--build", str(plugin), str(churchroad / "yosys-plugin/churchroad.cc")],
            cwd=churchroad,
            timeout=timeout_sec,
        )
        passes = preparation.step(
            "yosys-passes",
            [
                str(prefix / "bin/yosys"),
                "-m",
                str(plugin),
                "-Q",
                "-T",
                "-p",
                "help write_churchroad; help read_verilog; help prep",
            ],
            cwd=churchroad,
        )
        if "No such command" in passes:
            raise ValueError("Yosys or its Churchroad plugin lacks a required frontend pass")
        preparation.step(
            "churchroad-lock", environment + ["cargo", f"+{RUST_VERSION}", "generate-lockfile"], cwd=churchroad
        )
        lock_sha256 = sha256_file(churchroad / "Cargo.lock")
        preparation.step(
            "churchroad-build",
            environment + ["cargo", f"+{RUST_VERSION}", "build", "--locked", "-j1", "--bin", "churchroad"],
            cwd=churchroad,
            timeout=timeout_sec,
        )
        binary = build_root / "cargo/debug/churchroad"
        if any(not path.is_file() or not path.stat().st_size for path in (binary, plugin)):
            raise ValueError("build omitted the Churchroad exporter or Yosys plugin")
        if sha256_file(churchroad / "Cargo.lock") != lock_sha256:
            raise ValueError("locked Churchroad build changed its lockfile")
        launcher = prefix / "bin/churchroad-capture"
        launcher.write_text(
            "#!/bin/sh\nexec " + " ".join(shlex.quote(arg) for arg in [*environment, str(binary)]) + ' "$@"\n'
        )
        launcher.chmod(0o755)
        products = {
            str(path): sha256_file(path)
            for path in (
                binary,
                plugin,
                launcher,
                prefix / "bin/yosys",
                prefix / "bin/yosys-config",
                churchroad / "Cargo.lock",
            )
        }
        write_json(output / "build-products.json", products)
        settings_path = output / "settings.json"
        write_json(
            settings_path,
            {
                "churchroad": {
                    "paths": {"checkout": str(churchroad), "binary": str(launcher), "egglog": str(engine)},
                    "timeout_sec": 300,
                    "revision": REVISIONS["churchroad"][1],
                    "identity_paths": [str(patch), str(output / "build-products.json")],
                }
            },
        )
        record.update(
            status="success",
            settings=str(settings_path),
            checkout=str(churchroad),
            binary=str(launcher),
            patch_sha256=sha256_file(patch),
            artifacts=products,
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
    parser.add_argument("--build-root", type=Path)
    parser.add_argument("--timeout-sec", type=int, default=1200)
    args = parser.parse_args()
    with exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        result = prepare_churchroad(args.output, args.egglog, build_root=args.build_root, timeout_sec=args.timeout_sec)
    print(json.dumps({key: result.get(key) for key in ("status", "reason", "settings")}, indent=2))
    return 0 if result["status"] == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
