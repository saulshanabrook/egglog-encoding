"""Prepare the real Churchroad host optimizer in a fresh, durable environment.

This installs no system packages, initializes no private submodules, and runs no
benchmark or target device. Invoke through the coordinator's exclusive heavy
slot. Every child command has the ordinary native resource guard and one job.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import shlex
import shutil
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any

from benchmarking.processes import PilotProcessResult, run_bounded_command
from benchmarking.targets import sha256_file
from scripts.eggcc_churchroad_complete import patched_churchroad_sources, write_native_patch
from scripts.reproduction_process import exclusive_job

ROOT = Path(__file__).resolve().parents[1]
REVISIONS = {
    "churchroad": ("gussmith23/churchroad", "9f82ca23b273a5a500cc6a1ca60b30d3c33c5721"),
    "lakeroad": ("gussmith23/lakeroad", "7a69047ad20cad54e5c78d68d397b716b42ff462"),
    "yosys": ("YosysHQ/yosys", "f8d4d7128cf72456cc03b0738a8651ac5dbe52e1"),
    "bitwuzla": ("bitwuzla/bitwuzla", "9e5d7d82b0a0bfd3dc838eb3c3936acad500dc97"),
    "rosette": ("emina/rosette", "373c8c35e4a7667f38fce10cf0b74ae17de07f1d"),
    "yaml": ("esilkensen/yaml", "b60a1e4a01979ed447799b07e7f8dd5ff17019f0"),
}
RUST_VERSION = "1.88.0"
MESON_VERSION = "1.2.0"
NINJA_VERSION = "1.13.0"
DISK_RESERVE = 2 * 1024**3


def tree_identity(directory: Path) -> dict[str, Any]:
    """Record source/package contents, including symlink targets, excluding Git metadata."""
    files: dict[str, Any] = {}
    for path in sorted(directory.rglob("*")):
        relative = path.relative_to(directory)
        if ".git" in relative.parts:
            continue
        if path.is_symlink():
            files[str(relative)] = {"symlink": os.readlink(path)}
            if path.is_file():
                files[str(relative)]["sha256"] = sha256_file(path)
        elif path.is_file():
            files[str(relative)] = {"sha256": sha256_file(path)}
    if not files:
        raise ValueError(f"source/package directory is empty: {directory}")
    return files


def prepare_churchroad(
    output: Path, engine: Path, *, build_root: Path | None = None, timeout_sec: float = 1200
) -> dict[str, Any]:
    """Build a pinned host environment and publish settings only after dependency gates."""
    output = output.resolve()
    engine = engine.resolve()
    build_root = build_root.resolve() if build_root else output / "build"
    durable = (ROOT / "benchmarks/local/reproduction").resolve()
    if not output.is_relative_to(durable):
        raise ValueError(f"Churchroad source and evidence must remain below {durable}")
    if any(re.fullmatch(r"[A-Za-z0-9_./-]+", str(path)) is None for path in (output, build_root)):
        raise ValueError("Churchroad's native shell paths require absolute directories without spaces or shell syntax")
    if output.exists() or build_root.exists():
        raise ValueError("preparation requires fresh output and build directories; retained attempts are immutable")
    if not engine.is_file():
        raise ValueError(f"ordinary replay engine is missing: {engine}")
    if platform.system() not in {"Darwin", "Linux"}:
        raise ValueError("this preparation recipe supports native macOS and Linux")
    if timeout_sec <= 0:
        raise ValueError("step timeout must be positive")
    output.mkdir(parents=True)
    evidence = output / "evidence"
    evidence.mkdir()
    record: dict[str, Any] = {
        "status": "blocked",
        "reason": None,
        "steps": [],
        "sources": {},
        "artifacts": {},
        "platform": {"system": platform.system(), "machine": platform.machine(), "release": platform.release()},
        "source_revisions": REVISIONS,
        "rust_version": RUST_VERSION,
        "meson_version": MESON_VERSION,
        "ninja_version": NINJA_VERSION,
        "device_execution": False,
        "benchmark_execution": False,
        "implementation_sha256": sha256_file(Path(__file__)),
        "capture_implementation_sha256": sha256_file(ROOT / "scripts/eggcc_churchroad_complete.py"),
    }
    environment = {
        "PATH": os.environ.get("PATH", ""),
        "PLTUSERHOME": str(output / "racket-user"),
        "PLTCOLLECTS": "",
        "PYTHONNOUSERSITE": "1",
        "CARGO_HOME": str(output / "cargo-home"),
        "RUSTUP_HOME": str(output / "rustup-home"),
        "CARGO_TARGET_DIR": str(build_root / "cargo"),
        "CARGO_BUILD_JOBS": "1",
        "CARGO_PROFILE_DEV_DEBUG": "0",
        "CARGO_INCREMENTAL": "0",
        "RUSTC_WRAPPER": "",
        "MAKEFLAGS": "-j1",
        "CMAKE_BUILD_PARALLEL_LEVEL": "1",
    }
    receipt = output / "preparation.json"

    def step(name: str, command: list[str], cwd: Path) -> PilotProcessResult:
        """Persist command intent/results and halt the pipeline on any guarded failure."""
        argv = ["env", *(f"{key}={value}" for key, value in environment.items()), *command]
        prefix = evidence / f"{len(record['steps']):03}-{name}"
        row: dict[str, Any] = {"name": name, "command": argv, "cwd": str(cwd), "status": "running"}
        record["steps"].append(row)
        receipt.write_text(json.dumps(record, indent=2, default=str) + "\n")
        try:
            result = run_bounded_command(
                argv,
                cwd,
                prefix,
                timeout_sec=timeout_sec,
                require_guard=True,
                disk_reserve_bytes=DISK_RESERVE,
                allow_warning_pressure=False,
            )
        except ValueError as error:
            status = "resource-stopped" if "guard refused" in str(error) else "blocked"
            row.update(status=status, message=str(error))
            record.update(status=status, reason=f"{name}: {error}")
            raise
        row.update(asdict(result))
        receipt.write_text(json.dumps(record, indent=2, default=str) + "\n")
        if result.status != "success":
            record.update(status=result.status, reason=f"{name}: {result.message or result.status}")
            raise ValueError(record["reason"])
        return result

    try:
        required = ["git", "make", "pkg-config", "bison", "flex", "racket", "raco", "rustup", "cargo"]
        required += ["clang", "clang++", "otool"] if platform.system() == "Darwin" else ["gcc", "g++", "ldd"]
        tools = {name: shutil.which(name) for name in required}
        missing = [name for name, path in tools.items() if path is None]
        if missing:
            raise ValueError(
                "Missing host prerequisites: "
                + ", ".join(missing)
                + ". Install native build tools, GMP/readline/libffi/zlib headers and Racket >=8.1 first; "
                "no x86 emulation or private HDL is required."
            )
        record["host_tools"] = {
            name: {"path": path, "sha256": sha256_file(Path(path))} for name, path in tools.items() if path
        }
        record["host_tools"]["python"] = {"path": sys.executable, "sha256": sha256_file(Path(sys.executable))}
        build_root.mkdir(parents=True)
        prefix = output / "prefix"
        (prefix / "bin").mkdir(parents=True)
        python = output / "python/bin/python"
        environment["PATH"] = os.pathsep.join([str(prefix / "bin"), str(python.parent), environment["PATH"]])
        # Racket's user packages remain isolated while its installed runtime is reused.
        for name in ("racket", "raco"):
            (prefix / "bin" / name).symlink_to(str(tools[name]))
        racket_version = (
            step("racket-version", ["racket", "-e", "(display (version))"], output).stdout_path.read_text().strip()
        )
        if not re.fullmatch(r"\d+(?:\.\d+)+", racket_version) or tuple(map(int, racket_version.split("."))) < (8, 1):
            raise ValueError(f"Racket >=8.1 required, observed {racket_version!r}")
        record["racket_version"] = racket_version
        racket_dirs = step(
            "racket-runtime-paths",
            [
                "racket",
                "-e",
                "(require setup/dirs json) (write-json (map path->string (filter directory-exists? "
                "(append (get-collects-search-dirs) (get-pkgs-search-dirs) "
                "(filter path? (list (find-lib-dir) (find-config-dir)))))))",
            ],
            output,
        )
        racket_runtime_paths = [Path(path) for path in json.loads(racket_dirs.stdout_path.read_text())]
        if not racket_runtime_paths or any(not path.is_dir() for path in racket_runtime_paths):
            raise ValueError("Racket did not report its existing runtime package/collection directories")
        record["racket_runtime_paths"] = [str(path) for path in racket_runtime_paths]
        for name, args in [
            ("git", ["--version"]),
            ("make", ["--version"]),
            ("bison", ["--version"]),
            ("flex", ["--version"]),
            ("pkg-config", ["--modversion", "gmp"]),
            ("clang++" if platform.system() == "Darwin" else "g++", ["--version"]),
        ]:
            step(f"version-{name}", [name, *args], output)
        step("rust-toolchain", ["rustup", "toolchain", "install", RUST_VERSION, "--profile", "minimal"], output)
        step("rust-version", ["cargo", f"+{RUST_VERSION}", "--version"], output)
        step("python-environment", [sys.executable, "-m", "venv", str(python.parent.parent)], output)
        wheels = evidence / "python-wheels"
        wheels.mkdir()
        packages = [f"meson=={MESON_VERSION}", f"ninja=={NINJA_VERSION}"]
        step(
            "python-tools-download",
            [
                str(python),
                "-m",
                "pip",
                "download",
                "--disable-pip-version-check",
                "--only-binary=:all:",
                "--no-deps",
                "--dest",
                str(wheels),
                *packages,
            ],
            output,
        )
        step(
            "python-tools-install",
            [str(python), "-m", "pip", "install", "--no-index", "--find-links", str(wheels), *packages],
            output,
        )
        record["python_build_wheels"] = tree_identity(wheels)
        step("python-packages", [str(python), "-m", "pip", "freeze", "--all"], output)
        step("ninja-version", [str(python.parent / "ninja"), "--version"], output)
        sources = output / "sources"
        sources.mkdir()
        for name, (repository, revision) in REVISIONS.items():
            checkout = sources / name
            step(f"{name}-init", ["git", "init", str(checkout)], sources)
            step(
                f"{name}-fetch",
                ["git", "fetch", "--depth=1", f"https://github.com/{repository}.git", revision],
                checkout,
            )
            step(f"{name}-checkout", ["git", "checkout", "--detach", "FETCH_HEAD"], checkout)
            observed = step(f"{name}-revision", ["git", "rev-parse", "HEAD"], checkout).stdout_path.read_text().strip()
            if observed != revision:
                raise ValueError(f"{name} checkout resolved to {observed}, expected {revision}")
            identity = evidence / f"{name}-source.json"
            identity.write_text(json.dumps(tree_identity(checkout), indent=2) + "\n")
            record["sources"][name] = {
                "checkout": str(checkout),
                "revision": revision,
                "inventory": str(identity),
                "sha256": sha256_file(identity),
            }
        churchroad, lakeroad = sources / "churchroad", sources / "lakeroad"
        bitwuzla, yosys = sources / "bitwuzla", sources / "yosys"
        environment["LAKEROAD_DIR"] = str(lakeroad)
        environment["CHURCHROAD_DIR"] = environment["CARGO_MANIFEST_DIR"] = str(churchroad)
        # Do not recursively initialize the upstream private/simulation submodules.
        model = lakeroad / "racket/generated/xilinx-ultrascale-plus-dsp48e2.rkt"
        if not model.is_file() or not model.stat().st_size:
            raise ValueError("Pinned Lakeroad's public generated DSP48E2 model is missing")
        # Racket 9.1 rejects this test's unused name at two distinct ellipsis depths.
        # Rename only the outer test binding; every synthesis definition is unchanged.
        architecture = lakeroad / "racket/architecture-description.rkt"
        architecture_source = architecture.read_text()
        test_start = '(module+ test\n  (test-case "Construct smaller DSP from larger DSP"'
        test_end = '  (test-case "Construct a LUT5 on Lattice from LUT4s and a MUX2."'
        old_pattern = "                  others ...)))\n          #t]"
        if (
            architecture_source.count(test_start) != 1
            or architecture_source.count(test_end) != 1
            or architecture_source.count(old_pattern) != 1
            or not architecture_source.index(test_start)
            < architecture_source.index(old_pattern)
            < architecture_source.index(test_end)
        ):
            raise ValueError("Pinned Lakeroad Racket test compatibility patch no longer matches its source")
        patched_architecture = architecture_source.replace(old_pattern, old_pattern.replace("others", "other-outputs"))
        compatibility_patch = evidence / "lakeroad-racket-match.patch"
        write_native_patch(lakeroad, {"racket/architecture-description.rkt": patched_architecture}, compatibility_patch)
        record["lakeroad_compatibility"] = {
            "patch": str(compatibility_patch),
            "patch_sha256": sha256_file(compatibility_patch),
            "original_sha256": sha256_file(architecture),
        }
        architecture.write_text(patched_architecture)
        record["lakeroad_compatibility"]["patched_sha256"] = sha256_file(architecture)
        step(
            "bitwuzla-configure",
            [
                str(python),
                "configure.py",
                "release",
                f"--prefix={prefix}",
                f"--build-dir={build_root / 'bitwuzla'}",
                "--static",
                "--no-testing",
                "--no-unit-testing",
            ],
            bitwuzla,
        )
        if not (build_root / "bitwuzla/build.ninja").is_file():
            raise ValueError("Bitwuzla configure returned without a Meson build (upstream ignores Meson's exit status)")
        step("bitwuzla-build", ["ninja", "-C", str(build_root / "bitwuzla"), "-j1"], bitwuzla)
        step("bitwuzla-install", ["ninja", "-C", str(build_root / "bitwuzla"), "-j1", "install"], bitwuzla)
        step("bitwuzla-version", [str(prefix / "bin/bitwuzla"), "--version"], output)
        # An existing native Z3 avoids Rosette's optional prebuilt installer; Bitwuzla remains the selected solver.
        if z3 := shutil.which("z3"):
            (sources / "rosette/bin").mkdir(exist_ok=True)
            (sources / "rosette/bin/z3").symlink_to(z3)
            record["optional_rosette_setup_z3"] = {"path": z3, "sha256": sha256_file(Path(z3))}
        for name in ("rosette", "yaml"):
            step(
                f"racket-install-{name}",
                [
                    "raco",
                    "pkg",
                    "install",
                    "--scope",
                    "user",
                    "--deps",
                    "search-auto",
                    "--batch",
                    "--no-setup",
                    "--name",
                    name,
                    str(sources / name),
                ],
                output,
            )
        step("racket-setup", ["raco", "setup", "--jobs", "1", "--no-docs", "--pkgs", "rosette", "yaml"], output)
        step("racket-packages", ["raco", "pkg", "show", "--all", "--long"], output)
        step("lakeroad-compile", ["raco", "make", "-j", "1", str(lakeroad / "bin/main.rkt")], lakeroad)
        step("lakeroad-help", ["racket", str(lakeroad / "bin/main.rkt"), "--help"], lakeroad)
        # A real solver request checks the Rosette/SMT protocol, without synthesizing a paper workload.
        smoke = evidence / "bitwuzla-smoke.rkt"
        smoke.write_text(
            "#lang rosette\n(require rosette/solver/smt/bitwuzla)\n"
            "(current-solver (bitwuzla))\n(define-symbolic x (bitvector 8))\n"
            "(unless (sat? (solve (assert (bveq (bvadd x (bv 1 8)) (bv 2 8)))))\n"
            '  (error "Bitwuzla smoke failed"))\n(displayln "bitwuzla-smoke-ok")\n'
        )
        step("bitwuzla-smoke", ["racket", str(smoke)], output)
        # Full Yosys is required by synthesis: SMALL=1 omits BTOR/JSON/clk2fflogic.
        step("yosys-configure", ["make", "config-clang" if platform.system() == "Darwin" else "config-gcc"], yosys)
        make = ["make", "-j1", f"PREFIX={prefix}", "ENABLE_ABC=0", "ENABLE_TCL=0"]
        step("yosys-build", make, yosys)
        step("yosys-install", [*make, "install"], yosys)
        patched = patched_churchroad_sources(churchroad)
        write_native_patch(churchroad, patched, evidence / "churchroad-native-capture.patch")
        for relative, text in patched.items():
            (churchroad / relative).write_text(text)
        plugin = churchroad / "yosys-plugin/churchroad.so"
        step(
            "churchroad-plugin",
            [str(prefix / "bin/yosys-config"), "--build", str(plugin), str(churchroad / "yosys-plugin/churchroad.cc")],
            churchroad,
        )
        required_passes = [
            "write_churchroad",
            "write_btor",
            "clk2fflogic",
            "read_json",
            "write_verilog",
            "proc",
            "flatten",
            "prep",
        ]
        checked = step(
            "yosys-passes",
            [
                str(prefix / "bin/yosys"),
                "-m",
                str(plugin),
                "-Q",
                "-T",
                "-p",
                "; ".join(f"help {name}" for name in required_passes),
            ],
            churchroad,
        )
        if "No such command" in checked.stdout_path.read_text() + checked.stderr_path.read_text():
            raise ValueError("Full Yosys or its Churchroad plugin lacks a required synthesis pass")
        step("churchroad-lock", ["cargo", f"+{RUST_VERSION}", "generate-lockfile"], churchroad)
        shutil.copyfile(churchroad / "Cargo.lock", evidence / "churchroad-Cargo.lock")
        step(
            "churchroad-build",
            ["cargo", f"+{RUST_VERSION}", "build", "--locked", "-j1", "--bin", "churchroad"],
            churchroad,
        )
        binary = build_root / "cargo/debug/churchroad"
        step("churchroad-help", [str(binary), "--help"], churchroad)
        if not plugin.is_file() or not binary.is_file():
            raise ValueError("Churchroad build did not retain its native executable and plugin")
        package_identity = evidence / "racket-package-files.json"
        package_identity.write_text(json.dumps(tree_identity(output / "racket-user"), indent=2) + "\n")
        for info in sorted((build_root / "bitwuzla/meson-info").glob("*.json")):
            shutil.copyfile(info, evidence / f"bitwuzla-{info.name}")
        linked_libraries: set[Path] = set()
        for name, executable in [
            ("bitwuzla", prefix / "bin/bitwuzla"),
            ("yosys", prefix / "bin/yosys"),
            ("churchroad", binary),
            ("plugin", plugin),
            ("racket", Path(str(tools["racket"]))),
        ]:
            command = ["otool", "-L", str(executable)] if platform.system() == "Darwin" else ["ldd", str(executable)]
            observed = step(f"linked-{name}", command, output).stdout_path.read_text()
            for path in re.findall(r"(?:=>\s+|^\s*)(/[^\s]+)\s+\(", observed, re.M):
                if Path(path).is_file():
                    linked_libraries.add(Path(path))
        launcher = prefix / "bin/churchroad-capture"
        launcher.write_text(
            "#!/bin/sh\nexec env "
            + " ".join(shlex.quote(f"{key}={value}") for key, value in environment.items())
            + " "
            + shlex.quote(str(binary))
            + ' "$@"\n'
        )
        launcher.chmod(0o755)
        runtime_paths = [
            binary,
            plugin,
            prefix,
            lakeroad,
            sources / "rosette",
            sources / "yaml",
            output / "racket-user",
            churchroad / "Cargo.lock",
            evidence,
            Path(__file__).resolve(),
            *(Path(str(path)) for path in tools.values()),
            *racket_runtime_paths,
            *sorted(linked_libraries),
        ]
        if z3:
            runtime_paths.append(Path(z3))
        settings = {
            "churchroad": {
                "paths": {"checkout": str(churchroad), "binary": str(launcher), "egglog": str(engine)},
                "timeout_sec": 300,
                "revision": REVISIONS["churchroad"][1],
                "identity_paths": [str(path) for path in dict.fromkeys(runtime_paths)],
            }
        }
        record["runtime_environment"] = environment
        record["linked_libraries"] = {str(path): sha256_file(path) for path in sorted(linked_libraries)}
        record["artifacts"] = {
            str(path): sha256_file(path)
            for path in (binary, plugin, launcher, model, churchroad / "Cargo.lock", package_identity)
        }
        settings_path = output / "settings.json"
        settings_path.write_text(json.dumps(settings, indent=2) + "\n")
        record.update(
            status="success",
            settings=str(settings_path),
            settings_sha256=sha256_file(settings_path),
            reason="Host dependencies prepared; actual Churchroad optimization and ordinary replay still required",
        )
    except (OSError, ValueError) as error:
        if record["reason"] is None:
            record.update(status="blocked", reason=str(error))
    finally:
        receipt.write_text(json.dumps(record, indent=2, default=str) + "\n")
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path, required=True, help="Fresh directory below benchmarks/local/reproduction"
    )
    parser.add_argument("--egglog", type=Path, default=ROOT / "target/release/egglog-experimental")
    parser.add_argument("--build-root", type=Path, help="Fresh optional disposable build directory")
    parser.add_argument(
        "--timeout-sec", type=float, default=1200, help="Guarded timeout for each serial preparation step"
    )
    args = parser.parse_args()
    with exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        result = prepare_churchroad(args.output, args.egglog, build_root=args.build_root, timeout_sec=args.timeout_sec)
    print(json.dumps({key: result.get(key) for key in ("status", "reason", "settings")}, indent=2))
    return 0 if result["status"] == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
