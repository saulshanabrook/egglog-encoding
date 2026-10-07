"""Prepare the pinned native MISAAL x86 canary, without running its generator.

Run from the repository root with ``python -m scripts.reproduction_prepare_misaal``.
Every subprocess has the shared guard; one cross-process lock covers preparation.
Sources, patches and numbered logs belong to a fresh immutable attempt directory.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import tarfile
import tomllib
from pathlib import Path
from typing import Any

from benchmarking.memory_guard import GROUP_LIMIT_BYTES
from scripts.reproduction_process import DISK_RESERVE_BYTES
from scripts.source_tools import Preparation, acquire_source, sha256_file, write_json

ROOT = Path(__file__).resolve().parents[1]
MISAAL_REVISION = "44ff893445d664cd87f52b08a138260ed2015ba8"
HYDRIDE_REVISION = "beb825327fc946d65032e96f7cde9acf3d24c13e"
EGGLOG_REVISION = "6b6938bc0088163f61240482cd34a1579715b804"
EGGLOG_SHA256 = "6bbb9c3fa064b300590ce059ec25eb9cbe10b5572e1e2ed2d80ea1fa332eb0c7"
EGGLOG_ARCHIVE_SHA256 = "2ad90a57a4b940dc02476121b1d09d19ddb0025957ef4562dbf08cff9227959c"
EGGLOG_LOCK_SHA256 = "50da3a4e74386cfed4667df1e76748407b3b76f5e36282700dfa39373cedac45"
BOOST_SHA256 = "71feeed900fbccca04a3b4f2f84a7c217186f28a940ed8b7ed4725986baf99fa"
LLVM12 = Path("/opt/homebrew/opt/llvm@12")

MEMORY_BYTES = GROUP_LIMIT_BYTES
OPTIMIZED_BACKEND = "optimized-dev-assertions-v1"
BACKEND_PROFILE = {
    "name": "dev",
    "opt_level": 3,
    "debug": 0,
    "debug_assertions": True,
    "overflow_checks": True,
    "incremental": False,
    "jobs": 1,
    "default_features": True,
}
BACKEND_FLAG = re.compile(
    r"^(?:CARGO_(?:PROFILE_|BUILD_|TARGET_).*|CARGO_ENCODED_(?:RUST|RUSTDOC)FLAGS|"
    r"CARGO_INCREMENTAL|RUSTFLAGS|RUSTDOCFLAGS|RUSTC(?:_BOOTSTRAP|_WRAPPER|_WORKSPACE_WRAPPER)?|RUSTUP_TOOLCHAIN)$"
)
BACKEND_GUARD_SOURCES = (
    "benchmarking/processes.py",
    "benchmarking/memory_guard.py",
    "scripts/reproduction_process.py",
)


def backend_source_hashes(directory: Path) -> dict[str, str]:
    """Require the complete source tree to equal the pinned archive, with no additions."""
    archive = directory / "egglog.tar.gz"
    source = directory / f"egglog-{EGGLOG_REVISION}"
    if archive.is_symlink() or source.is_symlink() or sha256_file(archive) != EGGLOG_ARCHIVE_SHA256:
        raise ValueError("optimized backend archive/source identity changed")
    expected = {}
    with tarfile.open(archive) as tree:
        members = tree.getmembers()
        if sum(member.size for member in members) > 64 * 1024**2:
            raise ValueError("optimized backend archive exceeds source bound")
        for member in members:
            parts = Path(member.name).parts
            if not parts or parts[0] != source.name or ".." in parts or not (member.isfile() or member.isdir()):
                raise ValueError("unexpected optimized backend archive member")
            if member.isfile():
                data = tree.extractfile(member)
                assert data is not None
                expected[str(Path(*parts[1:]))] = hashlib.sha256(data.read()).hexdigest()
    paths = list(source.rglob("*"))
    if any(path.is_symlink() for path in paths):
        raise ValueError("optimized backend source contains a symlink")
    actual = {str(path.relative_to(source)): sha256_file(path) for path in paths if path.is_file()}
    if actual != expected or actual.get("Cargo.lock") != EGGLOG_LOCK_SHA256:
        raise ValueError("optimized backend source or dependency lock changed")
    return actual


def backend_cargo_configs(directory: Path) -> dict[str, str]:
    """Reject external Cargo semantics; only an empty or disabled wrapper config is allowed."""
    source = directory / f"egglog-{EGGLOG_REVISION}"
    roots = [directory / "backend-cargo-home", *(parent / ".cargo" for parent in (source, *source.parents))]
    configs = {}
    for root in roots:
        for name in ("config", "config.toml"):
            path = root / name
            if path.is_symlink():
                raise ValueError(f"symlinked Cargo configuration: {path}")
            if path.exists():
                config = tomllib.loads(path.read_text())
                wrapper = config.get("build", {}).get("rustc-wrapper")
                if config and (not isinstance(wrapper, str) or config != {"build": {"rustc-wrapper": wrapper}}):
                    raise ValueError(f"unreviewed Cargo configuration: {path}")
                configs[str(path)] = sha256_file(path)
    return configs


def optimized_backend_command(directory: Path, toolchain: dict[str, str], unset: list[str]) -> list[str]:
    """Bind the fixed profile and remove inherited compiler/profile/target overrides."""
    if unset != sorted(set(unset)) or any(BACKEND_FLAG.fullmatch(key) is None for key in unset):
        raise ValueError("invalid optimized backend environment removal list")
    return [
        "/usr/bin/env",
        *(item for key in unset for item in ("-u", key)),
        f"CARGO_HOME={directory / 'backend-cargo-home'}",
        f"CARGO_TARGET_DIR={directory / 'backend-target'}",
        f"RUSTC={toolchain['rustc']}",
        "CARGO_PROFILE_DEV_OPT_LEVEL=3",
        "CARGO_PROFILE_DEV_DEBUG=0",
        "CARGO_PROFILE_DEV_DEBUG_ASSERTIONS=true",
        "CARGO_PROFILE_DEV_OVERFLOW_CHECKS=true",
        "CARGO_INCREMENTAL=0",
        "RUSTC_WRAPPER=",
        "RUSTC_WORKSPACE_WRAPPER=",
        "CARGO_ENCODED_RUSTFLAGS=",
        toolchain["cargo"],
        "build",
        "--profile",
        "dev",
        "--locked",
        "--jobs",
        "1",
        "--bin",
        "egglog",
    ]


def verified_backend_receipt(receipt: Path) -> Path:
    """Accept only this source-verified, guarded optimized build, never an arbitrary binary."""
    if receipt.is_symlink() or receipt.name != "backend.json":
        raise ValueError("optimized backend requires its original backend.json receipt")
    receipt = receipt.resolve()
    directory = receipt.parent
    record = json.loads(receipt.read_text())
    if any(
        record.get(key) != value
        for key, value in {
            "contract": OPTIMIZED_BACKEND,
            "status": "success",
            "profile": BACKEND_PROFILE,
            "source_revision": EGGLOG_REVISION,
            "archive_sha256": EGGLOG_ARCHIVE_SHA256,
            "lock_sha256": EGGLOG_LOCK_SHA256,
        }.items()
    ):
        raise ValueError("unknown optimized backend source/profile contract")
    if backend_source_hashes(directory) != record["source_files"]:
        raise ValueError("optimized backend source inventory differs from receipt")
    if backend_cargo_configs(directory) != record["cargo_configs"]:
        raise ValueError("optimized backend Cargo configuration changed")
    for name in ("backend-cargo-home", "backend-target"):
        if (directory / name).is_symlink() or not (directory / name).is_dir():
            raise ValueError("optimized backend requires its attempt-owned Cargo directories")
    if sha256_file(directory / "backend-preparer.py") != sha256_file(Path(__file__)):
        raise ValueError("optimized backend preparer differs from this reviewed implementation")
    if record["guard_sources"] != {path: sha256_file(ROOT / path) for path in BACKEND_GUARD_SOURCES}:
        raise ValueError("optimized backend resource guard implementation changed")
    for relative, digest in record["evidence"].items():
        path = directory / relative
        if path.is_symlink() or not path.resolve().is_relative_to(directory) or sha256_file(path) != digest:
            raise ValueError(f"optimized backend evidence changed: {relative}")
    paths = record["toolchain_paths"]
    if set(paths) != {"rustc", "cargo"} or set(paths.values()) != set(record["toolchain"]):
        raise ValueError("optimized backend toolchain inventory is incomplete")
    if (
        any(not Path(path).is_absolute() for path in paths.values())
        or Path(paths["rustc"]).parent != Path(paths["cargo"]).parent
    ):
        raise ValueError("optimized backend requires one explicit native toolchain")
    for tool in ("rustc", "cargo"):
        outputs = list((directory / "steps").glob(f"*-backend-{tool}-path.stdout.log"))
        if len(outputs) != 1 or outputs[0].read_text().strip() != paths[tool]:
            raise ValueError("optimized backend toolchain path receipt changed")
        if str(outputs[0].relative_to(directory)) not in record["evidence"]:
            raise ValueError("optimized backend toolchain path receipt is not bound")
        discovery = outputs[0].with_name(outputs[0].name.replace(".stdout.log", ".request.json"))
        if str(discovery.relative_to(directory)) not in record["evidence"] or json.loads(discovery.read_text())[
            "command"
        ] != ["rustup", "which", "--toolchain", "1.91.0", tool]:
            raise ValueError("optimized backend toolchain discovery is not pinned to Rust 1.91.0")
    for path, digest in record["toolchain"].items():
        if sha256_file(Path(path)) != digest:
            raise ValueError(f"optimized backend toolchain changed: {path}")
    request_path = directory / record["build_request"]
    result_path = directory / record["build_result"]
    if any(str(path.relative_to(directory)) not in record["evidence"] for path in (request_path, result_path)):
        raise ValueError("optimized backend build receipts are not bound")
    request, result = json.loads(request_path.read_text()), json.loads(result_path.read_text())
    command = optimized_backend_command(directory, paths, record["environment_unset"])
    if (
        request
        != {
            "command": command,
            "cwd": str(directory / f"egglog-{EGGLOG_REVISION}"),
            "timeout_sec": 600,
            "memory_limit_bytes": MEMORY_BYTES,
            "require_guard": True,
            "disk_reserve_bytes": DISK_RESERVE_BYTES,
        }
        or result.get("status") != "success"
        or result.get("returncode") != 0
    ):
        raise ValueError("optimized backend lacks the exact successful guarded build")
    rust_outputs = list((directory / "steps").glob("*-backend-rust.stdout.log"))
    if (
        len(rust_outputs) != 1
        or rust_outputs[0].read_text() != record["rust"]
        or str(rust_outputs[0].relative_to(directory)) not in record["evidence"]
        or not record["rust"].startswith("rustc 1.91.0 ")
        or "host: aarch64-apple-darwin" not in record["rust"]
    ):
        raise ValueError("optimized backend toolchain provenance is incomplete")
    rust_request = rust_outputs[0].with_name(rust_outputs[0].name.replace(".stdout.log", ".request.json"))
    if str(rust_request.relative_to(directory)) not in record["evidence"] or json.loads(rust_request.read_text())[
        "command"
    ] != [paths["rustc"], "--version", "--verbose"]:
        raise ValueError("optimized backend Rust version is not from its recorded compiler")
    for key in ("stdout_path", "stderr_path"):
        path = Path(result[key])
        if not path.is_relative_to(directory) or str(path.relative_to(directory)) not in record["evidence"]:
            raise ValueError("optimized backend build logs are not bound")
    backend = directory / "backend-target/debug/egglog"
    if (
        record["backend"] != str(backend)
        or backend.is_symlink()
        or backend.parent.is_symlink()
        or not os.access(backend, os.X_OK)
        or sha256_file(backend) != record["sha256"]
    ):
        raise ValueError("optimized backend binary changed or is not its recorded product")
    return backend


def build_backend(preparation: Preparation) -> Path:
    """Build the original backend from pinned source, without a retained binary prerequisite."""
    directory = preparation.directory
    for name in (
        f"egglog-{EGGLOG_REVISION}",
        "egglog.tar.gz",
        "backend-target",
        "backend-cargo-home",
        "backend.json",
        "backend-preparer.py",
    ):
        if (directory / name).exists() or (directory / name).is_symlink():
            raise ValueError("optimized backend requires fresh source, Cargo home and target paths")
    (directory / "backend-cargo-home").mkdir()
    (directory / "backend-target").mkdir()
    with (directory / "backend-preparer.py").open("xb") as snapshot:
        snapshot.write(Path(__file__).read_bytes())
    archive = directory / "egglog.tar.gz"
    preparation.step(
        "backend-download",
        [
            "curl",
            "--fail",
            "--location",
            "--max-filesize",
            str(8 * 1024**2),
            f"https://codeload.github.com/egraphs-good/egglog/tar.gz/{EGGLOG_REVISION}",
            "-o",
            str(archive),
        ],
    )
    if sha256_file(archive) != EGGLOG_ARCHIVE_SHA256:
        raise ValueError("original backend archive differs from the verified source")
    with tarfile.open(archive) as tree:
        members = tree.getmembers()
        if sum(member.size for member in members) > 64 * 1024**2:
            raise ValueError("original backend source archive exceeds its size bound")
        for member in members:
            parts = Path(member.name).parts
            if (
                not parts
                or parts[0] != f"egglog-{EGGLOG_REVISION}"
                or ".." in parts
                or not (member.isfile() or member.isdir())
            ):
                raise ValueError("unexpected original backend archive member")
        tree.extractall(directory, filter="data")
    source = directory / f"egglog-{EGGLOG_REVISION}"
    if sha256_file(source / "Cargo.lock") != EGGLOG_LOCK_SHA256:
        raise ValueError("original backend dependency lock differs from the verified build")
    toolchain = {}
    toolchain_paths = {}
    for tool in ("rustc", "cargo"):
        actual = Path(
            preparation.step(
                f"backend-{tool}-path", ["rustup", "which", "--toolchain", "1.91.0", tool], timeout=30
            ).strip()
        )
        toolchain[str(actual)] = sha256_file(actual)
        toolchain_paths[tool] = str(actual)
    if any(not Path(path).is_absolute() for path in toolchain_paths.values()) or (
        Path(toolchain_paths["rustc"]).parent != Path(toolchain_paths["cargo"]).parent
    ):
        raise ValueError("optimized backend requires one explicit native toolchain")
    extra: dict[str, Any] = {
        "contract": OPTIMIZED_BACKEND,
        "status": "success",
        "profile": BACKEND_PROFILE,
        "source_files": backend_source_hashes(directory),
        "cargo_configs": backend_cargo_configs(directory),
        "toolchain": toolchain,
        "toolchain_paths": toolchain_paths,
        "environment_unset": sorted(key for key in os.environ if BACKEND_FLAG.fullmatch(key)),
        "guard_sources": {path: sha256_file(ROOT / path) for path in BACKEND_GUARD_SOURCES},
    }
    command = optimized_backend_command(directory, toolchain_paths, extra["environment_unset"])
    rust_command = [toolchain_paths["rustc"], "--version", "--verbose"]
    rust = preparation.step("backend-rust", rust_command, timeout=30)
    if not rust.startswith("rustc 1.91.0 ") or "host: aarch64-apple-darwin" not in rust:
        raise ValueError("backend requires the recorded native Rust 1.91.0 toolchain")
    preparation.step("backend-build", command, cwd=source, timeout=600)
    backend = directory / "backend-target/debug/egglog"
    if not backend.is_file() or not backend.stat().st_size or not os.access(backend, os.X_OK):
        raise ValueError("original backend build did not produce an executable")
    if sha256_file(source / "Cargo.lock") != EGGLOG_LOCK_SHA256:
        raise ValueError("backend build changed the dependency lock")
    if (
        backend_source_hashes(directory) != extra["source_files"]
        or backend_cargo_configs(directory) != extra["cargo_configs"]
    ):
        raise ValueError("optimized backend source/configuration changed during build")
    if any(sha256_file(Path(path)) != digest for path, digest in extra["toolchain"].items()):
        raise ValueError("optimized backend toolchain changed during build")
    extra.update(
        build_request=f"steps/{preparation.count:03}-backend-build.request.json",
        build_result=f"steps/{preparation.count:03}-backend-build.result.json",
        evidence={
            str(path.relative_to(directory)): sha256_file(path) for path in preparation.logs.iterdir() if path.is_file()
        },
    )
    extra["evidence"]["backend-preparer.py"] = sha256_file(directory / "backend-preparer.py")
    write_json(
        directory / "backend.json",
        {
            "source_revision": EGGLOG_REVISION,
            "archive_sha256": EGGLOG_ARCHIVE_SHA256,
            "lock_sha256": EGGLOG_LOCK_SHA256,
            "backend": str(backend),
            "sha256": sha256_file(backend),
            "rust": rust,
            **extra,
        },
    )
    verified_backend_receipt(directory / "backend.json")
    return backend


def prepare_exports(
    output: Path, engine: Path, *, case_ids: list[str] | None = None, timeout_sec: float = 300
) -> dict[str, Any]:
    """Build the Egglog-only frontend directly from sources, without LLVM legalization."""
    from scripts.reproduction_inventory import expected_cases
    from scripts.reproduction_misaal_export import SOURCE_SHA256, prepare_export_frontend, prepare_export_generator
    from scripts.reproduction_misaal_groups import CONTRACT, SOURCE
    from scripts.reproduction_misaal_groups import SOURCE_SHA256 as GROUP_SHA
    from scripts.reproduction_misaal_patterns import CONTRACT as PATTERN_DEDUPLICATION
    from scripts.reproduction_misaal_patterns import (
        LITERAL_WIDTH_CONTRACT,
        LITERAL_WIDTH_SOURCE_SHA256,
        PARAMETER_ABI_CONTRACT,
        PARAMETER_ABI_SOURCE_SHA256,
    )
    from scripts.reproduction_misaal_runtime import prepare_runtime
    from scripts.reproduction_prepare_misaal_cases import ARM_TARGET, DEFAULTS, HVX_TARGET, TARGET

    output = output.resolve()
    output.mkdir(parents=True)
    driver = Preparation(output)
    record: dict[str, Any] = {"status": "blocked", "reason": None}
    try:
        (output / "sources").mkdir()
        checkout = acquire_source(driver, "MISAAL", "https://github.com/RafaeNoor/MISAAL.git", MISAAL_REVISION)
        hydride = checkout / "Hydride"
        driver.step("hydride-init", ["git", "init", str(hydride)])
        driver.step(
            "hydride-fetch",
            ["git", "fetch", "--depth=1", "https://github.com/akothen/Hydride.git", HYDRIDE_REVISION],
            cwd=hydride,
        )
        driver.step(
            "hydride-sparse",
            ["git", "sparse-checkout", "set", "codegen-generator", "code-synthesizer/dsl-ir"],
            cwd=hydride,
        )
        driver.step("hydride-checkout", ["git", "checkout", "--detach", "FETCH_HEAD"], cwd=hydride)
        backend = build_backend(driver)
        driver.apply_patch(checkout, ROOT / "benchmarks/reproduction/patches/misaal-01-build.diff")
        python = output / "python/bin/python"
        driver.step("python-environment", ["uv", "venv", "--python", "3.13.11", str(python.parent.parent)])
        driver.step(
            "python-dependencies",
            [
                "uv",
                "pip",
                "install",
                "--python",
                str(python),
                "numpy==2.5.1",
                "psutil==7.2.2",
                "pyparsing==3.3.3",
                "z3-solver==5.1.0.0",
                "sympy==1.14.0",
                "mpmath==1.3.0",
                "ply==3.11",
                "toml==0.10.2",
            ],
        )
        keys = [
            "PYTHONPATH",
            "MISAAL_SRC",
            "MISAAL_ROOT_DIR",
            "HYDRIDE_DIR",
            "HYDRIDE_ROOT",
            "DYLD_LIBRARY_PATH",
            "LD_LIBRARY_PATH",
        ]
        environment = json.loads(
            driver.step(
                "source-environment",
                [
                    "env",
                    "-u",
                    "PYTHONPATH",
                    "-u",
                    "DYLD_LIBRARY_PATH",
                    "-u",
                    "LD_LIBRARY_PATH",
                    "/bin/bash",
                    "-ec",
                    'source ./setup.sh\nexec "$1" -c "$2"',
                    "prepare",
                    str(python),
                    f"import os,json; print(json.dumps({{k:os.environ.get(k,'') for k in {keys!r}}}))",
                ],
                cwd=checkout,
            )
        )
        environment.update(
            DEFAULTS,
            PATH=f"{python.parent}:{LLVM12}/bin:/usr/bin:/bin:/usr/sbin:/sbin:/opt/homebrew/bin",
            LLVM_ROOT=str(LLVM12),
            LLVM_DIS_ROOT=str(LLVM12),
            LLVM_CONFIG=str(LLVM12 / "bin/llvm-config"),
            LEGALIZERS_DIR=str(output / "unused-legalizers"),
            HALIDE_DISTRIB=str(output / "export/halide-build"),
            HALIDE_SRC=str(checkout / "frontends/halide"),
            HALIDE_DIR=str(output / "export/halide-build"),
        )
        pins = {**SOURCE_SHA256, **PARAMETER_ABI_SOURCE_SHA256, **LITERAL_WIDTH_SOURCE_SHA256, SOURCE: GROUP_SHA}
        pins.update(
            {str(path.relative_to(checkout)): sha256_file(path) for path in (checkout / "lib/patterns").glob("*.py")}
        )
        seed = {
            "revision": MISAAL_REVISION,
            "source_timeout_sec": timeout_sec,
            "source_memory_limit_bytes": GROUP_LIMIT_BYTES,
            "hydride_revision": HYDRIDE_REVISION,
            "egglog_revision": EGGLOG_REVISION,
            "checkout": str(checkout),
            "source_hashes": pins,
            "environment": environment,
            "environment_unset": [],
            "backend": str(backend),
            "backend_sha256": sha256_file(backend),
            "python": str(python),
            "python_sha256": sha256_file(python),
            "identity_paths": [],
            "pattern_cache_contract": {"environment": "MISAAL_PATTERN_CACHE_DIR"},
            "pattern_deduplication": PATTERN_DEDUPLICATION,
        }
        source_request = output / "source.json"
        write_json(source_request, seed)
        frontend = prepare_export_frontend(output / "export", source_request)
        if frontend["status"] != "success":
            return frontend
        checkout = Path(frontend["checkout"])
        runtime = prepare_runtime(output / "racket", checkout)
        seal = json.loads(runtime.read_text())
        environment = {
            **environment,
            **seal["environment"],
            "PATH": seal["environment"]["PATH"] + ":" + environment["PATH"],
        }
        seed.update(
            racket=seal["executables"]["racket"]["path"],
            racket_sha256=seal["executables"]["racket"]["sha256"],
            racket_group_containment=CONTRACT,
            parameter_abi=PARAMETER_ABI_CONTRACT,
            literal_width_guard=LITERAL_WIDTH_CONTRACT,
            racket_runtime={"path": str(runtime), "sha256": sha256_file(runtime)},
            environment=environment,
            environment_unset=seal["required_unset"],
        )
        requests = output / "requests"
        requests.mkdir()
        blockers = []
        for case in expected_cases():
            if case["family"] != "misaal" or (case_ids is not None and case["id"] not in case_ids):
                continue
            target = case["configuration"]["target"]
            name = Path(case["source"]).name
            request = json.loads(json.dumps(seed))
            request.update(case_id=case["id"], source=case["source"], configuration=case["configuration"])
            request["source_hashes"][case["source"] + f"/src/{name}_generator.cpp"] = sha256_file(
                Path(seed["checkout"]) / case["source"] / f"src/{name}_generator.cpp"
            )
            env = request["environment"]
            env["HYDRIDE_BENCHMARK"] = f"{name}_{target}_depth2_misaal"
            if target == "arm":
                env.pop("HL_EXPR_DEPTH", None)
                env.update(HYDRIDE_TARGET="arm", HYDRIDE_DISTRIBUTE_LOOK_AHEAD="1")
            elif target == "hexagon":
                for key in (
                    "HL_EXPR_DEPTH",
                    "HL_SYNTH_BW",
                    "HYDRIDE_INITIAL_HASH",
                    "MISAAL_DISABLE_FRONTEND_PATTERNS",
                    "HYDRIDE_DISTRIBUTE_LOOK_AHEAD",
                ):
                    env.pop(key, None)
                env.update(
                    HYDRIDE_BENCHMARK=f"{name}_hvx",
                    HYDRIDE_TARGET="hvx",
                    HL_FORCE_HEXAGON_OPT="1",
                    MISAAL_EQ_SAT_ITERS="3",
                )
                if name == "fully_connected":
                    env.update(HL_EXPR_DEPTH="2", HL_SYNTH_BW="16", HYDRIDE_INITIAL_HASH="empty_hash")
                    request["configuration_variances"] = [
                        {"reason": "HVX fully_connected: replace invalid empty EXPR_DEPTH with unset default 2"}
                    ]
            request["generator_command"] = [
                "pending-build",
                "-t",
                "0",
                "-o",
                "{output}",
                "-g",
                name,
                *(["output.type=uint8"] if target in {"arm", "hexagon"} and name == "fully_connected" else []),
                "-e",
                "stmt",
                "-f",
                name,
                "target=" + {"x86": TARGET, "arm": ARM_TARGET, "hexagon": HVX_TARGET}[target],
            ]
            source_request = output / (case["id"] + ".source.json")
            write_json(source_request, request)
            built = prepare_export_generator(
                output / "generators" / case["id"], source_request, output / "export/frontend.json"
            )
            if built["status"] != "success":
                if built["status"] in {"resource-stopped", "memory-limit", "cancelled", "interrupted"}:
                    return built
                blockers.append(
                    {
                        "case_ids": [case["id"]],
                        "configuration": case["configuration"],
                        "reason": built.get("reason", built["status"]),
                    }
                )
                continue
            (requests / (case["id"] + ".json")).write_bytes(
                (output / "generators" / case["id"] / "capture-request.json").read_bytes()
            )
        settings = output / "settings.json"
        write_json(
            settings,
            {
                "misaal": {
                    "revision": MISAAL_REVISION,
                    "paths": {"requests": str(requests), "egglog": str(engine)},
                    "configuration_blockers": blockers,
                }
            },
        )
        record.update(status="success", settings=str(settings))
    except (OSError, ValueError, RuntimeError) as error:
        record["reason"] = str(error)
        failures = [json.loads(path.read_text()) for path in output.rglob("*.result.json")]
        stop = next(
            (
                row
                for row in failures
                if row.get("status") in {"resource-stopped", "memory-limit", "cancelled", "interrupted"}
            ),
            None,
        )
        if stop:
            record["status"] = stop["status"]
        elif "guard refused" in str(error):
            record["status"] = "resource-stopped"
    write_json(output / "preparation.json", record)
    return record
