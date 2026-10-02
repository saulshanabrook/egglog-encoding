"""Seal and verify the tested MISAAL Racket runtime without executing native code.

The seal permits source capture with the explicit mixed-revision ABI contract;
it is not workload admission. Call verify_runtime before and after a guarded
capture. Original requests and historical blocked receipts remain unchanged.
"""

from __future__ import annotations

import json
import shutil
from dataclasses import asdict
from pathlib import Path
from typing import Any

from scripts.reproduction_misaal_groups import CONTRACT as GROUP_CONTRACT
from scripts.reproduction_misaal_patterns import PARAMETER_ABI_CONTRACT
from scripts.source_tools import sha256_file

CONTRACT = "misaal-racket-runtime-v1"
REVISION = "44ff893445d664cd87f52b08a138260ed2015ba8"
REQUIRED_UNSET = (
    "PLTCOLLECTS",
    "PLTCONFIGDIR",
    "PLTCOMPILEDROOTS",
    "PLT_ZO_PATH",
    "PLT_COMPILED_FILE_CHECK",
)


def prepare_runtime(output: Path, checkout: Path) -> Path:
    """Acquire pinned packages and exercise the actual parameter-synthesis API repair."""
    from scripts.reproduction_misaal_abi_gate import prepare_programs
    from scripts.reproduction_prepare_misaal_racket import (
        HEADER,
        PACKAGES,
        PARAMETER_SMOKE,
        RACKET,
        acquire_packages,
        unpack_z3,
    )
    from scripts.source_tools import Preparation

    output.mkdir(parents=True)
    driver = Preparation(output)
    for name in ("user", "addon", "tmp", "bin"):
        (output / name).mkdir()
    acquire_packages(output / "sources")
    archive = output / "z3.zip"
    driver.step(
        "download-z3",
        [
            "curl",
            "--fail",
            "--location",
            "--output",
            str(archive),
            "https://github.com/emina/rosette/releases/download/4.1/z3-4.8.8-aarch64-osx-13.3.1.zip",
        ],
    )
    solver = unpack_z3(archive, output / "bin/z3")
    racket = RACKET if RACKET.is_file() else Path(shutil.which("racket") or "/missing/racket")
    environment = {
        "PLTUSERHOME": str(output / "user"),
        "PLTADDONDIR": str(output / "addon"),
        "TMPDIR": str(output / "tmp"),
        "HYDRIDE_ROOT": str(checkout / "Hydride"),
        "MISAAL_Z3_PATH": solver["path"],
        "PATH": f"{output / 'bin'}:{racket.parent}:/usr/bin:/bin:/usr/sbin:/sbin",
    }
    command = ["env", "-i", *(f"{key}={value}" for key, value in environment.items())]
    if "v9.2" not in driver.step("racket-version", [*command, str(racket), "--version"], timeout=30):
        raise ValueError("MISAAL recipe requires Racket 9.2")
    files = {}
    for name in PACKAGES:
        driver.step(
            "install-" + name,
            [
                *command,
                str(racket.with_name("raco")),
                "pkg",
                "install",
                "--scope",
                "user",
                "--batch",
                "--deps",
                "fail",
                "--copy",
                "--no-setup",
                "--name",
                name,
                str(output / "sources" / name),
            ],
        )
        package_path = driver.step(
            "locate-" + name,
            [*command, str(racket), "-e", f'(require pkg/lib) (display (pkg-directory "{name}"))'],
            timeout=30,
        ).strip()
        installed = Path(package_path).resolve()
        if not installed.is_relative_to(output / "addon"):
            raise ValueError("Racket package escaped the isolated installation")
        original = json.loads((output / "sources" / (name + ".json")).read_text())
        for relative, expected in original["files"].items():
            file = installed / relative
            if sha256_file(file).removeprefix("sha256:") != expected:
                raise ValueError(f"installed {name} differs from its pinned source")
            files[str(file)] = expected
    smoke = output / "parameter-smoke.rkt"
    smoke.write_text(HEADER + PARAMETER_SMOKE)
    driver.step("compile-source-api", [*command, str(racket.with_name("raco")), "make", str(smoke)])
    driver.step("parameter-source-api", [*command, str(racket), str(smoke)], timeout=300)
    programs = prepare_programs(checkout, output / "abi-programs")
    from benchmarking.processes import run_bounded_command

    for name, program in programs["programs"].items():
        result = run_bounded_command(
            [*command, str(racket), program["path"]], output, output / name, timeout_sec=300, require_guard=True
        )
        (output / (name + ".result.json")).write_text(json.dumps(asdict(result), indent=2, default=str) + "\n")
        if result.status in {"resource-stopped", "memory-limit", "cancelled", "interrupted"}:
            raise RuntimeError(f"MISAAL parameter ABI gate stopped: {result.status}")
        if result.returncode != program["expected_exit"] or result.status not in {"success", "failure"}:
            raise ValueError(f"MISAAL parameter ABI gate failed: {name}: {result.status}")
        if program["expected_exit"] and "arity mismatch" not in result.stderr_path.read_text():
            raise ValueError("unadapted MISAAL API failed for an unexpected reason")
        if not program["expected_exit"] and not (output / program["result_file"]).stat().st_size:
            raise ValueError("MISAAL parameter ABI gate returned no selected program")
    executables = {
        name: {"path": str(file), "sha256": sha256_file(file).removeprefix("sha256:")}
        for name, file in {"racket": racket, "raco": racket.with_name("raco"), "z3": output / "bin/z3"}.items()
    }
    evidence = [
        *list((output / "addon").rglob("*")),
        *list((output / "steps").iterdir()),
        *list((output / "abi-programs").rglob("*")),
        *list(output.iterdir()),
    ]
    files.update({str(file): sha256_file(file).removeprefix("sha256:") for file in evidence if file.is_file()})
    seal = {
        "schema": CONTRACT,
        "status": "source-api-compatible",
        "checkout": str(checkout),
        "environment": environment,
        "required_unset": REQUIRED_UNSET,
        "executables": executables,
        "files": files,
        "packages": {name: row[0] for name, row in PACKAGES.items()},
        "racket_group_containment": GROUP_CONTRACT,
    }
    path = output / "runtime.json"
    path.write_text(json.dumps(seal, indent=2) + "\n")
    return path


def verify_runtime(request: dict[str, Any]) -> dict[str, Any]:
    """Bind each capture to the acquired package bytes, tested API, and isolated runtime."""
    reference = request["racket_runtime"]
    path = Path(reference["path"])
    if sha256_file(path).removeprefix("sha256:") != reference["sha256"]:
        raise ValueError("MISAAL runtime manifest changed")
    seal: dict[str, Any] = json.loads(path.read_text())
    if (
        seal["schema"] != CONTRACT
        or seal["status"] != "source-api-compatible"
        or seal["checkout"] != request["checkout"]
        or request["parameter_abi"] != PARAMETER_ABI_CONTRACT
        or request["racket_group_containment"] != GROUP_CONTRACT
    ):
        raise ValueError("MISAAL capture does not use the tested source/runtime contract")
    for name, digest in seal["files"].items():
        if sha256_file(Path(name)).removeprefix("sha256:") != digest:
            raise ValueError(f"MISAAL runtime input changed: {name}")
    for name, record in seal["executables"].items():
        if sha256_file(Path(record["path"])).removeprefix("sha256:") != record["sha256"]:
            raise ValueError(f"MISAAL {name} changed")
    if request["racket"] != seal["executables"]["racket"]["path"]:
        raise ValueError("MISAAL request changed its Racket executable")
    for key, value in seal["environment"].items():
        actual = request["environment"].get(key, "")
        if (key != "PATH" and actual != value) or (key == "PATH" and not actual.startswith(value)):
            raise ValueError("MISAAL request bypasses its isolated runtime")
    return seal
