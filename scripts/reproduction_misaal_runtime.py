"""Seal and verify the tested MISAAL Racket runtime without executing native code.

The seal permits source capture with the explicit mixed-revision ABI contract;
it is not workload admission. Call verify_runtime before and after a guarded
capture. Original requests and historical blocked receipts remain unchanged.
"""

from __future__ import annotations

import ast
import hashlib
import json
import os
import re
import shutil
from pathlib import Path
from typing import Any

from benchmarking.targets import sha256_file
from scripts.reproduction_misaal_groups import CONTRACT as GROUP_CONTRACT
from scripts.reproduction_misaal_groups import SOURCE, SOURCE_SHA256
from scripts.reproduction_misaal_patterns import PARAMETER_ABI_CONTRACT, PARAMETER_ABI_SOURCE_SHA256
from scripts.reproduction_stages import directory_identity

CONTRACT = "misaal-racket-runtime-v1"
REVISION = "44ff893445d664cd87f52b08a138260ed2015ba8"
PAPER_REVISION = "c098f0f289d03f0c58db1ef85d9b4ff7eef9dec4"
RACKET_INSTALLATION = Path("/Applications/Racket v9.2")
EXECUTABLE_SHA256 = {
    "racket": "5cd73913bd9ee3da9745fdecb6bfbc4516b39888f2fcd060b5d1282ee8c0d2d0",
    "raco": "03a77daf7c01a94f2021d5aa9760cbe753272792a53b2984779fbac49bba678c",
    "z3": "d216ccee33b874df2fc46b50eae237df4d0cdfecb48e41446741696ded396668",
}
PACKAGE_TREES = {
    "custom-load": "7a450084d7d94893c54037c41a7a5e865f62fd92",
    "rfc6455": "f30d7e5a1e1d91e32b03116806e238afec7461ae",
    "rosette": "d722c2d7f8d7f26612752230b04e3b7ef830ce42",
    "hydride": "71f6b3960f3707b632a1a595f19ec01f8ea54d34",
    "misaal": "25a09c474bf212ff8e49100abc8633193766d678",
}
REQUIRED_UNSET = (
    "PLTCOLLECTS",
    "PLTCONFIGDIR",
    "PLTCOMPILEDROOTS",
    "PLT_ZO_PATH",
    "PLT_COMPILED_FILE_CHECK",
)
ABI_HELPER = Path(__file__).with_name("reproduction_misaal_patterns.py")
PREPARER = Path(__file__).with_name("reproduction_prepare_misaal_racket.py")
CAPTURED_SHA256 = "32d0edbfbd86bdde0ba6b47af8eebd260f1421af79dcbb223923015f389a8521"
CAPTURED_BEFORE = "(synthesize-param-expression param-test-cases 2 3 (list ) #f)"
CAPTURED_AFTER = "(synthesize-param-expression param-test-cases 2 3 (list ))"
ABI_RUNS = {"ordinary-depth2": 0, "general-depth1": 0, "ordinary-depth2-unadapted": 1, "general-depth1-unadapted": 1}


def _bind(path: Path, artifacts: dict[str, str], expected: str | None = None) -> dict[str, str]:
    """Bind a regular retained file once, rejecting inconsistent or changed evidence."""
    if not path.is_absolute() or not path.is_file():
        raise ValueError(f"Runtime evidence must be an existing absolute file: {path}")
    digest = sha256_file(path).removeprefix("sha256:")
    if expected is not None and (re.fullmatch(r"[0-9a-f]{64}", expected) is None or digest != expected):
        raise ValueError(f"Runtime evidence identity changed: {path}")
    if str(path) in artifacts and artifacts[str(path)] != digest:
        raise ValueError(f"Runtime evidence changed while sealing: {path}")
    artifacts[str(path)] = digest
    return {"path": str(path), "sha256": digest}


def _read(reference: dict[str, str], artifacts: dict[str, str]) -> dict[str, Any]:
    """Validate a retained receipt's identity before interpreting its contents."""
    path = Path(reference["path"])
    _bind(path, artifacts, reference["sha256"])
    value: dict[str, Any] = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ValueError(f"Runtime receipt is not an object: {path}")
    return value


def _process_evidence(
    process: dict[str, Any], exit_code: int, declared: dict[str, str], artifacts: dict[str, str]
) -> None:
    """Require actual expected process completion and both identity-bound logs."""
    expected_status = "success" if exit_code == 0 else "failure"
    if (
        process["status"] != expected_status
        or type(process["returncode"]) is not int
        or process["returncode"] != exit_code
    ):
        raise ValueError("Runtime gate process did not complete with its expected outcome")
    for key in ("stdout_path", "stderr_path"):
        path = Path(process[key])
        _bind(path, artifacts, declared[str(path)])
    if exit_code:
        error = Path(process["stderr_path"]).read_text()
        if not all(
            text in error for text in ("synthesize-param-expression", "arity mismatch", "expected: 4", "given: 5")
        ):
            raise ValueError("Runtime ABI control lacks the exact four/five-argument failure")


def _prepared_smokes(source: Path) -> dict[str, bytes]:
    """Reconstruct only literal smoke templates from identity-verified historical source."""
    syntax = ast.parse(source.read_text())
    constants = {
        node.targets[0].id: ast.literal_eval(node.value)
        for node in syntax.body
        if isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id in {"HEADER", "SOLVE", "PARAMETER_SMOKE"}
    }
    writes = [
        node.args[0]
        for node in ast.walk(syntax)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and isinstance(node.func.value, ast.Name)
        and node.func.value.id == "imports"
        and node.func.attr == "write_text"
        and len(node.args) == 1
    ]
    if (
        len(writes) != 1
        or not isinstance(writes[0], ast.BinOp)
        or not isinstance(writes[0].op, ast.Add)
        or not isinstance(writes[0].left, ast.Name)
        or writes[0].left.id != "HEADER"
    ):
        raise ValueError("Historical preparer has an unrecognized import-smoke template")
    return {
        "imports.rkt": (constants["HEADER"] + ast.literal_eval(writes[0].right)).encode(),
        "solver.rkt": (constants["HEADER"] + constants["SOLVE"]).encode(),
        "parameter-four-args.rkt": (constants["HEADER"] + constants["PARAMETER_SMOKE"]).encode(),
    }


def _describe(runtime_path: Path, abi_gate_path: Path, captured_gate_path: Path, preparer_path: Path) -> dict[str, Any]:
    """Validate the fixed prerequisite/ABI evidence and compute its complete runtime identity."""
    artifacts: dict[str, str] = {}
    runtime_ref = _bind(runtime_path, artifacts)
    runtime = _read(runtime_ref, artifacts)
    root = runtime_path.parent
    if (
        runtime["status"] != "source-api-blocked"
        or runtime["promoted"] is not False
        or runtime["workflow_ready"] is not False
        or any(runtime["gates"][key]["status"] != "success" for key in ("imports", "tiny_solver", "source_four_args"))
        or runtime["gates"]["captured_five_args"]["status"] != "expected-api-failure"
        or runtime["gates"]["captured_five_args"]["modified"] is not False
        or runtime["gates"]["captured_five_args"]["sha256"] != CAPTURED_SHA256
    ):
        raise ValueError("Runtime prerequisite gates are incomplete")
    preparer = _bind(preparer_path, artifacts, runtime["implementation_sha256"])
    scan = _read(runtime["source_scan"], artifacts)
    if scan["status"] != "no-escape-patterns-found" or scan["findings"] or scan["files_scanned"] <= 0:
        raise ValueError("Runtime source containment scan is not clear")
    pgids = _read(
        {"path": str(root / "pgids.json"), "sha256": runtime["gates"]["tiny_solver"]["pgids_sha256"]}, artifacts
    )
    if (
        pgids != runtime["pgid_observation"]
        or pgids["status"] != "observed-same-group"
        or pgids["cleanup"]["status"] != "drained"
        or pgids["cleanup"]["release"] != "sent"
        or pgids["cleanup"]["racket_returncode"] != 0
        or pgids["cleanup"]["snapshots"][-1]["remaining"] != []
        or any(row["pgid"] != pgids["expected_pgid"] for row in pgids["processes"])
    ):
        raise ValueError("Runtime process-group observation or drain is incomplete")
    executables = {
        "racket": RACKET_INSTALLATION / "bin/racket",
        "raco": RACKET_INSTALLATION / "bin/raco",
        "z3": root / "bin/z3",
    }
    if runtime["racket"]["path"] != str(executables["racket"]) or runtime["solver"]["path"] != str(executables["z3"]):
        raise ValueError("Runtime executable paths differ from the pinned installation")
    if (
        runtime["racket"]["sha256"] != EXECUTABLE_SHA256["racket"]
        or runtime["racket"]["raco_sha256"] != EXECUTABLE_SHA256["raco"]
        or runtime["solver"]["sha256"] != EXECUTABLE_SHA256["z3"]
        or not {str(executables["racket"]), str(executables["z3"])} <= {row["executable"] for row in pgids["processes"]}
    ):
        raise ValueError("Runtime executable identities were not observed")
    binary_refs = {}
    for name, path in executables.items():
        if not os.access(path, os.X_OK):
            raise ValueError(f"Runtime executable is unavailable: {path}")
        binary_refs[name] = _bind(path, artifacts, EXECUTABLE_SHA256[name])
    environment = runtime["environment"]
    if (
        set(environment) != {"PLTUSERHOME", "PLTADDONDIR", "TMPDIR", "HYDRIDE_ROOT", "MISAAL_Z3_PATH", "PATH"}
        or environment["PLTUSERHOME"] != str(root / "user")
        or environment["PLTADDONDIR"] != str(root / "addon")
        or environment["TMPDIR"] != str(root / "tmp")
        or environment["MISAAL_Z3_PATH"] != str(executables["z3"])
        or environment["PATH"] != f"{root / 'bin'}:{RACKET_INSTALLATION / 'bin'}:/usr/bin:/bin:/usr/sbin:/sbin"
    ):
        raise ValueError("Runtime environment differs from the isolated preparation")
    packages = runtime["installed_packages"]
    if set(packages) != set(PACKAGE_TREES):
        raise ValueError("Runtime package closure differs from the reviewed recipe")
    for name, package in packages.items():
        directory = Path(package["path"])
        if (
            not directory.resolve().is_relative_to(root / "addon")
            or package["tree"] != PACKAGE_TREES[name]
            or not package["files"]
        ):
            raise ValueError("Runtime package path/tree is not pinned")
        for relative, digest in package["files"].items():
            path = directory / relative
            if not path.resolve().is_relative_to(directory.resolve()):
                raise ValueError("Runtime package source escapes its installed directory")
            _bind(path, artifacts, digest)
    modules = runtime["gates"]["imports"]["module_paths"]
    if set(modules) != {"rosette", "hydride", "misaal"} or any(
        not Path(path).resolve().is_relative_to(Path(packages[name]["path"]).resolve())
        for name, path in modules.items()
    ):
        raise ValueError("Runtime active imports differ from the installed package closure")
    for path in modules.values():
        _bind(Path(path), artifacts)
    _bind(root / "smokes/parameter-four-args.rkt", artifacts, runtime["gates"]["source_four_args"]["sha256"])
    _bind(root / "smokes/captured-five-args.rkt", artifacts, CAPTURED_SHA256)
    for name, contents in _prepared_smokes(preparer_path).items():
        _bind(root / "smokes" / name, artifacts, hashlib.sha256(contents).hexdigest())
    isolated = ["/usr/bin/env", "-i", *[f"{key}={value}" for key, value in environment.items()]]
    steps = runtime["steps"]
    child = steps[0]["command"][:3]
    bootstrap = (
        f"import runpy,sys; sys.path.insert(0,{str(PREPARER.parent.parent)!r}); "
        f"runpy.run_path({str(PREPARER)!r}, run_name='__main__')"
    )
    if len(child) != 3 or child[1:] != ["-c", bootstrap] or not Path(child[0]).is_absolute():
        raise ValueError("Runtime preparer bootstrap differs from the reviewed source")
    _bind(Path(child[0]), artifacts)
    commands = {
        "acquire-pinned-packages": [*child, "_acquire", str(root / "sources")],
        "racket-version": [*isolated, str(executables["racket"]), "--version"],
        "z3-version": [*isolated, str(executables["z3"]), "--version"],
        "installation-packages": [*isolated, str(executables["raco"]), "pkg", "show", "--all", "--long", "--dir"],
        **{
            f"install-{name}": [
                *isolated,
                str(executables["raco"]),
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
                str(root / "sources" / name),
            ]
            for name in PACKAGE_TREES
        },
        "isolated-packages": [*isolated, str(executables["raco"]), "pkg", "show", "--all", "--long", "--dir"],
        "compile-imports": [*isolated, str(executables["raco"]), "make", str(root / "smokes/imports.rkt")],
        "imports": [*isolated, str(executables["racket"]), str(root / "smokes/imports.rkt")],
        "tiny-solver-pgid": [
            *isolated,
            *child,
            "_observe",
            str(executables["racket"]),
            str(root / "smokes/solver.rkt"),
            str(executables["z3"]),
            str(root / "pgids.json"),
        ],
        "parameter-four-args": [*isolated, str(executables["racket"]), str(root / "smokes/parameter-four-args.rkt")],
        "captured-five-args": [*isolated, str(executables["racket"]), str(root / "smokes/captured-five-args.rkt")],
    }
    if [step["name"] for step in steps] != list(commands):
        raise ValueError("Runtime prerequisite steps are missing, repeated, or out of order")
    for step in runtime["steps"]:
        if step["cwd"] != str(root) or step["command"] != commands[step["name"]]:
            raise ValueError("Runtime prerequisite step command or environment changed")
        for key in ("stdout_path", "stderr_path"):
            _bind(Path(step[key]), artifacts)
        _process_evidence(step, int(step["name"] == "captured-five-args"), artifacts, artifacts)

    abi_ref = _bind(abi_gate_path, artifacts)
    abi = _read(abi_ref, artifacts)
    if abi["status"] != "success" or abi["runtime"] != runtime_ref:
        raise ValueError("ABI gate did not succeed against this runtime")
    manifest = _read(abi["manifest"], artifacts)
    adaptation = manifest["adaptation_receipt"]["parameter_abi"]
    source = manifest["request"]
    source_hashes = {**PARAMETER_ABI_SOURCE_SHA256, SOURCE: SOURCE_SHA256}
    checkout = Path(source["checkout"])
    if (
        source["revision"] != REVISION
        or source["parameter_abi"] != PARAMETER_ABI_CONTRACT
        or any(source["source_hashes"].get(key) != value for key, value in PARAMETER_ABI_SOURCE_SHA256.items())
        or adaptation["contract"] != PARAMETER_ABI_CONTRACT
        or adaptation["status"] != "complete"
        or adaptation["paper_revision"] != PAPER_REVISION
        or adaptation["sources"] != PARAMETER_ABI_SOURCE_SHA256
        or set(adaptation["adapted_methods"]) != {"emit_synthesize_query", "generate_param_expr_general"}
        or environment["HYDRIDE_ROOT"] != str(checkout / "Hydride")
    ):
        raise ValueError("ABI gate lacks the exact mixed-revision source contract")
    for relative, digest in source_hashes.items():
        _bind(checkout / relative, artifacts, digest)
    helper = _bind(ABI_HELPER, artifacts, adaptation["implementation_sha256"])
    if abi["implementation"] != helper:
        raise ValueError("ABI gate implementation differs from the active adaptation")
    for name, digest in manifest["source_pins"].items():
        _bind(Path(name), artifacts, digest)
    if (
        set(manifest["programs"]) != set(ABI_RUNS)
        or len(abi["runs"]) != len(ABI_RUNS)
        or {row["name"] for row in abi["runs"]} != set(ABI_RUNS)
    ):
        raise ValueError("ABI gate requires both positive methods and both original negative controls")
    environment_prefix = [
        "/usr/bin/env",
        "-i",
        *[f"{key}={value}" for key, value in environment.items()],
        str(executables["racket"]),
    ]
    for name, digest in abi["artifacts"].items():
        _bind(Path(name), artifacts, digest)
    for row in abi["runs"]:
        program = manifest["programs"][row["name"]]
        _bind(Path(program["path"]), artifacts, program["sha256"])
        actual = Path(row["command"][-1])
        if (
            row["passed"] is not True
            or row["program_sha256"] != program["sha256"]
            or actual.name != Path(program["path"]).name
            or row["command"] != [*environment_prefix, str(actual)]
        ):
            raise ValueError("ABI gate did not execute the pinned emitted program/environment")
        _bind(actual, artifacts, program["sha256"])
        _process_evidence(row["process"], ABI_RUNS[row["name"]], abi["artifacts"], artifacts)
        if ABI_RUNS[row["name"]] == 0:
            result = row["result"]
            _bind(Path(result["path"]), artifacts, result["sha256"])
            if (
                abi["artifacts"][result["path"]] != result["sha256"]
                or not result["text"]
                or Path(result["path"]).read_text() != result["text"]
            ):
                raise ValueError("ABI gate has no retained positive solver result")

    captured_ref = _bind(captured_gate_path, artifacts)
    captured = _read(captured_ref, artifacts)
    if (
        captured["status"] != "success"
        or captured["runtime"] != runtime_ref
        or captured["contract"] != PARAMETER_ABI_CONTRACT
    ):
        raise ValueError("Captured-case ABI gate did not succeed against this runtime")
    original = Path(captured["original"]["path"])
    adapted = Path(captured["adapted"]["path"])
    _bind(original, artifacts, CAPTURED_SHA256)
    _bind(adapted, artifacts, captured["adapted"]["sha256"])
    if (
        captured["original"]["sha256"] != CAPTURED_SHA256
        or captured["replacement"] != {"before": CAPTURED_BEFORE, "after": CAPTURED_AFTER, "count": 1}
        or original.read_bytes().count(CAPTURED_BEFORE.encode()) != 1
        or adapted.read_bytes() != original.read_bytes().replace(CAPTURED_BEFORE.encode(), CAPTURED_AFTER.encode(), 1)
        or captured["command"] != [*environment_prefix, str(adapted)]
    ):
        raise ValueError("Captured-case ABI gate changed more than the exact reviewed call")
    for name, digest in captured["artifacts"].items():
        _bind(Path(name), artifacts, digest)
    _process_evidence(captured["process"], 0, captured["artifacts"], artifacts)
    value = captured["output"]
    _bind(Path(value["path"]), artifacts, value["sha256"])
    if (
        captured["artifacts"][value["path"]] != value["sha256"]
        or not value["text"]
        or Path(value["path"]).read_text() != value["text"]
    ):
        raise ValueError("Captured-case ABI gate has no retained solver result")
    roots = {"addon": root / "addon", "user": root / "user", "racket_installation": RACKET_INSTALLATION}
    return {
        "schema": CONTRACT,
        "status": "source-api-compatible",
        "scope": "prerequisite and mixed-revision ABI diagnostics; source workflow and replay still required",
        "runtime": runtime_ref,
        "abi_gate": abi_ref,
        "captured_gate": captured_ref,
        "preparer": preparer,
        "code_trees": {name: {"path": str(path), "sha256": directory_identity(path)} for name, path in roots.items()},
        "executables": binary_refs,
        "artifacts": artifacts,
        "environment": environment,
        "required_unset": list(REQUIRED_UNSET),
        "source": {"checkout": str(checkout), "revision": REVISION, "source_hashes": source_hashes},
        "parameter_abi": PARAMETER_ABI_CONTRACT,
        "racket_group_containment": GROUP_CONTRACT,
        "implementation": helper,
    }


def seal_runtime(
    runtime_path: Path,
    abi_gate_path: Path,
    output_path: Path,
    *,
    captured_gate_path: Path,
    preparer_path: Path | None = None,
) -> dict[str, Any]:
    """Write one new data-only seal; never modify original receipts or requests."""
    if output_path.exists():
        raise ValueError("Runtime seal output must be fresh")
    try:
        seal = _describe(
            runtime_path.resolve(),
            abi_gate_path.resolve(),
            captured_gate_path.resolve(),
            (preparer_path or PREPARER).resolve(),
        )
    except (KeyError, TypeError, IndexError) as error:
        raise ValueError(f"Incomplete runtime evidence: {error}") from error
    if any(output_path.resolve().is_relative_to(Path(row["path"])) for row in seal["code_trees"].values()):
        raise ValueError("Runtime seal must be outside its immutable code trees")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("x") as stream:
        json.dump(seal, stream, indent=2)
        stream.write("\n")
    return seal


def verify_runtime(request: dict[str, Any]) -> dict[str, Any]:
    """Reject changed code/evidence or an environment that bypasses the sealed runtime."""
    try:
        seal = _read(request["racket_runtime"], {})
        if seal["schema"] != CONTRACT or seal["status"] != "source-api-compatible":
            raise ValueError("Request does not reference a compatible runtime seal")
        for reference in (seal["runtime"], seal["abi_gate"], seal["captured_gate"], seal["preparer"]):
            _bind(Path(reference["path"]), {}, reference["sha256"])
        current = _describe(
            Path(seal["runtime"]["path"]),
            Path(seal["abi_gate"]["path"]),
            Path(seal["captured_gate"]["path"]),
            Path(seal["preparer"]["path"]),
        )
        if seal != current:
            raise ValueError("Runtime code tree or retained evidence changed after sealing")
        environment = request["environment"]
        expected = seal["environment"]
        if (
            request["parameter_abi"] != PARAMETER_ABI_CONTRACT
            or request["racket_group_containment"] != GROUP_CONTRACT
            or any(request[key] != value for key, value in seal["source"].items() if key != "source_hashes")
            or any(request["source_hashes"].get(key) != value for key, value in seal["source"]["source_hashes"].items())
            or request["racket"] != seal["executables"]["racket"]["path"]
            or request["racket_sha256"] != seal["executables"]["racket"]["sha256"]
            or not set(REQUIRED_UNSET) <= set(request["environment_unset"])
            or any(key in environment for key in REQUIRED_UNSET)
            or any(environment.get(key) != value for key, value in expected.items() if key != "PATH")
            or any(key.startswith("PLT") and key not in expected for key in environment)
            or environment["PATH"].split(os.pathsep)[:2] != expected["PATH"].split(os.pathsep)[:2]
            or shutil.which("racket", path=environment["PATH"]) != request["racket"]
            or shutil.which("z3", path=environment["PATH"]) != seal["executables"]["z3"]["path"]
        ):
            raise ValueError("Request bypasses the sealed runtime, environment, or ABI contract")
        return seal
    except (KeyError, TypeError, IndexError) as error:
        raise ValueError(f"Incomplete runtime request or evidence: {error}") from error
