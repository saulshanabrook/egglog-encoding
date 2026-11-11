"""Observe a complete MISAAL generator, including live Python/LLVM feedback.

`capture --request REQUEST --output FRESH_DIRECTORY` is the guarded entrypoint.
Other modes are child hooks in that process group, never standalone benchmarks.
See benchmarks/reproduction/misaal-hardboiled.md for the request contract.
"""

from __future__ import annotations

import argparse
import ast
import fcntl
import hashlib
import importlib
import inspect
import json
import math
import os
import re
import runpy
import shlex
import shutil
import subprocess
import sys
import threading
import time
import traceback
from collections.abc import Iterator
from contextlib import contextmanager, nullcontext
from dataclasses import asdict
from pathlib import Path
from types import ModuleType
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
EGGLOG_EXPORT = "egglog-only-v1"
EXPORT_SOURCE_KIND = "misaal-egglog-export"
ARM_TERMINAL_EMPTY = "arm-empty-terminal-v1"
ARM_TERMINAL_SOURCES = {
    "frontends/halide/src/misaal.cpp": "8e39a64c506e90a531d11f56bb3321b899ecb4da057988d28a3d786bfcc4e894",
    "frontends/halide/src/Rosette.cpp": "ed4ebbed55882df1396ef233c0f2394cc1f08461341ae217344c6c3002998911",
    "frontends/halide/src/CodeGen_LLVM.cpp": "d74788b6e6ad003503918ea42841efffb8d0fd8d4db32dee9aa51096eb80d453",
    "lib/patterns/ARM.py": "624d3a917e2a594272621105b3537aa2a2739829722beee716771f3212a5d269",
    "lib/patterns/PatternUtils.py": "e89b1a4c9dda901f2416100dbc6b5e47554264e00eb755c52c669f48b54eb8d5",
}
ACQUISITION_TAIL = "llvm-ir-only-v1"
ACQUISITION_TAIL_SOURCES = {
    "frontends/halide/src/CodeGen_LLVM.cpp": "d74788b6e6ad003503918ea42841efffb8d0fd8d4db32dee9aa51096eb80d453",
    "frontends/halide/src/CodeGen_Hexagon.cpp": "1f77a013e412dd3922d0c2c4242f71db29628df24aea5be4e56f77cec99857bf",
    "frontends/halide/src/Module.cpp": "f754bb2f100744373276e3223200e3d76a67f9cecf9225f2afadcc6df11129a9",
}


def acquisition_tail_request(request: dict[str, Any]) -> dict[str, Any]:
    """Derive the pinned terminal-output policy without changing source work or inputs."""
    flagged = "acquisition_tail" in request
    if (flagged and request["acquisition_tail"] != ACQUISITION_TAIL) or request["revision"] != (
        "44ff893445d664cd87f52b08a138260ed2015ba8"
    ):
        raise ValueError("Unsupported MISAAL acquisition-tail contract or revision")
    command = list(request["generator_command"])
    targets = {
        "x86": "host-x86-64-no_bounds_query-no_asserts",
        "arm": "arm-64-osx-arm_dot_prod-no_asserts-no_bounds_query",
        "hexagon": "hexagon-32-noos-no_bounds_query-no_asserts-hvx_128-hvx_v66",
    }
    target = targets.get(request.get("configuration", {}).get("target"))
    if (
        target is None
        or [arg for arg in command if arg.startswith("target=")] != [f"target={target}"]
        or any(command.count(option) != 1 or command.index(option) == len(command) - 1 for option in ("-e", "-f"))
    ):
        raise ValueError("Acquisition-tail requires one pinned target and one output selection/name")
    emission = command.index("-e") + 1
    name = command[command.index("-f") + 1]
    expected_emission = "stmt,h,llvm_assembly" if flagged else "static_library,stmt,h,llvm_assembly,assembly"
    suffixes = ("stmt", "h", "ll") if flagged else ("a", "stmt", "h", "ll", "s")
    if (
        re.fullmatch(r"[A-Za-z0-9_-]+", name) is None
        or command[emission] != expected_emission
        or request["expected_generator_outputs"] != [f"{name}.{suffix}" for suffix in suffixes]
    ):
        raise ValueError("Acquisition-tail output selection or expected outputs conflict")
    environment = request.get("environment")
    option = "HYDRIDE_DISABLE_LLVM_OPTS"
    if not isinstance(environment, dict) or (environment.get(option) != "1" if flagged else option in environment):
        raise ValueError("Acquisition-tail environment conflicts with the explicit policy")
    pins = dict(request["source_hashes"])
    checkout = Path(request["checkout"]).resolve()
    for relative, digest in ACQUISITION_TAIL_SOURCES.items():
        if relative in pins and pins[relative] != digest:
            raise ValueError(f"Acquisition-tail source pin conflicts: {relative}")
        source = (checkout / relative).resolve()
        if not source.is_relative_to(checkout) or hashlib.sha256(source.read_bytes()).hexdigest() != digest:
            raise ValueError(f"Acquisition-tail source bytes changed: {relative}")
        pins[relative] = digest
    command[emission] = "stmt,h,llvm_assembly"
    return {
        **request,
        "acquisition_tail": ACQUISITION_TAIL,
        "source_hashes": pins,
        "generator_command": command,
        "expected_generator_outputs": [f"{name}.{suffix}" for suffix in ("stmt", "h", "ll")],
        "environment": {**environment, option: "1"},
    }


def save_receipt(path: Path, value: Any) -> None:
    """Publish complete JSON atomically, including before a risky subprocess."""
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, default=str) + "\n")
    temporary.replace(path)


def verified_request(path: Path) -> dict[str, Any]:
    """Bind the actual generator, source, backend, verifier and Python inputs."""
    from benchmarking.memory_guard import GROUP_LIMIT_BYTES

    request: dict[str, Any] = json.loads(path.read_text())
    export = request.get("egglog_export")
    if "egglog_export" in request or any(
        name in request.get("environment", {}) for name in ("MISAAL_EXPORT_MODE", "MISAAL_EXPORT_EVENTS")
    ):
        from scripts.reproduction_misaal_export import verify_export_request

        if export != EGGLOG_EXPORT or any(
            key in request for key in ("terminal_empty_child", "acquisition_tail", "hvx_link_contract")
        ):
            raise ValueError("Unsupported or conflicting Egglog export request")
        if any(name in request.get("environment", {}) for name in ("MISAAL_EXPORT_MODE", "MISAAL_EXPORT_EVENTS")):
            raise ValueError("Egglog export environment is supplied only by the adapter")
        verify_export_request(request)
    source_memory = request.get("source_memory_limit_bytes", 5 * 1024**3)
    if (
        not isinstance(source_memory, int)
        or isinstance(source_memory, bool)
        or not 0 < source_memory <= GROUP_LIMIT_BYTES
    ):
        raise ValueError(f"MISAAL source_memory_limit_bytes must be a positive integer <= {GROUP_LIMIT_BYTES}")
    source_timeout = request.get("source_timeout_sec", 900)
    valid_timeout = isinstance(source_timeout, (int, float)) and not isinstance(source_timeout, bool)
    try:
        valid_timeout = valid_timeout and math.isfinite(source_timeout) and source_timeout > 0
    except OverflowError:
        valid_timeout = False
    if not valid_timeout:
        raise ValueError("MISAAL source_timeout_sec must be a finite positive number")
    if (
        not export
        and (
            "acquisition_tail" in request
            or (isinstance(request.get("environment"), dict) and "HYDRIDE_DISABLE_LLVM_OPTS" in request["environment"])
            or "stmt,h,llvm_assembly" in request["generator_command"]
        )
        and acquisition_tail_request(request) != request
    ):
        raise ValueError("Acquisition-tail request must retain its explicit policy and all source pins")
    if runtime := request.get("racket_runtime"):
        # Full package verification belongs at the outer capture boundary, not
        # at every compiler callback. Bind the referenced seal here as well so
        # request selection cannot silently use a replaced runtime description.
        seal_path = Path(runtime["path"])
        if not seal_path.is_absolute() or hashlib.sha256(seal_path.read_bytes()).hexdigest() != runtime["sha256"]:
            raise ValueError("MISAAL Racket runtime seal identity changed")
        seal = json.loads(seal_path.read_text())
        if seal.get("schema") != "misaal-racket-runtime-v1" or seal.get("status") != "source-api-compatible":
            raise ValueError("MISAAL Racket runtime has not passed its source API gates")
    if re.fullmatch(r"[0-9a-f]{40}", request["revision"]) is None:
        raise ValueError("MISAAL request must record a full source revision")
    if "parameter_abi" in request:
        from scripts.reproduction_misaal_patterns import PARAMETER_ABI_CONTRACT, PARAMETER_ABI_SOURCE_SHA256

        if request["parameter_abi"] != PARAMETER_ABI_CONTRACT or any(
            request["source_hashes"].get(path) != digest for path, digest in PARAMETER_ABI_SOURCE_SHA256.items()
        ):
            raise ValueError("Unsupported or unpinned MISAAL parameter ABI restoration")
    if "literal_width_guard" in request:
        from scripts.reproduction_misaal_patterns import LITERAL_WIDTH_CONTRACT, LITERAL_WIDTH_SOURCE_SHA256

        if (
            request["literal_width_guard"] != LITERAL_WIDTH_CONTRACT
            or request["revision"] != "44ff893445d664cd87f52b08a138260ed2015ba8"
            or any(request["source_hashes"].get(path) != digest for path, digest in LITERAL_WIDTH_SOURCE_SHA256.items())
        ):
            raise ValueError("Unsupported or unpinned MISAAL literal-width guard")
    if "terminal_empty_child" in request and (
        request["terminal_empty_child"] != ARM_TERMINAL_EMPTY
        or request["revision"] != "44ff893445d664cd87f52b08a138260ed2015ba8"
        or request.get("configuration") != {"target": "arm"}
        or request["environment"].get("MISAAL_DISABLE_FRONTEND_PATTERNS") != "1"
        or request["environment"].get("MISAAL_EQ_SAT_ITERS", "5") != "5"
        or request.get("pattern_cache_contract")
        != {
            "environment": "MISAAL_PATTERN_CACHE_DIR",
            "required": "adapter supplies a fresh empty attempt-owned directory before child imports",
            "generation": "unchanged",
            "default": "source lib/patterns when variable is absent",
        }
        or any(request["source_hashes"].get(path) != digest for path, digest in ARM_TERMINAL_SOURCES.items())
    ):
        raise ValueError("Unsupported or unpinned ARM terminal-empty source policy")
    checkout = Path(request["checkout"]).resolve()
    if containment := request.get("racket_group_containment"):
        from scripts.reproduction_misaal_groups import CONTRACT, SOURCE, SOURCE_SHA256

        if containment != CONTRACT or request["source_hashes"].get(SOURCE) != SOURCE_SHA256:
            raise ValueError("Unsupported pinned Racket group containment request")
        if not isinstance(request.get("racket"), str) or not isinstance(request.get("racket_sha256"), str):
            raise ValueError("Registered Racket containment requires a pinned executable path and SHA-256")
        racket = Path(request["racket"])
        if (
            not racket.is_absolute()
            or not racket.is_file()
            or not os.access(racket, os.X_OK)
            or hashlib.sha256(racket.read_bytes()).hexdigest() != request["racket_sha256"]
        ):
            raise ValueError("MISAAL Racket executable identity changed")
    required = {"lib/compiler/EggLogCompiler.py", "lib/compiler/HydrideCompiler.py"}
    if not required.issubset(request["source_hashes"]):
        raise ValueError("Request must pin both observed compiler implementations")
    for relative, expected in request["source_hashes"].items():
        source = (checkout / relative).resolve()
        if not source.is_relative_to(checkout) or hashlib.sha256(source.read_bytes()).hexdigest() != expected:
            raise ValueError(f"MISAAL source identity changed: {relative}")
    for key in ("backend", "python", "generator") if export else ("backend", "llvm_as", "python", "generator"):
        executable = Path(request[key])
        if not os.access(executable, os.X_OK):
            raise ValueError(f"Missing executable: {executable}")
        if hashlib.sha256(executable.read_bytes()).hexdigest() != request[f"{key}_sha256"]:
            raise ValueError(f"MISAAL {key} identity changed")
    for key in ("library",) if export else ("library", "legalizer"):
        if key in request and hashlib.sha256(Path(request[key]).read_bytes()).hexdigest() != request[f"{key}_sha256"]:
            raise ValueError(f"MISAAL {key} identity changed")
    if request["generator_command"][0] != request["generator"]:
        raise ValueError("Generator command does not use the recorded executable")
    if not any("{output}" in argument for argument in request["generator_command"]):
        raise ValueError("Generator output must be scoped using {output}")
    outputs = request["expected_generator_outputs"]
    if export and outputs:
        raise ValueError("Egglog export does not request native generator outputs")
    if not export and (not outputs or not any(name.endswith(".ll") for name in outputs)):
        raise ValueError("Expected generator outputs must include final LLVM")
    if any(Path(name).is_absolute() or ".." in Path(name).parts for name in outputs):
        raise ValueError("Expected generator outputs must stay inside the fresh attempt")
    if contract := request.get("hvx_link_contract"):
        wrapper = checkout / "Hydride/codegen-generator/tools/low-level-codegen/wrappers/hvx_wrappers.ll"
        if (
            contract["mode"] != "intrinsics-only"
            or request["configuration"] != {"target": "hexagon"}
            or request["environment"].get("HYDRIDE_TARGET") != "hvx"
            or Path(contract["omitted_wrapper"]).absolute() != wrapper
            or wrapper.exists()
            or wrapper.is_symlink()
        ):
            raise ValueError("Wrapper omission requires the exact absent HVX wrapper and intrinsic-only target")
        preparation = Path(contract["selector_preparation"])
        if hashlib.sha256(preparation.read_bytes()).hexdigest() != contract["selector_preparation_sha256"]:
            raise ValueError("HVX selector preparation identity changed")
        prepared = json.loads(preparation.read_text())
        if (
            prepared["status"] != "success"
            or prepared["target"] != "hvx"
            or prepared["revision"] != request["revision"]
            or prepared["hydride_revision"] != request["hydride_revision"]
            or Path(prepared["legalizer_path"]).resolve() != Path(request["legalizer"]).resolve()
            or prepared["legalizer_sha256"] != request["legalizer_sha256"]
            or hashlib.sha256(Path(request["legalizer"]).read_bytes()).hexdigest() != prepared["legalizer_sha256"]
        ):
            raise ValueError("HVX wrapper omission requires the successfully prepared intrinsic-only selector")
    return request


def validate_llvm(path: Path, expected_functions: set[str], llvm_as: Path, evidence: Path) -> dict[str, Any]:
    """Require real, well-formed LLVM defining every requested source function."""
    from scripts.reproduction_misaal_legalizer import audit_simd_lowering

    content = path.read_bytes()
    if not content:
        raise ValueError(f"Empty LLVM output: {path}")
    text = content.decode()
    definitions = {
        quoted or plain for quoted, plain in re.findall(r'^define\b[^@\n]*@(?:"([^"\n]+)"|([\w.$-]+))\(', text, re.M)
    }
    receipt: dict[str, Any] = {
        "path": str(path),
        "sha256": hashlib.sha256(content).hexdigest(),
        "functions": sorted(definitions),
        "required_functions": sorted(expected_functions),
        "verify_returncode": None,
    }
    if expected_functions:
        receipt["lowering_audit"] = audit_simd_lowering(text, expected_functions)
        if receipt["lowering_audit"]["status"] != "success":
            save_receipt(evidence.with_suffix(".json"), receipt)
            raise ValueError(f"Required SIMD lowering audit failed: {receipt['lowering_audit']}")
    if not definitions:
        raise ValueError("LLVM output defines no functions")
    command = [str(llvm_as), str(path), "-o", os.devnull]
    with evidence.with_suffix(".stdout.log").open("wb") as out, evidence.with_suffix(".stderr.log").open("wb") as err:
        result = subprocess.run(command, stdout=out, stderr=err, timeout=120, check=False)
    receipt.update(verify_command=command, verify_returncode=result.returncode)
    save_receipt(evidence.with_suffix(".json"), receipt)
    if result.returncode:
        raise ValueError(f"LLVM verifier rejected {path}")
    return receipt


def run_low_level(script: Path, arguments: list[str], directory: Path, *, omitted_wrapper: Path | None = None) -> int:
    """Execute the real legalizer script, checking its formerly unchecked tools."""
    commands: list[dict[str, Any]] = []
    original_system = os.system
    original_argv = sys.argv
    omitted = 0

    def checked_system(command: str | bytes | os.PathLike[str] | os.PathLike[bytes]) -> int:
        nonlocal omitted
        argv = shlex.split(os.fsdecode(command))
        if not argv or any(token in {"|", ";", "&&", "||", ">", "<"} for token in argv):
            raise ValueError("Unexpected shell syntax in LLVM tool command")
        source_argv = argv.copy()
        if omitted_wrapper is not None and Path(argv[0]).name == "llvm-link":
            expected = [argv[0], arguments[4] + ".ll", str(omitted_wrapper), "-o", arguments[4] + ".linked.bc"]
            if omitted or argv != expected or arguments[2] != str(omitted_wrapper):
                raise ValueError("Unexpected LLVM link command for intrinsic-only HVX")
            # The real module still passes through llvm-link/dis/opt. No empty
            # wrapper or successful placeholder output is manufactured.
            del argv[2]
            omitted += 1
        executable = shutil.which(argv[0])
        if executable is None:
            raise FileNotFoundError(argv[0])
        entry: dict[str, Any] = {
            "command": argv,
            "executable": executable,
            "executable_sha256": hashlib.sha256(Path(executable).read_bytes()).hexdigest(),
            "status": "running",
        }
        if source_argv != argv:
            entry.update(source_command=source_argv, omitted_wrapper=str(omitted_wrapper))
        commands.append(entry)
        save_receipt(directory / "tools.json", commands)
        result = subprocess.run(argv, timeout=120, check=False)
        entry.update(returncode=result.returncode, status="success" if result.returncode == 0 else "failure")
        save_receipt(directory / "tools.json", commands)
        if result.returncode:
            raise subprocess.CalledProcessError(result.returncode, argv)
        return 0

    try:
        os.system = checked_system
        sys.argv = [str(script), *arguments]
        sys.path.insert(0, str(script.parent))
        runpy.run_path(str(script), run_name="__main__")
        if not commands:
            raise ValueError("LLVM legalizer did not invoke any native tools")
        if omitted_wrapper is not None and omitted != 1:
            raise ValueError("Intrinsic-only HVX must omit exactly its one nonexistent wrapper")
        return 0
    except BaseException:
        (directory / "failure.txt").write_text(traceback.format_exc())
        traceback.print_exc()
        return 1
    finally:
        os.system = original_system
        sys.argv = original_argv


@contextmanager
def observe_pattern_helpers(
    modules: list[ModuleType], request: dict[str, Any], directory: Path, record: dict[str, Any], lock: Any
) -> Iterator[None]:
    """Observe the two direct validation subprocesses without changing their Boolean results."""
    sources = {
        "compiler.EggLogCompiler": "lib/compiler/EggLogCompiler.py",
        "patterns.PatternUtils": "lib/patterns/PatternUtils.py",
    }
    if {module.__name__ for module in modules} != set(sources):
        raise ValueError("Pattern-helper observation requires both source modules")
    if record.get("helper_observation", {}).get("status") in {"installing", "observing"}:
        record["helper_observation"].update(status="failure", reason="Recursive pattern-helper observation refused")
        raise ValueError(record["helper_observation"]["reason"])
    callers = {}
    originals = {}
    observation: dict[str, Any] = {"status": "installing", "sources": {}, "scope": "pattern-validation-only"}
    pending_deletions: dict[tuple[int, str], dict[str, Any]] = {}
    for module in modules:
        relative = sources[module.__name__]
        source = Path(module.__file__ or "").resolve()
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        if (
            source != (Path(request["checkout"]) / relative).resolve()
            or request["source_hashes"].get(relative) != digest
        ):
            raise ValueError(f"Request must pin the observed pattern-helper source: {relative}")
        if module.sb is not subprocess:
            raise ValueError("Pattern-helper subprocess binding is already instrumented or unsupported")
        callers[module.is_pattern_valid_egg.__code__] = module.__name__
        originals[module] = module.sb
        observation["sources"][str(source)] = digest
    record["helper_observation"] = observation
    record["helper_invocations"] = []

    def capture_helper(command: Any, *args: Any, **kwargs: Any) -> subprocess.CompletedProcess[Any]:
        # Only module-local aliases are replaced. This call and optimizer hooks
        # continue to use the real subprocess module, preventing double capture.
        with lock:
            frame = inspect.currentframe()
            caller = frame.f_back if frame is not None else None
            entry: dict[str, Any] = {
                "index": len(record["helper_invocations"]),
                "status": "running",
                "kind": "pattern-validation",
                "source_command": str(command),
                "caller": callers.get(caller.f_code) if caller else None,
                "admitted_as_workload": False,
            }
            try:
                if caller is None or caller.f_code not in callers or args or not isinstance(command, str):
                    raise ValueError("Unexpected pattern-helper subprocess caller or arguments")
                argv = shlex.split(command)
                if (
                    len(argv) != 2
                    or command != " ".join(argv)
                    or any(re.fullmatch(r"[A-Za-z0-9_./+-]+", value) is None for value in argv)
                ):
                    raise ValueError("Pattern-helper command must be exactly two literal shell arguments")
                if (
                    kwargs.get("shell") is not True
                    or set(kwargs) - {"shell", "stdout", "stderr"}
                    or any(kwargs.get(name) not in {None, subprocess.DEVNULL} for name in ("stdout", "stderr"))
                ):
                    raise ValueError("Unsupported pattern-helper subprocess options")
                filename = Path(argv[1]).resolve()
                deletion_key = (threading.get_ident(), str(filename))
                if argv[0] == "rm":
                    if kwargs != {"shell": True} or deletion_key not in pending_deletions:
                        raise ValueError("Pattern-helper deletion has no observed backend input")
                    previous = pending_deletions.pop(deletion_key)
                    previous["cleanup"] = {"command": argv, "status": "running"}
                    save_receipt(directory / "capture.json", record)
                    result = subprocess.run(argv, check=False, timeout=120)
                    previous["cleanup"].update(
                        status="success" if result.returncode == 0 else "failure", returncode=result.returncode
                    )
                    save_receipt(Path(previous["raw"]).with_suffix(".result.json"), previous)
                    save_receipt(directory / "capture.json", record)
                    result.args = command
                    return result
                compiler = caller.f_locals.get("compiler")
                if argv[0] != getattr(compiler, "egglog_bin", None) or filename.suffix != ".egg":
                    raise ValueError("Pattern-helper command does not name its compiler backend and Egglog input")
                raw = directory / f"helper-{entry['index']:04}.egg"
                raw.write_bytes(filename.read_bytes())
                entry.update(
                    raw=str(raw),
                    sha256=hashlib.sha256(raw.read_bytes()).hexdigest(),
                    source_input=str(filename),
                    source_backend=argv[0],
                    command=[request["backend"], str(filename)],
                    backend_sha256=request["backend_sha256"],
                )
                record["helper_invocations"].append(entry)
                save_receipt(directory / "capture.json", record)
                with raw.with_suffix(".stdout.log").open("wb") as out, raw.with_suffix(".stderr.log").open("wb") as err:
                    result = subprocess.run(entry["command"], stdout=out, stderr=err, check=False, timeout=120)
                for name, stream in (("stdout", sys.stdout), ("stderr", sys.stderr)):
                    content = raw.with_suffix(f".{name}.log").read_bytes()
                    if kwargs.get(name) != subprocess.DEVNULL:
                        stream.flush()
                        stream.buffer.write(content)
                        stream.buffer.flush()
                entry.update(status="success", returncode=result.returncode, accepted=result.returncode == 0)
                pending_deletions[deletion_key] = entry
                # Return the real process result with the original call's args
                # metadata. A nonzero exit remains the source's normal False.
                result.args = command
                return result
            except BaseException:
                entry.update(status="failure", error=traceback.format_exc())
                if entry not in record["helper_invocations"]:
                    record["helper_invocations"].append(entry)
                raise
            finally:
                if "raw" in entry:
                    for name in ("stdout", "stderr"):
                        path = Path(entry["raw"]).with_suffix(f".{name}.log")
                        if path.is_file():
                            entry[name + "_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
                    save_receipt(Path(entry["raw"]).with_suffix(".result.json"), entry)
                save_receipt(directory / "capture.json", record)

    class ScopedSubprocess:
        DEVNULL = subprocess.DEVNULL
        run = staticmethod(capture_helper)

        def __getattr__(self, name: str) -> Any:
            observation.update(status="failure", reason=f"Unsupported helper subprocess operation: {name}")
            save_receipt(directory / "capture.json", record)
            raise ValueError(observation["reason"])

    try:
        for module in modules:
            module.__dict__["sb"] = ScopedSubprocess()
        observation["status"] = "observing"
        save_receipt(directory / "capture.json", record)
        yield
        if observation["status"] == "failure" or any(
            item["status"] != "success" for item in record["helper_invocations"]
        ):
            raise ValueError("Generated child swallowed an unobserved or incomplete pattern-helper call")
        observation.update(status="success", completed_calls=len(record["helper_invocations"]))
    except BaseException:
        observation["status"] = "failure"
        raise
    finally:
        for module, original in originals.items():
            module.__dict__["sb"] = original
        save_receipt(directory / "capture.json", record)


def validate_export_events(path: Path, children: list[Path], attempt: Path) -> dict[str, Any]:
    """Close the source's nested module/function/child ledger against observed children."""
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    stack: list[dict[str, Any]] = []
    function: dict[str, Any] | None = None
    child: dict[str, Any] | None = None
    pending_root: int | None = None
    modules = functions = child_count = roots = 0
    for seq, row in enumerate(rows):
        if row.get("schema") != "misaal-export-v1" or type(row.get("seq")) is not int or row["seq"] != seq:
            raise ValueError("Export ledger schema or sequence differs")
        if any(
            type(value) is not int
            for key, value in row.items()
            if key.endswith("_id") and not (key == "parent_module_id" and value is None)
        ):
            raise ValueError("Export source identities must be integers")
        event = row.get("event")
        if event == "module_begin":
            if function is not None or child is not None or pending_root is not None:
                raise ValueError("Export module begins outside the source traversal")
            parent = stack[-1] if stack else None
            if (
                row.get("module_id") != modules
                or row.get("parent_module_id") != (parent["module_id"] if parent else None)
                or any(
                    type(row.get(key)) is not int or row[key] < 0
                    for key in ("module_id", "function_count", "submodule_count")
                )
                or (parent is not None and (parent["functions"] or parent["submodules"] >= parent["submodule_count"]))
            ):
                raise ValueError("Export module identity, counts or source order differs")
            for key in ("name_hex", "target_hex"):
                value = bytes.fromhex(row[key]).decode("utf-8")
                if not value or value.encode().hex() != row[key]:
                    raise ValueError("Export module name/target is not canonical UTF-8 hex")
            stack.append({**row, "functions": 0, "submodules": 0})
            modules += 1
        elif event == "function_begin":
            if (
                not stack
                or function is not None
                or child is not None
                or row.get("module_id") != stack[-1]["module_id"]
                or type(row.get("function_id")) is not int
                or row["function_id"] != functions
                or stack[-1]["submodules"] != stack[-1]["submodule_count"]
                or stack[-1]["functions"] >= stack[-1]["function_count"]
            ):
                raise ValueError("Export function identity or source order differs")
            name = bytes.fromhex(row["name_hex"]).decode("utf-8")
            if not name or name.encode().hex() != row["name_hex"]:
                raise ValueError("Export function name is not canonical UTF-8 hex")
            function = row
            functions += 1
        elif event == "child_begin":
            if (
                function is None
                or child is not None
                or any(row.get(key) != function[key] for key in ("module_id", "function_id"))
                or type(row.get("child_id")) is not int
                or row["child_id"] != child_count
                or child_count >= len(children)
            ):
                raise ValueError("Export child has no matching source function or observed receipt")
            script = bytes.fromhex(row["script_hex"]).decode("utf-8")
            if not script or script.encode().hex() != row["script_hex"]:
                raise ValueError("Export child script is not canonical UTF-8 hex")
            observed = json.loads(children[child_count].read_text())
            program = (attempt / script).resolve()
            if (
                not program.is_relative_to(attempt)
                or observed.get("source_event") != row
                or observed.get("program") != str(program)
                or observed.get("status") != "success"
                or observed.get("source_capture_complete") is not True
                or observed.get("source_kind") != EXPORT_SOURCE_KIND
                or observed.get("legalizations") != []
                or hashlib.sha256((children[child_count].parent / "generated.py").read_bytes()).hexdigest()
                != observed.get("program_sha256")
            ):
                raise ValueError("Export child receipt does not bind its exact source event and completion")
            export = observed["egglog_export"]
            execution = Path(export["execution"])
            if hashlib.sha256(execution.read_bytes()).hexdigest() != export["execution_sha256"]:
                raise ValueError("Executed export child changed after completion")
            if export["inputs"]:
                completion = export.get("compilation", {})
                selected = completion.get("selected", {})
                if (
                    completion.get("status") != "complete"
                    or completion.get("input_count") != len(export["inputs"])
                    or completion.get("invocation_count") != len(observed["invocations"])
                    or [item["name"] for item in completion.get("named_results", [])]
                    != [item["name"] for item in export["inputs"]]
                    or hashlib.sha256(Path(selected["path"]).read_bytes()).hexdigest() != selected["sha256"]
                ):
                    raise ValueError("Export child lacks complete named-input and selected-output accounting")
            elif export.get("source_exit_code") != 0 or observed["invocations"]:
                raise ValueError("Empty export child lacks its exact successful source exit")
            if any(call.get("status") != "success" for call in observed["invocations"]):
                raise ValueError("Export child contains unfinished optimizer work")
            child = row
            child_count += 1
        elif event == "child_end":
            if (
                child is None
                or any(row.get(key) != child[key] for key in ("module_id", "function_id", "child_id"))
                or type(row.get("returncode")) is not int
                or row["returncode"] != 0
            ):
                raise ValueError("Export child did not return successfully to its source parent")
            child = None
        elif event == "function_end":
            if (
                function is None
                or child is not None
                or any(row.get(key) != function[key] for key in ("module_id", "function_id"))
            ):
                raise ValueError("Export function ended with missing or unfinished child work")
            stack[-1]["functions"] += 1
            function = None
        elif event == "module_end":
            if (
                not stack
                or function is not None
                or child is not None
                or row.get("module_id") != stack[-1]["module_id"]
                or any(stack[-1][key] != stack[-1][key[:-1] + "_count"] for key in ("functions", "submodules"))
            ):
                raise ValueError("Export module ended before all declared source work")
            finished = stack.pop()
            if stack:
                stack[-1]["submodules"] += 1
            else:
                pending_root = finished["module_id"]
        elif event == "export_complete":
            if (
                stack
                or function is not None
                or child is not None
                or pending_root is None
                or row.get("root_module_id") != pending_root
                or any(
                    type(row.get(key)) is not int or row[key] != count
                    for key, count in (
                        ("module_count", modules),
                        ("function_count", functions),
                        ("child_count", child_count),
                    )
                )
            ):
                raise ValueError("Export completion does not close its entire source enumeration")
            pending_root = None
            roots += 1
        else:
            raise ValueError("Unknown export source event")
    if (
        not roots
        or stack
        or function is not None
        or child is not None
        or pending_root is not None
        or child_count != len(children)
    ):
        raise ValueError("Missing or unfinished export ledger or unmatched observed child")
    return {
        "path": str(path),
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "roots": roots,
        "modules": modules,
        "functions": functions,
        "children": child_count,
        "events": len(rows),
    }


def terminal_state(attempt: Path, feedback: Path, request: dict[str, Any] | None = None) -> dict[str, Any]:
    """Bind target cache bytes and the prior real child's native or export artifact."""
    stems = ["ARM"]
    if request is not None:
        stems = [{"arm": "ARM", "hexagon": "hvx", "x86": "x86"}[request["configuration"]["target"]]]
        if "MISAAL_DISABLE_FRONTEND_PATTERNS" not in request["environment"]:
            stems.insert(0, "halide")
    allowed = {f"{stem}{suffix}.pickle" for stem in stems for suffix in ("", "_abstract")}
    artifact = "selected" if request is not None else "feedback"
    cache = attempt / "pattern-cache"
    if cache.is_symlink() or not cache.is_dir() or feedback.is_symlink() or not feedback.is_file():
        raise ValueError("ARM terminal-empty requires its isolated cache and existing real LLVM feedback")
    paths = list(cache.iterdir())
    if any(path.is_symlink() or not path.is_file() or path.name not in allowed for path in paths):
        raise ValueError("Unexpected ARM terminal-empty pattern cache entry")
    hashes = {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}
    states = {
        stem: "abstract" if f"{stem}_abstract.pickle" in hashes else "raw" if f"{stem}.pickle" in hashes else "cold"
        for stem in stems
    }
    return {
        "cache_state": states if request is not None else states["ARM"],
        "cache_sha256": hashes,
        artifact: str(feedback),
        artifact + "_sha256": hashlib.sha256(feedback.read_bytes()).hexdigest(),
    }


def source_child_program(request: dict[str, Any], program: Path, directory: Path, record: dict[str, Any]) -> Path:
    """Recognize the exact emitter and make only the requested export/empty-tail edits.

    The source's cold/raw/abstract transitions are not interchangeable. Once an
    empty child defers setup, no later nonempty child is allowed in this parent.
    """
    export = request.get("egglog_export") == EGGLOG_EXPORT
    target = request["configuration"]["target"] if export else "arm"
    semantics, patterns, wrapper, flag, so_name = {
        "arm": ("arm", "ARM import arm_patterns", "arm_wrappers.c.ll", "arm", "libARMLegalizer.so"),
        "hexagon": ("hvx", "HVX import HVX_patterns", "hvx_wrappers.ll", "hex", "libHVXLegalizer.so"),
        "x86": ("x86", "x86 import x86_patterns", "x86_wrappers.c.ll", "x86", "libx86LegalizerAllArgs.so"),
    }[target]
    frontend = (
        "from patterns.Halide import Halide_patterns as misaal_input_patterns"
        if export and "MISAAL_DISABLE_FRONTEND_PATTERNS" not in request["environment"]
        else "misaal_input_patterns = []"
    )
    iterations = int(request["environment"].get("MISAAL_EQ_SAT_ITERS", "5")) if export else 5
    so_path = str(Path(request["environment"]["LEGALIZERS_DIR"]) / so_name) if export else request["legalizer"]
    attempt = directory.parent.parent
    prefix = os.environ["MISAAL_CAPTURE_LLVM_PREFIX"]
    hydride = str(Path(request["checkout"]) / "Hydride")
    expected = ast.parse(f"""from compiler.HydrideCompiler import HydrideCompiler
from utils.egg_config import EGG_PKG_PATH
from sema.hexsemantics_new import semantics as hvx_semantics
from sema.x86SemanticsAllArgs import semantcs as x86_semantics
from sema.halide_decomposed import halide_decomposed as halide_semantics
from sema.hvx_swizzles_decomposed import hvx_swizzles_decomposed as hvx_swizzles
from sema.x86_swizzles_decomposed import x86_swizzles_decomposed as x86_swizzles
from sema.arm_swizzles_decomposed import arm_swizzles_decomposed as arm_swizzles
from sema.ARMSema import arm_semantics
from sema.repairs_sema import repair_semantics
from utils.DSLInstructionUtils import parse_dict_with_bounded
import sys
{frontend}
from patterns.{patterns} as misaal_output_patterns
misaal_patterns = misaal_input_patterns + misaal_output_patterns
halide_dsl_list = parse_dict_with_bounded(halide_semantics)
misaal_input = halide_dsl_list
inst_dict = parse_dict_with_bounded({semantics}_semantics)
swizzle_dict = parse_dict_with_bounded({semantics}_swizzles)
misaal_output = inst_dict + swizzle_dict
so_path = {so_path!r}
llvm_flags = [{"-" + flag + "-hydride-legalize"!r}]
intrin = {hydride + "/codegen-generator/tools/low-level-codegen/wrappers/" + wrapper!r}
HYDRIDE_ROOT = {hydride!r}
tests = []
if len(tests) == 0:
    sys.exit(0)
misaal_compiler = HydrideCompiler(misaal_patterns, src_dsl_list=misaal_input, target_dsl_list=misaal_output,
    run_iterations={iterations}, egg_pkg_path=EGG_PKG_PATH, tests=tests, llvm_so_path=so_path, llvm_flags=llvm_flags,
    intrinsics_file=intrin, hydride_root_path=HYDRIDE_ROOT, llvm_out_file_name={prefix!r})
misaal_compiler.compile_hydride()
misaal_compiler.run_llvm_legalizer()
misaal_compiler.print_stats()
""")
    source = program.read_text()
    actual = ast.parse(source)
    # The fixed emitter has 24 setup statements, then tests=[], a literal
    # name/string/append triple for each expression, the exit guard and compiler.
    tests_index = 24
    tail_count = 5
    if (
        len(actual.body) < len(expected.body)
        or [ast.dump(node) for node in actual.body[: tests_index + 1]]
        != [ast.dump(node) for node in expected.body[: tests_index + 1]]
        or [ast.dump(node) for node in actual.body[-tail_count:]]
        != [ast.dump(node) for node in expected.body[-tail_count:]]
    ):
        raise ValueError("Generated child differs from the pinned ARM emitter template")
    definitions = actual.body[tests_index + 1 : -tail_count]
    if len(definitions) % 3:
        raise ValueError("Unexpected ARM generated test definitions")
    inputs = []
    for index in range(len(definitions) // 3):
        name, expression, append = definitions[index * 3 : index * 3 + 3]
        if not (
            isinstance(name, ast.Assign)
            and isinstance(name.value, ast.Constant)
            and isinstance(name.value.value, str)
            and isinstance(expression, ast.Assign)
            and isinstance(expression.value, ast.Constant)
            and isinstance(expression.value.value, str)
        ):
            raise ValueError("ARM generated tests must use literal source names and expressions")
        template = ast.parse(
            f"test_{index}_name = {name.value.value!r}\ntest_{index}_str = {expression.value.value!r}\n"
            f"tests.append((test_{index}_name, test_{index}_str))"
        )
        if [ast.dump(node) for node in (name, expression, append)] != [ast.dump(node) for node in template.body]:
            raise ValueError("Unexpected generated test construction")
        inputs.append(
            {
                "name": name.value.value,
                "expression": expression.value.value,
                "expression_sha256": hashlib.sha256(expression.value.value.encode()).hexdigest(),
            }
        )
    if export:
        record["egglog_export"] = {"contract": EGGLOG_EXPORT, "inputs": inputs}
        execution = directory / "egglog-export.py"
        lines = program.read_text().splitlines(keepends=True)
        legalizer = actual.body[-2]
        del lines[legalizer.lineno - 1 : legalizer.end_lineno]
        pending = directory.parent / "terminal-export.json"
        if definitions:
            if pending.exists():
                raise ValueError("Nonempty export child follows deferred terminal-empty cache initialization")
        else:
            # Empty before the first real child keeps its original imports/cache
            # transitions; only an actual real completion can open a deferred suffix.
            prior_paths = sorted(
                path for path in directory.parent.glob("child-*/capture.json") if path.parent != directory
            )
            prior = json.loads(prior_paths[-1].read_text()) if prior_paths else {}
            if pending.exists():
                boundary = json.loads(pending.read_text())
                if boundary["state"] != terminal_state(attempt, Path(boundary["state"]["selected"]), request):
                    raise ValueError("Export terminal-empty cache or selected output changed")
            elif prior.get("egglog_export", {}).get("inputs"):
                compiled = prior["egglog_export"].get("compilation", {})
                if prior.get("status") != "success" or compiled.get("status") != "complete":
                    raise ValueError("Export terminal-empty lacks a successful preceding real compilation")
                selected = compiled["selected"]
                state = terminal_state(attempt, Path(selected["path"]), request)
                if selected["sha256"] != state["selected_sha256"]:
                    raise ValueError("Export selected output changed before empty suffix")
                boundary = {
                    "contract": EGGLOG_EXPORT,
                    "first_empty": directory.name,
                    "state": state,
                    "previous_child": str(prior_paths[-1]),
                    "previous_child_sha256": hashlib.sha256(prior_paths[-1].read_bytes()).hexdigest(),
                }
                save_receipt(pending, boundary)
            else:
                boundary = None
            if boundary is not None:
                tests, guard = actual.body[tests_index], actual.body[-tail_count]
                moved = lines[tests.lineno - 1 : guard.end_lineno]
                del lines[tests.lineno - 1 : guard.end_lineno]
                position = actual.body[11].end_lineno
                assert position is not None
                lines[position:position] = moved
                record["egglog_export"]["terminal_boundary"] = boundary
        execution.write_text("".join(lines))
        generated = ast.parse(execution.read_text())
        guard = next(node for node in generated.body if isinstance(node, ast.If))
        record["egglog_export"].update(
            execution=str(execution),
            execution_sha256=hashlib.sha256(execution.read_bytes()).hexdigest(),
            exit_line=guard.body[0].lineno,
        )
        return execution
    pending = directory.parent / "terminal-empty.json"
    if definitions:
        if pending.exists():
            raise ValueError("Nonempty ARM child follows deferred terminal-empty cache initialization")
        return program
    feedback = Path(prefix + ".ll")
    before = terminal_state(attempt, feedback)
    if pending.exists():
        boundary = json.loads(pending.read_text())
        if before != boundary["state"]:
            raise ValueError("ARM terminal-empty cache or LLVM feedback changed after the first empty child")
    else:
        previous = sorted(path for path in directory.parent.glob("child-*/capture.json") if path.parent != directory)
        if not previous:
            raise ValueError("ARM terminal-empty has no preceding real child")
        prior = json.loads(previous[-1].read_text())
        legalizations = prior.get("legalizations", [])
        if (
            prior.get("status") != "success"
            or prior.get("source_capture_complete") is not True
            or not prior.get("invocations")
            or not legalizations
            or any(item.get("status") != "success" for item in legalizations)
            or legalizations[-1]["feedback"] != str(feedback)
            or legalizations[-1]["feedback_sha256"] != before["feedback_sha256"]
        ):
            raise ValueError("ARM terminal-empty requires the preceding real child's successful LLVM feedback")
        boundary = {
            "contract": ARM_TERMINAL_EMPTY,
            "first_empty": directory.name,
            "state": before,
            "previous_child": str(previous[-1]),
            "previous_child_sha256": hashlib.sha256(previous[-1].read_bytes()).hexdigest(),
        }
    assignment, guard = actual.body[tests_index], actual.body[-tail_count]
    lines = source.splitlines(keepends=True)
    moved = lines[assignment.lineno - 1 : guard.end_lineno]
    del lines[assignment.lineno - 1 : guard.end_lineno]
    insertion = actual.body[11].end_lineno
    assert insertion is not None
    lines[insertion:insertion] = moved
    execution = directory / "terminal-empty.py"
    execution.write_text("".join(lines))
    record["terminal_empty_child"] = {
        "contract": ARM_TERMINAL_EMPTY,
        "kind": "empty-source-helper",
        "admitted_as_workload": False,
        "execution": str(execution),
        "execution_sha256": hashlib.sha256(execution.read_bytes()).hexdigest(),
        "exit_line": insertion + len(moved),
        "boundary": boundary,
        "cache_policy": "defer initialization only for a terminal empty suffix; preserve cache and prior LLVM bytes",
    }
    if not pending.exists():
        # Retain the boundary even if this child fails: a native parent that
        # ignores its nonzero return must never run a later real child on it.
        save_receipt(pending, boundary)
    return execution


def observe_python(request_path: Path, attempt: Path, arguments: list[str]) -> int:
    """Run the actual generated child and return its real feedback to its parent."""
    request = verified_request(request_path)
    if len(arguments) != 1:
        raise ValueError("Expected one generated MISAAL Python file")
    program = Path(arguments[0]).resolve()
    if not program.is_relative_to(attempt) or not program.name.endswith("_misaal.py"):
        raise ValueError(f"Unexpected frontend Python child: {program}")
    children = attempt / "children"
    children.mkdir(exist_ok=True)
    with (children / ".lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        directory = children / f"child-{len(list(children.glob('child-*'))):04}"
        directory.mkdir()
    (directory / "generated.py").write_bytes(program.read_bytes())
    record: dict[str, Any] = {
        "program": str(program),
        "program_sha256": hashlib.sha256(program.read_bytes()).hexdigest(),
        "status": "running",
        "source_capture_complete": False,
        "invocations": [],
        "legalizations": [],
    }
    save_receipt(directory / "capture.json", record)
    checkout = Path(request["checkout"])
    sys.path[:0] = [str(checkout / "lib"), *os.environ.get("PYTHONPATH", "").split(os.pathsep)]
    capture_lock = threading.Lock()

    def capture_backend(self: Any, filename: str) -> str:
        from scripts.hardboiled_replay import egglog_forms
        from scripts.suite_capture_hardboiled_misaal import preserve_invocation

        with capture_lock:
            frame = inspect.currentframe()
            assert frame is not None and frame.f_back is not None
            raw = preserve_invocation(directory, Path(filename).read_bytes(), {"caller": frame.f_back.f_code.co_name})
            call: dict[str, Any] = {
                "index": len(record["invocations"]),
                "raw": str(raw),
                "sha256": hashlib.sha256(raw.read_bytes()).hexdigest(),
                "status": "running",
                "caller": frame.f_back.f_code.co_name,
                "source_backend": str(self.egglog_bin),
                "command": [request["backend"], str(raw)],
                "backend_sha256": request["backend_sha256"],
            }
            record["invocations"].append(call)
            save_receipt(directory / "capture.json", record)
            try:
                if guard := record.get("literal_width_guard"):
                    evidence = {}
                    for name in ("original", "guarded"):
                        item = guard[name + "_axioms"]
                        contents = Path(item["path"]).read_bytes()
                        if hashlib.sha256(contents).hexdigest() != item["sha256"]:
                            raise ValueError("Literal-width guard evidence changed before backend execution")
                        evidence[name] = contents
                    actual = raw.read_bytes()
                    count = actual.count(evidence["guarded"])
                    if count > 1 or evidence["original"] in actual or (count == 0 and not self.skip_axioms):
                        raise ValueError("Backend input does not contain the expected guarded axioms")
                    call["literal_width_guard"] = {"contract": guard["contract"], "guarded_axioms_copies": count}
                    if count:
                        reconstructed = actual.replace(evidence["guarded"], evidence["original"], 1)
                        counterpart = (
                            directory / "literal-width-guard" / raw.with_suffix(".unexecuted-original.egg").name
                        )
                        counterpart.write_bytes(reconstructed)
                        call["literal_width_guard"]["original_counterpart"] = {
                            "path": str(counterpart),
                            "sha256": hashlib.sha256(reconstructed).hexdigest(),
                            "executed": False,
                            "provenance": "reconstructed by replacing guarded axioms in the actual backend input",
                        }
                    save_receipt(directory / "capture.json", record)
                with raw.with_suffix(".stdout.log").open("wb") as out, raw.with_suffix(".stderr.log").open("wb") as err:
                    result = subprocess.run(call["command"], stdout=out, stderr=err, timeout=120, check=False)
                call["returncode"] = result.returncode
                content = raw.with_suffix(".stdout.log").read_text()
                call["stdout_sha256"] = hashlib.sha256(content.encode()).hexdigest()
                if result.returncode or not content.strip():
                    raise ValueError("Original Egglog backend failed or returned no expression")
                # Preserve the source API's last-line selection, with its full
                # stream retained independently. Never fabricate a continuation.
                selected = content.strip().splitlines()[-1]
                if len(egglog_forms(selected)) != 1:
                    raise ValueError("Backend result is not one complete expression")
                call.update(status="success", selected=selected)
                return selected
            except BaseException:
                call.update(status="failure", error=traceback.format_exc())
                raise
            finally:
                save_receipt(raw.with_suffix(".result.json"), call)
                save_receipt(directory / "capture.json", record)

    def checked_legalizer(self: Any) -> None:
        if request.get("egglog_export") == EGGLOG_EXPORT:
            raise ValueError("LLVM legalization is not requested by Egglog export")
        if any(call["status"] != "success" for call in record["invocations"]):
            raise ValueError("A failed backend call cannot proceed to LLVM legalization")
        prefix = Path(self.llvm_out_file_name)
        if prefix != Path(os.environ["MISAAL_CAPTURE_LLVM_PREFIX"]):
            raise ValueError("LLVM feedback path escaped the owned fresh prefix")
        functions = {name for name, _ in self.input_tests}
        if not functions:
            raise ValueError("No requested functions reached the LLVM legalizer")
        evidence = directory / f"legalize-{len(record['legalizations']):04}"
        evidence.mkdir()
        artifacts = [Path(str(prefix) + suffix) for suffix in (".ll", ".linked.bc", ".linked.ll", ".legalize.ll")]
        # The prefix was absent before the generator started. Repeated native
        # compilations may overwrite it; prior outputs already have durable copies.
        for artifact in artifacts:
            artifact.unlink(missing_ok=True)
        script = Path(self.hydride_root_path) / "codegen-generator/tools/low-level-codegen/RoseLowLevelCodeGen.py"
        required_inputs = [Path(self.output_file_path), Path(self.llvm_so_path), script]
        if (
            "legalizer" in request
            and hashlib.sha256(Path(self.llvm_so_path).read_bytes()).hexdigest() != request["legalizer_sha256"]
        ):
            raise ValueError("Source selected a legalizer with an unexpected identity")
        contract = request.get("hvx_link_contract")
        if contract:
            if Path(self.intrinsics_file).absolute() != Path(contract["omitted_wrapper"]):
                raise ValueError("Source selected an unexpected HVX wrapper")
            if Path(self.llvm_so_path).resolve() != Path(request["legalizer"]).resolve():
                raise ValueError("Source selected an unexpected HVX legalizer")
            required_inputs.append(Path(contract["selector_preparation"]))
        else:
            required_inputs.append(Path(self.intrinsics_file))
        entry: dict[str, Any] = {
            "status": "running",
            "required_functions": sorted(functions),
            "inputs": [
                {"path": str(p.resolve()), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
                for p in required_inputs
            ],
        }
        record["legalizations"].append(entry)
        if contract:
            entry["hvx_link_contract"] = contract
        save_receipt(directory / "capture.json", record)
        command = [
            request["python"],
            str(Path(__file__).resolve()),
            "low-level",
            "--request",
            str(request_path),
            "--output",
            str(evidence),
            "--script",
            str(script),
            "--",
            str(self.output_file_path),
            str(self.llvm_so_path),
            str(self.intrinsics_file),
            " ".join(self.llvm_flags),
            str(prefix),
        ]
        entry["command"] = command
        start = time.monotonic()
        try:
            with (evidence / "stdout.log").open("wb") as out, (evidence / "stderr.log").open("wb") as err:
                result = subprocess.run(command, stdout=out, stderr=err, timeout=600, check=False)
            entry["returncode"] = result.returncode
            if result.returncode:
                raise ValueError("Native LLVM legalization failed")
            if any(not p.is_file() or p.stat().st_size == 0 for p in artifacts):
                raise ValueError("Native LLVM legalization omitted an output")
            legal = Path(str(prefix) + ".legalize.ll")
            for artifact in artifacts:
                shutil.copyfile(artifact, evidence / artifact.name)
            entry["validation"] = validate_llvm(legal, functions, Path(request["llvm_as"]), evidence / "verify")
            # Same feedback operation as HydrideCompiler.run_llvm_legalizer: the
            # still-running Halide generator reads this exact .ll after return.
            shutil.copyfile(legal, Path(str(prefix) + ".ll"))
            entry.update(status="success", feedback=str(prefix) + ".ll", feedback_sha256=entry["validation"]["sha256"])
            self.compile_times.append(("LLVM Legalize", time.monotonic() - start))
        except BaseException:
            entry.update(status="failure", error=traceback.format_exc())
            raise
        finally:
            save_receipt(directory / "capture.json", record)

    try:
        if request.get("egglog_export") == EGGLOG_EXPORT:
            rows = Path(os.environ["MISAAL_EXPORT_EVENTS"]).read_text().splitlines()
            event = json.loads(rows[-1]) if rows else {}
            script = bytes.fromhex(event.get("script_hex", "")).decode("utf-8")
            if (
                event.get("schema") != "misaal-export-v1"
                or event.get("event") != "child_begin"
                or type(event.get("child_id")) is not int
                or event["child_id"] != int(directory.name.removeprefix("child-"))
                or (attempt / script).resolve() != program
            ):
                raise ValueError("Generated export child does not match the active parent source event")
            record.update(source_kind=EXPORT_SOURCE_KIND, source_event=event)
        execution = (
            source_child_program(request, program, directory, record)
            if "terminal_empty_child" in request or "egglog_export" in request
            else program
        )
        from scripts.reproduction_misaal_patterns import (
            accelerate_pattern_preparation,
            guard_literal_width,
            restore_parameter_abi,
        )

        egg_module = importlib.import_module("compiler.EggLogCompiler")
        pattern_module = importlib.import_module("patterns.PatternUtils")
        egg_compiler = egg_module.EggLogCompiler
        hydride_compiler = importlib.import_module("compiler.HydrideCompiler").HydrideCompiler
        egg_compiler.execute_egglog_file = capture_backend
        hydride_compiler.run_llvm_legalizer = checked_legalizer
        if request.get("egglog_export") == EGGLOG_EXPORT:
            original_compile = hydride_compiler.compile_hydride
            original_result = hydride_compiler.get_rosette_expression_str
            active: Any = None
            rendered: list[str] = []

            def observe_result(self: Any, input_expr: Any, output_expr: Any, function_name: str) -> str:
                if active is not self:
                    raise ValueError("Selected-expression serialization escaped original compilation")
                result = original_result(self, input_expr, output_expr, function_name)
                if not isinstance(result, str) or not result.strip():
                    raise ValueError("Original compilation produced an empty selected expression")
                rendered.append(result)
                record["egglog_export"]["compilation"]["named_results"].append(
                    {"name": function_name, "sha256": hashlib.sha256(result.encode()).hexdigest()}
                )
                return result

            def observe_compile(self: Any) -> Any:
                nonlocal active
                export = record["egglog_export"]
                expected = [(item["name"], item["expression"]) for item in export["inputs"]]
                if active is not None or "compilation" in export or not expected or self.input_tests != expected:
                    raise ValueError("Original compilation does not match every source-emitted named input")
                export["compilation"] = {"status": "running", "input_count": len(expected), "named_results": []}
                save_receipt(directory / "capture.json", record)
                active = self
                try:
                    result = original_compile(self)
                    selected = Path(self.output_file_path).absolute()
                    content = "\n".join(rendered).encode()
                    if (
                        [item["name"] for item in export["compilation"]["named_results"]]
                        != [name for name, _ in expected]
                        or not selected.is_relative_to(attempt)
                        or selected.is_symlink()
                        or selected.read_bytes() != content
                        or any(call["status"] != "success" for call in record["invocations"])
                    ):
                        raise ValueError("Original compilation did not complete every named result and backend call")
                    retained = directory / "selected-expressions.txt"
                    retained.write_bytes(content)
                    export["compilation"].update(
                        status="complete",
                        invocation_count=len(record["invocations"]),
                        selected={"path": str(retained), "sha256": hashlib.sha256(content).hexdigest()},
                    )
                    return result
                except BaseException:
                    export["compilation"]["status"] = "failure"
                    raise
                finally:
                    active = None
                    save_receipt(directory / "capture.json", record)

            hydride_compiler.compile_hydride = observe_compile
            hydride_compiler.get_rosette_expression_str = observe_result
        sys.argv = [str(program)]
        containment: Any = nullcontext()
        if request.get("racket_group_containment"):
            from scripts.reproduction_misaal_groups import observe_racket_launch

            endpoint = os.environ.get("MISAAL_RACKET_GROUP_SOCKET")
            if endpoint is None:
                raise ValueError("Known Racket launch containment has no live guard endpoint")
            containment = observe_racket_launch(
                importlib.import_module("utils.DSLInstructionUtils"), request, Path(endpoint)
            )
        with (
            containment,
            guard_literal_width(
                egg_module,
                request,
                directory,
                record,
                lambda: save_receipt(directory / "capture.json", record),
                capture_lock,
            ),
            restore_parameter_abi(
                pattern_module, request, record, lambda: save_receipt(directory / "capture.json", record)
            ),
            accelerate_pattern_preparation(
                pattern_module,
                request,
                record,
                lambda: save_receipt(directory / "capture.json", record),
                capture_lock,
            ),
            observe_pattern_helpers([egg_module, pattern_module], request, directory, record, capture_lock),
        ):
            try:
                runpy.run_path(str(execution), run_name="__main__")
            except SystemExit as error:
                empty = record.get("terminal_empty_child")
                if request.get("egglog_export") == EGGLOG_EXPORT and not record["egglog_export"]["inputs"]:
                    empty = record["egglog_export"]
                origin = error.__traceback__
                while origin is not None and origin.tb_next is not None:
                    origin = origin.tb_next
                if (
                    empty is None
                    or type(error.code) is not int
                    or error.code != 0
                    or origin is None
                    or origin.tb_frame.f_code.co_filename != str(execution)
                    or origin.tb_lineno != empty["exit_line"]
                ):
                    raise
                empty["source_exit_code"] = 0
        if export := record.get("egglog_export"):
            if record["legalizations"] or any(call["status"] != "success" for call in record["invocations"]):
                raise ValueError("Egglog export reached LLVM or unfinished optimizer work")
            if export["inputs"]:
                compiled = export.get("compilation", {})
                if compiled.get("status") != "complete" or compiled.get("invocation_count") != len(
                    record["invocations"]
                ):
                    raise ValueError("Original compile_hydride did not return with every captured call complete")
            elif export.get("source_exit_code") != 0 or record["invocations"]:
                raise ValueError("Empty export child lacks its exact original successful exit")
            if (boundary := export.get("terminal_boundary")) and (
                record["helper_invocations"]
                or terminal_state(attempt, Path(boundary["state"]["selected"]), request) != boundary["state"]
            ):
                raise ValueError("Deferred empty export changed source cache or selection state")
            record.update(status="success", source_capture_complete=True)
            return 0
        if empty := record.get("terminal_empty_child"):
            boundary = empty["boundary"]
            if (
                empty.get("source_exit_code") != 0
                or record["invocations"]
                or record["helper_invocations"]
                or record["legalizations"]
                or terminal_state(attempt, Path(boundary["state"]["feedback"])) != boundary["state"]
            ):
                raise ValueError("ARM terminal-empty child changed work, cache or LLVM feedback")
            record.update(status="success", source_capture_complete=True)
            return 0
        if not record["legalizations"] or any(item["status"] != "success" for item in record["legalizations"]):
            raise ValueError("Generated child did not complete native LLVM feedback")
        if any(item["status"] != "success" for item in record["invocations"]):
            raise ValueError("Generated child swallowed a failed Egglog call")
        record.update(status="success", source_capture_complete=True)
        return 0
    except BaseException:
        record.update(status="failure", error=traceback.format_exc())
        traceback.print_exc()
        return 1
    finally:
        save_receipt(directory / "capture.json", record)


def materialize_invocations(children: list[Path], replay_directory: Path, record: dict[str, Any]) -> None:
    """Package every observed backend call without running or changing its graph."""
    from scripts.hardboiled_replay import check_observed_selections, egglog_forms, native_check_contract
    from scripts.paper_benchmarks.materialize import prefix_atoms

    replay_directory.mkdir()
    record["materialization"] = {
        "expected_sessions": sum(len(json.loads(child.read_text())["invocations"]) for child in children),
        "materialized_sessions": 0,
        "complete": False,
    }
    for child in children:
        for call in json.loads(child.read_text())["invocations"]:
            raw = Path(call["raw"]).read_text()
            if hashlib.sha256(raw.encode()).hexdigest() != call["sha256"]:
                raise ValueError("Captured backend input changed before replay preparation")
            stdout = Path(call["raw"]).with_suffix(".stdout.log").read_bytes()
            if hashlib.sha256(stdout).hexdigest() != call["stdout_sha256"]:
                raise ValueError("Captured backend output changed before replay preparation")
            forms = egglog_forms(raw)
            names = {tokens[2] for _, _, tokens in forms if tokens[1] == "let"}
            boundary = next((start for start, _, tokens in forms if tokens[1] == "let"), len(raw))
            modern = raw[:boundary] + prefix_atoms(raw[boundary:], names)
            replay, selections = check_observed_selections(modern, stdout.decode())
            extracts = [i for i, (_, _, tokens) in enumerate(egglog_forms(replay)) if tokens[1] == "extract"]
            destination = replay_directory / f"invocation-{len(record['invocations']):04}.egg"
            destination.write_text(replay)
            record["invocations"].append(
                {
                    **call,
                    "child": str(child),
                    "replay": str(destination),
                    "replay_sha256": hashlib.sha256(replay.encode()).hexdigest(),
                    "selections": selections,
                    "root_count": len(selections),
                    "output_contract": native_check_contract(
                        replay, [(i + 1, s["check"]) for i, s in zip(extracts, selections, strict=True)], selections
                    ),
                    "ordinary_contract": "Original extracts plus equality checks for all actual backend selections",
                }
            )
            record["materialization"]["materialized_sessions"] = len(record["invocations"])
    if not record["invocations"]:
        raise ValueError("No reached Egglog work; classify this source as a helper, not an optimization replay")
    record.update(
        status="ordinary-validation-pending",
        workloads=[item["replay"] for item in record["invocations"]],
        reason=(
            "Original Egglog export completed; standalone outputs await ordinary validation"
            if record.get("source_kind") == EXPORT_SOURCE_KIND
            else "Native generator and LLVM feedback completed; standalone outputs await ordinary validation"
        ),
    )
    record["materialization"]["complete"] = True


def run_frontend(request_path: Path, attempt: Path, *, group_endpoint: Path | None = None) -> int:
    """Keep the native parent alive until all compiler outputs are verified."""
    request = verified_request(request_path)
    if any(name in os.environ for name in ("MISAAL_EXPORT_MODE", "MISAAL_EXPORT_EVENTS")):
        raise ValueError("Ambient export activation is not a verified request")
    export = request.get("egglog_export") == EGGLOG_EXPORT
    patterns = Path(request["checkout"]) / "lib/patterns"
    if list(patterns.glob("*.pickle")):
        raise ValueError("Canary requires a prepared checkout with fresh pattern caches")
    attempt.mkdir(parents=True, exist_ok=False)
    save_receipt(attempt / "request.json", request)
    environment = dict(os.environ)
    for key in request.get("environment_unset", []):
        environment.pop(key, None)
    for key in list(environment):
        if key.startswith(("HL_", "HYDRIDE_", "MISAAL_", "PLT")):
            del environment[key]
    environment.update(request["environment"])
    if export:
        environment.update(
            MISAAL_EXPORT_MODE=EGGLOG_EXPORT, MISAAL_EXPORT_EVENTS=str((attempt / "parent-export.jsonl").resolve())
        )
    environment.pop("MISAAL_RACKET_GROUP_SOCKET", None)
    if request.get("racket_group_containment"):
        if group_endpoint is None:
            raise ValueError("Known Racket launch containment requires the guarded capture entrypoint")
        environment["MISAAL_RACKET_GROUP_SOCKET"] = str(group_endpoint)
    cache_contract = request.get("pattern_cache_contract")
    if cache_contract is not None:
        if cache_contract.get("environment") != "MISAAL_PATTERN_CACHE_DIR":
            raise ValueError("unknown pattern cache isolation contract")
        patterns = attempt / "pattern-cache"
        patterns.mkdir()
        environment["MISAAL_PATTERN_CACHE_DIR"] = str(patterns.resolve())
    base_name = environment.get("HYDRIDE_BENCHMARK", request["case_id"])
    suffix = hashlib.sha256(str(attempt).encode()).hexdigest()[:16]
    benchmark = re.sub(r"[^A-Za-z0-9_-]", "_", base_name) + "__capture_" + suffix
    prefix = Path("/tmp") / benchmark
    if list(prefix.parent.glob(prefix.name + ".*")):
        raise ValueError("Owned LLVM prefix already exists; choose a fresh attempt")
    environment.update(
        HYDRIDE_BENCHMARK=benchmark,
        MISAAL_CAPTURE_LLVM_PREFIX=str(prefix),
        MISAAL_SRC=request["checkout"],
        MISAAL_ROOT_DIR=request["checkout"],
    )
    shim = attempt / "shim"
    shim.mkdir()
    wrapper = shim / "python3"
    wrapper.write_text(
        "#!/bin/sh\nexec "
        + " ".join(
            shlex.quote(value)
            for value in (
                request["python"],
                str(Path(__file__).resolve()),
                "child",
                "--request",
                str(request_path),
                "--output",
                str(attempt),
                "--",
            )
        )
        + ' "$@"\n'
    )
    wrapper.chmod(0o755)
    environment["PATH"] = str(shim) + os.pathsep + environment["PATH"]
    command = [argument.replace("{output}", str(attempt)) for argument in request["generator_command"]]
    record: dict[str, Any] = {
        "case_id": request["case_id"],
        "revision": request["revision"],
        "command": command,
        "environment": request["environment"],
        "pattern_cache_directory": str(patterns),
        "source_capture_complete": False,
        "status": "running",
        "output_name_adaptation": {"original": base_name, "actual": benchmark, "feedback_prefix": str(prefix)},
        "children": [],
        "native_outputs": [],
        "device_execution": False,
        "workloads": [],
        "invocations": [],
        "source_completion": {"status": "running", "outputs": []},
    }
    if export:
        record.update(source_kind=EXPORT_SOURCE_KIND, native_codegen="not_requested")
    if "acquisition_tail" in request:
        record["acquisition_tail"] = request["acquisition_tail"]
    save_receipt(attempt / "capture.json", record)
    try:
        result = subprocess.run(command, cwd=attempt, env=environment, check=False)
        record["generator_returncode"] = result.returncode
        record["source_completion"]["parent_returncode"] = result.returncode
        children = sorted((attempt / "children").glob("child-*/capture.json"))
        record["children"] = [{"path": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()} for p in children]
        if (
            result.returncode
            or (not children and not export)
            or [path.parent for path in children] != sorted((attempt / "children").glob("child-*"))
            or any(not json.loads(p.read_text())["source_capture_complete"] for p in children)
        ):
            raise ValueError("Generator or a reached Python/LLVM child did not complete")
        if export:
            record["export_enumeration"] = validate_export_events(attempt / "parent-export.jsonl", children, attempt)
            if (
                any(attempt.glob("*.ll"))
                or any(attempt.glob("*.bc"))
                or any(attempt.glob("*.a"))
                or any(attempt.glob("*.s"))
                or list(prefix.parent.glob(prefix.name + ".*"))
            ):
                raise ValueError("Egglog export unexpectedly created native outputs")
            marker = attempt / "children/terminal-export.json"
            if marker.exists():
                boundary = json.loads(marker.read_text())
                previous = Path(boundary["previous_child"])
                if (
                    boundary.get("contract") != EGGLOG_EXPORT
                    or hashlib.sha256(previous.read_bytes()).hexdigest() != boundary["previous_child_sha256"]
                    or terminal_state(attempt, Path(boundary["state"]["selected"]), request) != boundary["state"]
                ):
                    raise ValueError("Export terminal-empty boundary changed before completion")
                empty_suffix = [path for path in children if path.parent.name >= boundary["first_empty"]]
                if not empty_suffix:
                    raise ValueError("Export terminal boundary has no executed empty child")
                for path in empty_suffix:
                    observed = json.loads(path.read_text())
                    empty = observed.get("egglog_export", {})
                    if (
                        empty.get("inputs") != []
                        or empty.get("terminal_boundary") != boundary
                        or empty.get("source_exit_code") != 0
                        or observed["invocations"]
                        or observed["helper_invocations"]
                    ):
                        raise ValueError("Export terminal suffix contains changed or nonempty source work")
                record["export_terminal_empty"] = {
                    "boundary": boundary,
                    "children": [str(path) for path in empty_suffix],
                    "admitted_workloads": 0,
                }
            elif any("terminal_boundary" in json.loads(path.read_text()).get("egglog_export", {}) for path in children):
                raise ValueError("Export terminal boundary receipt is missing")
        if "terminal_empty_child" in request:
            marker = attempt / "children/terminal-empty.json"
            if not marker.exists() and any(
                "terminal_empty_child" in json.loads(child.read_text()) for child in children
            ):
                raise ValueError("ARM terminal-empty source boundary receipt is missing")
            if marker.exists():
                boundary = json.loads(marker.read_text())
                prior = Path(boundary["previous_child"])
                if (
                    hashlib.sha256(prior.read_bytes()).hexdigest() != boundary["previous_child_sha256"]
                    or terminal_state(attempt, Path(boundary["state"]["feedback"])) != boundary["state"]
                ):
                    raise ValueError("ARM terminal-empty boundary changed before parent completion")
                empty_suffix = [path for path in children if path.parent.name >= boundary["first_empty"]]
                if not empty_suffix:
                    raise ValueError("ARM terminal-empty boundary has no executed child")
                for child in empty_suffix:
                    observed = json.loads(child.read_text())
                    empty = observed.get("terminal_empty_child", {})
                    if (
                        empty.get("boundary") != boundary
                        or empty.get("source_exit_code") != 0
                        or empty.get("admitted_as_workload") is not False
                        or observed["invocations"]
                        or observed["legalizations"]
                        or observed["helper_invocations"]
                        or hashlib.sha256(Path(empty["execution"]).read_bytes()).hexdigest()
                        != empty["execution_sha256"]
                    ):
                        raise ValueError("ARM terminal-empty suffix lacks exact successful empty-child evidence")
                record["terminal_empty_child"] = {
                    "contract": ARM_TERMINAL_EMPTY,
                    "boundary": boundary,
                    "children": [str(child) for child in empty_suffix],
                    "status": "complete",
                    "admitted_workloads": 0,
                }
        for name in request["expected_generator_outputs"]:
            output = attempt / name
            if not output.is_file() or output.stat().st_size == 0:
                raise ValueError(f"Missing final generator output: {name}")
            item: dict[str, Any] = {"path": str(output), "sha256": hashlib.sha256(output.read_bytes()).hexdigest()}
            if output.suffix == ".ll":
                item["llvm_validation"] = validate_llvm(
                    output, set(), Path(request["llvm_as"]), attempt / (output.name + ".verify")
                )
            record["native_outputs"].append(item)
        record.update(source_capture_complete=True)
        record["source_completion"] = {
            "status": "success",
            "parent_returncode": result.returncode,
            "outputs": record["native_outputs"],
            "children": record["children"],
        }
        if export:
            record["source_completion"].update(
                source_kind=EXPORT_SOURCE_KIND, native_codegen="not_requested", enumeration=record["export_enumeration"]
            )
        helper_calls = [call for child in children for call in json.loads(child.read_text())["helper_invocations"]]
        record["helper_accounting"] = {
            "status": "success",
            "calls": len(helper_calls),
            "accepted": sum(call["accepted"] for call in helper_calls),
            "rejected": sum(not call["accepted"] for call in helper_calls),
            "admitted_workloads": 0,
        }
        if export and not any(json.loads(path.read_text())["invocations"] for path in children):
            record.update(
                status="source-helper", reason="Complete source export reached no optimizer sessions", workloads=[]
            )
            return 0
        materialize_invocations(children, attempt / "replays", record)
        return 0
    except BaseException:
        record.update(status="failure", reason=str(sys.exc_info()[1]), error=traceback.format_exc())
        if not record["source_capture_complete"]:
            record["source_completion"]["status"] = "failure"
        traceback.print_exc()
        return 1
    finally:
        record["pattern_cache_after"] = []
        for path in sorted(patterns.glob("*.pickle")):
            with path.open("rb") as stream:
                record["pattern_cache_after"].append(
                    {"path": str(path), "sha256": hashlib.file_digest(stream, "sha256").hexdigest()}
                )
        save_receipt(attempt / "capture.json", record)


def capture_misaal(request_path: Path, output: Path) -> dict[str, Any]:
    """Run one source parent with inherited children and registered Racket groups.

    Call directly from a coordinator, not from another session-creating guard.
    LLVM/backend children inherit the root group; pinned detached Racket groups
    require the outer guard's live launch lease and aggregate RSS accounting.
    """
    from benchmarking.pilot import run_bounded_command

    request_path, output = request_path.resolve(), output.resolve()
    request = verified_request(request_path)
    from scripts.reproduction_misaal_groups import CONTRACT, RacketGroups

    if request.get("racket_group_containment") != CONTRACT:
        raise ValueError(
            "Complete MISAAL capture requires a prepared registered-group contract and pinned Racket executable"
        )
    from scripts.reproduction_misaal_runtime import verify_runtime

    verify_runtime(request)
    output.mkdir(parents=True, exist_ok=False)
    save_receipt(output / "request.json", request)
    command = [
        request["python"],
        str(Path(__file__).resolve()),
        "frontend",
        "--request",
        str(output / "request.json"),
        "--output",
        str(output / "generation"),
    ]
    groups = RacketGroups(output / "group-containment")
    command.extend(["--group-endpoint", str(groups.endpoint)])
    try:
        process = run_bounded_command(
            command,
            ROOT,
            output / "process",
            timeout_sec=request.get("source_timeout_sec", 900),
            memory_limit_bytes=request.get("source_memory_limit_bytes", 5 * 1024**3),
            require_guard=True,
            disk_reserve_bytes=10 * 1024**3,
            allow_warning_pressure=True,
            sample_rss=groups.sample,
            cleanup_descendants=groups.close,
        )
    finally:
        if not groups.closed:
            groups.close()
    save_receipt(output / "process.json", asdict(process))
    receipt = output / "generation/capture.json"
    record = (
        json.loads(receipt.read_text())
        if receipt.is_file()
        else {
            "case_id": request["case_id"],
            "source_capture_complete": False,
            "source_completion": {"status": "not-reached", "outputs": []},
            "invocations": [],
            "workloads": [],
        }
    )
    if request.get("egglog_export") == EGGLOG_EXPORT:
        record.update(source_kind=EXPORT_SOURCE_KIND, native_codegen="not_requested")
    record["process"] = asdict(process)
    record["source_timeout_sec"] = request.get("source_timeout_sec", 900)
    record["source_memory_limit_bytes"] = request.get("source_memory_limit_bytes", 5 * 1024**3)
    record["process_accounting"] = {
        "contract": groups.record["contract"],
        "scope": groups.record["scope"],
        "receipt": str(groups.directory / "groups.json"),
        "sha256": hashlib.sha256((groups.directory / "groups.json").read_bytes()).hexdigest(),
    }
    if process.status != "success":
        record.update(status=process.status, reason=process.message or "Source attempt did not finish", workloads=[])
        if not record["source_capture_complete"]:
            record["source_completion"].update(status="incomplete", process=asdict(process))
    try:
        verify_runtime(request)
    except (OSError, ValueError) as error:
        # Preserve the actual process outcome even when runtime drift prevents
        # accepting its outputs. Never publish a successful partial capture.
        record.update(
            status="blocked" if process.status == "success" else process.status,
            reason=f"Racket runtime changed during capture: {error}",
            workloads=[],
        )
    record["racket_runtime"] = request.get("racket_runtime")
    save_receipt(output / "capture.json", record)
    return record


def capture_implementation_contract(source: str) -> tuple[str, str]:
    """Compare archived native hooks and the narrowly extracted packaging body."""
    functions = {node.name: node for node in ast.parse(source).body if isinstance(node, ast.FunctionDef)}
    frontend = functions["run_frontend"]
    execution = next(node for node in frontend.body if isinstance(node, ast.Try))
    boundary = next((index for index, node in enumerate(execution.body) if isinstance(node, ast.ImportFrom)), None)
    if boundary is not None:
        packaging = execution.body[boundary:-1]
        packaging = [
            node
            for node in packaging
            if not isinstance(node, ast.ImportFrom)
            and not (
                isinstance(node, ast.Assign)
                and isinstance(node.targets[0], ast.Name)
                and node.targets[0].id == "replay_directory"
            )
        ]
        execution.body[boundary:-1] = ast.parse("materialize_invocations(children, attempt / 'replays', record)").body
    else:
        packaging = [
            node for node in functions["materialize_invocations"].body[1:] if not isinstance(node, ast.ImportFrom)
        ]
    native: list[ast.stmt] = [
        functions[name]
        for name in (
            "save_receipt",
            "verified_request",
            "validate_llvm",
            "run_low_level",
            "observe_python",
            "run_frontend",
            "capture_misaal",
        )
    ]
    for optional in (
        "observe_pattern_helpers",
        "acquisition_tail_request",
        "arm_terminal_state",
        "arm_terminal_program",
        "terminal_state",
        "source_child_program",
        "validate_export_events",
    ):
        if optional in functions:
            native.append(functions[optional])
    native.extend(
        node
        for node in ast.parse(source).body
        if isinstance(node, ast.Assign)
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id in {"ARM_TERMINAL_EMPTY", "ARM_TERMINAL_SOURCES", "EGGLOG_EXPORT", "EXPORT_SOURCE_KIND"}
    )
    return ast.dump(ast.Module(body=native, type_ignores=[])), ast.dump(ast.Module(body=packaging, type_ignores=[]))


def materialize_complete_capture(source_stage: Path, output: Path, *, native_implementation: Path) -> dict[str, Any]:
    """Recover packaging from sealed native success; never rerun a native tool.

    The original stage and every retained artifact must still match. A wrapper's
    packaging failure is historical evidence, not a failed native parent that
    this function may waive. Ordinary replay remains a separate required gate.
    """
    source_stage, output = source_stage.resolve(), output.resolve()
    if output.exists() or output.is_relative_to(source_stage.parent):
        raise ValueError("recovery requires a fresh output outside the original attempt")
    output.mkdir(parents=True)
    record: dict[str, Any] = {"status": "failure", "workloads": [], "invocations": []}
    evidence: dict[str, str] = {}

    def verify(path: Path, expected: str | None = None, *, retained: bool = True) -> str:
        """Check sealed membership and bytes before admitting any referenced file."""
        path = path.absolute()
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if expected is not None and actual != expected.removeprefix("sha256:"):
            raise ValueError(f"Recovery evidence changed: {path}")
        if retained and (
            not path.is_relative_to(source_stage.parent)
            or stage["artifacts"].get(str(path), "").removeprefix("sha256:") != actual
        ):
            raise ValueError(f"Recovery evidence was not sealed by the original stage: {path}")
        evidence[str(path)] = actual
        return actual

    try:
        stage = json.loads(source_stage.read_text())
        verify(source_stage, retained=False)
        old_hooks = {
            path: digest
            for path, digest in stage["identity"]["inputs"].items()
            if path.endswith("/scripts/misaal_reproduction.py")
        }
        if len(old_hooks) != 1:
            raise ValueError("Original stage must identify exactly one native capture implementation")
        verify(native_implementation, next(iter(old_hooks.values())), retained=False)
        if capture_implementation_contract(native_implementation.read_text()) != capture_implementation_contract(
            Path(__file__).read_text()
        ):
            raise ValueError("Archived native capture or packaging differs beyond the supported import/helper repair")
        if not stage.get("artifacts"):
            raise ValueError("Recovery requires original stage artifact hashes")
        for path, digest in stage["artifacts"].items():
            verify(Path(path), digest)
        capture_path = Path(stage["capture"])
        verify(capture_path)
        native = json.loads(capture_path.read_text())
        # The stage recorder seals both the returned capture and native receipts.
        capture = source_stage.parent / "capture"
        generation = capture / "generation"
        for path in (
            capture / "capture.json",
            generation / "capture.json",
            capture / "request.json",
            generation / "request.json",
            capture / "process.json",
        ):
            verify(path)
        if json.loads((capture / "capture.json").read_text()) != native:
            raise ValueError("Returned capture differs from the sealed native receipt")
        frontend = json.loads((generation / "capture.json").read_text())
        request = verified_request(capture / "request.json")
        if json.loads((generation / "request.json").read_text()) != request:
            raise ValueError("Native frontend request differs from the sealed capture request")
        if native.get("case_id") != request["case_id"] or native.get("revision") != request["revision"]:
            raise ValueError("Native capture identity differs from its request")
        for key in (
            "generator_returncode",
            "source_capture_complete",
            "source_completion",
            "children",
            "native_outputs",
        ):
            if frontend.get(key) != native.get(key):
                raise ValueError(f"Native completion receipts disagree: {key}")
        completion = native.get("source_completion", {})
        process = json.loads((capture / "process.json").read_text())
        if (
            native.get("generator_returncode") != 0
            or native.get("source_capture_complete") is not True
            or completion.get("status") != "success"
            or completion.get("parent_returncode") != 0
            or process != native.get("process")
            or process.get("status") not in {"success", "failure"}
            or process.get("returncode") not in {0, 1}
        ):
            raise ValueError("Recovery requires completed native parent, not failed or interrupted source work")
        for key in ("backend", "llvm_as", "python", "generator", "library", "legalizer"):
            if key in request:
                verify(Path(request[key]), request[key + "_sha256"], retained=False)
        for relative, digest in request["source_hashes"].items():
            verify(Path(request["checkout"]) / relative, digest, retained=False)
        outputs = native["native_outputs"]
        expected_outputs = [str(generation / name) for name in request["expected_generator_outputs"]]
        if [item["path"] for item in outputs] != expected_outputs or completion.get("outputs") != outputs:
            raise ValueError("Native parent output set is incomplete or differs from the request")
        for item in outputs:
            path = Path(item["path"])
            verify(path, item["sha256"])
            if not path.stat().st_size:
                raise ValueError("Native parent output is empty")
            if path.suffix == ".ll":
                validation = item.get("llvm_validation", {})
                verify(path.with_suffix(".ll.json"))
                if (
                    validation.get("verify_returncode") != 0
                    or validation.get("sha256") != item["sha256"]
                    or validation.get("path") != str(path)
                    or validation.get("verify_command") != [request["llvm_as"], str(path), "-o", os.devnull]
                    or json.loads(path.with_suffix(".ll.json").read_text()) != validation
                ):
                    raise ValueError("Final LLVM lacks its successful retained verifier result")
        children = [Path(item["path"]) for item in native["children"]]
        if (
            len(children) != 1
            or children != sorted((generation / "children").glob("child-*/capture.json"))
            or [child.parent for child in children] != sorted((generation / "children").glob("child-*"))
            or completion.get("children") != native["children"]
        ):
            raise ValueError(
                "Recovery requires exactly one complete cold-cache native child; child set changed or unsupported"
            )
        for child, item in zip(children, native["children"], strict=True):
            verify(child, item["sha256"])
            child_record = json.loads(child.read_text())
            if child_record.get("status") != "success" or child_record.get("source_capture_complete") is not True:
                raise ValueError("A native child did not complete")
            verify(Path(child_record["program"]), child_record["program_sha256"])
            verify(child.parent / "generated.py", child_record["program_sha256"])
            calls = child_record["invocations"]
            if not calls or [Path(call["raw"]) for call in calls] != sorted(child.parent.glob("invocation-*.egg")):
                raise ValueError("Native invocation set is incomplete or changed")
            for index, call in enumerate(calls):
                raw = Path(call["raw"])
                if (
                    call.get("index") != index
                    or call.get("status") != "success"
                    or call.get("returncode") != 0
                    or call.get("backend_sha256") != request["backend_sha256"]
                    or call.get("command") != [request["backend"], str(raw)]
                ):
                    raise ValueError("A native backend invocation did not complete with the pinned executable")
                verify(raw, call["sha256"])
                verify(raw.with_suffix(".stdout.log"), call["stdout_sha256"])
                verify(raw.with_suffix(".result.json"))
                if json.loads(raw.with_suffix(".result.json").read_text()) != call:
                    raise ValueError("Backend invocation receipt differs from its child")
            legalizations = child_record["legalizations"]
            expected_legal = [child.parent / f"legalize-{index:04}" for index in range(len(legalizations))]
            if not legalizations or expected_legal != sorted(child.parent.glob("legalize-*")):
                raise ValueError("LLVM feedback set is incomplete or changed")
            for directory, legal in zip(expected_legal, legalizations, strict=True):
                validation = legal["validation"]
                legal_path = Path(validation["path"])
                prefix = native["output_name_adaptation"]["feedback_prefix"]
                if (
                    legal.get("status") != "success"
                    or legal.get("returncode") != 0
                    or validation.get("verify_returncode") != 0
                    or not legal["required_functions"]
                    or validation["required_functions"] != legal["required_functions"]
                    or not set(legal["required_functions"]).issubset(validation["functions"])
                    or legal["feedback"] != prefix + ".ll"
                    or str(legal_path) != prefix + ".legalize.ll"
                    or legal["feedback_sha256"] != validation["sha256"]
                    or validation["verify_command"] != [request["llvm_as"], str(legal_path), "-o", os.devnull]
                ):
                    raise ValueError("Native LLVM feedback was not successfully returned to the parent")
                verify(directory / legal_path.name, validation["sha256"])
                verify(directory / "verify.json")
                if json.loads((directory / "verify.json").read_text()) != validation:
                    raise ValueError("LLVM feedback verifier receipt differs from its child")
                for dependency in legal["inputs"]:
                    path = Path(dependency["path"])
                    verify(path, dependency["sha256"], retained=path.is_relative_to(source_stage.parent))
                verify(directory / "tools.json")
                tools = json.loads((directory / "tools.json").read_text())
                if not tools or any(tool.get("status") != "success" or tool.get("returncode") != 0 for tool in tools):
                    raise ValueError("Native LLVM tool execution did not complete")
                for tool in tools:
                    verify(Path(tool["executable"]), tool["executable_sha256"], retained=False)
        record = {
            key: value
            for key, value in native.items()
            if key not in {"process", "error", "reason", "materialization", "invocations", "workloads"}
        }
        record.update(status="materializing", invocations=[], workloads=[])
        record["recovery"] = {
            "source_stage": str(source_stage),
            "source_stage_sha256": evidence[str(source_stage)],
            "historical_status": native["status"],
            "historical_process": process,
            "historical_reason": native.get("reason"),
            "native_execution_repeated": False,
            "archived_native_implementation": str(native_implementation.absolute()),
            "native_implementation_comparison": (
                "AST equality of all native hooks and the extracted packaging body; "
                "imports excluded only within packaging"
            ),
            "invocation_accounting_scope": (
                "One generated child under the archived frontend's fresh-cache precondition. "
                "Warm/multiple-child pattern-validation subprocess accounting is unsupported."
            ),
            "old_implementation_hashes": {
                path: digest
                for path, digest in stage["identity"]["inputs"].items()
                if "/scripts/" in path or "/benchmarking/" in path
            },
            "materializer_hashes": {
                str(ROOT / name): hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                for name in (
                    "scripts/misaal_reproduction.py",
                    "scripts/hardboiled_replay.py",
                    "scripts/paper_benchmarks/materialize.py",
                )
            },
            "verified_evidence": evidence,
        }
        save_receipt(output / "request.json", request)
        materialize_invocations(children, output / "replays", record)
    except (OSError, ValueError, KeyError, TypeError, SyntaxError, StopIteration) as error:
        record.update(status="failure", reason=str(error), workloads=[])
    finally:
        save_receipt(output / "capture.json", record)
    return record


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("capture", "frontend", "child", "low-level", "materialize"))
    parser.add_argument("--source-stage", type=Path)
    parser.add_argument("--native-implementation", type=Path)
    parser.add_argument("--request", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--script", type=Path)
    parser.add_argument("--group-endpoint", type=Path)
    parser.add_argument("arguments", nargs="*")
    args = parser.parse_args(argv)
    sys.path.insert(0, str(ROOT))
    if args.mode == "materialize":
        if args.source_stage is None or args.native_implementation is None:
            parser.error("materialize requires --source-stage and --native-implementation")
        result = materialize_complete_capture(
            args.source_stage, args.output, native_implementation=args.native_implementation
        )
        return 0 if result["status"] == "ordinary-validation-pending" else 1
    if args.mode == "low-level":
        if args.script is None:
            parser.error("low-level requires --script")
        request = verified_request(args.request) if args.request else {}
        if request.get("egglog_export") == EGGLOG_EXPORT:
            raise ValueError("LLVM tools are not requested by Egglog export")
        contract = request.get("hvx_link_contract")
        return run_low_level(
            args.script.resolve(),
            args.arguments,
            args.output.resolve(),
            omitted_wrapper=Path(contract["omitted_wrapper"]) if contract else None,
        )
    if args.request is None:
        parser.error("--request is required")
    request_path = args.request.resolve()
    output = args.output.resolve()
    if args.mode == "child":
        return observe_python(request_path, output, args.arguments)
    if args.mode == "frontend":
        return run_frontend(request_path, output, group_endpoint=args.group_endpoint)
    result = capture_misaal(request_path, output)
    return 0 if result["status"] == "ordinary-validation-pending" else 1


if __name__ == "__main__":
    raise SystemExit(main())
