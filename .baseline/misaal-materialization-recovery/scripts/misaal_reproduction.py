"""Observe a complete MISAAL generator, including live Python/LLVM feedback.

`capture --request REQUEST --output FRESH_DIRECTORY` is the guarded entrypoint.
Other modes are child hooks in that process group, never standalone benchmarks.
See benchmarks/reproduction/misaal-hardboiled.md for the request contract.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import importlib
import inspect
import json
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
from dataclasses import asdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]


def save_receipt(path: Path, value: Any) -> None:
    """Publish complete JSON atomically, including before a risky subprocess."""
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, default=str) + "\n")
    temporary.replace(path)


def verified_request(path: Path) -> dict[str, Any]:
    """Bind the actual generator, source, backend, verifier and Python inputs."""
    request: dict[str, Any] = json.loads(path.read_text())
    if re.fullmatch(r"[0-9a-f]{40}", request["revision"]) is None:
        raise ValueError("MISAAL request must record a full source revision")
    checkout = Path(request["checkout"]).resolve()
    required = {"lib/compiler/EggLogCompiler.py", "lib/compiler/HydrideCompiler.py"}
    if not required.issubset(request["source_hashes"]):
        raise ValueError("Request must pin both observed compiler implementations")
    for relative, expected in request["source_hashes"].items():
        source = (checkout / relative).resolve()
        if not source.is_relative_to(checkout) or hashlib.sha256(source.read_bytes()).hexdigest() != expected:
            raise ValueError(f"MISAAL source identity changed: {relative}")
    for key in ("backend", "llvm_as", "python", "generator"):
        executable = Path(request[key])
        if not os.access(executable, os.X_OK):
            raise ValueError(f"Missing executable: {executable}")
        if hashlib.sha256(executable.read_bytes()).hexdigest() != request[f"{key}_sha256"]:
            raise ValueError(f"MISAAL {key} identity changed")
    if request["generator_command"][0] != request["generator"]:
        raise ValueError("Generator command does not use the recorded executable")
    if not any("{output}" in argument for argument in request["generator_command"]):
        raise ValueError("Generator output must be scoped using {output}")
    outputs = request["expected_generator_outputs"]
    if not outputs or not any(name.endswith(".ll") for name in outputs):
        raise ValueError("Expected generator outputs must include final LLVM")
    if any(Path(name).is_absolute() or ".." in Path(name).parts for name in outputs):
        raise ValueError("Expected generator outputs must stay inside the fresh attempt")
    return request


def validate_llvm(path: Path, expected_functions: set[str], llvm_as: Path, evidence: Path) -> dict[str, Any]:
    """Require real, well-formed LLVM defining every requested source function."""
    content = path.read_bytes()
    if not content:
        raise ValueError(f"Empty LLVM output: {path}")
    definitions = {
        quoted or plain
        for quoted, plain in re.findall(r'^define\b[^@\n]*@(?:"([^"\n]+)"|([\w.$-]+))\(', content.decode(), re.M)
    }
    if not definitions or expected_functions - definitions:
        raise ValueError(f"LLVM output is missing requested functions: {sorted(expected_functions - definitions)}")
    command = [str(llvm_as), str(path), "-o", os.devnull]
    with evidence.with_suffix(".stdout.log").open("wb") as out, evidence.with_suffix(".stderr.log").open("wb") as err:
        result = subprocess.run(command, stdout=out, stderr=err, timeout=120, check=False)
    receipt = {
        "path": str(path),
        "sha256": hashlib.sha256(content).hexdigest(),
        "functions": sorted(definitions),
        "required_functions": sorted(expected_functions),
        "verify_command": command,
        "verify_returncode": result.returncode,
    }
    save_receipt(evidence.with_suffix(".json"), receipt)
    if result.returncode:
        raise ValueError(f"LLVM verifier rejected {path}")
    return receipt


def run_low_level(script: Path, arguments: list[str], directory: Path) -> int:
    """Execute the real legalizer script, checking its formerly unchecked tools."""
    commands: list[dict[str, Any]] = []
    original_system = os.system
    original_argv = sys.argv

    def checked_system(command: str | bytes | os.PathLike[str] | os.PathLike[bytes]) -> int:
        argv = shlex.split(os.fsdecode(command))
        if not argv or any(token in {"|", ";", "&&", "||", ">", "<"} for token in argv):
            raise ValueError("Unexpected shell syntax in LLVM tool command")
        executable = shutil.which(argv[0])
        if executable is None:
            raise FileNotFoundError(argv[0])
        entry: dict[str, Any] = {
            "command": argv,
            "executable": executable,
            "executable_sha256": hashlib.sha256(Path(executable).read_bytes()).hexdigest(),
            "status": "running",
        }
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
        return 0
    except BaseException:
        (directory / "failure.txt").write_text(traceback.format_exc())
        traceback.print_exc()
        return 1
    finally:
        os.system = original_system
        sys.argv = original_argv


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
        required_inputs = [Path(self.output_file_path), Path(self.llvm_so_path), Path(self.intrinsics_file), script]
        entry: dict[str, Any] = {
            "status": "running",
            "required_functions": sorted(functions),
            "inputs": [
                {"path": str(p.resolve()), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
                for p in required_inputs
            ],
        }
        record["legalizations"].append(entry)
        save_receipt(directory / "capture.json", record)
        command = [
            request["python"],
            str(Path(__file__).resolve()),
            "low-level",
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
            entry["validation"] = validate_llvm(legal, functions, Path(request["llvm_as"]), evidence / "verify")
            for artifact in artifacts:
                shutil.copyfile(artifact, evidence / artifact.name)
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
        egg_compiler = importlib.import_module("compiler.EggLogCompiler").EggLogCompiler
        hydride_compiler = importlib.import_module("compiler.HydrideCompiler").HydrideCompiler
        egg_compiler.execute_egglog_file = capture_backend
        hydride_compiler.run_llvm_legalizer = checked_legalizer
        sys.argv = [str(program)]
        runpy.run_path(str(program), run_name="__main__")
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


def run_frontend(request_path: Path, attempt: Path) -> int:
    """Keep the native parent alive until all compiler outputs are verified."""
    request = verified_request(request_path)
    patterns = Path(request["checkout"]) / "lib/patterns"
    if list(patterns.glob("*.pickle")):
        raise ValueError("Canary requires a prepared checkout with fresh pattern caches")
    attempt.mkdir(parents=True, exist_ok=False)
    save_receipt(attempt / "request.json", request)
    environment = dict(os.environ)
    for key in list(environment):
        if key.startswith(("HL_", "HYDRIDE_", "MISAAL_")):
            del environment[key]
    environment.update(request["environment"])
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
    save_receipt(attempt / "capture.json", record)
    try:
        result = subprocess.run(command, cwd=attempt, env=environment, check=False)
        record["generator_returncode"] = result.returncode
        record["source_completion"]["parent_returncode"] = result.returncode
        children = sorted((attempt / "children").glob("child-*/capture.json"))
        record["children"] = [{"path": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()} for p in children]
        if (
            result.returncode
            or not children
            or any(not json.loads(p.read_text())["source_capture_complete"] for p in children)
        ):
            raise ValueError("Generator or a reached Python/LLVM child did not complete")
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
        from scripts.hardboiled_replay import check_observed_selections, egglog_forms, native_check_contract
        from scripts.paper_benchmarks.materialize import prefix_atoms

        replay_directory = attempt / "replays"
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
            reason="Native generator and LLVM feedback completed; standalone outputs await ordinary validation",
        )
        record["materialization"]["complete"] = True
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
    """Run one complete source attempt in one guarded native process group.

    Call directly from a coordinator, not from another session-creating guard.
    LLVM/backend children deliberately inherit this group's resource boundary.
    """
    from benchmarking.pilot import run_bounded_command

    request_path, output = request_path.resolve(), output.resolve()
    request = verified_request(request_path)
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
    process = run_bounded_command(
        command,
        ROOT,
        output / "process",
        timeout_sec=900,
        memory_limit_bytes=5 * 1024**3,
        require_guard=True,
        disk_reserve_bytes=10 * 1024**3,
        allow_warning_pressure=True,
    )
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
    record["process"] = asdict(process)
    if process.status != "success":
        record.update(status=process.status, reason=process.message or "Source attempt did not finish", workloads=[])
        if not record["source_capture_complete"]:
            record["source_completion"].update(status="incomplete", process=asdict(process))
    save_receipt(output / "capture.json", record)
    return record


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("capture", "frontend", "child", "low-level"))
    parser.add_argument("--request", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--script", type=Path)
    parser.add_argument("arguments", nargs="*")
    args = parser.parse_args(argv)
    sys.path.insert(0, str(ROOT))
    if args.mode == "low-level":
        if args.script is None:
            parser.error("low-level requires --script")
        return run_low_level(args.script.resolve(), args.arguments, args.output.resolve())
    if args.request is None:
        parser.error("--request is required")
    request_path = args.request.resolve()
    output = args.output.resolve()
    if args.mode == "child":
        return observe_python(request_path, output, args.arguments)
    if args.mode == "frontend":
        return run_frontend(request_path, output)
    result = capture_misaal(request_path, output)
    return 0 if result["status"] == "ordinary-validation-pending" else 1


if __name__ == "__main__":
    raise SystemExit(main())
