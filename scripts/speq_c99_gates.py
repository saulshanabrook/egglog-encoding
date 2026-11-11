"""Guarded prerequisite gates for the scoped PolyBench C99 frontend repair.

The caller owns the shared lock and supplies a fail-stop, 5 GiB guarded step.
Only child CLI modes execute native tools; passing these gates is not admission.
Scope isolation uses the actual original-C regions, including init_array.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import subprocess
import sys
from collections.abc import Callable
from dataclasses import asdict
from pathlib import Path
from typing import Any

from benchmarking.pilot import PilotProcessResult
from scripts import speq_c99_diagnostic as c99
from scripts.paper_benchmarks import record_speq as recorder


def fixture_output(name: str, output: str) -> None:
    """Require exact closure/address evidence and the harness's unchanged-IR check."""
    lines = [line.strip() for line in output.splitlines()]
    for value in (
        "memory-type: ptr 1 double",
        "LLVM module unchanged",
        "%n64 = zext i32 %n to i64",
        "%row64 = zext i32 %row to i64",
    ):
        if lines.count(value) != 1:
            raise ValueError(f"{name}: missing or duplicated fixture evidence: {value}")
    right = "%shifted" if name == "nonzero_offset" else "%j64"
    offset = f"%reproduction.c99.offset.0 = add nsw i64 %row.offset, {right}"
    element = "%element = getelementptr inbounds double, ptr %C, i64 %reproduction.c99.offset.0"
    if [line for line in lines if line.startswith("%reproduction.c99.offset.")] != [offset]:
        raise ValueError(f"{name}: unexpected flattened address")
    if lines.count(element) != 1 or lines.index(offset) >= lines.index(element):
        raise ValueError(f"{name}: flattened address order differs")
    for operand in ("%row.offset", right):
        definitions = [i for i, line in enumerate(lines) if line.startswith(operand + " = ")]
        if len(definitions) != 1 or definitions[0] >= lines.index(offset):
            raise ValueError(f"{name}: incomplete dominating address closure")
    expected = {
        "nonzero_offset": ["%shifted = add nuw nsw i64 %j64, 3"],
        "different_stride": [
            "%wide.stride = add nuw nsw i64 %n64, 7",
            "%row.offset = mul nuw nsw i64 %row64, %wide.stride",
        ],
    }
    if any(lines.count(line) != 1 for line in expected.get(name, [])):
        raise ValueError(f"{name}: offset/stride evidence changed")


def _process(
    command: list[str], directory: Path, *, error: str | None = None, enabled: str | None = None
) -> dict[str, Any]:
    """Retain one real native outcome; expected rejections never hide outer guard stops."""
    directory.mkdir()
    environment = {key: value for key, value in os.environ.items() if key != c99.ENABLE_ENV}
    if enabled is not None:
        environment[c99.ENABLE_ENV] = enabled
    stdout, stderr = directory / "stdout.log", directory / "stderr.log"
    with stdout.open("wb") as out, stderr.open("wb") as err:
        result = subprocess.run(command, stdout=out, stderr=err, check=False, env=environment)
    row = {
        "command": command,
        "returncode": result.returncode,
        "environment_override": {c99.ENABLE_ENV: enabled},
        "expected_error": error,
        "stdout": str(stdout),
        "stderr": str(stderr),
    }
    (directory / "process.json").write_text(json.dumps(row, indent=2) + "\n")
    if error is None:
        if result.returncode != 0:
            raise ValueError(f"native positive gate failed: {directory.name}")
    elif result.returncode == 0 or result.returncode in (-9, -15) or error not in stderr.read_text():
        raise ValueError(f"native rejection did not match its reviewed diagnostic: {directory.name}")
    return row


def _child(request: dict[str, Any], output: Path) -> dict[str, Any]:
    """Execute one gate inside the caller's monitored process group."""
    kind = request["kind"]
    if kind == "build":
        built = c99.build_plugins(Path(request["source"]), Path(request["llvm_config"]), output / "plugins")
        if built["llvm_version"] != "17.0.6" or built["selected_function"] != c99.FUNCTION:
            raise ValueError("C99 gates require LLVM17.0.6 and the exact selected function")
        materialized = Path(built["materialization"]["path"]).parent
        llvm_config = Path(request["llvm_config"])
        flags = recorder.command_output(
            [
                str(llvm_config),
                "--cxxflags",
                "--ldflags",
                "--libs",
                "core",
                "analysis",
                "irreader",
                "support",
                "--system-libs",
            ]
        )
        harness = output / "c99-harness"
        _process(
            [
                str(Path(built["opt"]).parent / "clang++"),
                str(materialized / "c99-harness.cpp"),
                *shlex.split(flags),
                "-o",
                str(harness),
            ],
            output / "compile-harness",
        )
        tools = [Path(built["opt"]), Path(built["opt"]).parent / "clang++", harness]
        built["artifacts"].update({str(p.resolve()): hashlib.sha256(p.read_bytes()).hexdigest() for p in tools})
        return {**built, "harness": str(harness), "materialized": str(materialized)}
    built = request["build"]
    if kind == "fixture":
        name = request["name"]
        expected = c99.fixture_cases()[name][1]
        row = _process(
            [built["harness"], str(Path(built["materialized"]) / "fixtures" / f"{name}.ll"), name],
            output / "native",
            error=expected,
        )
        if expected is None:
            fixture_output(name, Path(row["stdout"]).read_text())
        return {
            "classification": "positive-unchanged-module" if expected is None else "reviewed-domain-rejection",
            "process": row,
        }
    artifact = Path(request["artifact"])
    if kind == "reference":
        name = request["name"]
        source = artifact / "analysis" / f"{name}.ll"
        recorder.read_verified(source, recorder.REFERENCE_ANALYSIS_SHA256[name])
        row = _process(
            [
                built["opt"],
                f"-load-pass-plugin={built[request['variant'] + '_plugin']}",
                "-S",
                "-passes=print<revpass>",
                str(source),
                "-disable-output",
            ],
            output / "native",
        )
        match = re.fullmatch(r"REV Start\n(.*)REV End\n", Path(row["stderr"]).read_text(), re.DOTALL)
        if match is None or recorder.sha256_text(match[1]) != recorder.REFERENCE_FIR_SHA256[name]:
            raise ValueError("disabled C99 reference FIR differs from the original snapshot")
        (output / "reference.fir").write_text(match[1])
        return {"process": row, "fir_sha256": recorder.sha256_text(match[1])}
    if kind == "frontend":
        baseline_dir, disabled_dir, candidate_dir = (output / name for name in ("baseline", "disabled", "candidate"))
        firs = []
        for directory, plugin, enabled in (
            (baseline_dir, built["baseline_plugin"], False),
            (disabled_dir, built["candidate_plugin"], False),
            (candidate_dir, built["candidate_plugin"], True),
        ):
            fir = recorder.application_fir(
                artifact,
                Path(built["opt"]),
                Path(plugin),
                "polybench_gemm",
                directory,
                complete=True,
                frontend_flags=c99.FRONTEND_FLAGS,
                c99_frontend_repair=enabled,
            )
            if not isinstance(fir, list):
                raise ValueError("complete C99 frontend did not return ordered regions")
            firs.append(fir)
        if firs[0] != firs[1]:
            raise ValueError("disabled candidate changed an original FIR region")
        return {
            "comparison": c99.compare_frontends(firs[0], firs[2], baseline_dir, candidate_dir),
            "disabled_regions_byte_identical": True,
            "source_complete": False,
        }
    if kind != "selection":
        raise ValueError(f"unknown C99 gate: {kind}")
    name = request["name"]
    reference = artifact / "analysis/gemv.ll"
    source_text = recorder.read_verified(reference, recorder.REFERENCE_ANALYSIS_SHA256["gemv"])
    selected = f"define void @{c99.FUNCTION}() {{ ret void }}\n"
    fixture = output / "input.ll"
    fixture.write_text(selected * 2 if name == "duplicate" else source_text + (selected if name == "empty" else ""))
    command = [
        built["opt"],
        f"-load-pass-plugin={built['candidate_plugin']}",
        "-S",
        "-passes=print<revpass>",
        str(fixture),
        "-disable-output",
    ]
    errors = {
        "missing": "REV C99 selected definition is missing",
        "duplicate": "redefinition of function",
        "invalid-enable": "REV C99 diagnostic enable value must be 1",
        "empty": "REV C99 address domain: selected function has no chained GEP",
    }
    row = _process(command, output / "enabled", enabled="0" if name == "invalid-enable" else "1", error=errors[name])
    return {"process": row, "classification": "selection-rejection"}


def run_gates(
    source: Path, artifact: Path, llvm_config: Path, output: Path, step: Callable[[str, list[str]], PilotProcessResult]
) -> dict[str, Any]:
    """Build and check fresh source only; caller failures propagate without relabeling."""
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    result: dict[str, Any] = {
        "status": "running",
        "contract": c99.CONTRACT,
        "selected_function": c99.FUNCTION,
        "corpus_admission": False,
        "gates": {},
        "artifacts": {},
    }
    try:
        inputs = [
            source / name
            for name in (
                "llvm/lib/Analysis/REVPass.cpp",
                "llvm/include/llvm/Analysis/REVPass.h",
                "llvm/include/llvm/Analysis/MemorySSA.h",
            )
        ]
        inputs.extend(artifact / "analysis" / f"{name}.ll" for name in recorder.REFERENCE_ANALYSIS_SHA256)
        inputs.extend(
            artifact / "benchmarks" / name for name in ("polybench_gemm.c", *recorder.APPLICATION_HEADER_SHA256)
        )
        inputs.extend(
            [Path(__file__), Path(c99.__file__), Path(recorder.__file__), Path(c99.phi.__file__), llvm_config]
        )
        inputs.extend(
            c99.SUPPORT / name
            for name in ("speq_c99_fir.inc", "speq_c99_fixture.ll", "speq_c99_harness.cpp", "speq_rev_plugin.cpp")
        )
        identities = {str(p.resolve()): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
        result["inputs"] = identities
        requests: list[tuple[str, dict[str, Any]]] = [
            ("build", {"kind": "build", "source": str(source.resolve()), "llvm_config": str(llvm_config.resolve())})
        ]
        requests.extend(("fixture-" + name, {"kind": "fixture", "name": name}) for name in c99.fixture_cases())
        requests.extend(
            (f"{variant}-reference-{name}", {"kind": "reference", "variant": variant, "name": name})
            for variant in ("baseline", "candidate")
            for name in recorder.REFERENCE_ANALYSIS_SHA256
        )
        requests.extend(
            ("selection-" + name, {"kind": "selection", "name": name})
            for name in ("missing", "duplicate", "invalid-enable", "empty")
        )
        requests.append(("fresh-original-c", {"kind": "frontend"}))
        if len(c99.fixture_cases()) != 16 or len(recorder.REFERENCE_ANALYSIS_SHA256) != 4:
            raise ValueError("C99 gates require the reviewed 16 fixtures and four references")
        for name, request in requests:
            result["active_gate"] = name
            for path, expected in {**identities, **result["artifacts"]}.items():
                if hashlib.sha256(Path(path).read_bytes()).hexdigest() != expected:
                    raise ValueError(f"C99 gate input/evidence changed: {path}")
            directory = output / name
            directory.mkdir()
            request.update(artifact=str(artifact.resolve()), build=result.get("build"))
            request_path = directory / "request.json"
            request_path.write_text(json.dumps(request, indent=2) + "\n")
            process = step(
                "c99-" + name,
                [
                    "/usr/bin/env",
                    "-u",
                    c99.ENABLE_ENV,
                    sys.executable,
                    "-m",
                    "scripts.speq_c99_gates",
                    str(request_path),
                ],
            )
            result["process"] = asdict(process)
            if process.status != "success" or process.returncode != 0:
                result["status"] = process.status
                raise ValueError(f"C99 guarded gate failed: {name}")
            receipt = json.loads((directory / "result.json").read_text())
            if (
                receipt.get("status") != "success"
                or receipt.get("request_sha256") != hashlib.sha256(request_path.read_bytes()).hexdigest()
            ):
                raise ValueError(f"C99 child did not retain successful exact-request evidence: {name}")
            result["gates"][name] = receipt
            if name == "build":
                result["build"] = receipt["evidence"]
                for path, expected in receipt["evidence"]["artifacts"].items():
                    if hashlib.sha256(Path(path).read_bytes()).hexdigest() != expected:
                        raise ValueError(f"C99 plugin/tool changed after guarded build: {path}")
                materialization = receipt["evidence"]["materialization"]
                if hashlib.sha256(Path(materialization["path"]).read_bytes()).hexdigest() != materialization["sha256"]:
                    raise ValueError("C99 materialization receipt changed after guarded build")
                result["artifacts"].update(receipt["evidence"]["artifacts"])
            result["artifacts"].update(
                {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in directory.rglob("*") if p.is_file()}
            )
        for path, expected in {**identities, **result["artifacts"]}.items():
            if hashlib.sha256(Path(path).read_bytes()).hexdigest() != expected:
                raise ValueError(f"C99 gate input/evidence changed: {path}")
        result.update(status="success", inputs_unchanged=True)
        return result
    except BaseException as error:
        if result["status"] == "running":
            result["status"] = "blocked"
        result["reason"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        (output / "result.json").write_text(json.dumps(result, indent=2, default=str) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("request", type=Path)
    args = parser.parse_args()
    data = args.request.read_bytes()
    result: dict[str, Any] = {"status": "blocked", "request_sha256": hashlib.sha256(data).hexdigest()}
    try:
        result.update(evidence=_child(json.loads(data), args.request.parent), status="success")
    except BaseException as error:
        result["reason"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        (args.request.parent / "result.json").write_text(json.dumps(result, indent=2, default=str) + "\n")


if __name__ == "__main__":
    main()
