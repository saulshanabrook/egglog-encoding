#!/usr/bin/env python3
"""Preserve the pinned HardBoiled and MISAAL compiler's raw Egglog calls.

Capture is separate from benchmark admission. Missing original backends cause
partial captures; the script never invents backend responses to continue a
compiler. Every run needs a fresh output directory. See --help for entrypoints.

HardBoiled requires the pinned Halide library built under --build; --sidecar
may name the separately pinned acquisition dependency. MISAAL's program mode
requires the original Hydride Python paths/dependencies in the environment.
The evidence logs contain exact dependency acquisition and build commands.
"""

from __future__ import annotations

import argparse
import ast
import fcntl
import hashlib
import importlib
import inspect
import json
import os
import re
import runpy
import subprocess
import sys
import tempfile
import traceback
from dataclasses import asdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
STORAGE = ROOT / "benchmarks/local"
PINS = {
    "hardboiled": "b99cf0c6400e954a278f697bf3a0596ac3fa4f25",
    "misaal": "c098f0f289d03f0c58db1ef85d9b4ff7eef9dec4",
}
MISAAL_ADD_RAW_SHA256 = "20e0c90b8157820e06f8790f439ea1c7b4e11341f881cec6e58099c33b758672"
MISAAL_ADD_GENERATOR_SHA256 = "68de5416335e9f838760c4da5643642c84ada3bb1fa66f7ff2502c5f4f912f40"


def prepare_misaal_capture(capture_path: Path, directory: Path) -> dict[str, Any]:
    """Prepare recorded successful calls; retain blockers and partial capture status.

    Only terminal global names change. Source extractions remain intact. No engine is launched.
    Failed or unexpected calls remain explicit; identity drift rejects the input.
    """
    sys.path.insert(0, str(ROOT))
    from scripts.hardboiled_replay import egglog_forms
    from scripts.paper_benchmarks.materialize import prefix_atoms

    capture = json.loads(capture_path.read_text())
    process_path = capture_path.parent / "python.result.json"
    process = json.loads(process_path.read_text())
    if capture["revision"] != PINS["misaal"]:
        raise ValueError("unexpected MISAAL source revision")
    program = Path(capture["program"])
    if hashlib.sha256(program.read_bytes()).hexdigest() != capture["program_sha256"]:
        raise ValueError("captured MISAAL generated program changed")
    compilers = [
        node
        for node in ast.walk(ast.parse(program.read_text()))
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "HydrideCompiler"
    ]
    iterations = [
        keyword.value.value
        for node in compilers
        for keyword in node.keywords
        if keyword.arg == "run_iterations" and isinstance(keyword.value, ast.Constant)
    ]
    if len(compilers) != 1 or len(iterations) != 1 or type(iterations[0]) is not int or iterations[0] <= 0:
        raise ValueError("expected one source compiler with a positive literal iteration count")
    record: dict[str, Any] = {
        "id": capture["case_id"],
        "source_capture_evidence": str(capture_path.relative_to(ROOT)),
        "source_capture_sha256": hashlib.sha256(capture_path.read_bytes()).hexdigest(),
        **{
            key: capture[key]
            for key in (
                "revision",
                "source_sha256",
                "program_sha256",
                "backend_sha256",
                "egglog_phase_status",
                "source_capture_complete",
                "external_llvm_phase",
            )
        },
        "process_evidence": str(process_path.relative_to(ROOT)),
        "process_evidence_sha256": hashlib.sha256(process_path.read_bytes()).hexdigest(),
        "process_status": process["status"],
        "workloads": [],
        "classification": "unvalidated-replay-preparation",
        "adaptation": "Prefix globals with $; preserve rules, seeds, schedule and original extraction commands",
        "invocations": [],
    }
    outputs: dict[Path, str] = {}
    for index, call in enumerate(capture["invocations"]):
        if call["index"] != index:
            raise ValueError("MISAAL capture contains unordered invocations")
        raw_path = Path(call["raw"])
        raw = raw_path.read_text()
        if hashlib.sha256(raw.encode()).hexdigest() != call["sha256"]:
            raise ValueError("MISAAL captured input differs from its recorded hash")
        prepared = {
            "index": index,
            "caller": call["caller"],
            "raw": str(raw_path.relative_to(ROOT)),
            "sha256": call["sha256"],
            "backend_status": call["status"],
            "backend_returncode": call.get("returncode"),
            "preparation_status": "blocked",
        }
        record["invocations"].append(prepared)
        if call["status"] != "success" or call.get("returncode") != 0:
            prepared["reason"] = (
                f"Original backend interrupted: source process {process['status']}"
                if call["status"] == "running" and process["status"] != "success"
                else f"Original backend {call['status']} (exit {call.get('returncode')})"
            )
            continue
        stdout = raw_path.with_suffix(".stdout.log")
        try:
            root = {"apply_rewrite": "srcexpr", "lower_swizzles": "swizzleexpr", "move_swizzles": "swizzleexpr"}.get(
                call["caller"]
            )
            if root is None:
                raise ValueError("unexpected MISAAL invocation caller")
            forms = egglog_forms(raw)
            boundary = next((i for i, form in enumerate(forms) if form[2][1] == "let"), len(forms))
            prefix, tail = forms[:boundary], forms[boundary:]
            if (
                len(tail) < 3
                or any(form[2][1] not in {"datatype", "rewrite", "birewrite", "rule"} for form in prefix)
                or tail[-2][2] != ["(", "run", str(iterations[0]), ")"]
                or tail[-1][2][:3] != ["(", "extract", root]
                or len(tail[-1][2]) not in (4, 5)
                or (len(tail[-1][2]) == 5 and not tail[-1][2][3].isdigit())
                or raw[tail[-1][1] :].strip()
            ):
                raise ValueError("unexpected MISAAL declaration, schedule or extraction boundary")
            bindings = tail[:-2]
            names = [form[2][2] for form in bindings]
            if (
                any(form[2][1] != "let" for form in bindings)
                or len(set(names)) != len(names)
                or names[-1] != root
                or any(re.fullmatch(r"reg_\d+", name) is None for name in names[:-1])
            ):
                raise ValueError("unexpected MISAAL terminal globals")
        except (OSError, ValueError) as error:
            prepared["reason"] = str(error)
            continue
        seeds = raw[: tail[0][0]] + prefix_atoms(raw[tail[0][0] : tail[-2][0]], set(names))
        schedule = raw[tail[-2][0] : tail[-1][0]]
        extraction = prefix_atoms(raw[tail[-1][0] :], set(names))
        replay = directory / f"{capture['case_id']}-{index:04d}.egg"
        outputs[replay] = seeds + schedule + extraction
        prepared.update(
            {
                "preparation_status": "candidate",
                **(
                    {
                        "stdout": str(stdout.relative_to(ROOT)),
                        "stdout_sha256": hashlib.sha256(stdout.read_bytes()).hexdigest(),
                    }
                    if stdout.is_file()
                    else {}
                ),
                "candidate_replay": str(replay.relative_to(ROOT)),
                "replay_sha256": hashlib.sha256(outputs[replay].encode()).hexdigest(),
                "extraction": extraction.strip(),
            }
        )
    directory.mkdir(parents=True, exist_ok=False)
    for path, text in outputs.items():
        path.write_text(text)
    (directory / "capture.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def prepare_misaal_replay(
    compatibility: Path, directory: Path, validation: Path | None = None, continuation: Path | None = None
) -> dict[str, Any]:
    """Preserve the observed add input and source extraction without running an engine.

    Imported validation must establish successful ordinary extraction before
    exposing a workload. Strict-proof failure remains explicit for pilot exclusion.
    The two original call aliases never imply that source generation completed.
    """
    observations = json.loads(compatibility.read_text())
    raw_observations = [
        row for row in observations if row["kind"] == "raw-capture" and row["case_id"] == "misaal-x86-add"
    ]
    if len(raw_observations) != 1:
        raise ValueError("expected exactly one deduplicated MISAAL add raw observation")
    observed = raw_observations[0]
    if observed["process"]["status"] != "success" or observed["process"]["returncode"] != 0:
        raise ValueError("the original backend invocation did not succeed")
    raw_path = ROOT / observed["command"][-1]
    raw = raw_path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != MISAAL_ADD_RAW_SHA256 or observed["input_sha256"] != MISAAL_ADD_RAW_SHA256:
        raise ValueError("MISAAL add raw identity differs from the pinned capture")
    stdout = ROOT / observed["process"]["stdout_path"]
    capture_path = raw_path.parent / "capture.json"
    capture = json.loads(capture_path.read_text())
    if capture["revision"] != PINS["misaal"] or capture["capture_status"] != "partial":
        raise ValueError("expected the pinned partial MISAAL source capture")
    program = Path(capture["program"])
    if hashlib.sha256(program.read_bytes()).hexdigest() != capture["program_sha256"]:
        raise ValueError("captured MISAAL generated program changed")
    generator = program.parent / "add/src/add_generator.cpp"
    if hashlib.sha256(generator.read_bytes()).hexdigest() != MISAAL_ADD_GENERATOR_SHA256:
        raise ValueError("original MISAAL add generator changed")
    aliases = observed["source_aliases"]
    if [alias["logical_invocation"] for alias in aliases] != [0, 1]:
        raise ValueError("expected both ordered MISAAL add invocation aliases")
    calls = []
    for alias in aliases:
        path = ROOT / alias["path"]
        if alias["input_sha256"] != MISAAL_ADD_RAW_SHA256 or path.read_bytes() != raw:
            raise ValueError("MISAAL invocation alias differs from its raw identity")
        calls.append(
            {"index": alias["logical_invocation"], "raw": str(path.relative_to(ROOT)), "sha256": MISAAL_ADD_RAW_SHA256}
        )
    suffix = b"(run 5)\n(extract srcexpr)"
    if not raw.endswith(suffix):
        raise ValueError("unexpected terminal MISAAL schedule/extraction boundary")
    replay = raw
    directory.mkdir(parents=True, exist_ok=False)
    replay_path = directory / "misaal-x86-add-rewrite.egg"
    replay_path.write_bytes(replay)
    record: dict[str, Any] = {
        "id": "misaal-x86-add",
        "revision": PINS["misaal"],
        "source_sha256": MISAAL_ADD_GENERATOR_SHA256,
        "program": str(program),
        "program_sha256": capture["program_sha256"],
        "status": "partial",
        "capture_status": "partial",
        "capture_complete": False,
        "capture_boundary": capture["capture_boundary"],
        "capture_reason": capture["error"],
        "source_capture_evidence": str(capture_path.relative_to(ROOT)),
        "source_capture_sha256": hashlib.sha256(capture_path.read_bytes()).hexdigest(),
        "invocations": calls,
        "workloads": [],
        "candidate_replay": str(replay_path.relative_to(ROOT)),
        "replay_sha256": hashlib.sha256(replay).hexdigest(),
        "extraction": "(extract srcexpr)",
        "reference_output_provenance": {
            "compatibility_evidence": str(compatibility.relative_to(ROOT)),
            "compatibility_sha256": hashlib.sha256(compatibility.read_bytes()).hexdigest(),
            **(
                {
                    "stdout": str(stdout.relative_to(ROOT)),
                    "stdout_sha256": hashlib.sha256(stdout.read_bytes()).hexdigest(),
                }
                if stdout.is_file()
                else {}
            ),
            "engine_sha256": observed["engine_sha256"],
        },
        "adaptation": "Preserve the original source commands, including run 5 and terminal extraction.",
        "classification": "partial-capture-unvalidated-replay",
        "reason": "Source extraction prepared; ordinary execution and strict-proof validation remain pending.",
    }
    if validation is not None:
        evidence = json.loads(validation.read_text())
        if evidence["timeout_sec"] != 120 or evidence["memory_limit_bytes"] != 8 * 1024**3:
            raise ValueError("MISAAL validation must use the approved 120-second / 8-GiB policy")
        checks = evidence["checks"]
        phases = ["ordinary-original-schedule", "strict-proof"]
        if [check["phase"] for check in checks] != phases:
            raise ValueError("expected ordinary and strict-proof MISAAL validation controls")
        for check in checks:
            expected = record["replay_sha256"]
            checked_path = ROOT / check["command"][-1]
            if check["input_sha256"] != expected or hashlib.sha256(checked_path.read_bytes()).hexdigest() != expected:
                raise ValueError("MISAAL validation input differs from the prepared replay")
        after, strict = checks
        ordinary_controls_passed = after["status"] == "success" and after["returncode"] == 0
        strict_passed = strict["status"] == "success" and strict["returncode"] == 0
        record.update(
            validation_evidence=str(validation.relative_to(ROOT)),
            validation_sha256=hashlib.sha256(validation.read_bytes()).hexdigest(),
            validation_engine_sha256=evidence["engine_sha256"],
            ordinary_controls_passed=ordinary_controls_passed,
            strict_proof_passed=strict_passed,
            validation_checks=checks,
            validation_logs=[
                {
                    "path": check[f"{stream}_path"],
                    "sha256": hashlib.sha256((ROOT / check[f"{stream}_path"]).read_bytes()).hexdigest(),
                }
                for check in checks
                for stream in ("stdout", "stderr")
            ],
        )
        if ordinary_controls_passed:
            record["workloads"] = [str(replay_path.relative_to(ROOT))]
            for call in calls:
                call["workload"] = record["workloads"][0]
            record["classification"] = "partial-capture-extraction-replay"
            record["reason"] = "Source extraction validated; original source capture remains partial."
            if not strict_passed:
                record["classification"] = "partial-capture-strict-proof-failure"
                record["reason"] = (
                    f"Ordinary controls pass; strict proof {strict['status']} (exit {strict['returncode']}). "
                    "Original source capture remains partial."
                )
        else:
            record["reason"] = "Ordinary extraction failed; replay remains unavailable for admission."
    if continuation is not None:
        result = json.loads(continuation.read_text())
        phase = result["phase"]
        current_capture_path = continuation.parent / "capture/capture.json"
        current_capture = json.loads(current_capture_path.read_text())
        if (
            result["status"] != "success"
            or result["returncode"] != 0
            or phase["boundary_reached"] is not True
            or phase["egglog_phase_status"] != "complete"
            or phase["failed_attempts"]
            or phase["source_capture_status"] != "partial"
            or phase["llvm_legalizer_status"] != "intentionally-not-run"
            or current_capture["revision"] != PINS["misaal"]
            or current_capture["program_sha256"] != record["program_sha256"]
            or current_capture["raw_invocations"] != phase["raw_invocations"]
            or len(phase["raw_invocations"]) != 1
        ):
            raise ValueError("expected the completed one-call MISAAL Egglog phase before the external LLVM boundary")
        current_raw = ROOT / phase["raw_invocations"][0]
        if current_raw.read_bytes() != raw:
            raise ValueError("continued MISAAL raw invocation differs from the pinned capture")
        record["historical_capture"] = {
            "evidence": record["source_capture_evidence"],
            "sha256": record["source_capture_sha256"],
            "invocations": record["invocations"],
            "reason": record["capture_reason"],
        }
        record.update(
            source_capture_evidence=str(current_capture_path.relative_to(ROOT)),
            source_capture_sha256=hashlib.sha256(current_capture_path.read_bytes()).hexdigest(),
            continuation_evidence=str(continuation.relative_to(ROOT)),
            continuation_sha256=hashlib.sha256(continuation.read_bytes()).hexdigest(),
            egglog_phase_status="complete",
            capture_reason="Egglog phase complete; external LLVM legalization intentionally not run.",
            raw_call_semantics=(
                "One invocation in the completed Egglog phase; both source outputs reuse its memoized result. "
                "Two earlier failed-attempt aliases are retained only in historical_capture."
            ),
            external_phases={"llvm_legalizer": "intentionally-not-run"},
            invocations=[
                {
                    "index": 0,
                    "raw": str(current_raw.relative_to(ROOT)),
                    "sha256": MISAAL_ADD_RAW_SHA256,
                    **({"workload": record["workloads"][0]} if record["workloads"] else {}),
                }
            ],
        )
        record["reason"] = record["reason"].replace(
            "Original source capture remains partial.",
            "Egglog phase complete; external LLVM legalization intentionally not run.",
        )
    (directory / "capture.json").write_text(json.dumps(record, indent=2) + "\n")
    (directory / "cases.json").write_text(json.dumps([record], indent=2) + "\n")
    return record


def modernize_hardboiled(source: str) -> str:
    """Modernize syntax and omit only provably unscheduled unsupported rules."""
    sys.path.insert(0, str(ROOT))
    from scripts.hardboiled_replay import omit_unexecuted_higher_order_rules, omit_unexecuted_keep_best

    source = omit_unexecuted_higher_order_rules(omit_unexecuted_keep_best(source))
    from scripts.paper_benchmarks.materialize import constructors, prefix_atoms

    names = set(re.findall(r"^\(function ([^\s()]+)", source, re.MULTILINE))
    # This primitive-valued lookup was partial and rejected inconsistent values.
    # It must remain a function; do not silently choose one conflicting value.
    lookup = "(function LanesInType (Type) i64)"
    if source.count(lookup) != 1:
        raise ValueError("unexpected LanesInType declaration")
    source = constructors(source, names - {"LanesInType"}).replace(
        lookup, "(function LanesInType (Type) i64 :no-merge)"
    )
    source = prefix_atoms(source, set(re.findall(r"^\(let ([^\s()]+)", source, re.MULTILINE)))
    # Current Egglog cannot extract inside a rule. Keep the same failing guard
    # and panic; omit only the three diagnostic prints that preceded its panic.
    diagnostic = '((extract e) (extract t1) (extract t2) (panic "type error"))'
    if source.count(diagnostic) != 1:
        raise ValueError("unexpected type-error diagnostic rule")
    source = source.replace(diagnostic, '((panic "type error"))')
    # The old frontend permits rule variables named after sorts. Rename only
    # atoms inside rules, preserving sort declarations, strings and comments.
    sorts = set(re.findall(r"^\((?:datatype|sort) ([^\s()]+)", source, re.MULTILINE))
    tokens = re.finditer(r';[^\n]*|"(?:\\.|[^"\\])*"|[()]|[^\s();"]+', source)
    depth = 0
    head = ""
    pieces: list[str] = []
    end = 0
    for token in tokens:
        value = token.group()
        if value.startswith((";", '"')):
            continue
        if value == "(":
            depth += 1
            if depth == 1:
                head = ""
        elif value == ")":
            depth -= 1
        elif depth == 1 and not head:
            head = value
        elif head in {"rule", "rewrite", "birewrite"} and value in sorts:
            replacement = "capture-var-" + value
            if replacement in source:
                raise ValueError(f"alpha-renaming would collide: {replacement}")
            pieces.extend((source[end : token.start()], replacement))
            end = token.end()
    pieces.append(source[end:])
    return "".join(pieces).rstrip() + "\n"


def preserve_invocation(directory: Path, content: bytes, metadata: dict) -> Path:
    """Serialize concurrent capture boundaries and never overwrite an input."""
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / ".capture.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        index = len(list(directory.glob("invocation-*.egg")))
        path = directory / f"invocation-{index:04d}.egg"
        with path.open("xb") as output:
            output.write(content)
        metadata = {
            **metadata,
            "sequence": index,
            "bytes": len(content),
            "sha256": hashlib.sha256(content).hexdigest(),
        }
        with path.with_suffix(".json").open("x") as output:
            json.dump(metadata, output, indent=2)
            output.write("\n")
        return path


def hardboiled_sidecar(directory: Path, delegate: Path | None) -> int:
    """Capture at the subprocess boundary, before an upstream temp file is reused."""
    content = sys.stdin.buffer.read()
    path = preserve_invocation(
        directory,
        content,
        {
            "boundary": "ExtractTileOperations::run_egglog sidecar stdin",
            "delegate": str(delegate),
            "delegate_sha256": hashlib.sha256(delegate.read_bytes()).hexdigest() if delegate else None,
        },
    )
    if delegate is None:
        path.with_suffix(".failure.txt").write_text(
            "The artifact does not pin or provide egglog-halide-sidecar; capture is partial.\n"
        )
        return 127
    with path.with_suffix(".stderr.log").open("wb") as errors:
        result = subprocess.run([str(delegate)], input=content, stdout=subprocess.PIPE, stderr=errors, check=False)
    path.with_suffix(".stdout.log").write_bytes(result.stdout)
    sys.stdout.buffer.write(result.stdout)
    path.with_suffix(".exit.json").write_text(json.dumps({"returncode": result.returncode}) + "\n")
    if result.returncode:
        path.with_suffix(".failure.txt").write_text(f"Sidecar exited {result.returncode}.\n")
    return result.returncode


def capture_misaal_program(checkout: Path, program: Path, directory: Path) -> int:
    """Observe the central method shared by rewrite, lower-swizzles and move-swizzles."""
    directory.mkdir(parents=True, exist_ok=False)
    original_directory = Path.cwd()
    os.chdir(directory)
    sys.path.insert(0, str(checkout / "lib"))
    os.environ["MISAAL_SRC"] = str(checkout)
    os.environ["MISAAL_ROOT_DIR"] = str(checkout)
    record: dict[str, Any] = {
        "revision": PINS["misaal"],
        "program": str(program),
        "program_sha256": hashlib.sha256(program.read_bytes()).hexdigest(),
        "working_directory": str(directory),
        "capture_boundary": "EggLogCompiler.execute_egglog_file (all callers)",
        "capture_status": "not-reached",
    }
    try:
        EggLogCompiler = importlib.import_module("compiler.EggLogCompiler").EggLogCompiler

        original = EggLogCompiler.execute_egglog_file

        def capture(self: Any, filename: str) -> Any:
            frame = inspect.currentframe()
            assert frame is not None and frame.f_back is not None
            path = preserve_invocation(
                directory,
                Path(filename).read_bytes(),
                {
                    "boundary": "EggLogCompiler.execute_egglog_file",
                    "caller": frame.f_back.f_code.co_name,
                    "original_filename": str(filename),
                    "delegate": self.egglog_bin,
                },
            )
            try:
                # Fail explicitly rather than letting the upstream shell wrapper
                # turn a missing executable into an empty, invented expression.
                if not os.access(self.egglog_bin, os.X_OK):
                    raise FileNotFoundError(f"Pinned Egglog executable is absent: {self.egglog_bin}")
                return original(self, filename)
            except BaseException:
                path.with_suffix(".failure.txt").write_text(traceback.format_exc())
                raise

        EggLogCompiler.execute_egglog_file = capture
        runpy.run_path(str(program), run_name="__main__")
        record["capture_status"] = "complete"
        returncode = 0
    except BaseException as error:
        record["error"] = f"{type(error).__name__}: {error}"
        traceback.print_exc()
        returncode = 1
    finally:
        invocations = sorted(directory.glob("invocation-*.egg"))
        if record["capture_status"] != "complete" and invocations:
            record["capture_status"] = "partial"
        if list(directory.glob("invocation-*.failure.txt")):
            record["capture_status"] = "partial"
        record["raw_invocations"] = [str(path) for path in invocations]
        (directory / "capture.json").write_text(json.dumps(record, indent=2) + "\n")
        os.chdir(original_directory)
    return returncode


def capture_hardboiled(
    checkout: Path, build: Path, directory: Path, delegate: Path | None, case_ids: set[str] | None = None
) -> None:
    """Compile original generator sources and attempt every declared configuration."""
    sys.path.insert(0, str(ROOT))
    from benchmarking.pilot import run_bounded_command

    directory.mkdir(parents=True, exist_ok=False)
    wrapper = directory / "bin/egglog-halide-sidecar"
    wrapper.parent.mkdir()
    # Environment variables are read by our own CLI; original generators stay intact.
    wrapper.write_text(
        f"#!{sys.executable}\nimport os\n"
        f"os.execv({sys.executable!r}, [{sys.executable!r}, "
        f"{str(Path(__file__).resolve())!r}, 'hardboiled-sidecar'])\n"
    )
    wrapper.chmod(0o755)
    library = build / "src/libHalide.dylib"
    catalog = json.loads((ROOT / "benchmarks/catalog.json").read_text())
    cases = [case for case in catalog["cases"] if case["family"] == "hardboiled"]
    if case_ids is not None:
        unknown = case_ids - {case["id"] for case in cases}
        if unknown:
            raise ValueError(f"unknown HardBoiled cases: {sorted(unknown)}")
        cases = [case for case in cases if case["id"] in case_ids]
    records = []
    compiled = {}
    compiled_directory = ROOT / "target/benchmark-acquisition/hardboiled" / directory.name
    compiled_directory.mkdir(parents=True, exist_ok=True)
    for case in cases:
        attempt = directory / case["id"]
        attempt.mkdir()
        source = checkout / case["source"]
        gpu = "tensorcore_benchmarks" in case["source"]
        generator = source.stem.removesuffix("_generator")
        binary = compiled_directory / source.stem
        if source not in compiled:
            command = [
                "clang++",
                "-std=c++20",
                "-O1",
                "-I",
                str(build / "include"),
                "-I",
                str(checkout / "tools"),
                "-I",
                str(checkout / "src"),
                "-I",
                str(checkout / "test/common"),
                str(source),
            ]
            if gpu:
                command += [str(checkout / "tools/GenGen.cpp")]
            command += [str(library), f"-Wl,-rpath,{library.parent}", "-o", str(binary)]
            result = run_bounded_command(
                command, checkout, attempt / "compile", timeout_sec=120, memory_limit_bytes=2 * 1024**3
            )
            compiled[source] = {"command": command, **asdict(result)}
        record = {
            "id": case["id"],
            "revision": PINS["hardboiled"],
            "source": str(source),
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "configuration": case.get("configuration", {}),
            "compile": compiled[source],
            "capture_status": "not-reached",
            "raw_invocations": [],
        }
        if compiled[source]["status"] == "success":
            command = ["env", f"PATH={wrapper.parent}:{os.environ['PATH']}", f"SUITE_CAPTURE_DIR={attempt}"]
            if delegate is not None:
                command += [f"SUITE_SIDECAR_DELEGATE={delegate}"]
            command += [str(binary)]
            if gpu:
                output = attempt / "compiler-output"
                output.mkdir()
                command += [
                    "-g",
                    generator,
                    "-f",
                    generator,
                    "-o",
                    str(output),
                    "-e",
                    "static_library,stmt,h,llvm_assembly,assembly",
                    "target=x86-64-linux-cuda-cuda_capability_80",
                ]
                command += [
                    f"{key}={str(value).lower() if isinstance(value, bool) else value}"
                    for key, value in case.get("configuration", {}).items()
                ]
            result = run_bounded_command(
                command, attempt, attempt / "generate", timeout_sec=120, memory_limit_bytes=2 * 1024**3
            )
            record["generate"] = {"command": command, **asdict(result)}
            diagnostics = []
            # Original instruction-selection mains redirect stderr to shared /tmp
            # paths. Preserve each one before the next original main overwrites it.
            for index, filename in enumerate(re.findall(r'freopen\("([^"\n]+)", "w", stderr\)', source.read_text())):
                original = Path(filename)
                if original.is_file():
                    saved = attempt / f"original-stderr-{index}.log"
                    saved.write_bytes(original.read_bytes())
                    diagnostics.append({"original": filename, "saved": str(saved)})
            record["redirected_diagnostics"] = diagnostics
            invocations = sorted(attempt.glob("invocation-*.egg"))
            record["raw_invocations"] = [str(path.relative_to(ROOT)) for path in invocations]
            if invocations:
                record["capture_status"] = (
                    "complete"
                    if (
                        result.status == "success"
                        and delegate is not None
                        and not list(attempt.glob("invocation-*.failure.txt"))
                    )
                    else "partial"
                )
            record["reason"] = result.message
            if delegate is None and invocations:
                record["reason"] = (
                    "First sidecar input preserved; missing unpinned sidecar prevents "
                    "continuation and complete capture."
                )
        else:
            record["reason"] = "Original generator compilation failed; see compile logs."
        records.append(record)
        (directory / "cases.json").write_text(json.dumps(records, indent=2, default=str) + "\n")
        print(f"{case['id']}: {record['capture_status']} ({len(record['raw_invocations'])} calls)", flush=True)


def record_misaal_blocker(checkout: Path, prerequisite: Path, directory: Path) -> None:
    """Account for every declared case when its shared generator toolchain fails."""
    evidence = json.loads(prerequisite.read_text())
    if evidence["status"] == "success":
        raise ValueError("a successful prerequisite cannot justify blocked cases")
    directory.mkdir(parents=True, exist_ok=False)
    catalog = json.loads((ROOT / "benchmarks/catalog.json").read_text())
    cases = []
    for case in catalog["cases"]:
        if case["family"] != "misaal":
            continue
        original = checkout / case["source"]
        generator = original / "src" / (original.name + "_generator.cpp")
        makefile = original.parent / "Makefile"
        cases.append(
            {
                "id": case["id"],
                "revision": PINS["misaal"],
                "source": str(generator),
                "source_sha256": hashlib.sha256(generator.read_bytes()).hexdigest(),
                "configuration": case["configuration"],
                "makefile": str(makefile),
                "makefile_sha256": hashlib.sha256(makefile.read_bytes()).hexdigest(),
                "capture_status": "not-reached",
                "raw_invocations": [],
                "blocking_phase": "shared-generator-toolchain",
                "prerequisite_evidence": str(prerequisite),
                "prerequisite_status": evidence["status"],
                "prerequisite_stdout": evidence["stdout_path"],
                "prerequisite_stderr": evidence["stderr_path"],
                "reason": "Shared generator toolchain did not complete; per-case generation was not reached.",
            }
        )
    (directory / "cases.json").write_text(json.dumps(cases, indent=2) + "\n")
    print(f"Recorded {len(cases)} MISAAL cases blocked by the shared generator build.")


def self_test() -> None:
    """Exercise overwrites, concurrency, and the shared MISAAL capture boundary."""
    from concurrent.futures import ThreadPoolExecutor

    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        original = directory / "reused.egg"
        saved = directory / "saved"
        for content in (b"first", b"second"):
            original.write_bytes(content)
            preserve_invocation(saved, original.read_bytes(), {"original_filename": str(original)})
        with ThreadPoolExecutor(max_workers=4) as pool:
            list(pool.map(lambda i: preserve_invocation(saved, str(i).encode(), {}), range(12)))
        paths = sorted(saved.glob("invocation-*.egg"))
        assert len(paths) == 14
        assert paths[0].read_bytes() == b"first"
        assert paths[1].read_bytes() == b"second"
        for index, path in enumerate(paths):
            metadata = json.loads(path.with_suffix(".json").read_text())
            assert metadata["sequence"] == index
            assert metadata["sha256"] == hashlib.sha256(path.read_bytes()).hexdigest()
        checkout = directory / "misaal"
        package = checkout / "lib/compiler"
        package.mkdir(parents=True)
        (package / "__init__.py").write_text("")
        (package / "EggLogCompiler.py").write_text(
            "import sys\nfrom pathlib import Path\nclass EggLogCompiler:\n"
            "    egglog_bin = sys.executable\n"
            "    def execute_egglog_file(self, filename):\n"
            "        return Path(filename).read_text()\n"
            + "".join(
                f"    def {caller}(self):\n"
                f"        path = Path({str(directory / 'same.egg')!r})\n"
                f"        path.write_text({caller!r})\n"
                f"        assert self.execute_egglog_file(str(path)) == {caller!r}\n"
                for caller in ("apply_rewrite", "lower_swizzles", "move_swizzles")
            )
        )
        program = checkout / "program.py"
        program.write_text(
            "from compiler.EggLogCompiler import EggLogCompiler\n"
            "compiler = EggLogCompiler()\n"
            "compiler.apply_rewrite()\ncompiler.lower_swizzles()\ncompiler.move_swizzles()\n"
        )
        captured = directory / "central-boundary"
        assert capture_misaal_program(checkout, program, captured) == 0
        assert json.loads((captured / "capture.json").read_text())["capture_status"] == "complete"
        callers = ("apply_rewrite", "lower_swizzles", "move_swizzles")
        for path, caller in zip(sorted(captured.glob("invocation-*.egg")), callers, strict=True):
            assert path.read_text() == caller
            assert json.loads(path.with_suffix(".json").read_text())["caller"] == caller
    print("capture self-test passed")


def main() -> int:
    if len(sys.argv) > 1 and sys.argv[1] == "hardboiled-sidecar":
        delegate = os.environ.get("SUITE_SIDECAR_DELEGATE")
        return hardboiled_sidecar(Path(os.environ["SUITE_CAPTURE_DIR"]), Path(delegate) if delegate else None)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "mode",
        choices=(
            "hardboiled",
            "misaal-program",
            "misaal-blocked",
            "misaal-replay",
            "misaal-capture-replay",
            "self-test",
        ),
    )
    parser.add_argument("--checkout", type=Path)
    parser.add_argument("--build", type=Path)
    parser.add_argument("--program", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--sidecar", type=Path)
    parser.add_argument("--case", action="append")
    parser.add_argument("--prerequisite", type=Path)
    parser.add_argument("--compatibility", type=Path, help="recorded raw extraction results for misaal-replay")
    parser.add_argument("--validation", type=Path, help="existing bounded oracle-control results; never runs an engine")
    parser.add_argument("--continuation", type=Path, help="completed Egglog-phase evidence for misaal-replay")
    parser.add_argument("--capture", type=Path, help="backend capture manifest for misaal-capture-replay")
    args = parser.parse_args()
    if args.mode == "self-test":
        self_test()
    elif args.mode == "hardboiled":
        if not all((args.checkout, args.build, args.output)):
            parser.error("hardboiled requires --checkout, --build and --output")
        capture_hardboiled(
            args.checkout.resolve(),
            args.build.resolve(),
            args.output.resolve(),
            args.sidecar.resolve() if args.sidecar else None,
            set(args.case) if args.case else None,
        )
    elif args.mode == "misaal-blocked":
        if not all((args.checkout, args.prerequisite, args.output)):
            parser.error("misaal-blocked requires --checkout, --prerequisite and --output")
        record_misaal_blocker(args.checkout.resolve(), args.prerequisite.resolve(), args.output.resolve())
    elif args.mode == "misaal-capture-replay":
        if not all((args.capture, args.output)):
            parser.error("misaal-capture-replay requires --capture and --output")
        prepare_misaal_capture(args.capture.resolve(), args.output.resolve())
    elif args.mode == "misaal-replay":
        if not all((args.compatibility, args.output)):
            parser.error("misaal-replay requires --compatibility and --output")
        prepare_misaal_replay(
            args.compatibility.resolve(),
            args.output.resolve(),
            args.validation.resolve() if args.validation else None,
            args.continuation.resolve() if args.continuation else None,
        )
    else:
        if not all((args.checkout, args.program, args.output)):
            parser.error("misaal-program requires --checkout, --program and --output")
        return capture_misaal_program(args.checkout.resolve(), args.program.resolve(), args.output.resolve())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
