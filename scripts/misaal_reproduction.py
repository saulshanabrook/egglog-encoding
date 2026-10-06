"""Observe every Egglog invocation reached by a complete MISAAL export.

`capture --request REQUEST --output FRESH_DIRECTORY` is the guarded entrypoint.
Other modes are child hooks in that process group, never standalone benchmarks.
Fresh requests are produced by scripts.reproduction_prepare_misaal.
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
import traceback
from dataclasses import asdict
from pathlib import Path
from types import ModuleType
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
EGGLOG_EXPORT = "egglog-only-v1"
EXPORT_SOURCE_KIND = "misaal-egglog-export"


def save_receipt(path: Path, value: Any) -> None:
    """Publish complete JSON atomically, including before a risky subprocess."""
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, default=str) + "\n")
    temporary.replace(path)


def verified_request(path: Path) -> dict[str, Any]:
    """Bind a generated Egglog-only request to its current source, tools and runtime."""
    from scripts.reproduction_misaal_export import EXPORT_SOURCE_SHA256, verify_export_request
    from scripts.reproduction_misaal_groups import CONTRACT, SOURCE
    from scripts.reproduction_misaal_patterns import PARAMETER_ABI_CONTRACT, PARAMETER_ABI_SOURCE_SHA256

    request: dict[str, Any] = json.loads(path.read_text())
    if request.get("egglog_export") != EGGLOG_EXPORT or request.get("expected_generator_outputs"):
        raise ValueError("MISAAL preparation supports only Egglog export; no native code-generation request")
    if any(key in request for key in ("terminal_empty_child", "acquisition_tail", "hvx_link_contract")):
        raise ValueError("obsolete native-lowering request")
    from benchmarking.memory_guard import GROUP_LIMIT_BYTES

    timeout = request.get("source_timeout_sec", 900)
    memory = request.get("source_memory_limit_bytes", GROUP_LIMIT_BYTES)
    if not isinstance(timeout, (int, float)) or not math.isfinite(timeout) or timeout <= 0:
        raise ValueError("source timeout must be finite and positive")
    if not isinstance(memory, int) or not 0 < memory <= GROUP_LIMIT_BYTES:
        raise ValueError("source memory limit exceeds the guarded policy")
    if any(key.startswith("MISAAL_EXPORT_") for key in request["environment"]):
        raise ValueError("export activation belongs to the guarded frontend")
    verify_export_request(request)
    if request["generator_command"][0] != request["generator"] or "{output}" not in request["generator_command"]:
        raise ValueError("generator request escaped its recorded executable/output directory")
    pins = {}
    if "parameter_abi" in request:
        if request["parameter_abi"] != PARAMETER_ABI_CONTRACT:
            raise ValueError("unsupported parameter ABI contract")
        pins.update(
            {name: EXPORT_SOURCE_SHA256.get(name, digest) for name, digest in PARAMETER_ABI_SOURCE_SHA256.items()}
        )
    if "racket_group_containment" in request:
        if request["racket_group_containment"] != CONTRACT:
            raise ValueError("unsupported process containment contract")
        pins[SOURCE] = EXPORT_SOURCE_SHA256[SOURCE]
    if any(request["source_hashes"].get(key) != value for key, value in pins.items()):
        raise ValueError("source API or process containment pins changed")
    checkout = Path(request["checkout"])
    for relative, digest in request["source_hashes"].items():
        if hashlib.sha256((checkout / relative).read_bytes()).hexdigest() != digest:
            raise ValueError(f"MISAAL source changed: {relative}")
    for key in ("backend", "python", "generator", *(["racket"] if "racket" in request else [])):
        if (
            not os.access(request[key], os.X_OK)
            or hashlib.sha256(Path(request[key]).read_bytes()).hexdigest() != request[key + "_sha256"]
        ):
            raise ValueError(f"MISAAL executable changed: {key}")
    return request


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
    """Bind target cache bytes and the prior real child's selected expressions."""
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
    target = request["configuration"]["target"]
    semantics, patterns, wrapper, flag, so_name = {
        "arm": ("arm", "ARM import arm_patterns", "arm_wrappers.c.ll", "arm", "libARMLegalizer.so"),
        "hexagon": ("hvx", "HVX import HVX_patterns", "hvx_wrappers.ll", "hex", "libHVXLegalizer.so"),
        "x86": ("x86", "x86 import x86_patterns", "x86_wrappers.c.ll", "x86", "libx86LegalizerAllArgs.so"),
    }[target]
    frontend = (
        "from patterns.Halide import Halide_patterns as misaal_input_patterns"
        if "MISAAL_DISABLE_FRONTEND_PATTERNS" not in request["environment"]
        else "misaal_input_patterns = []"
    )
    iterations = int(request["environment"].get("MISAAL_EQ_SAT_ITERS", "5"))
    so_path = str(Path(request["environment"]["LEGALIZERS_DIR"]) / so_name)
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
        prior_paths = sorted(path for path in directory.parent.glob("child-*/capture.json") if path.parent != directory)
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
    }
    save_receipt(directory / "capture.json", record)
    checkout = Path(request["checkout"])
    sys.path[:0] = [str(checkout / "lib"), *os.environ.get("PYTHONPATH", "").split(os.pathsep)]
    capture_lock = threading.Lock()

    def capture_backend(self: Any, filename: str) -> str:
        from scripts.hardboiled_replay import egglog_forms

        with capture_lock:
            frame = inspect.currentframe()
            assert frame is not None and frame.f_back is not None
            raw = directory / f"invocation-{len(record['invocations']):04}.egg"
            with raw.open("xb") as stream:
                stream.write(Path(filename).read_bytes())
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
                    result = subprocess.run(
                        call["command"],
                        stdout=out,
                        stderr=err,
                        timeout=request.get("source_timeout_sec", 300),
                        check=False,
                    )
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

    def capture_helper(backend: str, filename: str, *, quiet: bool) -> subprocess.CompletedProcess[Any]:
        """Run an actual source helper; its Boolean result never becomes a workload."""
        with capture_lock:
            raw = directory / f"helper-{len(record['helper_invocations']):04}.egg"
            raw.write_bytes(Path(filename).read_bytes())
            entry: dict[str, Any] = {
                "index": len(record["helper_invocations"]),
                "kind": "pattern-validation",
                "admitted_as_workload": False,
                "raw": str(raw),
                "sha256": hashlib.sha256(raw.read_bytes()).hexdigest(),
                "source_input": filename,
                "source_backend": backend,
                "command": [request["backend"], filename],
                "backend_sha256": request["backend_sha256"],
                "status": "running",
            }
            record["helper_invocations"].append(entry)
            save_receipt(directory / "capture.json", record)
            try:
                with raw.with_suffix(".stdout.log").open("wb") as out, raw.with_suffix(".stderr.log").open("wb") as err:
                    result = subprocess.run(entry["command"], stdout=out, stderr=err, check=False, timeout=120)
                for name, stream in (("stdout", sys.stdout), ("stderr", sys.stderr)):
                    content = raw.with_suffix(f".{name}.log").read_bytes()
                    entry[name + "_sha256"] = hashlib.sha256(content).hexdigest()
                    if not quiet:
                        stream.flush()
                        stream.buffer.write(content)
                entry.update(status="success", returncode=result.returncode, accepted=result.returncode == 0)
                return result
            except BaseException:
                entry.update(status="failure", error=traceback.format_exc())
                raise
            finally:
                save_receipt(raw.with_suffix(".result.json"), entry)
                save_receipt(directory / "capture.json", record)

    def launch_racket(command: list[str], **kwargs: Any) -> subprocess.Popen[Any]:
        from scripts.reproduction_misaal_groups import launch_registered

        endpoint = os.environ.get("MISAAL_RACKET_GROUP_SOCKET")
        if endpoint is None or command[0] != "racket" or shutil.which("racket") != request["racket"]:
            raise ValueError("Racket launch requires the prepared executable and live guard")
        return launch_registered(command, Path(endpoint), request["python"], **kwargs)

    callbacks = ModuleType("misaal_capture")
    callbacks.__dict__.update(capture_helper=capture_helper, launch_racket=launch_racket)
    sys.modules["misaal_capture"] = callbacks
    record["helper_invocations"] = []

    def checked_legalizer(self: Any) -> None:
        raise ValueError("LLVM legalization is not requested by Egglog export")

    try:
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
        execution = source_child_program(request, program, directory, record)
        egg_module = importlib.import_module("compiler.EggLogCompiler")
        importlib.import_module("patterns.PatternUtils")
        egg_compiler = egg_module.EggLogCompiler
        hydride_compiler = importlib.import_module("compiler.HydrideCompiler").HydrideCompiler
        egg_compiler.execute_egglog_file = capture_backend
        hydride_compiler.run_llvm_legalizer = checked_legalizer
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
                    [item["name"] for item in export["compilation"]["named_results"]] != [name for name, _ in expected]
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
        try:
            runpy.run_path(str(execution), run_name="__main__")
        except SystemExit as error:
            empty = record["egglog_export"] if not record["egglog_export"]["inputs"] else None
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
        export = record["egglog_export"]
        if any(call["status"] != "success" for call in [*record["invocations"], *record["helper_invocations"]]):
            raise ValueError("Egglog export reached LLVM or unfinished optimizer work")
        if export["inputs"]:
            compiled = export.get("compilation", {})
            if compiled.get("status") != "complete" or compiled.get("invocation_count") != len(record["invocations"]):
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
        "expected_sessions": sum(
            call.get("status") == "success"
            for child in children
            for call in json.loads(child.read_text())["invocations"]
        ),
        "materialized_sessions": 0,
        "complete": False,
    }
    source_order = 0
    for child in children:
        for call in json.loads(child.read_text())["invocations"]:
            order = source_order
            source_order += 1
            if call.get("status") != "success":
                record.setdefault("failed_invocations", []).append({"child": str(child), **call})
                continue
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
                    "source_order": order,
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
        reason="Original Egglog export completed; standalone outputs await ordinary validation",
    )
    record["materialization"]["complete"] = True


def run_frontend(request_path: Path, attempt: Path, *, group_endpoint: Path | None = None) -> int:
    """Keep the source parent alive until its complete export ledger is verified."""
    request = verified_request(request_path)
    if any(name in os.environ for name in ("MISAAL_EXPORT_MODE", "MISAAL_EXPORT_EVENTS")):
        raise ValueError("Ambient export activation is not a verified request")
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
    record.update(source_kind=EXPORT_SOURCE_KIND, native_codegen="not_requested")
    save_receipt(attempt / "capture.json", record)
    recover_independent = False
    try:
        result = subprocess.run(command, cwd=attempt, env=environment, check=False)
        record["generator_returncode"] = result.returncode
        record["source_completion"]["parent_returncode"] = result.returncode
        children = sorted((attempt / "children").glob("child-*/capture.json"))
        record["children"] = [{"path": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()} for p in children]
        recover_independent = bool(result.returncode) or any(
            not json.loads(path.read_text())["source_capture_complete"] for path in children
        )
        if (
            result.returncode
            or [path.parent for path in children] != sorted((attempt / "children").glob("child-*"))
            or any(not json.loads(p.read_text())["source_capture_complete"] for p in children)
        ):
            raise ValueError("Generator or a reached Python child did not complete")
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
        record.update(source_capture_complete=True)
        record["source_completion"] = {
            "status": "success",
            "parent_returncode": result.returncode,
            "outputs": record["native_outputs"],
            "children": record["children"],
        }
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
        if not any(json.loads(path.read_text())["invocations"] for path in children):
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
        children = sorted((attempt / "children").glob("child-*/capture.json"))
        if (
            recover_independent
            and not (attempt / "replays").exists()
            and any(
                call.get("status") == "success"
                for child in children
                for call in json.loads(child.read_text()).get("invocations", [])
            )
        ):
            # Backend calls create independent graphs. A completed response and
            # its exact query/output contract do not depend on later compiler work.
            record["parent_failure"] = {"reason": record["reason"], "error": record["error"]}
            try:
                materialize_invocations(children, attempt / "replays", record)
            except (OSError, ValueError, KeyError):
                record.update(status="failure", reason=str(sys.exc_info()[1]), workloads=[])
            else:
                record["source_completion"].update(status="complete", scope="completed-independent-egglog-calls")
                return 0
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
    Backend children inherit the root group; pinned detached Racket groups
    require the outer guard's live launch lease and aggregate RSS accounting.
    """
    from benchmarking.processes import run_bounded_command

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
            memory_limit_bytes=request.get("source_memory_limit_bytes", 10 * 1024**3),
            require_guard=True,
            disk_reserve_bytes=2 * 1024**3,
            allow_warning_pressure=False,
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
    record.update(source_kind=EXPORT_SOURCE_KIND, native_codegen="not_requested")
    record["process"] = asdict(process)
    record["source_timeout_sec"] = request.get("source_timeout_sec", 900)
    record["source_memory_limit_bytes"] = request.get("source_memory_limit_bytes", 10 * 1024**3)
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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("capture", "frontend", "child"))
    parser.add_argument("--request", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--group-endpoint", type=Path)
    parser.add_argument("arguments", nargs="*")
    args = parser.parse_intermixed_args()
    if args.mode == "child":
        return observe_python(args.request, args.output, args.arguments)
    if args.mode == "frontend":
        return run_frontend(args.request, args.output, group_endpoint=args.group_endpoint)
    return int(capture_misaal(args.request, args.output)["status"] != "ordinary-validation-pending")


if __name__ == "__main__":
    raise SystemExit(main())
