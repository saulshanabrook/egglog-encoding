"""Exercise live capture handoffs with tiny fake tools, never native validation."""

from __future__ import annotations

import ast
import hashlib
import json
import os
import subprocess
import sys
import threading
from collections.abc import Iterator
from pathlib import Path
from types import ModuleType
from typing import Any

import pytest

from scripts import misaal_reproduction as misaal


@pytest.fixture
def protocol_request(tmp_path: Path) -> Iterator[Path]:
    checkout = tmp_path / "source"
    compiler = checkout / "lib/compiler"
    compiler.mkdir(parents=True)
    (checkout / "lib/patterns").mkdir()
    (compiler / "EggLogCompiler.py").write_text(
        "import subprocess as sb\nfrom types import SimpleNamespace\nclass EggLogCompiler: pass\n"
        "def is_pattern_valid_egg(filename, backend='original/configured/backend'):\n"
        "    compiler = SimpleNamespace(egglog_bin=backend)\n"
        "    result = sb.run(compiler.egglog_bin + ' ' + filename, shell=True)\n"
        "    return result.returncode == 0\n"
    )
    pattern_utils = checkout / "lib/patterns/PatternUtils.py"
    pattern_utils.write_text(
        "import subprocess as sb\nfrom types import SimpleNamespace\n"
        "def is_pattern_valid_egg(filename, backend='original/configured/backend'):\n"
        "    compiler = SimpleNamespace(egglog_bin=backend)\n"
        "    result = sb.run(compiler.egglog_bin + ' ' + filename, shell=True, stdout=sb.DEVNULL, stderr=sb.DEVNULL)\n"
        "    sb.run('rm ' + filename, shell=True)\n"
        "    return result.returncode == 0\n"
    )
    (compiler / "HydrideCompiler.py").write_text(
        "from compiler.EggLogCompiler import EggLogCompiler\nclass HydrideCompiler(EggLogCompiler): pass\n"
    )
    legalizer = checkout / "Hydride/codegen-generator/tools/low-level-codegen/RoseLowLevelCodeGen.py"
    legalizer.parent.mkdir(parents=True)
    legalizer.write_text(
        "import os, shlex, sys\nfrom pathlib import Path\n"
        "prefix = sys.argv[5]\n"
        "Path(prefix + '.ll').write_text('define i32 @hydride_expr_0() {\\n ret i32 0\\n}\\n')\n"
        "for suffix in ('.linked.bc', '.linked.ll', '.legalize.ll'):\n"
        "    os.system(shlex.join([os.environ['PROTOCOL_LLVM_TOOL'], prefix + suffix]))\n"
    )
    (checkout / "legalizer.so").write_text("fake input identity only")
    (checkout / "intrinsics.ll").write_text("fake input identity only")
    child_program = """import os
from pathlib import Path
from compiler.HydrideCompiler import HydrideCompiler
c = HydrideCompiler()
c.egglog_bin = "original/configured/backend"
raw = Path("temporary-backend.egg")
raw.write_text("(datatype E (Seed))\\n(let srcexpr (Seed))\\n" + "(run 5)\\n(extract srcexpr)\\n")
if os.environ.get("PROTOCOL_HELPERS"):
    from compiler.EggLogCompiler import is_pattern_valid_egg as compiler_helper
    from patterns.PatternUtils import is_pattern_valid_egg as pattern_helper
    for index, helper in enumerate((compiler_helper, pattern_helper)):
        for accepted in (True, False):
            helper_input = Path(f"helper-input-{index}-{accepted}.egg")
            helper_input.write_text("accepted input" if accepted else "rejected input")
            assert helper(str(helper_input)) is accepted
if os.environ.get("PROTOCOL_MULTI_ROOT"):
    raw.write_text(raw.read_text() + "(extract srcexpr)\\n")
for _ in range(2):
    try:
        assert c.execute_egglog_file(str(raw)) == "(Seed)"
    except ValueError:
        if not os.environ.get("PROTOCOL_SWALLOW_BACKEND_FAILURE"):
            raise
c.llvm_out_file_name = os.environ["MISAAL_CAPTURE_LLVM_PREFIX"]
c.input_tests = [("hydride_expr_0", "source expression")]
c.output_file_path = "rosette-input.txt"
Path(c.output_file_path).write_text("real source data would go here")
c.hydride_root_path = os.environ["MISAAL_ROOT_DIR"] + "/Hydride"
c.llvm_so_path = os.environ["MISAAL_ROOT_DIR"] + "/legalizer.so"
c.intrinsics_file = os.environ["MISAAL_ROOT_DIR"] + "/intrinsics.ll"
c.llvm_flags = ["-source-legalize"]
c.compile_times = []
c.run_llvm_legalizer()
"""
    tools = {
        "backend": (
            "import os, sys\nprint('(Seed)')\n"
            "from pathlib import Path\n"
            "if Path(sys.argv[1]).read_text() == 'rejected input': sys.exit(9)\n"
            "if os.environ.get('PROTOCOL_MULTI_ROOT'): print('(Seed)')\n"
            "sys.exit(7 if os.environ.get('PROTOCOL_BACKEND_FAILURE') else 0)\n"
        ),
        "llvm_as": "# Intentionally fake syntax validator: protocol evidence only.\n",
        "llvm_tool": (
            "import os, sys\nfrom pathlib import Path\n"
            "if os.environ.get('PROTOCOL_LLVM_FAILURE'): sys.exit(42)\n"
            "name = 'wrong_function' if os.environ.get('PROTOCOL_BAD_FUNCTION') else 'hydride_expr_0'\n"
            "value = 'undef' if os.environ.get('PROTOCOL_UNDEFINED_RESULT') else '0'\n"
            "Path(sys.argv[1]).write_text('define i32 @' + name + '() {\\n ret i32 ' + value + '\\n}\\n')\n"
        ),
        "generator": (
            "import os, subprocess, sys\nfrom pathlib import Path\n"
            f"program = {child_program!r}\n"
            "child = Path(os.environ['HYDRIDE_BENCHMARK'] + '_misaal.py')\n"
            "child.write_text(program)\n"
            "result = subprocess.run(['python3', str(child)], check=False)\n"
            "if result.returncode: sys.exit(result.returncode)\n"
            "feedback = Path(os.environ['MISAAL_CAPTURE_LLVM_PREFIX'] + '.ll').read_text()\n"
            "Path('parent-consumed-feedback.txt').write_text(feedback)\n"
            "if os.environ.get('PROTOCOL_PARENT_FAILURE'): sys.exit(19)\n"
            "Path(sys.argv[1], 'generator.ll').write_text(feedback)\n"
            "Path(sys.argv[1], 'generator.a').write_text('fake final archive')\n"
        ),
    }
    for name, script in tools.items():
        executable = tmp_path / name
        executable.write_text(f"#!{sys.executable}\n" + script)
        executable.chmod(0o755)
    request: dict[str, Any] = {
        "case_id": "protocol-only",
        "revision": "a" * 40,
        "checkout": str(checkout),
        "source_hashes": {
            str(path.relative_to(checkout)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [*compiler.glob("*.py"), pattern_utils]
        },
        "generator_command": [str(tmp_path / "generator"), "{output}"],
        "expected_generator_outputs": ["generator.a", "generator.ll"],
        "environment": {"PATH": os.environ["PATH"], "PROTOCOL_LLVM_TOOL": str(tmp_path / "llvm_tool")},
    }
    for name in ("python", "backend", "llvm_as", "generator"):
        executable = Path(sys.executable).resolve() if name == "python" else tmp_path / name
        request[name] = str(executable)
        request[name + "_sha256"] = hashlib.sha256(executable.read_bytes()).hexdigest()
    request_path = tmp_path / "request.json"
    request_path.write_text(json.dumps(request))
    yield request_path
    # Remove only this fixture's unique feedback prefix, recorded by the hook.
    for receipt in tmp_path.glob("*/capture.json"):
        record = json.loads(receipt.read_text())
        if "output_name_adaptation" in record:
            prefix = Path(record["output_name_adaptation"]["feedback_prefix"])
            for path in prefix.parent.glob(prefix.name + ".*"):
                path.unlink()


def test_complete_child_returns_llvm_to_live_parent_and_keeps_duplicate_calls(
    protocol_request: Path, tmp_path: Path
) -> None:
    attempt = tmp_path / "attempt"
    assert misaal.run_frontend(protocol_request, attempt) == 0
    record = json.loads((attempt / "capture.json").read_text())
    assert (attempt / "parent-consumed-feedback.txt").read_text() == (attempt / "generator.ll").read_text()
    assert record["source_completion"]["status"] == "success"
    assert record["source_completion"]["parent_returncode"] == 0
    assert record["status"] == "ordinary-validation-pending"
    assert len(record["workloads"]) == len(record["invocations"]) == 2
    assert record["materialization"] == {"complete": True, "expected_sessions": 2, "materialized_sessions": 2}
    assert all(len(call["output_contract"]["checks"]) == call["root_count"] for call in record["invocations"])
    assert record["invocations"][0]["sha256"] == record["invocations"][1]["sha256"]
    assert record["invocations"][0]["raw"] != record["invocations"][1]["raw"]
    for path in record["workloads"]:
        text = Path(path).read_text()
        assert "(let $srcexpr (Seed))\n(run 5)\n(extract $srcexpr)\n(check (= $srcexpr (Seed)))" in text
        assert text.count("(let ") == 1
        assert "(union " not in text
    child = json.loads(Path(record["children"][0]["path"]).read_text())
    assert child["legalizations"][0]["validation"]["required_functions"] == ["hydride_expr_0"]
    tools = json.loads((Path(record["children"][0]["path"]).parent / "legalize-0000/tools.json").read_text())
    assert len(tools) == 3 and all(tool["returncode"] == 0 for tool in tools)


@pytest.mark.parametrize(
    "failure", ("LLVM_FAILURE", "BAD_FUNCTION", "UNDEFINED_RESULT", "PARENT_FAILURE", "BACKEND_FAILURE")
)
def test_failed_native_boundary_cannot_admit_partial_work(protocol_request: Path, tmp_path: Path, failure: str) -> None:
    request = json.loads(protocol_request.read_text())
    request["environment"]["PROTOCOL_" + failure] = "1"
    request["environment"]["PROTOCOL_SWALLOW_BACKEND_FAILURE"] = "1"
    protocol_request.write_text(json.dumps(request))
    attempt = tmp_path / "attempt"
    assert misaal.run_frontend(protocol_request, attempt) == 1
    record = json.loads((attempt / "capture.json").read_text())
    assert record["status"] == "failure"
    assert record["workloads"] == []
    assert record["source_capture_complete"] is False
    assert record["source_completion"]["status"] == "failure"
    assert record["source_completion"]["parent_returncode"] != 0
    if failure != "PARENT_FAILURE":
        assert not (attempt / "parent-consumed-feedback.txt").exists()
    if failure == "UNDEFINED_RESULT":
        evidence = attempt / "children/child-0000/legalize-0000"
        assert "ret i32 undef" in next(evidence.glob("*.legalize.ll")).read_text()
        audit = json.loads((evidence / "verify.json").read_text())["lowering_audit"]
        assert audit["status"] == "failure" and audit["undefined_return_functions"] == ["hydride_expr_0"]


def test_request_rejects_changed_sources_and_reused_pattern_cache(protocol_request: Path, tmp_path: Path) -> None:
    request = json.loads(protocol_request.read_text())
    checkout = Path(request["checkout"])
    cache = checkout / "lib/patterns/old.pickle"
    cache.touch()
    with pytest.raises(ValueError, match="fresh pattern caches"):
        misaal.run_frontend(protocol_request, tmp_path / "attempt")
    assert not (tmp_path / "attempt").exists()
    (checkout / "lib/compiler/EggLogCompiler.py").write_text("changed source")
    with pytest.raises(ValueError, match="source identity changed"):
        misaal.verified_request(protocol_request)


@pytest.mark.parametrize("key", ["library", "legalizer"])
def test_request_rechecks_declared_libraries(protocol_request: Path, key: str) -> None:
    request = json.loads(protocol_request.read_text())
    library = protocol_request.parent / f"{key}.dylib"
    library.write_text("original library bytes")
    library.chmod(0o644)
    request.update({key: str(library), f"{key}_sha256": hashlib.sha256(library.read_bytes()).hexdigest()})
    protocol_request.write_text(json.dumps(request))
    misaal.verified_request(protocol_request)
    library.write_text("changed library bytes")
    with pytest.raises(ValueError, match=f"{key} identity changed"):
        misaal.verified_request(protocol_request)


def test_native_legalizer_must_match_declared_library(protocol_request: Path, tmp_path: Path) -> None:
    request = json.loads(protocol_request.read_text())
    selected = tmp_path / "different-legalizer.so"
    selected.write_text("different selector bytes")
    request.update(legalizer=str(selected), legalizer_sha256=hashlib.sha256(selected.read_bytes()).hexdigest())
    protocol_request.write_text(json.dumps(request))
    attempt = tmp_path / "attempt"
    assert misaal.run_frontend(protocol_request, attempt) == 1
    assert not (attempt / "parent-consumed-feedback.txt").exists()
    record = json.loads((attempt / "capture.json").read_text())
    assert record["source_capture_complete"] is False and record["workloads"] == []
    child = json.loads(Path(record["children"][0]["path"]).read_text())
    assert "unexpected identity" in str(child)


def test_pattern_cache_is_fresh_and_attempt_owned(protocol_request: Path, tmp_path: Path) -> None:
    request = json.loads(protocol_request.read_text())
    request["pattern_cache_contract"] = {"environment": "MISAAL_PATTERN_CACHE_DIR"}
    request["environment"]["MISAAL_PATTERN_CACHE_DIR"] = "must-not-be-used"
    generator = Path(request["generator"])
    generator.write_text(
        generator.read_text()
        + "\ncache = Path(os.environ['MISAAL_PATTERN_CACHE_DIR'])\n"
        + "assert cache.is_dir() and not list(cache.iterdir())\n"
        + "(cache / 'generated.pickle').write_bytes(b'fake pattern cache for isolation testing')\n"
    )
    request["generator_sha256"] = hashlib.sha256(generator.read_bytes()).hexdigest()
    protocol_request.write_text(json.dumps(request))
    for label in ("first", "second"):
        attempt = tmp_path / label
        assert misaal.run_frontend(protocol_request, attempt) == 0
        record = json.loads((attempt / "capture.json").read_text())
        assert record["pattern_cache_directory"] == str(attempt / "pattern-cache")
        assert len(record["pattern_cache_after"]) == 1
        assert Path(record["pattern_cache_after"][0]["path"]).is_relative_to(attempt)
    assert not list((Path(request["checkout"]) / "lib/patterns").glob("*.pickle"))


def test_llvm_syntax_failure_is_not_hidden(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    llvm = tmp_path / "output.ll"
    llvm.write_text("define i32 @requested() {\n malformed\n}\n")
    monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: subprocess.CompletedProcess(args[0], 1))
    with pytest.raises(ValueError, match="verifier rejected"):
        misaal.validate_llvm(llvm, {"requested"}, Path("llvm-as"), tmp_path / "verify")
    assert json.loads((tmp_path / "verify.json").read_text())["verify_returncode"] == 1


def test_all_backend_outputs_retained_even_when_source_api_uses_last_line(
    protocol_request: Path, tmp_path: Path
) -> None:
    request = json.loads(protocol_request.read_text())
    request["environment"]["PROTOCOL_MULTI_ROOT"] = "1"
    protocol_request.write_text(json.dumps(request))
    attempt = tmp_path / "attempt"
    assert misaal.run_frontend(protocol_request, attempt) == 0
    record = json.loads((attempt / "capture.json").read_text())
    assert len(record["invocations"]) == 2
    for call in record["invocations"]:
        assert call["selected"] == "(Seed)"
        assert call["root_count"] == 2
        assert Path(call["replay"]).read_text().count("(check (= $srcexpr (Seed)))") == 2


@pytest.mark.parametrize("source_timeout", [None, 3600, 3600.5])
def test_public_capture_requires_guard_and_preserves_resource_stop(
    protocol_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, source_timeout: int | float | None
) -> None:
    from benchmarking.pilot import PilotProcessResult

    request = json.loads(protocol_request.read_text())
    if source_timeout is not None:
        request["source_timeout_sec"] = source_timeout
        protocol_request.write_text(json.dumps(request))
    original_request = protocol_request.read_bytes()
    calls: list[dict[str, Any]] = []

    def stopped(command: list[str], cwd: Path, output: Path, **kwargs: Any) -> PilotProcessResult:
        calls.append(kwargs)
        return PilotProcessResult("resource-stopped", None, 0, 0, output, output, "test guard stop")

    monkeypatch.setattr("benchmarking.pilot.run_bounded_command", stopped)
    result = misaal.capture_misaal(protocol_request, tmp_path / "capture")
    assert calls == [
        {
            "timeout_sec": source_timeout if source_timeout is not None else 900,
            "memory_limit_bytes": 5 * 1024**3,
            "require_guard": True,
            "disk_reserve_bytes": 10 * 1024**3,
            "allow_warning_pressure": True,
        }
    ]
    assert result["source_timeout_sec"] == (source_timeout if source_timeout is not None else 900)
    assert protocol_request.read_bytes() == original_request
    assert result["status"] == "resource-stopped"
    assert result["source_capture_complete"] is False
    assert result["workloads"] == []


@pytest.mark.parametrize(
    "value", [True, False, None, "3600", 0, -1, float("nan"), float("inf"), -float("inf"), 10**400]
)
def test_request_rejects_invalid_source_timeout(protocol_request: Path, value: Any) -> None:
    request = json.loads(protocol_request.read_text())
    request["source_timeout_sec"] = value
    protocol_request.write_text(json.dumps(request))
    with pytest.raises(ValueError, match="source_timeout_sec must be a finite positive number"):
        misaal.verified_request(protocol_request)


def test_source_timeout_changes_only_selected_request_identity(
    protocol_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts import suite_reproduction as reproduction

    request = json.loads(protocol_request.read_text())
    request.update(source="generator.cpp", configuration={})
    source = Path(request["checkout"]) / request["source"]
    source.write_text("pinned source generator")
    request["source_hashes"][request["source"]] = hashlib.sha256(source.read_bytes()).hexdigest()
    requests = tmp_path / "requests"
    requests.mkdir()
    selected = requests / f"{request['case_id']}.json"
    selected.write_text(json.dumps(request))
    other = requests / "other.json"
    other.write_text("unrelated request")
    performance_cache = tmp_path / ".reports.jsonl"
    performance_cache.write_text("unchanged timed observations\n")
    monkeypatch.setattr(reproduction, "ROOT", tmp_path)
    case = {"id": request["case_id"], "family": "misaal", "source": request["source"], "configuration": {}}
    settings = {"paths": {"requests": str(requests)}}
    original = reproduction.case_identity(case, settings)
    request["source_timeout_sec"] = 3600
    selected.write_text(json.dumps(request))
    extended = reproduction.case_identity(case, settings)
    assert original != extended
    assert [key for key in extended["inputs"] if original["inputs"][key] != extended["inputs"][key]] == [str(selected)]
    other.write_text("changed unrelated request")
    assert reproduction.case_identity(case, settings) == extended
    assert performance_cache.read_text() == "unchanged timed observations\n"


@pytest.fixture
def complete_packaging_failure(
    protocol_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> Iterator[Path]:
    """Seal a tiny completed fake-tool protocol run whose packaging alone fails."""
    attempt = tmp_path / "old-attempt"
    capture = attempt / "capture"
    capture.mkdir(parents=True)
    (capture / "request.json").write_bytes(protocol_request.read_bytes())

    def failed_packaging(*args: Any) -> None:
        raise ValueError("fixture packaging import failure after native completion")

    with monkeypatch.context() as patch:
        patch.setattr(misaal, "materialize_invocations", failed_packaging)
        assert misaal.run_frontend(protocol_request, capture / "generation") == 1
    record = json.loads((capture / "generation/capture.json").read_text())
    process = {"status": "failure", "returncode": 1, "message": "packaging failed"}
    record["process"] = process
    misaal.save_receipt(capture / "capture.json", record)
    misaal.save_receipt(capture / "process.json", process)
    misaal.save_receipt(attempt / "capture-result.json", record)
    archived = tmp_path / "native-implementation.py"
    archived.write_bytes(Path(misaal.__file__).read_bytes())
    stage = {
        "status": "failure",
        "capture": str(attempt / "capture-result.json"),
        "identity": {
            "inputs": {
                str(misaal.ROOT / "scripts/misaal_reproduction.py"): hashlib.sha256(archived.read_bytes()).hexdigest()
            }
        },
        "artifacts": {
            str(path): "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()
            for path in attempt.rglob("*")
            if path.is_file()
        },
    }
    misaal.save_receipt(attempt / "stage.json", stage)
    yield attempt / "stage.json"
    prefix = Path(record["output_name_adaptation"]["feedback_prefix"])
    for path in prefix.parent.glob(prefix.name + ".*"):
        path.unlink()


def test_recover_completed_capture_without_native_execution(
    complete_packaging_failure: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    original = {path: path.read_bytes() for path in complete_packaging_failure.parent.rglob("*") if path.is_file()}
    monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: pytest.fail("recovery must not execute tools"))
    output = tmp_path / "recovered"
    record = misaal.materialize_complete_capture(
        complete_packaging_failure, output, native_implementation=tmp_path / "native-implementation.py"
    )
    assert record["status"] == "ordinary-validation-pending", record.get("reason")
    assert record["source_completion"]["status"] == "success"
    assert record["materialization"] == {"complete": True, "expected_sessions": 2, "materialized_sessions": 2}
    assert len(record["workloads"]) == 2 and "process" not in record
    assert record["recovery"]["historical_process"]["status"] == "failure"
    assert record["recovery"]["native_execution_repeated"] is False
    assert record["recovery"]["old_implementation_hashes"]
    assert len(record["recovery"]["materializer_hashes"]) == 3
    for replay in record["workloads"]:
        assert Path(replay).is_relative_to(output)
        assert "(extract $srcexpr)\n(check (= $srcexpr (Seed)))" in Path(replay).read_text()
    assert all(path.read_bytes() == content for path, content in original.items())
    with pytest.raises(ValueError, match="fresh output"):
        misaal.materialize_complete_capture(
            complete_packaging_failure, output, native_implementation=tmp_path / "native-implementation.py"
        )


@pytest.mark.parametrize(
    "change",
    [
        "output",
        "child",
        "raw",
        "stdout",
        "missing-invocation",
        "extra-invocation",
        "extra-child",
        "source",
        "executable",
    ],
)
def test_recovery_rejects_changed_or_partial_native_evidence(
    complete_packaging_failure: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, change: str
) -> None:
    capture = complete_packaging_failure.parent / "capture"
    generation = capture / "generation"
    child = generation / "children/child-0000"
    request = json.loads((capture / "request.json").read_text())
    if change == "missing-invocation":
        (child / "invocation-0001.egg").unlink()
    elif change == "extra-invocation":
        (child / "invocation-0002.egg").write_text("extra call")
    elif change == "extra-child":
        (generation / "children/child-0001").mkdir()
    else:
        path = {
            "output": generation / "generator.a",
            "child": child / "capture.json",
            "raw": child / "invocation-0000.egg",
            "stdout": child / "invocation-0000.stdout.log",
            "source": Path(request["checkout"]) / "lib/compiler/EggLogCompiler.py",
            "executable": Path(request["backend"]),
        }[change]
        path.write_bytes(path.read_bytes() + b"changed")
    monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: pytest.fail("recovery must not execute tools"))
    result = misaal.materialize_complete_capture(
        complete_packaging_failure, tmp_path / "rejected", native_implementation=tmp_path / "native-implementation.py"
    )
    assert result["status"] == "failure" and result["workloads"] == []
    assert not (tmp_path / "rejected/replays").exists()


@pytest.mark.parametrize("failure", ["parent", "child", "invocation", "llvm-feedback"])
def test_recovery_rejects_sealed_unsuccessful_native_boundary(
    complete_packaging_failure: Path, tmp_path: Path, failure: str
) -> None:
    attempt = complete_packaging_failure.parent
    capture = attempt / "capture"
    generation = capture / "generation"
    child = generation / "children/child-0000/capture.json"
    frontend = json.loads((generation / "capture.json").read_text())
    child_record = json.loads(child.read_text())
    if failure == "parent":
        frontend["generator_returncode"] = 19
        frontend["source_completion"]["parent_returncode"] = 19
    else:
        if failure == "child":
            child_record["status"] = "failure"
        elif failure == "invocation":
            child_record["invocations"][0]["status"] = "failure"
        else:
            child_record["legalizations"][0]["feedback_sha256"] = "wrong"
        misaal.save_receipt(child, child_record)
        frontend["children"][0]["sha256"] = hashlib.sha256(child.read_bytes()).hexdigest()
        frontend["source_completion"]["children"] = frontend["children"]
    misaal.save_receipt(generation / "capture.json", frontend)
    frontend["process"] = json.loads((capture / "process.json").read_text())
    misaal.save_receipt(capture / "capture.json", frontend)
    misaal.save_receipt(attempt / "capture-result.json", frontend)
    stage = json.loads(complete_packaging_failure.read_text())
    stage["artifacts"] = {
        path: "sha256:" + hashlib.sha256(Path(path).read_bytes()).hexdigest() for path in stage["artifacts"]
    }
    misaal.save_receipt(complete_packaging_failure, stage)
    result = misaal.materialize_complete_capture(
        complete_packaging_failure, tmp_path / "rejected", native_implementation=tmp_path / "native-implementation.py"
    )
    assert result["status"] == "failure" and result["workloads"] == []
    assert not (tmp_path / "rejected/replays").exists()


def test_archived_inline_packaging_matches_only_the_narrow_helper_extraction() -> None:
    current = Path(misaal.__file__).read_text()
    module = ast.parse(current)
    functions = {node.name: node for node in module.body if isinstance(node, ast.FunctionDef)}
    packaging = functions["materialize_invocations"]
    execution = next(node for node in functions["run_frontend"].body if isinstance(node, ast.Try))
    execution.body[-2:-1] = [
        *packaging.body[1:3],
        *ast.parse("replay_directory = attempt / 'replays'").body,
        *packaging.body[3:],
    ]
    module.body.remove(packaging)
    archived = ast.unparse(module)
    assert misaal.capture_implementation_contract(archived) == misaal.capture_implementation_contract(current)
    execution.body.insert(1, ast.parse("result.returncode = 0").body[0])
    assert misaal.capture_implementation_contract(ast.unparse(module)) != misaal.capture_implementation_contract(
        current
    )


def test_recovery_requires_the_sealed_archived_native_implementation(
    complete_packaging_failure: Path, tmp_path: Path
) -> None:
    archived = tmp_path / "native-implementation.py"
    archived.write_text(archived.read_text() + "\n# changed after capture\n")
    result = misaal.materialize_complete_capture(
        complete_packaging_failure, tmp_path / "rejected", native_implementation=archived
    )
    assert result["status"] == "failure" and "evidence changed" in result["reason"]
    assert result["workloads"] == []


@pytest.fixture
def helper_protocol(protocol_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple:
    request = json.loads(protocol_request.read_text())
    modules = []
    for name, relative in (
        ("compiler.EggLogCompiler", "lib/compiler/EggLogCompiler.py"),
        ("patterns.PatternUtils", "lib/patterns/PatternUtils.py"),
    ):
        path = Path(request["checkout"]) / relative
        module = ModuleType(name)
        module.__file__ = str(path)
        exec(compile(path.read_text(), str(path), "exec"), module.__dict__)
        modules.append(module)
    directory = tmp_path / "helpers"
    directory.mkdir()
    record: dict[str, Any] = {"invocations": []}
    commands = []

    def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess:
        commands.append(command)
        assert isinstance(command, list) and "shell" not in kwargs
        if command[0] == "rm":
            Path(command[1]).unlink()
            return subprocess.CompletedProcess(command, 0)
        assert command[0] == request["backend"]
        content = Path(command[1]).read_text()
        kwargs["stdout"].write(b"actual helper stdout\n")
        kwargs["stderr"].write(b"actual helper stderr\n")
        return subprocess.CompletedProcess(command, 9 if content == "rejected input" else 0)

    monkeypatch.setattr(subprocess, "run", run)
    return modules, request, directory, record, commands


def test_direct_helpers_keep_actual_boolean_rejections_and_preserve_deleted_inputs(
    helper_protocol: tuple, tmp_path: Path, capsys: pytest.CaptureFixture
) -> None:
    modules, request, directory, record, commands = helper_protocol
    # References imported before installation retain the observed module globals.
    helpers = [module.is_pattern_valid_egg for module in modules]
    with misaal.observe_pattern_helpers(modules, request, directory, record, threading.Lock()):
        for index, helper in enumerate(helpers):
            for accepted in (True, False):
                source = tmp_path / f"input-{index}-{accepted}.egg"
                source.write_text("accepted input" if accepted else "rejected input")
                assert helper(str(source)) is accepted
                assert source.exists() is (index == 0)
    assert len(commands) == 6  # Four backend calls and the two real source deletions.
    assert record["invocations"] == []
    calls = record["helper_invocations"]
    assert len(calls) == 4 and all(call["status"] == "success" for call in calls)
    assert [call["accepted"] for call in calls] == [True, False, True, False]
    assert [call["returncode"] for call in calls] == [0, 9, 0, 9]
    assert all(call["admitted_as_workload"] is False for call in calls)
    assert record["helper_observation"]["completed_calls"] == 4
    for call in calls:
        raw = Path(call["raw"])
        assert hashlib.sha256(raw.read_bytes()).hexdigest() == call["sha256"]
        assert raw.read_text() == ("accepted input" if call["accepted"] else "rejected input")
        for name in ("stdout", "stderr"):
            assert hashlib.sha256(raw.with_suffix(f".{name}.log").read_bytes()).hexdigest() == call[name + "_sha256"]
        assert json.loads(raw.with_suffix(".result.json").read_text()) == call
    assert all(module.sb is subprocess for module in modules)
    captured = capsys.readouterr()
    assert captured.out == "actual helper stdout\n" * 2
    assert captured.err == "actual helper stderr\n" * 2


@pytest.mark.parametrize("fault", ["shell", "deletion", "caller", "operation", "recursive"])
def test_swallowed_unexpected_helper_operation_cannot_complete(helper_protocol: tuple, fault: str) -> None:
    modules, request, directory, record, commands = helper_protocol
    with (
        pytest.raises(ValueError, match="swallowed"),
        misaal.observe_pattern_helpers(modules, request, directory, record, threading.Lock()),
    ):
        try:
            if fault == "shell":
                modules[1].is_pattern_valid_egg("input.egg;touch injected")
            elif fault == "deletion":
                modules[1].is_pattern_valid_egg("input.egg", backend="rm")
            elif fault == "caller":
                modules[1].sb.run("backend input.egg", shell=True)
            elif fault == "operation":
                modules[0].sb.Popen(["backend", "input.egg"], start_new_session=True)
            else:
                with misaal.observe_pattern_helpers(modules, request, directory, record, threading.Lock()):
                    pytest.fail("recursive observer must not install")
        except ValueError:
            pass
    assert commands == [] and record["helper_observation"]["status"] == "failure"
    assert all(module.sb is subprocess for module in modules)


def test_direct_helper_source_must_be_pinned(helper_protocol: tuple) -> None:
    modules, request, directory, record, commands = helper_protocol
    del request["source_hashes"]["lib/patterns/PatternUtils.py"]
    with (
        pytest.raises(ValueError, match="pin the observed pattern-helper source"),
        misaal.observe_pattern_helpers(modules, request, directory, record, threading.Lock()),
    ):
        pytest.fail("unpinned helper source must not run")
    assert commands == [] and all(module.sb is subprocess for module in modules)


def test_helpers_are_accounted_without_becoming_optimizer_workloads(protocol_request: Path, tmp_path: Path) -> None:
    request = json.loads(protocol_request.read_text())
    request["environment"]["PROTOCOL_HELPERS"] = "1"
    protocol_request.write_text(json.dumps(request))
    attempt = tmp_path / "attempt"
    assert misaal.run_frontend(protocol_request, attempt) == 0
    record = json.loads((attempt / "capture.json").read_text())
    assert record["helper_accounting"] == {
        "status": "success",
        "calls": 4,
        "accepted": 2,
        "rejected": 2,
        "admitted_workloads": 0,
    }
    assert record["source_capture_complete"] is True
    assert record["materialization"] == {"complete": True, "expected_sessions": 2, "materialized_sessions": 2}
    assert len(record["workloads"]) == len(record["invocations"]) == 2
    assert all("helper-" not in path for path in record["workloads"])
    child = json.loads(Path(record["children"][0]["path"]).read_text())
    assert len(child["helper_invocations"]) == 4
    assert child["helper_observation"]["status"] == "success"


@pytest.mark.parametrize(
    ("body", "failure"),
    [
        ("ret <32 x i16> undef", "undefined_return_functions"),
        ("ret <32 x i16> poison", "undefined_return_functions"),
        (
            "%result = call <32 x i16> @llvm.hydride.unlowered()\n ret <32 x i16> %result",
            "unlowered_hydride_call_functions",
        ),
    ],
)
def test_failed_simd_lowering_cannot_be_returned_to_parent(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, body: str, failure: str
) -> None:
    llvm = tmp_path / "undefined.ll"
    llvm.write_text(f"define <32 x i16> @required() {{\nentry:\n  {body}\n}}\n")
    monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: pytest.fail("invalid feedback must not advance"))
    with pytest.raises(ValueError, match="SIMD lowering audit failed"):
        misaal.validate_llvm(llvm, {"required"}, Path("llvm-as"), tmp_path / "verify")
    receipt = json.loads((tmp_path / "verify.json").read_text())
    assert receipt["lowering_audit"][failure] == ["required"]
    assert receipt["lowering_audit"]["status"] == "failure" and receipt["verify_returncode"] is None


def test_defined_llvm_result_and_unrelated_runtime_undef_are_not_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    llvm = tmp_path / "defined.ll"
    llvm.write_text(
        "define i32 @required() {\n %undef = add i32 1, 2\n ret i32 %undef\n}\n"
        "define i32 @unrelated() { ret i32 undef }\n"
    )
    commands = []

    def verify(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess:
        commands.append(command)
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(subprocess, "run", verify)
    record = misaal.validate_llvm(llvm, {"required"}, Path("llvm-as"), tmp_path / "verify")
    assert len(commands) == 1 and record["lowering_audit"]["status"] == "success"
    assert record["verify_returncode"] == 0


def test_helper_interruption_retains_partial_streams_without_deleting_source(
    helper_protocol: tuple, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    modules, request, directory, record, _ = helper_protocol
    source = tmp_path / "interrupted.egg"
    source.write_text("real helper input")

    def interrupted(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess:
        kwargs["stdout"].write(b"partial stdout")
        kwargs["stderr"].write(b"partial stderr")
        raise subprocess.TimeoutExpired(command, 120)

    monkeypatch.setattr(subprocess, "run", interrupted)
    with (
        pytest.raises(subprocess.TimeoutExpired),
        misaal.observe_pattern_helpers(modules, request, directory, record, threading.Lock()),
    ):
        modules[1].is_pattern_valid_egg(str(source))
    assert source.read_text() == "real helper input"
    [call] = record["helper_invocations"]
    assert call["status"] == record["helper_observation"]["status"] == "failure"
    raw = Path(call["raw"])
    assert raw.read_bytes() == source.read_bytes()
    for name in ("stdout", "stderr"):
        assert hashlib.sha256(raw.with_suffix(f".{name}.log").read_bytes()).hexdigest() == call[name + "_sha256"]
    assert json.loads(raw.with_suffix(".result.json").read_text()) == call


@pytest.fixture
def hvx_request(protocol_request: Path) -> Path:
    request = json.loads(protocol_request.read_text())
    checkout = Path(request["checkout"])
    legalizer = checkout / "legalizer.so"
    request.update(
        configuration={"target": "hexagon"},
        hydride_revision="b" * 40,
        legalizer=str(legalizer),
        legalizer_sha256=hashlib.sha256(legalizer.read_bytes()).hexdigest(),
    )
    request["environment"]["HYDRIDE_TARGET"] = "hvx"
    preparation = protocol_request.parent / "selector-preparation.json"
    preparation.write_text(
        json.dumps(
            {
                "status": "success",
                "target": "hvx",
                "revision": request["revision"],
                "hydride_revision": request["hydride_revision"],
                "legalizer_path": str(legalizer),
                "legalizer_sha256": request["legalizer_sha256"],
            }
        )
    )
    request["hvx_link_contract"] = {
        "mode": "intrinsics-only",
        "omitted_wrapper": str(checkout / "Hydride/codegen-generator/tools/low-level-codegen/wrappers/hvx_wrappers.ll"),
        "selector_preparation": str(preparation),
        "selector_preparation_sha256": hashlib.sha256(preparation.read_bytes()).hexdigest(),
    }
    protocol_request.write_text(json.dumps(request))
    return protocol_request


def test_hvx_wrapper_omission_requires_verified_selector(hvx_request: Path) -> None:
    request = misaal.verified_request(hvx_request)
    assert request["hvx_link_contract"]["mode"] == "intrinsics-only"
    Path(request["legalizer"]).write_text("changed selector")
    with pytest.raises(ValueError, match="legalizer identity changed"):
        misaal.verified_request(hvx_request)


@pytest.mark.parametrize("mutation", ["target", "wrapper", "existing-wrapper", "preparation-hash", "failed-build"])
def test_hvx_link_contract_rejects_unverified_omission(hvx_request: Path, mutation: str) -> None:
    request = json.loads(hvx_request.read_text())
    contract = request["hvx_link_contract"]
    if mutation == "target":
        request["configuration"]["target"] = "x86"
    elif mutation == "wrapper":
        contract["omitted_wrapper"] += ".different"
    elif mutation == "existing-wrapper":
        path = Path(contract["omitted_wrapper"])
        path.parent.mkdir()
        path.write_text("real wrapper must not be discarded")
    elif mutation == "preparation-hash":
        contract["selector_preparation_sha256"] = "wrong"
    else:
        path = Path(contract["selector_preparation"])
        record = json.loads(path.read_text())
        record["status"] = "failure"
        path.write_text(json.dumps(record))
        contract["selector_preparation_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
    hvx_request.write_text(json.dumps(request))
    with pytest.raises(ValueError, match="HVX"):
        misaal.verified_request(hvx_request)


@pytest.mark.parametrize("extra_argument", [False, True])
def test_intrinsic_only_link_preserves_real_tool_and_original_argv(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, extra_argument: bool
) -> None:
    tool = tmp_path / "llvm-link"
    tool.write_text(
        f"#!{sys.executable}\nimport sys\nfrom pathlib import Path\n"
        "Path(sys.argv[-1]).write_bytes(Path(sys.argv[1]).read_bytes())\n"
    )
    tool.chmod(0o755)
    monkeypatch.setenv("PATH", str(tmp_path) + os.pathsep + os.environ["PATH"])
    source = tmp_path / "codegen.py"
    prefix = tmp_path / "module"
    Path(str(prefix) + ".ll").write_text("the actual input module")
    missing = tmp_path / "hvx_wrappers.ll"
    argv = ["llvm-link", str(prefix) + ".ll", str(missing), "-o", str(prefix) + ".linked.bc"]
    if extra_argument:
        argv.insert(3, "unexpected.ll")
    source.write_text("import os\nos.system(" + repr(" ".join(argv)) + ")\n")
    result = misaal.run_low_level(
        source, ["rosette", "selector", str(missing), "-hvx", str(prefix)], tmp_path, omitted_wrapper=missing
    )
    assert result == int(extra_argument)
    if extra_argument:
        assert not Path(str(prefix) + ".linked.bc").exists()
        assert "Unexpected LLVM link command" in (tmp_path / "failure.txt").read_text()
    else:
        assert Path(str(prefix) + ".linked.bc").read_text() == "the actual input module"
        assert not missing.exists()
        tool_record = json.loads((tmp_path / "tools.json").read_text())[0]
        assert tool_record["source_command"] == argv
        assert tool_record["command"] == [value for value in argv if value != str(missing)]
        assert tool_record["returncode"] == 0


@pytest.mark.parametrize("scenario", ["missing-link", "duplicate-link", "failed-link"])
def test_intrinsic_only_link_cannot_hide_missing_duplicate_or_failed_tools(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, scenario: str
) -> None:
    prefix, missing = tmp_path / "module", tmp_path / "hvx_wrappers.ll"
    command = f"llvm-link {prefix}.ll {missing} -o {prefix}.linked.bc"
    commands = [command, command] if scenario == "duplicate-link" else [command]
    if scenario == "missing-link":
        commands = [f"llvm-as {prefix}.ll -o {prefix}.bc"]
    source = tmp_path / "codegen.py"
    source.write_text("import os\n" + "\n".join(f"os.system({cmd!r})" for cmd in commands))
    monkeypatch.setattr(misaal.shutil, "which", lambda name: sys.executable)
    launches = []

    def run(argv: list[str], **kwargs: Any) -> subprocess.CompletedProcess:
        launches.append(argv)
        return subprocess.CompletedProcess(argv, 7 if scenario == "failed-link" else 0)

    monkeypatch.setattr(misaal.subprocess, "run", run)
    assert (
        misaal.run_low_level(
            source, ["rosette", "selector", str(missing), "-hvx", str(prefix)], tmp_path, omitted_wrapper=missing
        )
        == 1
    )
    assert len(launches) == 1
    receipt = json.loads((tmp_path / "tools.json").read_text())
    if scenario == "failed-link":
        assert receipt[0]["status"] == "failure" and receipt[0]["returncode"] == 7
    else:
        assert receipt[0]["status"] == "success"
    assert (tmp_path / "failure.txt").is_file()
