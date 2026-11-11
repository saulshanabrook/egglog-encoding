"""Exercise live capture handoffs with tiny fake tools, never native validation."""

from __future__ import annotations

import ast
import hashlib
import json
import os
import subprocess
import sys
from collections.abc import Iterator
from pathlib import Path
from typing import Any

import pytest

from scripts import misaal_reproduction as misaal


@pytest.fixture
def protocol_request(tmp_path: Path) -> Iterator[Path]:
    checkout = tmp_path / "source"
    compiler = checkout / "lib/compiler"
    compiler.mkdir(parents=True)
    (checkout / "lib/patterns").mkdir()
    (compiler / "EggLogCompiler.py").write_text("class EggLogCompiler: pass\n")
    (compiler / "HydrideCompiler.py").write_text(
        "from compiler.EggLogCompiler import EggLogCompiler\nclass HydrideCompiler(EggLogCompiler): pass\n"
    )
    legalizer = checkout / "Hydride/codegen-generator/tools/low-level-codegen/RoseLowLevelCodeGen.py"
    legalizer.parent.mkdir(parents=True)
    legalizer.write_text(
        "import os, shlex, sys\nfrom pathlib import Path\n"
        "prefix = sys.argv[5]\n"
        "Path(prefix + '.ll').write_text('define i32 @hydride_expr_0() { ret i32 0 }\\n')\n"
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
            "if os.environ.get('PROTOCOL_MULTI_ROOT'): print('(Seed)')\n"
            "sys.exit(7 if os.environ.get('PROTOCOL_BACKEND_FAILURE') else 0)\n"
        ),
        "llvm_as": "# Intentionally fake syntax validator: protocol evidence only.\n",
        "llvm_tool": (
            "import os, sys\nfrom pathlib import Path\n"
            "if os.environ.get('PROTOCOL_LLVM_FAILURE'): sys.exit(42)\n"
            "name = 'wrong_function' if os.environ.get('PROTOCOL_BAD_FUNCTION') else 'hydride_expr_0'\n"
            "Path(sys.argv[1]).write_text('define i32 @' + name + '() { ret i32 0 }\\n')\n"
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
            for path in compiler.glob("*.py")
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


@pytest.mark.parametrize("failure", ("LLVM_FAILURE", "BAD_FUNCTION", "PARENT_FAILURE", "BACKEND_FAILURE"))
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
    llvm.write_text("define i32 @requested() { malformed }\n")
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


def test_public_capture_requires_guard_and_preserves_resource_stop(
    protocol_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking.pilot import PilotProcessResult

    calls: list[dict[str, Any]] = []

    def stopped(command: list[str], cwd: Path, output: Path, **kwargs: Any) -> PilotProcessResult:
        calls.append(kwargs)
        return PilotProcessResult("resource-stopped", None, 0, 0, output, output, "test guard stop")

    monkeypatch.setattr("benchmarking.pilot.run_bounded_command", stopped)
    result = misaal.capture_misaal(protocol_request, tmp_path / "capture")
    assert calls == [
        {
            "timeout_sec": 900,
            "memory_limit_bytes": 5 * 1024**3,
            "require_guard": True,
            "disk_reserve_bytes": 10 * 1024**3,
            "allow_warning_pressure": True,
        }
    ]
    assert result["status"] == "resource-stopped"
    assert result["source_capture_complete"] is False
    assert result["workloads"] == []


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
