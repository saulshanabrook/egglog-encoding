"""Exercise live capture handoffs with tiny fake tools, never native validation."""

from __future__ import annotations

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
        }
    ]
    assert result["status"] == "resource-stopped"
    assert result["source_capture_complete"] is False
    assert result["workloads"] == []
