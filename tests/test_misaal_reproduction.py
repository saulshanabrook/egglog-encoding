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
from typing import Any, Literal

import pytest

from scripts import misaal_reproduction as misaal


@pytest.fixture
def tail_request(protocol_request: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    request = json.loads(protocol_request.read_text())
    request["revision"] = "44ff893445d664cd87f52b08a138260ed2015ba8"
    request["configuration"] = {"target": "x86"}
    request["generator_command"] = [
        request["generator"],
        "-o",
        "{output}",
        "-e",
        "static_library,stmt,h,llvm_assembly,assembly",
        "-f",
        "generator",
        "target=host-x86-64-no_bounds_query-no_asserts",
    ]
    request["expected_generator_outputs"] = [f"generator.{suffix}" for suffix in ("a", "stmt", "h", "ll", "s")]
    pins = {}
    for relative in misaal.ACQUISITION_TAIL_SOURCES:
        source = Path(request["checkout"]) / relative
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text("pinned terminal code fixture")
        pins[relative] = hashlib.sha256(source.read_bytes()).hexdigest()
    monkeypatch.setattr(misaal, "ACQUISITION_TAIL_SOURCES", pins)
    protocol_request.write_text(json.dumps(request))
    return protocol_request


def test_tail_derivation_is_immutable_and_retains_all_other_fields(tail_request: Path) -> None:
    original = tail_request.read_bytes()
    before = misaal.verified_request(tail_request)
    after = misaal.acquisition_tail_request(before)
    assert tail_request.read_bytes() == original
    assert before == json.loads(original)
    assert set(key for key in after if before.get(key) != after[key]) == {
        "acquisition_tail",
        "environment",
        "source_hashes",
        "generator_command",
        "expected_generator_outputs",
    }
    assert after["generator_command"] == [
        before["generator"],
        "-o",
        "{output}",
        "-e",
        "stmt,h,llvm_assembly",
        "-f",
        "generator",
        "target=host-x86-64-no_bounds_query-no_asserts",
    ]
    assert after["expected_generator_outputs"] == ["generator.stmt", "generator.h", "generator.ll"]
    assert after["environment"] == {**before["environment"], "HYDRIDE_DISABLE_LLVM_OPTS": "1"}
    assert after["source_hashes"] == {**before["source_hashes"], **misaal.ACQUISITION_TAIL_SOURCES}
    tail_request.write_text(json.dumps(after))
    assert misaal.verified_request(tail_request) == after
    assert misaal.acquisition_tail_request(after) == after


def test_archived_native_contract_binds_tail_helper_without_changing_packaging() -> None:
    source = Path(misaal.__file__).read_text()
    original = misaal.capture_implementation_contract(source)
    changed = source.replace('command[emission] = "stmt,h,llvm_assembly"', 'command[emission] = "llvm_assembly"')
    assert changed != source
    candidate = misaal.capture_implementation_contract(changed)
    assert original[0] != candidate[0] and original[1] == candidate[1]
    helper = next(
        node
        for node in ast.parse(source).body
        if isinstance(node, ast.FunctionDef) and node.name == "acquisition_tail_request"
    )
    lines = source.splitlines(keepends=True)
    del lines[helper.lineno - 1 : helper.end_lineno]
    legacy = misaal.capture_implementation_contract("".join(lines))
    assert legacy[0] != original[0] and legacy[1] == original[1]


@pytest.mark.parametrize(
    "failure",
    [
        "null-contract",
        "unknown-contract",
        "revision",
        "missing-contract",
        "missing-pin",
        "conflicting-pin",
        "changed-source",
        "duplicate-e",
        "duplicate-f",
        "missing-e",
        "multi-target",
        "target",
        "emission",
        "extra-output",
        "missing-output",
        "output-path",
        "environment",
        "null-env",
        "integer-env",
        "empty-env",
    ],
)
def test_tail_policy_rejects_ambiguous_or_unpinned_requests(tail_request: Path, failure: str) -> None:
    request = misaal.acquisition_tail_request(misaal.verified_request(tail_request))
    relative = next(iter(misaal.ACQUISITION_TAIL_SOURCES))
    if failure.endswith("contract"):
        if failure == "missing-contract":
            del request["acquisition_tail"]
        else:
            request["acquisition_tail"] = None if failure == "null-contract" else "unknown"
    elif failure == "revision":
        request["revision"] = "b" * 40
    elif failure == "missing-pin":
        del request["source_hashes"][relative]
    elif failure == "conflicting-pin":
        request["source_hashes"][relative] = "0" * 64
    elif failure == "changed-source":
        (Path(request["checkout"]) / relative).write_text("changed terminal code")
    elif failure in ("duplicate-e", "duplicate-f"):
        request["generator_command"].extend(["-" + failure[-1], "other"])
    elif failure == "missing-e":
        request["generator_command"].remove("-e")
    elif failure in ("multi-target", "target"):
        request["generator_command"][-1] += ",arm-64-osx" if failure == "multi-target" else "-no_runtime"
    elif failure == "emission":
        request["generator_command"][4] = "stmt,h"
    elif failure == "extra-output":
        request["expected_generator_outputs"].append("generator.a")
    elif failure == "missing-output":
        request["expected_generator_outputs"].pop()
    elif failure == "output-path":
        request["generator_command"][6] = "../escape"
    elif failure == "environment":
        del request["environment"]["HYDRIDE_DISABLE_LLVM_OPTS"]
    else:
        request["environment"]["HYDRIDE_DISABLE_LLVM_OPTS"] = {"null-env": None, "integer-env": 1, "empty-env": ""}[
            failure
        ]
    tail_request.write_text(json.dumps(request))
    with pytest.raises(ValueError, match="[Aa]cquisition-tail"):
        misaal.verified_request(tail_request)


@pytest.mark.parametrize(
    "failure",
    [None, "PROTOCOL_LLVM_FAILURE", "PROTOCOL_UNDEFINED_RESULT", "PROTOCOL_BAD_FUNCTION", "PROTOCOL_PARENT_FAILURE"],
)
def test_tail_keeps_complete_feedback_and_native_failures(
    tail_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, failure: str | None
) -> None:
    # Carry only the fake source-pin fixture into the real protocol child and
    # low-level hook. Native behavior is still the unmodified adapter code.
    wrapper = tmp_path / "protocol_adapter.py"
    wrapper.write_text(
        f"import sys\nsys.path.insert(0, {str(Path(misaal.__file__).resolve().parents[1])!r})\n"
        "from scripts import misaal_reproduction as adapter\n"
        f"adapter.ACQUISITION_TAIL_SOURCES = {misaal.ACQUISITION_TAIL_SOURCES!r}\n"
        "adapter.__file__ = __file__\nraise SystemExit(adapter.main())\n"
    )
    monkeypatch.setattr(misaal, "__file__", str(wrapper))
    request = misaal.acquisition_tail_request(misaal.verified_request(tail_request))
    if failure:
        request["environment"][failure] = "1"
    tail_request.write_text(json.dumps(request))
    attempt = tmp_path / "tail-attempt"
    assert misaal.run_frontend(tail_request, attempt) == (1 if failure else 0)
    record = json.loads((attempt / "capture.json").read_text())
    assert record["acquisition_tail"] == misaal.ACQUISITION_TAIL
    assert record["source_capture_complete"] is (failure is None)
    if failure:
        assert record["workloads"] == []
    else:
        assert len(record["invocations"]) == 2  # Duplicate calls must both survive.
        assert record["source_completion"]["parent_returncode"] == 0
        assert len(record["native_outputs"]) == 3
        assert (attempt / "parent-consumed-feedback.txt").read_bytes() == (attempt / "generator.ll").read_bytes()
        assert not (attempt / "generator.a").exists()


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
            "output = Path(sys.argv[sys.argv.index('-o') + 1] if '-o' in sys.argv else sys.argv[1])\n"
            "(output / 'generator.ll').write_text(feedback)\n"
            "if 'HYDRIDE_DISABLE_LLVM_OPTS' in os.environ:\n"
            "    assert os.environ['HYDRIDE_DISABLE_LLVM_OPTS'] == '1'\n"
            "    assert sys.argv[sys.argv.index('-e') + 1] == 'stmt,h,llvm_assembly'\n"
            "    for suffix in ('stmt', 'h'): (output / ('generator.' + suffix)).write_text('fake final output')\n"
            "else: (output / 'generator.a').write_text('fake final archive')\n"
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


def test_frontend_removes_inherited_runtime_overrides_before_applying_pins(
    protocol_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    request = json.loads(protocol_request.read_text())
    excluded = ["PLTCOLLECTS", "PLTCONFIGDIR", "PLTCOMPILEDROOTS", "PLT_ZO_PATH", "PLT_COMPILED_FILE_CHECK"]
    monkeypatch.setenv("PLT_COMPILE_ANY", "1")
    request["environment_unset"] = [*excluded, "PLTADDONDIR"]
    request["environment"]["PLTADDONDIR"] = "/recorded/isolated/addon"
    protocol_request.write_text(json.dumps(request))
    for key in request["environment_unset"]:
        monkeypatch.setenv(key, "/unrelated/ambient/override")
    observed = []

    def launch(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess:
        environment = kwargs["env"]
        assert not set(excluded).intersection(environment)
        assert environment["PLTADDONDIR"] == "/recorded/isolated/addon"
        assert "PLT_COMPILE_ANY" not in environment
        observed.append(command)
        return subprocess.CompletedProcess(command, 1)

    monkeypatch.setattr(misaal.subprocess, "run", launch)
    assert misaal.run_frontend(protocol_request, tmp_path / "attempt") == 1
    assert len(observed) == 1


@pytest.mark.parametrize("failure", ["unknown-contract", "missing-source-pin", "changed-source"])
def test_parameter_abi_request_rejects_unknown_or_changed_source_before_launch(
    protocol_request: Path, failure: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts import reproduction_misaal_patterns as patterns

    request = json.loads(protocol_request.read_text())
    source = Path(request["checkout"]) / "misaal/synthesis/param_abstract.rkt"
    source.parent.mkdir(parents=True)
    source.write_text("pinned fixture only; never executed")
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    relative = "misaal/synthesis/param_abstract.rkt"
    monkeypatch.setattr(patterns, "PARAMETER_ABI_SOURCE_SHA256", {relative: digest})
    request["source_hashes"][relative] = digest
    request["parameter_abi"] = patterns.PARAMETER_ABI_CONTRACT
    if failure == "unknown-contract":
        request["parameter_abi"] = "unreviewed"
    elif failure == "missing-source-pin":
        del request["source_hashes"][relative]
    else:
        source.write_text("changed fixture")
    protocol_request.write_text(json.dumps(request))
    with pytest.raises(ValueError, match="parameter ABI|source identity changed"):
        misaal.verified_request(protocol_request)


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
@pytest.mark.parametrize("source_memory", [None, 7 * 1024**3, 10 * 1024**3])
@pytest.mark.parametrize("process_status", ["success", "memory-limit", "resource-stopped"])
def test_public_capture_requires_guard_and_preserves_resource_stop(
    protocol_request: Path,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    source_timeout: int | float | None,
    source_memory: int | None,
    process_status: Literal["success", "memory-limit", "resource-stopped"],
) -> None:
    from benchmarking.pilot import PilotProcessResult
    from scripts import reproduction_misaal_groups as group_scope

    request = json.loads(protocol_request.read_text())
    source = Path(request["checkout"]) / group_scope.SOURCE
    source.parent.mkdir()
    source.write_text("protocol-only source; never imported")
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    monkeypatch.setattr(group_scope, "SOURCE_SHA256", digest)
    monkeypatch.setattr(group_scope, "process_snapshot", lambda: {})
    request["source_hashes"][group_scope.SOURCE] = digest
    request.update(
        racket_group_containment=group_scope.CONTRACT,
        racket=request["backend"],
        racket_sha256=request["backend_sha256"],
    )
    if source_timeout is not None:
        request["source_timeout_sec"] = source_timeout
    if source_memory is not None:
        request["source_memory_limit_bytes"] = source_memory
    protocol_request.write_text(json.dumps(request))
    original_request = protocol_request.read_bytes()
    calls: list[dict[str, Any]] = []
    runtime_checks: list[dict[str, Any]] = []
    monkeypatch.setattr(
        "scripts.reproduction_misaal_runtime.verify_runtime", lambda value: runtime_checks.append(value)
    )

    def stopped(command: list[str], cwd: Path, output: Path, **kwargs: Any) -> PilotProcessResult:
        assert "--group-endpoint" in command
        assert callable(kwargs.pop("sample_rss")) and callable(kwargs.pop("cleanup_descendants"))
        calls.append(kwargs)
        if process_status == "success":
            generation = output.parent / "generation"
            generation.mkdir()
            misaal.save_receipt(
                generation / "capture.json",
                {
                    "status": "ordinary-validation-pending",
                    "source_capture_complete": True,
                    "source_completion": {"status": "success"},
                    "workloads": ["mock-complete.egg"],
                },
            )
        return PilotProcessResult(
            process_status, 0 if process_status == "success" else -9, 1, 123, output, output, "mock process receipt"
        )

    monkeypatch.setattr("benchmarking.pilot.run_bounded_command", stopped)
    result = misaal.capture_misaal(protocol_request, tmp_path / "capture")
    assert calls == [
        {
            "timeout_sec": source_timeout if source_timeout is not None else 900,
            "memory_limit_bytes": source_memory if source_memory is not None else 5 * 1024**3,
            "require_guard": True,
            "disk_reserve_bytes": 10 * 1024**3,
            "allow_warning_pressure": True,
        }
    ]
    assert result["process_accounting"]["contract"] == group_scope.CONTRACT
    assert runtime_checks == [request, request]
    assert Path(result["process_accounting"]["receipt"]).is_file()
    assert result["source_timeout_sec"] == (source_timeout if source_timeout is not None else 900)
    assert result["source_memory_limit_bytes"] == (source_memory if source_memory is not None else 5 * 1024**3)
    assert json.loads((tmp_path / "capture/capture.json").read_text()) == json.loads(json.dumps(result, default=str))
    assert (tmp_path / "capture/request.json").read_text() == json.dumps(request, indent=2) + "\n"
    assert protocol_request.read_bytes() == original_request
    assert result["status"] == ("ordinary-validation-pending" if process_status == "success" else process_status)
    assert result["source_capture_complete"] is (process_status == "success")
    assert result["workloads"] == (["mock-complete.egg"] if process_status == "success" else [])


def test_public_complete_capture_rejects_uncontained_legacy_request_before_launch(
    protocol_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr("benchmarking.pilot.run_bounded_command", lambda *_a, **_k: pytest.fail("must not launch"))
    with pytest.raises(ValueError, match="prepared registered-group contract"):
        misaal.capture_misaal(protocol_request, tmp_path / "capture")
    assert not (tmp_path / "capture").exists()


@pytest.mark.parametrize("failure_at", [1, 2])
def test_public_capture_checks_runtime_before_launch_and_before_admission(
    protocol_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, failure_at: int
) -> None:
    from benchmarking.pilot import PilotProcessResult
    from scripts import reproduction_misaal_groups as group_scope

    request = json.loads(protocol_request.read_text())
    request["racket_group_containment"] = group_scope.CONTRACT
    monkeypatch.setattr(misaal, "verified_request", lambda _: request)
    monkeypatch.setattr(group_scope, "process_snapshot", lambda: {})
    checks = 0
    launched = False

    def runtime(_request: dict[str, Any]) -> None:
        nonlocal checks
        checks += 1
        if checks == failure_at:
            raise ValueError("changed compiled Racket package")

    def native(_command: list[str], _cwd: Path, output: Path, **_kwargs: Any) -> PilotProcessResult:
        nonlocal launched
        launched = True
        generation = output.parent / "generation"
        generation.mkdir()
        misaal.save_receipt(
            generation / "capture.json",
            {
                "status": "reproduced",
                "source_capture_complete": True,
                "source_completion": {"status": "success"},
                "workloads": ["unaccepted.egg"],
            },
        )
        return PilotProcessResult("success", 0, 1, 0, output, output, None)

    monkeypatch.setattr("scripts.reproduction_misaal_runtime.verify_runtime", runtime)
    monkeypatch.setattr("benchmarking.pilot.run_bounded_command", native)
    output = tmp_path / "capture"
    if failure_at == 1:
        with pytest.raises(ValueError, match="changed compiled Racket package"):
            misaal.capture_misaal(protocol_request, output)
        assert not launched and not output.exists()
    else:
        result = misaal.capture_misaal(protocol_request, output)
        assert launched and checks == 2
        assert result["status"] == "blocked" and result["workloads"] == []
        assert result["process"]["status"] == "success"
        assert "changed compiled Racket package" in result["reason"]
        assert json.loads((output / "capture.json").read_text()) == json.loads(json.dumps(result, default=str))


@pytest.mark.parametrize(
    "value", [True, False, None, "3600", 0, -1, float("nan"), float("inf"), -float("inf"), 10**400]
)
def test_request_rejects_invalid_source_timeout(protocol_request: Path, value: Any) -> None:
    request = json.loads(protocol_request.read_text())
    request["source_timeout_sec"] = value
    protocol_request.write_text(json.dumps(request))
    with pytest.raises(ValueError, match="source_timeout_sec must be a finite positive number"):
        misaal.verified_request(protocol_request)


@pytest.mark.parametrize("policy,value", [("source_timeout_sec", 3600), ("source_memory_limit_bytes", 7 * 1024**3)])
def test_source_policy_changes_only_selected_request_identity(
    protocol_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, policy: str, value: int
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
    # Test verified request hashing independently of the export-only dispatch
    # gate; these protocol fixtures do not launch a source compiler here.
    monkeypatch.setattr(
        reproduction,
        "misaal_request",
        lambda case, settings, root: misaal.verified_request(
            root / settings["paths"]["requests"] / f"{case['id']}.json"
        ),
    )
    case = {"id": request["case_id"], "family": "misaal", "source": request["source"], "configuration": {}}
    settings = {"paths": {"requests": str(requests)}}
    original = reproduction.case_identity(case, settings)
    request[policy] = value
    selected.write_text(json.dumps(request))
    extended = reproduction.case_identity(case, settings)
    assert original != extended
    assert [key for key in extended["inputs"] if original["inputs"][key] != extended["inputs"][key]] == [str(selected)]
    other.write_text("changed unrelated request")
    assert reproduction.case_identity(case, settings) == extended
    assert performance_cache.read_text() == "unchanged timed observations\n"


@pytest.mark.parametrize(
    "value",
    [True, False, None, "7516192768", 0, -1, 1.5, float(7 * 1024**3), float("nan"), float("inf"), 10 * 1024**3 + 1],
)
def test_source_memory_invalid_before_any_launch(
    protocol_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, value: Any
) -> None:
    request = json.loads(protocol_request.read_text())
    request["source_memory_limit_bytes"] = value
    protocol_request.write_text(json.dumps(request))
    original = protocol_request.read_bytes()
    monkeypatch.setattr("benchmarking.pilot.run_bounded_command", lambda *_a, **_k: pytest.fail("must not launch"))
    monkeypatch.setattr(
        "scripts.reproduction_misaal_runtime.verify_runtime", lambda *_a, **_k: pytest.fail("must reject policy first")
    )
    with pytest.raises(ValueError, match="source_memory_limit_bytes must be a positive integer <= 10737418240"):
        misaal.capture_misaal(protocol_request, tmp_path / "capture")
    assert not (tmp_path / "capture").exists()
    assert protocol_request.read_bytes() == original


def test_source_memory_policy_accepts_smallest_positive_integer(protocol_request: Path) -> None:
    request = json.loads(protocol_request.read_text())
    request["source_memory_limit_bytes"] = 1
    protocol_request.write_text(json.dumps(request))
    assert misaal.verified_request(protocol_request) == request


def test_misaal_adapter_policy_does_not_change_other_family_identities(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts import suite_reproduction as reproduction

    monkeypatch.setattr(reproduction, "ROOT", tmp_path)
    adapter = tmp_path / "scripts/misaal_reproduction.py"
    adapter.parent.mkdir()
    adapter.write_text("prior MISAAL policy")
    settings: dict[str, Any] = {"paths": {}}
    cases = [{"id": family, "family": family} for family in ("eggcc", "churchroad", "hardboiled", "dialegg", "speq")]
    before = [reproduction.case_identity(case, settings) for case in cases]
    adapter.write_text("new MISAAL source-memory policy")
    assert [reproduction.case_identity(case, settings) for case in cases] == before


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


def test_registered_group_helper_and_racket_are_capture_identities(
    protocol_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts import reproduction_misaal_groups as group_scope
    from scripts import suite_reproduction as reproduction

    request = json.loads(protocol_request.read_text())
    request.update(source="generator.cpp", configuration={})
    source = Path(request["checkout"]) / request["source"]
    source.write_text("pinned source generator")
    request["source_hashes"][request["source"]] = hashlib.sha256(source.read_bytes()).hexdigest()
    launcher = Path(request["checkout"]) / group_scope.SOURCE
    launcher.parent.mkdir()
    launcher.write_text("pinned mock launcher; never executed")
    digest = hashlib.sha256(launcher.read_bytes()).hexdigest()
    monkeypatch.setattr(group_scope, "SOURCE_SHA256", digest)
    request["source_hashes"][group_scope.SOURCE] = digest
    request.update(
        racket_group_containment=group_scope.CONTRACT,
        racket=request["backend"],
        racket_sha256=request["backend_sha256"],
    )
    requests = tmp_path / "requests"
    requests.mkdir()
    selected = requests / f"{request['case_id']}.json"
    selected.write_text(json.dumps(request))
    helper = tmp_path / "scripts/reproduction_misaal_groups.py"
    helper.parent.mkdir()
    helper.write_text("known group protocol version one")
    monkeypatch.setattr(reproduction, "ROOT", tmp_path)
    # Identity hashing remains testable with the archived native protocol;
    # production dispatch separately requires prepared Egglog export requests.
    monkeypatch.setattr(
        reproduction,
        "misaal_request",
        lambda case, settings, root: misaal.verified_request(
            root / settings["paths"]["requests"] / f"{case['id']}.json"
        ),
    )
    case = {"id": request["case_id"], "family": "misaal", "source": request["source"], "configuration": {}}
    settings = {"paths": {"requests": str(requests)}}
    initial = reproduction.case_identity(case, settings)
    assert initial["inputs"][request["racket"]] == "sha256:" + request["racket_sha256"]
    helper.write_text("changed group protocol")
    revised = reproduction.case_identity(case, settings)
    assert [path for path in initial["inputs"] if initial["inputs"][path] != revised["inputs"][path]] == [str(helper)]
    del request["racket"]
    selected.write_text(json.dumps(request))
    with pytest.raises(ValueError, match="pinned executable path and SHA-256"):
        misaal.verified_request(selected)


def test_runtime_seal_and_compiled_package_members_are_capture_identities(
    protocol_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts import suite_reproduction as reproduction

    request = json.loads(protocol_request.read_text())
    request.update(source="generator.cpp", configuration={})
    source = Path(request["checkout"]) / request["source"]
    source.write_text("pinned generator")
    request["source_hashes"][request["source"]] = hashlib.sha256(source.read_bytes()).hexdigest()
    tree = tmp_path / "addon"
    tree.mkdir()
    compiled = tree / "module_rkt.zo"
    compiled.write_bytes(b"compiled source")
    solver = tmp_path / "z3"
    solver.write_text("original solver")
    seal = tmp_path / "runtime.json"
    seal.write_text(
        json.dumps(
            {
                "schema": "misaal-racket-runtime-v1",
                "status": "source-api-compatible",
                "code_trees": {"addon": {"path": str(tree)}},
                "artifacts": {str(solver): hashlib.sha256(solver.read_bytes()).hexdigest()},
            }
        )
    )
    request["racket_runtime"] = {"path": str(seal), "sha256": hashlib.sha256(seal.read_bytes()).hexdigest()}
    requests = tmp_path / "requests"
    requests.mkdir()
    selected = requests / f"{request['case_id']}.json"
    selected.write_text(json.dumps(request))
    monkeypatch.setattr(reproduction, "ROOT", tmp_path)
    # Keep runtime identity coverage independent of the export preparation gate.
    monkeypatch.setattr(
        reproduction,
        "misaal_request",
        lambda case, settings, root: misaal.verified_request(
            root / settings["paths"]["requests"] / f"{case['id']}.json"
        ),
    )
    case = {"id": request["case_id"], "family": "misaal", "source": request["source"], "configuration": {}}
    settings = {"paths": {"requests": str(requests)}}
    initial = reproduction.case_identity(case, settings)
    assert str(seal) in initial["inputs"] and str(tree) in initial["inputs"]
    compiled.write_bytes(b"changed compiled source")
    changed = reproduction.case_identity(case, settings)
    assert initial["inputs"][str(tree)] != changed["inputs"][str(tree)]
    (tree / "links.rktd").write_text("new package link")
    added = reproduction.case_identity(case, settings)
    assert changed["inputs"][str(tree)] != added["inputs"][str(tree)]
    external = tmp_path / "external-package"
    external.mkdir()
    dependency = external / "dependency.zo"
    dependency.write_text("original external package")
    (tree / "linked-package").symlink_to(external, target_is_directory=True)
    linked = reproduction.case_identity(case, settings)
    dependency.write_text("changed external package")
    relinked = reproduction.case_identity(case, settings)
    assert linked["inputs"][str(tree)] != relinked["inputs"][str(tree)]
    solver.write_text("changed solver")
    solver_changed = reproduction.case_identity(case, settings)
    assert relinked["inputs"][str(solver)] != solver_changed["inputs"][str(solver)]
    seal.write_text(seal.read_text() + " ")
    with pytest.raises(ValueError, match="runtime seal identity changed"):
        reproduction.case_identity(case, settings)


@pytest.mark.parametrize("failure", ["unknown", "missing", "changed", "revision"])
def test_literal_guard_request_fails_closed_before_launch(
    protocol_request: Path, monkeypatch: pytest.MonkeyPatch, failure: str
) -> None:
    from scripts import reproduction_misaal_patterns as patterns

    request = json.loads(protocol_request.read_text())
    relative = "targets/halide/axioms.egg"
    source = Path(request["checkout"]) / relative
    source.parent.mkdir(parents=True)
    source.write_text("pinned fixture; never executed")
    pins = {relative: hashlib.sha256(source.read_bytes()).hexdigest()}
    monkeypatch.setattr(patterns, "LITERAL_WIDTH_SOURCE_SHA256", pins)
    request.update(
        literal_width_guard=patterns.LITERAL_WIDTH_CONTRACT, revision="44ff893445d664cd87f52b08a138260ed2015ba8"
    )
    request["source_hashes"].update(pins)
    if failure == "unknown":
        request["literal_width_guard"] = "unknown"
    elif failure == "missing":
        del request["source_hashes"][relative]
    elif failure == "changed":
        source.write_text("changed fixture")
    else:
        request["revision"] = "0" * 40
    protocol_request.write_text(json.dumps(request))
    with pytest.raises(ValueError, match="literal-width guard|source identity changed"):
        misaal.verified_request(protocol_request)


@pytest.mark.parametrize("mutation", [None, "evidence", "unguarded-input", "omitted-axioms"])
def test_literal_guard_captures_actual_backend_input_and_labels_unexecuted_counterpart(
    protocol_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mutation: str | None
) -> None:
    """Exercise the live child hook with a fake backend, never LLVM or native Egglog."""
    from scripts import reproduction_misaal_patterns as patterns

    request = json.loads(protocol_request.read_text())
    checkout = Path(request["checkout"])
    source = checkout / "lib/compiler/EggLogCompiler.py"
    source.write_text(
        source.read_text().replace(
            "class EggLogCompiler: pass",
            "import os\nclass EggLogCompiler:\n"
            "    def __init__(self):\n"
            "        super().__init__()\n"
            "        self.axioms_file = os.path.join(os.environ['MISAAL_SRC'], 'targets/halide/axioms.egg')\n"
            "        self.egglog_bin = 'original/configured/backend'\n"
            "        self.skip_axioms = False\n",
        )
    )
    axioms = "\n".join(
        "(rewrite\n     (LIT val prec)\n"
        f"    (typed_cast-{kind}-extend (LIT val (/ prec 2)) (/ prec 2) 1 1 prec)\n"
        "    ;:when ((< val 255))\n)"
        for kind in ("int", "uint")
    )
    axiom_path = checkout / "targets/halide/axioms.egg"
    axiom_path.parent.mkdir(parents=True)
    axiom_path.write_text(axioms)
    pins = {
        str(path.relative_to(checkout)): hashlib.sha256(path.read_bytes()).hexdigest() for path in (source, axiom_path)
    }
    monkeypatch.setattr(patterns, "LITERAL_WIDTH_SOURCE_SHA256", pins)
    request.update(
        literal_width_guard=patterns.LITERAL_WIDTH_CONTRACT, revision="44ff893445d664cd87f52b08a138260ed2015ba8"
    )
    request["source_hashes"].update(pins)
    protocol_request.write_text(json.dumps(request))
    monkeypatch.setenv("MISAAL_SRC", str(checkout))
    monkeypatch.setattr(sys, "path", list(sys.path))
    for package in ("compiler", "patterns"):
        parent = ModuleType(package)
        parent.__path__ = []
        monkeypatch.setitem(sys.modules, package, parent)
    modules = {}
    for name, relative in (
        ("compiler.EggLogCompiler", "lib/compiler/EggLogCompiler.py"),
        ("compiler.HydrideCompiler", "lib/compiler/HydrideCompiler.py"),
        ("patterns.PatternUtils", "lib/patterns/PatternUtils.py"),
    ):
        path = checkout / relative
        module = ModuleType(name)
        module.__file__ = str(path)
        monkeypatch.setitem(sys.modules, name, module)
        exec(compile(path.read_text(), str(path), "exec", dont_inherit=True), vars(module))
        modules[name] = module
    original = modules["compiler.EggLogCompiler"].EggLogCompiler.__init__
    attempt = tmp_path / "attempt"
    attempt.mkdir()
    program = attempt / "fixture_misaal.py"
    program.write_text("# The source child is represented by execute_child below.\n")
    instances = []

    def execute_child(path: str, run_name: str) -> None:
        instance = modules["compiler.HydrideCompiler"].HydrideCompiler()
        instances.append(instance)
        content = Path(instance.axioms_file).read_text()
        if mutation == "evidence":
            Path(instance.axioms_file).write_text(content + "\nchanged")
        elif mutation == "unguarded-input":
            content = axioms
        elif mutation == "omitted-axioms":
            content = ""
        raw = attempt / "source-backend.egg"
        raw.write_text(content + "\n(let srcexpr (Seed))\n(run 5)\n(extract srcexpr)\n")
        for _ in range(2):
            assert instance.execute_egglog_file(str(raw)) == "(Seed)"

    launches = []

    def backend(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess:
        assert command[0] == request["backend"]
        launches.append(command)
        kwargs["stdout"].write(b"(Seed)\n")
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(misaal.runpy, "run_path", execute_child)
    monkeypatch.setattr(misaal.subprocess, "run", backend)
    # No fake LLVM completion is invented: this hook must remain incomplete.
    assert misaal.observe_python(protocol_request, attempt, [str(program)]) == 1
    record = json.loads((attempt / "children/child-0000/capture.json").read_text())
    assert record["source_capture_complete"] is False
    assert modules["compiler.EggLogCompiler"].EggLogCompiler.__init__ is original
    assert all(instance.axioms_file == str(axiom_path) for instance in instances)
    assert axiom_path.read_text() == axioms
    call = record["invocations"][0]
    actual = Path(call["raw"]).read_text()
    if mutation is not None:
        assert not launches and call["status"] == "failure"
        assert (
            "evidence changed" in call["error"]
            if mutation == "evidence"
            else "expected guarded axioms" in call["error"]
        )
        return
    assert len(launches) == 2 and all(item["status"] == "success" for item in record["invocations"])
    assert [Path(item["raw"]).name for item in record["invocations"]] == ["invocation-0000.egg", "invocation-0001.egg"]
    assert len(list(Path(call["raw"]).parent.glob("invocation-*.egg"))) == 2
    assert launches[0][1] == call["raw"]
    assert actual.count(":when ((> prec 1))") == 2
    assert hashlib.sha256(actual.encode()).hexdigest() == call["sha256"]
    counterpart = call["literal_width_guard"]["original_counterpart"]
    assert counterpart["executed"] is False and "reconstructed" in counterpart["provenance"]
    unexecuted = Path(counterpart["path"]).read_text()
    assert unexecuted == actual.replace("    :when ((> prec 1))\n", "")
    assert hashlib.sha256(unexecuted.encode()).hexdigest() == counterpart["sha256"]
    assert record["literal_width_guard"]["status"] == "complete"
    assert "did not complete native LLVM" in record["error"]


# The retained pinned44ff child-0001 emitter output, with only path literals parameterized.
ARM_EMPTY_PROGRAM = """from compiler.HydrideCompiler import HydrideCompiler
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

misaal_input_patterns = []
from patterns.ARM import arm_patterns as misaal_output_patterns
misaal_patterns = misaal_input_patterns + misaal_output_patterns
halide_dsl_list = parse_dict_with_bounded(halide_semantics)
misaal_input = halide_dsl_list
inst_dict = parse_dict_with_bounded(arm_semantics)
swizzle_dict = parse_dict_with_bounded(arm_swizzles)
misaal_output = inst_dict + swizzle_dict
so_path = "{legalizer}"
llvm_flags = ["-arm-hydride-legalize"]
intrin = "{hydride}/codegen-generator/tools/low-level-codegen/wrappers/arm_wrappers.c.ll"
HYDRIDE_ROOT = "{hydride}"
# Defining Tests\x20
tests = []
if len(tests) == 0:
	sys.exit(0)
# Defining MISAAL Rewrite compiler
misaal_compiler = HydrideCompiler(misaal_patterns, src_dsl_list = misaal_input, target_dsl_list = misaal_output,
    run_iterations = 5, egg_pkg_path = EGG_PKG_PATH, tests = tests, llvm_so_path = so_path, llvm_flags =  llvm_flags,
    intrinsics_file =  intrin, hydride_root_path =  HYDRIDE_ROOT, llvm_out_file_name = "{prefix}")
# Invoke compiler and print stats
misaal_compiler.compile_hydride()
misaal_compiler.run_llvm_legalizer()
misaal_compiler.print_stats()
"""


@pytest.fixture
def arm_terminal_request(protocol_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    request = json.loads(protocol_request.read_text())
    checkout = Path(request["checkout"])
    request.update(
        revision="44ff893445d664cd87f52b08a138260ed2015ba8",
        configuration={"target": "arm"},
        terminal_empty_child=misaal.ARM_TERMINAL_EMPTY,
        pattern_cache_contract={
            "environment": "MISAAL_PATTERN_CACHE_DIR",
            "required": "adapter supplies a fresh empty attempt-owned directory before child imports",
            "generation": "unchanged",
            "default": "source lib/patterns when variable is absent",
        },
        legalizer=str(checkout / "legalizer.so"),
        legalizer_sha256=hashlib.sha256((checkout / "legalizer.so").read_bytes()).hexdigest(),
    )
    request["environment"]["MISAAL_DISABLE_FRONTEND_PATTERNS"] = "1"
    modules = {
        "utils/egg_config.py": 'EGG_PKG_PATH = "original/configured/backend"\n',
        "utils/DSLInstructionUtils.py": "def parse_dict_with_bounded(value): return []\n",
    }
    for module, symbol in {
        "hexsemantics_new": "semantics",
        "x86SemanticsAllArgs": "semantcs",
        "halide_decomposed": "halide_decomposed",
        "hvx_swizzles_decomposed": "hvx_swizzles_decomposed",
        "x86_swizzles_decomposed": "x86_swizzles_decomposed",
        "arm_swizzles_decomposed": "arm_swizzles_decomposed",
        "ARMSema": "arm_semantics",
        "repairs_sema": "repair_semantics",
    }.items():
        modules[f"sema/{module}.py"] = f"{symbol} = {{}}\n"
    modules["patterns/ARM.py"] = """import os
from pathlib import Path
cache = Path(os.environ['MISAAL_PATTERN_CACHE_DIR'])
with Path('pattern-imports.txt').open('a') as log: log.write('import\n')
if (cache / 'ARM_abstract.pickle').exists():
    arm_patterns = ['abstract']
elif (cache / 'ARM.pickle').exists():
    arm_patterns = ['raw']
    (cache / 'ARM_abstract.pickle').write_text('abstract fixture')
else:
    arm_patterns = ['raw']
    (cache / 'ARM.pickle').write_text('raw fixture')
""".replace("log.write('import\n')", "log.write('import\\n')")
    modules["compiler/HydrideCompiler.py"] = """from pathlib import Path
from compiler.EggLogCompiler import EggLogCompiler
class HydrideCompiler(EggLogCompiler):
    def __init__(self, patterns, **options):
        self.egglog_bin = options['egg_pkg_path']
        self.input_tests = options['tests']
        self.llvm_out_file_name = options['llvm_out_file_name']
        self.llvm_so_path = options['llvm_so_path']
        self.intrinsics_file = options['intrinsics_file']
        self.hydride_root_path = options['hydride_root_path']
        self.llvm_flags = options['llvm_flags']
        self.compile_times = []
        self.output_file_path = 'rosette-input.txt'
    def compile_hydride(self):
        raw = Path('real-source.egg')
        raw.write_text('(datatype E (Seed))\\n(let srcexpr (Seed))\\n(run 5)\\n(extract srcexpr)\\n')
        for _ in range(2): assert self.execute_egglog_file(str(raw)) == '(Seed)'
        Path(self.output_file_path).write_text('source fixture')
    def print_stats(self): pass
"""
    for relative, content in modules.items():
        path = checkout / "lib" / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
    wrapper_ir = checkout / "Hydride/codegen-generator/tools/low-level-codegen/wrappers/arm_wrappers.c.ll"
    wrapper_ir.parent.mkdir(parents=True, exist_ok=True)
    wrapper_ir.write_text("fake ARM wrapper input identity")
    pins = {}
    for relative in misaal.ARM_TERMINAL_SOURCES:
        path = checkout / relative
        if not path.exists():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("pinned emitter/parent fixture")
        pins[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
    monkeypatch.setattr(misaal, "ARM_TERMINAL_SOURCES", pins)
    request["source_hashes"].update(pins)
    request["source_hashes"].update(
        {
            str(path.relative_to(checkout)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in (checkout / "lib").rglob("*.py")
        }
    )
    generator = Path(request["generator"])
    generator.write_text(f"""#!{sys.executable}
import os, subprocess, sys
from pathlib import Path
empty = {ARM_EMPTY_PROGRAM!r}.format(
    legalizer={request["legalizer"]!r}, hydride={str(checkout / "Hydride")!r},
    prefix=os.environ['MISAAL_CAPTURE_LLVM_PREFIX'])
real = empty.replace('tests = []\\n', "tests = []\\ntest_0_name = 'hydride_expr_0'\\n"
    "test_0_str = 'source expression'\\ntests.append((test_0_name, test_0_str))\\n")
programs = [real] + [empty] * int(os.environ.get('PROTOCOL_EMPTY_COUNT', '1'))
if os.environ.get('PROTOCOL_LATE_NONEMPTY'): programs.append(real)
child = Path(os.environ['HYDRIDE_BENCHMARK'] + '_misaal.py')
for program in programs:
    child.write_text(program)
    outcome = subprocess.run(['python3', str(child)], check=False)
    if outcome.returncode and not os.environ.get('PROTOCOL_IGNORE_CHILD_FAILURE'): sys.exit(outcome.returncode)
feedback = Path(os.environ['MISAAL_CAPTURE_LLVM_PREFIX'] + '.ll').read_text()
Path('parent-consumed-feedback.txt').write_text(feedback)
if os.environ.get('PROTOCOL_PARENT_FAILURE'): sys.exit(19)
if os.environ.get('PROTOCOL_REMOVE_EMPTY_BOUNDARY'): Path('children/terminal-empty.json').unlink()
if os.environ.get('PROTOCOL_CHANGE_EXECUTED_EMPTY'):
    Path('children/child-0001/terminal-empty.py').write_text('changed after child success')
output = Path(sys.argv[1])
(output / 'generator.ll').write_text(feedback)
(output / 'generator.a').write_text('final parent fixture')
""")
    request["generator_sha256"] = hashlib.sha256(generator.read_bytes()).hexdigest()
    protocol_request.write_text(json.dumps(request))
    wrapper = tmp_path / "terminal_adapter.py"
    wrapper.write_text(
        f"import sys\nsys.path.insert(0, {str(Path(misaal.__file__).resolve().parents[1])!r})\n"
        "from scripts import misaal_reproduction as adapter\n"
        f"adapter.ARM_TERMINAL_SOURCES = {pins!r}\n"
        "adapter.__file__ = __file__\nraise SystemExit(adapter.main())\n"
    )
    monkeypatch.setattr(misaal, "__file__", str(wrapper))
    return protocol_request


@pytest.mark.parametrize("failure", [None, "PROTOCOL_LATE_NONEMPTY", "PROTOCOL_PARENT_FAILURE"])
def test_arm_terminal_empty_suffix_preserves_parent_feedback_and_real_sessions(
    arm_terminal_request: Path, tmp_path: Path, failure: str | None
) -> None:
    request = json.loads(arm_terminal_request.read_text())
    request["environment"]["PROTOCOL_EMPTY_COUNT"] = "2"
    if failure:
        request["environment"][failure] = "1"
    arm_terminal_request.write_text(json.dumps(request))
    attempt = tmp_path / "terminal-attempt"
    assert misaal.run_frontend(arm_terminal_request, attempt) == (1 if failure else 0)
    record = json.loads((attempt / "capture.json").read_text())
    children = sorted((attempt / "children").glob("child-*/capture.json"))
    assert (attempt / "pattern-imports.txt").read_text() == "import\n"
    assert (attempt / "pattern-cache/ARM.pickle").read_text() == "raw fixture"
    assert not (attempt / "pattern-cache/ARM_abstract.pickle").exists()
    assert len(children) == (4 if failure == "PROTOCOL_LATE_NONEMPTY" else 3)
    for child in children[1:3]:
        empty = json.loads(child.read_text())
        assert empty["status"] == "success" and empty["source_capture_complete"] is True
        assert empty["terminal_empty_child"]["source_exit_code"] == 0
        assert empty["terminal_empty_child"]["admitted_as_workload"] is False
        assert empty["invocations"] == empty["helper_invocations"] == empty["legalizations"] == []
    if failure:
        assert record["source_capture_complete"] is False and record["workloads"] == []
        if failure == "PROTOCOL_LATE_NONEMPTY":
            assert "Nonempty ARM child follows" in json.loads(children[-1].read_text())["error"]
    else:
        assert record["source_capture_complete"] is True
        assert record["terminal_empty_child"]["status"] == "complete"
        assert len(record["workloads"]) == len(record["invocations"]) == 2
        assert (attempt / "parent-consumed-feedback.txt").read_bytes() == (attempt / "generator.ll").read_bytes()


@pytest.mark.parametrize(
    "mutation", ["contract", "revision", "isa", "frontend", "iterations", "cache", "pin", "source"]
)
def test_arm_terminal_policy_requires_exact_source_and_configuration(arm_terminal_request: Path, mutation: str) -> None:
    request = json.loads(arm_terminal_request.read_text())
    if mutation == "contract":
        request["terminal_empty_child"] = "unknown"
    elif mutation == "revision":
        request["revision"] = "a" * 40
    elif mutation == "isa":
        request["configuration"] = {"target": "x86"}
    elif mutation == "frontend":
        del request["environment"]["MISAAL_DISABLE_FRONTEND_PATTERNS"]
    elif mutation == "iterations":
        request["environment"]["MISAAL_EQ_SAT_ITERS"] = "6"
    elif mutation == "cache":
        request["pattern_cache_contract"]["generation"] = "preseeded"
    elif mutation == "pin":
        request["source_hashes"].pop("frontends/halide/src/misaal.cpp")
    else:
        (Path(request["checkout"]) / "lib/patterns/ARM.py").write_text("changed")
    arm_terminal_request.write_text(json.dumps(request))
    with pytest.raises(ValueError):
        misaal.verified_request(arm_terminal_request)


@pytest.fixture
def arm_empty_boundary(
    arm_terminal_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> tuple[dict[str, Any], Path, Path, Path]:
    request = json.loads(arm_terminal_request.read_text())
    attempt = tmp_path / "empty-boundary"
    (attempt / "pattern-cache").mkdir(parents=True)
    previous = attempt / "children/child-0000/capture.json"
    previous.parent.mkdir(parents=True)
    feedback = tmp_path / "real-feedback.ll"
    feedback.write_text("previous validated LLVM fixture")
    previous.write_text(
        json.dumps(
            {
                "status": "success",
                "source_capture_complete": True,
                "invocations": [{"status": "success"}],
                "legalizations": [
                    {
                        "status": "success",
                        "feedback": str(feedback),
                        "feedback_sha256": hashlib.sha256(feedback.read_bytes()).hexdigest(),
                    }
                ],
            }
        )
    )
    monkeypatch.setenv("MISAAL_CAPTURE_LLVM_PREFIX", str(feedback.with_suffix("")))
    directory = attempt / "children/child-0001"
    directory.mkdir()
    program = attempt / "observed_misaal.py"
    program.write_text(
        ARM_EMPTY_PROGRAM.format(
            legalizer=request["legalizer"],
            hydride=str(Path(request["checkout"]) / "Hydride"),
            prefix=str(feedback.with_suffix("")),
        )
    )
    return request, program, directory, feedback


@pytest.mark.parametrize("cache_state", ["cold", "raw", "abstract"])
def test_arm_terminal_defers_each_cache_state_and_rejects_later_real_child(
    arm_empty_boundary: tuple[dict[str, Any], Path, Path, Path], cache_state: str
) -> None:
    request, program, directory, feedback = arm_empty_boundary
    cache = directory.parent.parent / "pattern-cache"
    if cache_state in {"raw", "abstract"}:
        (cache / "ARM.pickle").write_text("raw bytes")
    if cache_state == "abstract":
        (cache / "ARM_abstract.pickle").write_text("abstract bytes")
    before = {path.name: path.read_bytes() for path in cache.iterdir()}
    source = program.read_bytes()
    record: dict[str, Any] = {}
    execution = misaal.source_child_program(request, program, directory, record)
    assert execution != program and program.read_bytes() == source
    assert record["terminal_empty_child"]["boundary"]["state"]["cache_state"] == cache_state
    # The only text movement is tests=[] plus the exact source exit guard.
    moved = "tests = []\nif len(tests) == 0:\n\tsys.exit(0)\n"
    assert execution.read_text().replace(moved, "", 1) == source.decode().replace(moved, "", 1)
    assert execution.read_text().index(moved) < execution.read_text().index("from patterns.ARM")
    assert {path.name: path.read_bytes() for path in cache.iterdir()} == before
    assert feedback.read_text() == "previous validated LLVM fixture"
    misaal.save_receipt(directory.parent / "terminal-empty.json", record["terminal_empty_child"]["boundary"])
    program.write_text(
        source.decode().replace(
            "tests = []\n",
            "tests = []\n"
            "test_0_name = 'real'\ntest_0_str = 'literal expression'\ntests.append((test_0_name, test_0_str))\n",
        )
    )
    with pytest.raises(ValueError, match="Nonempty ARM child follows"):
        misaal.source_child_program(request, program, directory, {})
    assert {path.name: path.read_bytes() for path in cache.iterdir()} == before


@pytest.mark.parametrize(
    "mutation",
    [
        "exit-one",
        "unexpected-empty",
        "dynamic-tests",
        "iterations",
        "missing-feedback",
        "changed-feedback",
        "symlink-cache",
        "foreign-cache",
    ],
)
def test_arm_terminal_rejects_template_and_boundary_drift(
    arm_empty_boundary: tuple[dict[str, Any], Path, Path, Path], mutation: str
) -> None:
    request, program, directory, feedback = arm_empty_boundary
    original = program.read_text()
    if mutation == "exit-one":
        program.write_text(original.replace("sys.exit(0)", "sys.exit(1)"))
    elif mutation == "unexpected-empty":
        program.write_text(original.replace("tests = []", "tests = []\nprint('extra')"))
    elif mutation == "dynamic-tests":
        program.write_text(original.replace("tests = []", "tests = list()"))
    elif mutation == "iterations":
        program.write_text(original.replace("run_iterations = 5", "run_iterations = 6"))
    elif mutation == "missing-feedback":
        feedback.unlink()
    elif mutation == "changed-feedback":
        feedback.write_text("unverified replacement")
    elif mutation == "symlink-cache":
        (directory.parent.parent / "pattern-cache/ARM.pickle").symlink_to(feedback)
    else:
        (directory.parent.parent / "pattern-cache/foreign.pickle").write_text("unknown")
    with pytest.raises(ValueError):
        misaal.source_child_program(request, program, directory, {})
    assert not (directory / "terminal-empty.py").exists()


@pytest.mark.parametrize("mutation", ["import-exit-zero", "cache", "feedback"])
def test_arm_terminal_never_accepts_other_exit_or_state_changes(
    arm_terminal_request: Path, tmp_path: Path, mutation: str
) -> None:
    request = json.loads(arm_terminal_request.read_text())
    module = Path(request["checkout"]) / "lib/utils/egg_config.py"
    action = {
        "import-exit-zero": "raise SystemExit(0)",
        "cache": "Path(os.environ['MISAAL_PATTERN_CACHE_DIR'], 'ARM.pickle').write_text('changed')",
        "feedback": "Path(os.environ['MISAAL_CAPTURE_LLVM_PREFIX'] + '.ll').write_text('changed')",
    }[mutation]
    module.write_text(
        module.read_text()
        + "import os\nfrom pathlib import Path\n"
        + "if Path('pattern-imports.txt').exists():\n    "
        + action
        + "\n"
    )
    request["source_hashes"]["lib/utils/egg_config.py"] = hashlib.sha256(module.read_bytes()).hexdigest()
    arm_terminal_request.write_text(json.dumps(request))
    attempt = tmp_path / "changed-attempt"
    assert misaal.run_frontend(arm_terminal_request, attempt) == 1
    record = json.loads((attempt / "capture.json").read_text())
    assert record["source_capture_complete"] is False and record["workloads"] == []
    child = json.loads((attempt / "children/child-0001/capture.json").read_text())
    assert child["status"] == "failure" and child["source_capture_complete"] is False
    assert (attempt / "children/terminal-empty.json").is_file()
    assert (
        "SystemExit: 0" in child["error"]
        if mutation == "import-exit-zero"
        else "changed work, cache or LLVM" in child["error"]
    )


@pytest.mark.parametrize("mutation", ["PROTOCOL_REMOVE_EMPTY_BOUNDARY", "PROTOCOL_CHANGE_EXECUTED_EMPTY"])
def test_arm_terminal_parent_requires_preserved_boundary_and_executed_program(
    arm_terminal_request: Path, tmp_path: Path, mutation: str
) -> None:
    request = json.loads(arm_terminal_request.read_text())
    request["environment"][mutation] = "1"
    arm_terminal_request.write_text(json.dumps(request))
    attempt = tmp_path / "changed-receipt-attempt"
    assert misaal.run_frontend(arm_terminal_request, attempt) == 1
    record = json.loads((attempt / "capture.json").read_text())
    assert record["generator_returncode"] == 0
    assert record["source_capture_complete"] is False and record["workloads"] == []
    assert "ARM terminal-empty" in record["error"]


def test_arm_terminal_failed_empty_still_blocks_later_real_child(arm_terminal_request: Path, tmp_path: Path) -> None:
    request = json.loads(arm_terminal_request.read_text())
    module = Path(request["checkout"]) / "lib/utils/egg_config.py"
    module.write_text(
        module.read_text() + "from pathlib import Path\nif Path('pattern-imports.txt').exists(): raise SystemExit(0)\n"
    )
    request["source_hashes"]["lib/utils/egg_config.py"] = hashlib.sha256(module.read_bytes()).hexdigest()
    request["environment"].update(PROTOCOL_IGNORE_CHILD_FAILURE="1", PROTOCOL_LATE_NONEMPTY="1")
    arm_terminal_request.write_text(json.dumps(request))
    attempt = tmp_path / "ignored-failure-attempt"
    assert misaal.run_frontend(arm_terminal_request, attempt) == 1
    record = json.loads((attempt / "capture.json").read_text())
    assert record["generator_returncode"] == 0
    assert record["source_capture_complete"] is False and record["workloads"] == []
    empty = json.loads((attempt / "children/child-0001/capture.json").read_text())
    real = json.loads((attempt / "children/child-0002/capture.json").read_text())
    assert "SystemExit: 0" in empty["error"]
    assert "Nonempty ARM child follows" in real["error"]
    assert empty["status"] == real["status"] == "failure"
    assert real["invocations"] == real["legalizations"] == []
    assert "helper_invocations" not in real  # Rejected before imports and helper observation start.
    assert (attempt / "pattern-imports.txt").read_text() == "import\n"


def test_arm_terminal_helpers_and_pins_change_archived_native_identity() -> None:
    source = Path(misaal.__file__).read_text()
    contract = misaal.capture_implementation_contract(source)
    for before, after in [
        ('ARM_TERMINAL_EMPTY = "arm-empty-terminal-v1"', 'ARM_TERMINAL_EMPTY = "changed"'),
        ("run_iterations={iterations}, egg_pkg_path=EGG_PKG_PATH", "run_iterations=6, egg_pkg_path=EGG_PKG_PATH"),
    ]:
        candidate = source.replace(before, after)
        assert candidate != source
        assert misaal.capture_implementation_contract(candidate)[0] != contract[0]
        assert misaal.capture_implementation_contract(candidate)[1] == contract[1]


@pytest.fixture
def export_request(arm_terminal_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    request = json.loads(arm_terminal_request.read_text())
    checkout = Path(request["checkout"])
    request.pop("terminal_empty_child")
    request.update(egglog_export=misaal.EGGLOG_EXPORT, expected_generator_outputs=[])
    request["environment"].update(
        LEGALIZERS_DIR=str(checkout / "absent-selectors"), HYDRIDE_DIR=str(checkout / "Hydride")
    )
    # Source/preparation verification is independently owned; these protocol tests
    # inject only its API boundary. All adapter source/tool hashes remain checked.
    module = ModuleType("scripts.reproduction_misaal_export")
    module.verify_export_request = lambda request: None  # type: ignore[attr-defined]
    monkeypatch.setitem(sys.modules, module.__name__, module)
    for target, symbol in (("halide", "Halide_patterns"), ("hvx", "HVX_patterns"), ("x86", "x86_patterns")):
        name = {"halide": "Halide", "hvx": "HVX", "x86": "x86"}[target]
        (checkout / f"lib/patterns/{name}.py").write_text(f"""import os
from pathlib import Path
cache = Path(os.environ['MISAAL_PATTERN_CACHE_DIR'])
with Path('pattern-imports.txt').open('a') as log: log.write({target + chr(10)!r})
if (cache / '{target}_abstract.pickle').exists(): pass
elif (cache / '{target}.pickle').exists(): (cache / '{target}_abstract.pickle').write_text('abstract fixture')
else: (cache / '{target}.pickle').write_text('raw fixture')
{symbol} = []
""")
    compiler = checkout / "lib/compiler/HydrideCompiler.py"
    compiler.write_text("""import os
from pathlib import Path
from compiler.EggLogCompiler import EggLogCompiler
class HydrideCompiler(EggLogCompiler):
    def __init__(self, patterns, **options):
        self.input_tests = options['tests']
        self.egglog_bin = options['egg_pkg_path']
        self.output_file_path = 'test.out'
    def get_rosette_expression_str(self, input_expr, output_expr, function_name):
        return '; ' + function_name + '\\n' + output_expr
    def recursive_rewrite(self, raw):
        if os.environ.get('PROTOCOL_RECURSIVE_EXIT'): raise SystemExit(0)
        self.execute_egglog_file(str(raw))
        self.swizzle(raw)
    def swizzle(self, raw): self.execute_egglog_file(str(raw))
    def compile_hydride(self):
        if os.environ.get('PROTOCOL_EARLY_EXIT'): raise SystemExit(0)
        if os.environ.get('PROTOCOL_COMPILE_FAILURE'): raise ValueError('original compile failed')
        if os.environ.get('PROTOCOL_TRY_LLVM'): self.run_llvm_legalizer()
        raw = Path('input.egg')
        raw.write_text('(datatype E (Seed))\\n(let srcexpr (Seed))\\n(run 5)\\n(extract srcexpr)\\n')
        try:
            self.execute_egglog_file(str(raw))
            self.recursive_rewrite(raw)
        except ValueError:
            if not os.environ.get('PROTOCOL_SWALLOW_BACKEND_FAILURE'): raise
        tests = self.input_tests[:-1] if os.environ.get('PROTOCOL_MISSING_RESULT') else self.input_tests
        results = [self.get_rosette_expression_str(expr, '(Seed)', name) for name, expr in tests]
        if os.environ.get('PROTOCOL_CHANGED_SELECTED'): results.append('extra')
        Path(self.output_file_path).write_text('\\n'.join(results))
    def print_stats(self): pass
""")
    request["source_hashes"].update(
        {
            str(path.relative_to(checkout)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in (checkout / "lib").rglob("*.py")
        }
    )
    generator = Path(request["generator"])
    generator.write_text(f"""#!{sys.executable}
import json, os, subprocess, sys
from pathlib import Path
assert os.environ['MISAAL_EXPORT_MODE'] == 'egglog-only-v1'
events = Path(os.environ['MISAAL_EXPORT_EVENTS'])
assert events.is_absolute() and not events.exists()
rows = []
modules = functions = children = 0
def emit(event, **fields):
    row = dict(schema='misaal-export-v1', seq=len(rows), event=event, **fields)
    if event == 'child_begin' and os.environ.get('PROTOCOL_ACTIVE_EVENT_DRIFT'): row['child_id'] += 1
    rows.append(row)
    with events.open('a') as stream: stream.write(json.dumps(row) + '\\n')
target = os.environ.get('PROTOCOL_TARGET', 'arm')
semantics, pattern, wrapper, flag, so = {{
    'arm': ('arm','ARM import arm_patterns','arm_wrappers.c.ll','arm','libARMLegalizer.so'),
    'hexagon': ('hvx','HVX import HVX_patterns','hvx_wrappers.ll','hex','libHVXLegalizer.so'),
    'x86': ('x86','x86 import x86_patterns','x86_wrappers.c.ll','x86','libx86LegalizerAllArgs.so'),
}}[target]
empty = {ARM_EMPTY_PROGRAM!r}.format(legalizer=str(Path(os.environ['LEGALIZERS_DIR']) / so),
    hydride=os.environ['HYDRIDE_DIR'], prefix=os.environ['MISAAL_CAPTURE_LLVM_PREFIX'])
empty = empty.replace('from patterns.ARM import arm_patterns', 'from patterns.' + pattern)
empty = empty.replace('parse_dict_with_bounded(arm_semantics)', 'parse_dict_with_bounded(' + semantics + '_semantics)')
empty = empty.replace('parse_dict_with_bounded(arm_swizzles)', 'parse_dict_with_bounded(' + semantics + '_swizzles)')
empty = empty.replace('arm_wrappers.c.ll', wrapper).replace('-arm-hydride-legalize', '-' + flag + '-hydride-legalize')
empty = empty.replace('run_iterations = 5', 'run_iterations = ' + os.environ.get('MISAAL_EQ_SAT_ITERS', '5'))
if 'MISAAL_DISABLE_FRONTEND_PATTERNS' not in os.environ:
    empty = empty.replace('misaal_input_patterns = []',
        'from patterns.Halide import Halide_patterns as misaal_input_patterns')
real = empty.replace('tests = []\\n', "tests = []\\ntest_0_name = 'hydride_expr_0'\\n"
    "test_0_str = 'shared input'\\ntests.append((test_0_name, test_0_str))\\n"
    "test_1_name = 'hydride_expr_1'\\ntest_1_str = 'shared input'\\ntests.append((test_1_name, test_1_str))\\n")
programs = ([empty] * int(os.environ.get('PROTOCOL_INITIAL_EMPTY', '0'))
    + [real] * int(os.environ.get('PROTOCOL_REAL_COUNT', '2'))
    + [empty] * int(os.environ.get('PROTOCOL_EMPTY_COUNT', '2')))
if os.environ.get('PROTOCOL_LATE_NONEMPTY'): programs.append(real)
def run_function(mid, program):
    global functions, children
    fid = functions; functions += 1
    emit('function_begin', module_id=mid, function_id=fid, name_hex=('func_' + str(fid)).encode().hex())
    if 'HALIDE_COMPILE_LLVM' in os.environ:
        emit('function_end', module_id=mid, function_id=fid)
        return
    script = os.environ['HYDRIDE_BENCHMARK'] + '_misaal.py'
    if os.environ.get('PROTOCOL_TEMPLATE_DRIFT'): program += "raise ValueError('unexpected source')\\n"
    Path(script).write_text(program)
    cid = children; children += 1
    emit('child_begin', module_id=mid, function_id=fid, child_id=cid, script_hex=script.encode().hex())
    outcome = subprocess.run(['python3', script], check=False)
    if outcome.returncode and not os.environ.get('PROTOCOL_IGNORE_CHILD_FAILURE'): sys.exit(outcome.returncode)
    emit('child_end', module_id=mid, function_id=fid, child_id=cid, returncode=outcome.returncode)
    emit('function_end', module_id=mid, function_id=fid)
if os.environ.get('PROTOCOL_SHARED_RUNTIME'):
    emit('module_begin', module_id=0, parent_module_id=None, name_hex=b'shared_runtime'.hex(),
        target_hex=target.encode().hex(), function_count=0, submodule_count=0)
    emit('module_end', module_id=0)
    modules = 1
    emit('export_complete', root_module_id=0, module_count=1, function_count=0, child_count=0)
for root in range(int(os.environ.get('PROTOCOL_ROOTS', '1'))):
    rid = modules; modules += 1
    emit('module_begin', module_id=rid, parent_module_id=None, name_hex=b'root'.hex(),
        target_hex=target.encode().hex(), function_count=1, submodule_count=1)
    mid = modules; modules += 1
    emit('module_begin', module_id=mid, parent_module_id=rid, name_hex=b'leaf'.hex(),
        target_hex=target.encode().hex(), function_count=len(programs)-1, submodule_count=0)
    for program in programs[:-1]: run_function(mid, program)
    emit('module_end', module_id=mid)
    run_function(rid, programs[-1])
    emit('module_end', module_id=rid)
    emit('export_complete', root_module_id=rid, module_count=modules, function_count=functions, child_count=children)
mutation = os.environ.get('PROTOCOL_LEDGER_MUTATION')
if mutation == 'missing-complete': rows.pop()
elif mutation == 'count': rows[-1]['child_count'] += 1
elif mutation == 'module-count': rows[0]['function_count'] += 1
elif mutation == 'parent': rows[1]['parent_module_id'] = None
elif mutation == 'function-id': next(row for row in rows if row['event']=='function_end')['function_id'] = 999
elif mutation == 'child-id': next(row for row in rows if row['event']=='child_end')['child_id'] = 999
elif mutation == 'nonzero-child': next(row for row in rows if row['event']=='child_end')['returncode'] = 1
elif mutation == 'sequence': rows[-1]['seq'] += 1
elif mutation == 'duplicate': rows.insert(-1, rows[-2])
elif mutation == 'target-hex': rows[0]['target_hex'] = 'ff'
elif mutation == 'unknown': rows[-1]['event'] = 'unknown'
elif mutation == 'drop-child': rows = [row for row in rows if row.get('child_id') != 0]
if mutation: events.write_text(''.join(json.dumps(row)+'\\n' for row in rows))
if os.environ.get('PROTOCOL_REMOVE_BOUNDARY'): Path('children/terminal-export.json').unlink()
if os.environ.get('PROTOCOL_CACHE_CHANGE'): next(Path('pattern-cache').glob('*.pickle')).write_text('changed')
if os.environ.get('PROTOCOL_SELECTED_CHANGE'):
    Path('children/child-0000/selected-expressions.txt').write_text('changed')
if os.environ.get('PROTOCOL_EXECUTION_CHANGE'): Path('children/child-0000/egglog-export.py').write_text('changed')
if os.environ.get('PROTOCOL_NATIVE_OUTPUT'): Path('unexpected.ll').write_text('forbidden')
if os.environ.get('PROTOCOL_PARENT_FAILURE'): sys.exit(19)
""")
    request["generator_sha256"] = hashlib.sha256(generator.read_bytes()).hexdigest()
    # LLVM binaries and selector files are deliberately absent in the request.
    for key in ("llvm_as", "llvm_as_sha256", "legalizer", "legalizer_sha256"):
        request.pop(key, None)
    arm_terminal_request.write_text(json.dumps(request))
    wrapper = tmp_path / "export_adapter.py"
    wrapper.write_text(
        f"import sys\nsys.path.insert(0, {str(Path(__file__).resolve().parents[1])!r})\n"
        "from types import ModuleType\n"
        "module = ModuleType('scripts.reproduction_misaal_export')\n"
        "module.verify_export_request = lambda request: None\n"
        "sys.modules[module.__name__] = module\n"
        "from scripts import misaal_reproduction as adapter\n"
        "adapter.__file__ = __file__\nraise SystemExit(adapter.main())\n"
    )
    monkeypatch.setattr(misaal, "__file__", str(wrapper))
    return arm_terminal_request


@pytest.mark.parametrize(
    "target,real,initial", [("arm", 1, 0), ("arm", 3, 1), ("hexagon", 1, 0), ("hexagon", 3, 0), ("x86", 2, 0)]
)
def test_export_closes_all_source_work_and_skips_llvm(
    export_request: Path, tmp_path: Path, target: str, real: int, initial: int
) -> None:
    request = json.loads(export_request.read_text())
    request["configuration"] = {"target": target}
    request["environment"].update(
        PROTOCOL_TARGET=target, PROTOCOL_REAL_COUNT=str(real), PROTOCOL_INITIAL_EMPTY=str(initial)
    )
    if target == "hexagon":
        request["environment"].pop("MISAAL_DISABLE_FRONTEND_PATTERNS")
        request["environment"]["MISAAL_EQ_SAT_ITERS"] = "3"
    export_request.write_text(json.dumps(request))
    attempt = tmp_path / "export-attempt"
    assert misaal.run_frontend(export_request, attempt) == 0
    record = json.loads((attempt / "capture.json").read_text())
    assert record["source_kind"] == misaal.EXPORT_SOURCE_KIND
    assert record["native_outputs"] == [] and record["native_codegen"] == "not_requested"
    assert record["source_capture_complete"] and record["source_completion"]["enumeration"]["modules"] == 2
    assert len(record["invocations"]) == real * 3 == len(record["workloads"])
    assert {call["caller"] for call in record["invocations"]} == {"compile_hydride", "recursive_rewrite", "swizzle"}
    assert len({call["sha256"] for call in record["invocations"]}) == 1  # Keep every repeated source call.
    assert not list(attempt.glob("**/legalize-*")) and not list(attempt.glob("*.ll"))
    assert len((attempt / "pattern-imports.txt").read_text().splitlines()) == (real + initial) * (
        2 if target == "hexagon" else 1
    )
    children = [json.loads(Path(item["path"]).read_text()) for item in record["children"]]
    for child in children[initial : initial + real]:
        completion = child["egglog_export"]["compilation"]
        assert completion["status"] == "complete" and completion["input_count"] == 2
        assert [row["name"] for row in completion["named_results"]] == ["hydride_expr_0", "hydride_expr_1"]
        assert Path(completion["selected"]["path"]).read_text() == "; hydride_expr_0\n(Seed)\n; hydride_expr_1\n(Seed)"
    assert all(child["egglog_export"]["source_exit_code"] == 0 for child in children[-2:])


@pytest.mark.parametrize(
    "mutation",
    [
        "missing-complete",
        "count",
        "module-count",
        "parent",
        "function-id",
        "child-id",
        "nonzero-child",
        "sequence",
        "duplicate",
        "target-hex",
        "unknown",
        "drop-child",
    ],
)
def test_export_rejects_incomplete_or_changed_source_ledger(
    export_request: Path, tmp_path: Path, mutation: str
) -> None:
    request = json.loads(export_request.read_text())
    request["environment"].update(PROTOCOL_LEDGER_MUTATION=mutation, PROTOCOL_EMPTY_COUNT="0", PROTOCOL_REAL_COUNT="1")
    export_request.write_text(json.dumps(request))
    attempt = tmp_path / "ledger-failure"
    assert misaal.run_frontend(export_request, attempt) == 1
    record = json.loads((attempt / "capture.json").read_text())
    assert record["source_capture_complete"] is False and record["workloads"] == []


@pytest.mark.parametrize(
    "failure",
    [
        "COMPILE_FAILURE",
        "EARLY_EXIT",
        "RECURSIVE_EXIT",
        "ACTIVE_EVENT_DRIFT",
        "TRY_LLVM",
        "MISSING_RESULT",
        "CHANGED_SELECTED",
        "LATE_NONEMPTY",
        "TEMPLATE_DRIFT",
        "REMOVE_BOUNDARY",
        "CACHE_CHANGE",
        "SELECTED_CHANGE",
        "EXECUTION_CHANGE",
        "NATIVE_OUTPUT",
        "PARENT_FAILURE",
        "SWALLOW_BACKEND_FAILURE",
    ],
)
def test_export_preserves_failures_and_never_admits_a_prefix(
    export_request: Path, tmp_path: Path, failure: str
) -> None:
    request = json.loads(export_request.read_text())
    request["environment"]["PROTOCOL_" + failure] = "1"
    if failure == "SWALLOW_BACKEND_FAILURE":
        request["environment"]["PROTOCOL_BACKEND_FAILURE"] = "1"
    export_request.write_text(json.dumps(request))
    attempt = tmp_path / "failed-export"
    assert misaal.run_frontend(export_request, attempt) == 1
    record = json.loads((attempt / "capture.json").read_text())
    assert record["source_capture_complete"] is False and record["workloads"] == []
    assert not list(attempt.glob("**/legalize-*"))


def test_export_multiple_root_enumeration_and_zero_optimizer_helpers(export_request: Path, tmp_path: Path) -> None:
    request = json.loads(export_request.read_text())
    request["environment"].update(PROTOCOL_ROOTS="2", PROTOCOL_REAL_COUNT="0", PROTOCOL_EMPTY_COUNT="1")
    export_request.write_text(json.dumps(request))
    attempt = tmp_path / "helper-export"
    assert misaal.run_frontend(export_request, attempt) == 0
    record = json.loads((attempt / "capture.json").read_text())
    assert record["source_capture_complete"] and record["status"] == "source-helper" and record["workloads"] == []
    assert record["export_enumeration"]["roots"] == 2 and record["export_enumeration"]["children"] == 2
    assert not (attempt / "children/terminal-export.json").exists()


@pytest.mark.parametrize(
    "mutation",
    ["contract", "native-policy", "native-outputs", "request-mode", "request-events", "ambient-mode", "ambient-events"],
)
def test_export_request_rejects_ambiguous_activation(
    export_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mutation: str
) -> None:
    request = json.loads(export_request.read_text())
    if mutation == "contract":
        request["egglog_export"] = None
    elif mutation == "native-policy":
        request["terminal_empty_child"] = misaal.ARM_TERMINAL_EMPTY
    elif mutation == "native-outputs":
        request["expected_generator_outputs"] = ["unexpected.ll"]
    elif mutation.startswith("request-"):
        request["environment"]["MISAAL_EXPORT_" + mutation.removeprefix("request-").upper()] = "injected"
    else:
        monkeypatch.setenv("MISAAL_EXPORT_" + mutation.removeprefix("ambient-").upper(), "injected")
    export_request.write_text(json.dumps(request))
    with pytest.raises(ValueError):
        misaal.run_frontend(export_request, tmp_path / "not-started")
    assert not (tmp_path / "not-started").exists()


@pytest.mark.parametrize("halide", ["cold", "raw", "abstract"])
@pytest.mark.parametrize("hvx", ["cold", "raw", "abstract"])
def test_export_terminal_state_binds_both_independent_hvx_caches(tmp_path: Path, halide: str, hvx: str) -> None:
    cache = tmp_path / "pattern-cache"
    cache.mkdir()
    for stem, cache_state in (("halide", halide), ("hvx", hvx)):
        if cache_state != "cold":
            (cache / f"{stem}.pickle").write_text(stem + " raw")
        if cache_state == "abstract":
            (cache / f"{stem}_abstract.pickle").write_text(stem + " abstract")
    selected = tmp_path / "selected-expressions.txt"
    selected.write_text("retained original selection")
    request = {"configuration": {"target": "hexagon"}, "environment": {}}
    state = misaal.terminal_state(tmp_path, selected, request)
    assert state["cache_state"] == {"halide": halide, "hvx": hvx}
    assert set(state["cache_sha256"]) == {path.name for path in cache.iterdir()}
    assert state["selected"] == str(selected) and "feedback" not in state
    for stem in ("halide", "hvx"):
        changed = cache / f"{stem}.pickle"
        previous = changed.read_bytes() if changed.exists() else None
        changed.write_text("changed independently")
        assert misaal.terminal_state(tmp_path, selected, request) != state
        if previous is None:
            changed.unlink()
        else:
            changed.write_bytes(previous)


@pytest.mark.parametrize(
    "mutation",
    [
        None,
        "frontend",
        "patterns",
        "semantics",
        "swizzles",
        "flags",
        "wrapper",
        "iterations",
        "dynamic-input",
        "extra-statement",
        "legalizer-call",
    ],
)
def test_export_exact_child_edit_preserves_original_graph_text(
    export_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mutation: str | None
) -> None:
    request = json.loads(export_request.read_text())
    attempt = tmp_path / "recognition"
    directory = attempt / "children/child-0000"
    directory.mkdir(parents=True)
    prefix = str(attempt / "unused-feedback")
    monkeypatch.setenv("MISAAL_CAPTURE_LLVM_PREFIX", prefix)
    source = ARM_EMPTY_PROGRAM.format(
        legalizer=str(Path(request["environment"]["LEGALIZERS_DIR"]) / "libARMLegalizer.so"),
        hydride=request["environment"]["HYDRIDE_DIR"],
        prefix=prefix,
    )
    source = source.replace(
        "tests = []\n",
        "tests = []\ntest_0_name = 'original'\ntest_0_str = 'unchanged graph'\n"
        "tests.append((test_0_name, test_0_str))\n",
    )
    replacements = {
        "frontend": ("misaal_input_patterns = []", "misaal_input_patterns = list()"),
        "patterns": ("patterns.ARM", "patterns.HVX"),
        "semantics": ("parse_dict_with_bounded(arm_semantics)", "parse_dict_with_bounded(hvx_semantics)"),
        "swizzles": ("parse_dict_with_bounded(arm_swizzles)", "parse_dict_with_bounded(hvx_swizzles)"),
        "flags": ("-arm-hydride-legalize", "-hex-hydride-legalize"),
        "wrapper": ("arm_wrappers.c.ll", "hvx_wrappers.ll"),
        "iterations": ("run_iterations = 5", "run_iterations = 6"),
        "dynamic-input": ("test_0_str = 'unchanged graph'", "test_0_str = str('unchanged graph')"),
        "extra-statement": ("tests = []", "tests = []\nprint('unexpected')"),
        "legalizer-call": ("misaal_compiler.run_llvm_legalizer()", "misaal_compiler.run_llvm_legalizer(1)"),
    }
    if mutation:
        before, after = replacements[mutation]
        source = source.replace(before, after)
    program = attempt / "source_misaal.py"
    program.write_text(source)
    record: dict[str, Any] = {}
    if mutation:
        with pytest.raises(ValueError):
            misaal.source_child_program(request, program, directory, record)
    else:
        execution = misaal.source_child_program(request, program, directory, record)
        assert execution.read_text() == source.replace("misaal_compiler.run_llvm_legalizer()\n", "")
        assert program.read_text() == source
        assert record["egglog_export"]["inputs"][0]["expression"] == "unchanged graph"


def test_export_failed_empty_still_blocks_later_real_child(export_request: Path, tmp_path: Path) -> None:
    request = json.loads(export_request.read_text())
    module = Path(request["checkout"]) / "lib/utils/egg_config.py"
    module.write_text(
        module.read_text() + "from pathlib import Path\nif Path('pattern-imports.txt').exists(): raise SystemExit(0)\n"
    )
    request["source_hashes"]["lib/utils/egg_config.py"] = hashlib.sha256(module.read_bytes()).hexdigest()
    request["environment"].update(
        PROTOCOL_REAL_COUNT="1", PROTOCOL_EMPTY_COUNT="1", PROTOCOL_IGNORE_CHILD_FAILURE="1", PROTOCOL_LATE_NONEMPTY="1"
    )
    export_request.write_text(json.dumps(request))
    attempt = tmp_path / "ignored-empty-failure"
    assert misaal.run_frontend(export_request, attempt) == 1
    empty = json.loads((attempt / "children/child-0001/capture.json").read_text())
    real = json.loads((attempt / "children/child-0002/capture.json").read_text())
    assert "SystemExit: 0" in empty["error"]
    assert "Nonempty export child follows" in real["error"]
    assert empty["status"] == real["status"] == "failure"
    assert real["invocations"] == real["legalizations"] == []
    assert (attempt / "children/terminal-export.json").is_file()


@pytest.mark.parametrize("value", ["0", "1"])
def test_export_no_synthesis_flag_and_zero_function_runtime_are_helpers(
    export_request: Path, tmp_path: Path, value: str
) -> None:
    request = json.loads(export_request.read_text())
    request["environment"].update(HALIDE_COMPILE_LLVM=value, PROTOCOL_SHARED_RUNTIME="1")
    export_request.write_text(json.dumps(request))
    attempt = tmp_path / "no-synthesis"
    assert misaal.run_frontend(export_request, attempt) == 0
    record = json.loads((attempt / "capture.json").read_text())
    assert record["status"] == "source-helper" and record["source_capture_complete"]
    assert record["children"] == record["invocations"] == record["workloads"] == record["native_outputs"] == []
    assert record["export_enumeration"]["roots"] == 2 and record["export_enumeration"]["modules"] == 3


def test_export_low_level_entrypoint_rejects_before_any_tool(export_request: Path, tmp_path: Path) -> None:
    sentinel = tmp_path / "must-not-run.py"
    sentinel.write_text("raise AssertionError('LLVM must not execute')")
    output = tmp_path / "no-llvm"
    with pytest.raises(ValueError, match="LLVM tools are not requested"):
        misaal.main(["low-level", "--request", str(export_request), "--output", str(output), "--script", str(sentinel)])
    assert not output.exists()
