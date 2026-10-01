"""Diagnostic protocol tests only: no LLVM compilation or native execution."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from benchmarking.pilot import PilotProcessResult
from scripts import reproduction_misaal_hvx_diagnostic as diagnostic


@pytest.fixture
def environment(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple:
    monkeypatch.setattr(diagnostic, "ROOT", tmp_path)
    accessor = (Path(__file__).parent / "fixtures/misaal-hvx-common-accessor.cpp.txt").read_text()
    common = tmp_path / "original/Legalizer.cpp"
    common.parent.mkdir()
    common.write_text(accessor + diagnostic.ACCESSOR_END + "unused tail")
    monkeypatch.setattr(diagnostic, "COMMON_SOURCE_SHA256", hashlib.sha256(common.read_bytes()).hexdigest())
    compiler, llvm = tmp_path / "clang++", tmp_path / "llvm"
    for path in (compiler, llvm / "bin/llvm-config"):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("fake executable; tests never launch this")
        path.chmod(0o755)
    library = llvm / "lib/libLLVM.dylib"
    header = llvm / "include/llvm/Analysis/ConstantFolding.h"
    for path in (library, header):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("fake prerequisite")
    output = tmp_path / "benchmarks/local/reproduction/hvx-diagnostic"
    state: dict[str, Any] = {"calls": [], "library": library}

    def run(command: list[str], cwd: Path, prefix: Path, **options: Any) -> PilotProcessResult:
        assert cwd == output
        name = prefix.name.split("-", 1)[1]
        state["calls"].append((name, command, options))
        stdout, stderr = prefix.with_suffix(".stdout.log"), prefix.with_suffix(".stderr.log")
        text, error, code = "", "", 0
        if name == "llvm-version":
            text = state.get("version", "12.0.1")
        elif name == "compiler-version":
            text = "test compiler identity"
        elif name == "llvm-flags":
            text = "-I/retained/include -std=c++14 -L/retained/lib -lLLVM"
        elif name == "llvm-libraries":
            text = str(library)
        elif name == "compile":
            (output / "concat-harness").write_bytes(b"fake compiled output")
        else:
            mode, width = command[1], int(command[2])
            if mode in diagnostic.POSITIVE_MODES:
                row = {
                    "mode": mode,
                    "width": width,
                    "checks": 1 if mode == "unrelated" else 1 << width,
                    "verified_ir": True,
                }
                if state.get("partial") == name:
                    row["checks"] = 0
                text = json.dumps(row)
            else:
                code = state.get("rejection_code", 86)
                error = "CONCAT_REJECT: " + state.get("rejection_reason", diagnostic.REJECTIONS[mode]) + "\n"
        stdout.write_text(text)
        stderr.write_text(error)
        if state.get("change_library") == name:
            library.write_text("changed during execution")
        status: Any = "success" if code == 0 else "failure"
        if state.get("stop") == name:
            status = "memory-limit"
            code = -9
        if state.get("refuse") == name:
            raise ValueError("resource guard refused to launch")
        return PilotProcessResult(status, code, 0.01, 1024, stdout, stderr, None)

    monkeypatch.setattr(diagnostic, "run_bounded_command", run)
    return common, llvm, output, compiler, state


def test_materialization_uses_exact_production_fragment_and_original_accessor(environment: tuple) -> None:
    common, _, output, _, state = environment
    result = diagnostic.materialize(common, output)
    assert state["calls"] == []
    assert result["status"] == "materialized-unrun"
    assert result["device_execution"] is result["source_parent_execution"] is result["corpus_admission"] is False
    cpp = (output / "concat-harness.cpp").read_text()
    fragment = diagnostic.lowering.concat_lowering_cpp()
    accessor = (Path(__file__).parent / "fixtures/misaal-hvx-common-accessor.cpp.txt").read_text()
    assert fragment in cpp and accessor in cpp
    assert "INSERT_EXACT" not in cpp
    assert "ConstantFoldInstOperands(instruction, operands, layout)" in cpp
    assert "value < count" in cpp and "actual->getAggregateElement(lane)" in cpp
    assert (output / "Legalizer.cpp.original").read_bytes() == common.read_bytes()
    for name, digest in result["files"].items():
        assert hashlib.sha256((output / name).read_bytes()).hexdigest() == digest
    with pytest.raises(ValueError, match="fresh"):
        diagnostic.materialize(common, output)


def test_changed_common_source_is_rejected_before_materialization(environment: tuple) -> None:
    common, _, output, _, state = environment
    common.write_text(common.read_text().replace("return nullptr", "return Bitvector", 1))
    with pytest.raises(ValueError, match="pinned Hydride"):
        diagnostic.materialize(common, output)
    assert not output.exists() and not state["calls"]


def test_complete_protocol_records_every_guard_and_exact_native_outcome(environment: tuple) -> None:
    common, llvm, output, compiler, state = environment
    result = diagnostic.run_diagnostic(common, llvm, output, compiler=compiler)
    assert result["status"] == "success", result
    assert result["exhaustive_value_cases"] == 197376
    assert result["rejected_shapes"] == 36
    assert len(result["results"]) == 44
    assert result["corpus_admission"] is False
    for _, _, options in state["calls"]:
        assert options["memory_limit_bytes"] == 5 * 1024**3
        assert options["disk_reserve_bytes"] == 2 * 1024**3
        assert options["require_guard"] and options["allow_warning_pressure"]
    for prefix in result["steps"]:
        assert Path(prefix + ".request.json").is_file()
        assert Path(prefix + ".result.json").is_file()
    compile_command = next(command for name, command, _ in state["calls"] if name == "compile")
    assert str(output / "concat-harness.cpp") in compile_command
    assert result["tools"][str(state["library"])] == hashlib.sha256(state["library"].read_bytes()).hexdigest()


@pytest.mark.parametrize("code,reason", [(0, None), (-6, None), (1, None), (86, "unrelated LLVM error")])
def test_rejection_requires_exact_fatal_protocol(environment: tuple, code: int, reason: str | None) -> None:
    common, llvm, output, compiler, state = environment
    state["rejection_code"] = code
    if reason:
        state["rejection_reason"] = reason
    result = diagnostic.run_diagnostic(common, llvm, output, compiler=compiler)
    assert result["status"] == "blocked"
    assert "exact source-fragment rejection" in result["reason"]
    assert state["calls"][-1][0] == "16-arity-two"


@pytest.mark.parametrize("kind,name", [("stop", "compile"), ("stop", "16-arity-two"), ("refuse", "compile")])
def test_safety_stop_retains_evidence_and_launches_no_followup(environment: tuple, kind: str, name: str) -> None:
    common, llvm, output, compiler, state = environment
    state[kind] = name
    result = diagnostic.run_diagnostic(common, llvm, output, compiler=compiler)
    assert result["status"] == ("memory-limit" if kind == "stop" else "launch-refused")
    assert state["calls"][-1][0] == name
    assert (output / "diagnostic.json").exists()
    assert not result["corpus_admission"]


@pytest.mark.parametrize("mutation", ["version", "partial", "change_library"])
def test_invalid_or_changed_evidence_never_succeeds(environment: tuple, mutation: str) -> None:
    common, llvm, output, compiler, state = environment
    state[mutation] = {"version": "17.0.6", "partial": "16-mapped-vector", "change_library": "8-mapped-width"}[mutation]
    result = diagnostic.run_diagnostic(common, llvm, output, compiler=compiler)
    assert result["status"] == "blocked" and result["reason"]
    assert "exhaustive_value_cases" not in result
