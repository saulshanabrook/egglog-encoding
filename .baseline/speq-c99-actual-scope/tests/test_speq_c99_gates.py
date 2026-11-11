"""Mocked orchestration and exact-output checks; these tests never invoke LLVM."""

from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any, Literal

import pytest

from benchmarking.pilot import PilotProcessResult
from scripts import speq_c99_gates as gates


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


@pytest.fixture(autouse=True)
def forbid_native(monkeypatch: pytest.MonkeyPatch) -> None:
    def forbidden(*args: Any, **kwargs: Any) -> None:
        pytest.fail("unexpected native launch in mocked gate tests")

    monkeypatch.setattr(subprocess, "run", forbidden)
    monkeypatch.setattr(subprocess, "Popen", forbidden)


@pytest.fixture
def inputs(tmp_path: Path) -> tuple[Path, Path, Path]:
    source, artifact, llvm = tmp_path / "source", tmp_path / "artifact", tmp_path / "llvm-config"
    paths = [
        source / name
        for name in (
            "llvm/lib/Analysis/REVPass.cpp",
            "llvm/include/llvm/Analysis/REVPass.h",
            "llvm/include/llvm/Analysis/MemorySSA.h",
        )
    ]
    paths += [artifact / "analysis" / f"{name}.ll" for name in gates.recorder.REFERENCE_ANALYSIS_SHA256]
    paths += [
        artifact / "benchmarks" / name for name in ("polybench_gemm.c", *gates.recorder.APPLICATION_HEADER_SHA256)
    ]
    for path in [*paths, llvm]:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(path.name)
    return source, artifact, llvm


def successful_child(command: list[str]) -> PilotProcessResult:
    """Model only the child receipt boundary; never claim real compilation."""
    request_path = Path(command[-1])
    request = json.loads(request_path.read_text())
    directory = request_path.parent
    evidence: dict[str, Any] = {"mock": True}
    if request["kind"] == "build":
        plugin = directory / "plugin.so"
        plugin.write_text("mock plugin")
        metadata = directory / "diagnostic.json"
        metadata.write_text("mock source metadata")
        evidence = {
            "artifacts": {str(plugin): digest(plugin)},
            "materialization": {"path": str(metadata), "sha256": digest(metadata)},
        }
    (directory / "result.json").write_text(
        json.dumps({"status": "success", "request_sha256": digest(request_path), "evidence": evidence})
    )
    stdout, stderr = directory / "guard.stdout", directory / "guard.stderr"
    stdout.write_text("")
    stderr.write_text("")
    return PilotProcessResult("success", 0, 0.1, 100, stdout, stderr, None)


def test_full_gate_sequence_is_guarded_fresh_and_non_admitting(inputs: tuple[Path, Path, Path], tmp_path: Path) -> None:
    calls = []
    before = {p: p.read_bytes() for root in inputs[:2] for p in root.rglob("*") if p.is_file()}

    def step(name: str, command: list[str]) -> PilotProcessResult:
        calls.append((name, json.loads(Path(command[-1]).read_text())))
        assert command[:3] == ["/usr/bin/env", "-u", gates.c99.ENABLE_ENV]
        assert command[-3:-1] == ["-m", "scripts.speq_c99_gates"]
        return successful_child(command)

    output = tmp_path / "gates"
    result = gates.run_gates(*inputs, output, step)
    assert result["status"] == "success" and result["inputs_unchanged"] is True
    assert result["corpus_admission"] is False
    assert result["contract"] == gates.c99.CONTRACT and result["selected_function"] == gates.c99.FUNCTION
    assert len(calls) == len(result["gates"]) == 31
    assert calls[0][0] == "c99-build" and calls[-1][0] == "c99-fresh-original-c"
    assert [request["name"] for _, request in calls if request["kind"] == "fixture"] == list(gates.c99.fixture_cases())
    references = [(request["variant"], request["name"]) for _, request in calls if request["kind"] == "reference"]
    assert references == [
        (variant, name) for variant in ("baseline", "candidate") for name in gates.recorder.REFERENCE_ANALYSIS_SHA256
    ]
    assert [request["name"] for _, request in calls if request["kind"] == "selection"] == [
        "missing",
        "duplicate",
        "invalid-enable",
        "empty",
        "unrelated",
    ]
    assert all(path.read_bytes() == data for path, data in before.items())
    assert json.loads((output / "result.json").read_text()) == json.loads(json.dumps(result, default=str))
    for path, expected in result["artifacts"].items():
        assert digest(Path(path)) == expected
    with pytest.raises(FileExistsError):
        gates.run_gates(*inputs, output, step)


@pytest.mark.parametrize("status", ["timed-out", "memory-limit", "resource-stopped"])
def test_guard_stop_is_terminal_and_retained(
    inputs: tuple[Path, Path, Path], tmp_path: Path, status: Literal["timed-out", "memory-limit", "resource-stopped"]
) -> None:
    calls = []

    def step(name: str, command: list[str]) -> PilotProcessResult:
        calls.append(name)
        result = successful_child(command)
        return PilotProcessResult(
            status, None, result.wall_sec, 100, result.stdout_path, result.stderr_path, "guard stop"
        )

    with pytest.raises(ValueError, match="guarded gate failed"):
        gates.run_gates(*inputs, tmp_path / "gates", step)
    receipt = json.loads((tmp_path / "gates/result.json").read_text())
    assert receipt["status"] == receipt["process"]["status"] == status
    assert receipt["corpus_admission"] is False and calls == ["c99-build"]


@pytest.mark.parametrize(
    "mode", ["raised-stop", "interrupted", "request-hash", "child-failure", "plugin-hash", "input-drift"]
)
def test_failure_evidence_is_preserved_and_no_later_gate_runs(
    inputs: tuple[Path, Path, Path], tmp_path: Path, mode: str
) -> None:
    calls = []

    def step(name: str, command: list[str]) -> PilotProcessResult:
        calls.append(name)
        if mode == "raised-stop":
            raise RuntimeError("caller retained resource-stopped process")
        if mode == "interrupted":
            raise KeyboardInterrupt()
        process = successful_child(command)
        directory = Path(command[-1]).parent
        path = directory / "result.json"
        receipt = json.loads(path.read_text())
        if mode == "request-hash":
            receipt["request_sha256"] = "wrong"
        elif mode == "child-failure":
            receipt["status"] = "blocked"
        elif mode == "plugin-hash":
            (directory / "plugin.so").write_text("mutated")
        elif mode == "input-drift":
            inputs[2].write_text("changed tool")
        path.write_text(json.dumps(receipt))
        return process

    with pytest.raises((ValueError, RuntimeError, KeyboardInterrupt)):
        gates.run_gates(*inputs, tmp_path / "gates", step)
    receipt = json.loads((tmp_path / "gates/result.json").read_text())
    assert receipt["status"] == "blocked" and receipt["corpus_admission"] is False
    assert "reason" in receipt and calls == ["c99-build"]


def test_missing_input_retains_terminal_receipt(inputs: tuple[Path, Path, Path], tmp_path: Path) -> None:
    inputs[2].unlink()
    with pytest.raises(FileNotFoundError):
        gates.run_gates(*inputs, tmp_path / "gates", lambda *_: pytest.fail("must not launch"))
    assert json.loads((tmp_path / "gates/result.json").read_text())["status"] == "blocked"


BASE_OUTPUT = """memory-type: ptr 1 double
%n64 = zext i32 %n to i64
%row64 = zext i32 %row to i64
%j64 = zext i32 %j to i64
%row.offset = mul nuw nsw i64 %row64, %n64
%reproduction.c99.offset.0 = add nsw i64 %row.offset, %j64
%element = getelementptr inbounds double, ptr %C, i64 %reproduction.c99.offset.0
LLVM module unchanged
"""


@pytest.mark.parametrize("mode", ["valid", "missing-closure", "wrong-address", "duplicate-offset", "changed-module"])
def test_positive_fixture_exact_address_closure(mode: str) -> None:
    output = BASE_OUTPUT
    if mode == "missing-closure":
        output = output.replace("%j64 = zext i32 %j to i64\n", "")
    elif mode == "wrong-address":
        output = output.replace("ptr %C, i64 %reproduction", "ptr %B, i64 %reproduction")
    elif mode == "duplicate-offset":
        output += "%reproduction.c99.offset.1 = add nsw i64 %row.offset, %j64\n"
    elif mode == "changed-module":
        output = output.replace("LLVM module unchanged", "LLVM module mutated")
    if mode == "valid":
        gates.fixture_output("positive", output)
    else:
        with pytest.raises(ValueError):
            gates.fixture_output("positive", output)


@pytest.mark.parametrize(
    "returncode,error,stderr,accept",
    [
        (0, None, "", True),
        (1, None, "bad", False),
        (1, "reviewed", "reviewed rejection", True),
        (0, "reviewed", "reviewed", False),
        (-9, "reviewed", "reviewed", False),
        (-15, "reviewed", "reviewed", False),
        (1, "reviewed", "other", False),
    ],
)
def test_rejections_cannot_hide_failure_or_stop(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, returncode: int, error: str | None, stderr: str, accept: bool
) -> None:
    def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        assert command == ["mock-native"] and kwargs["check"] is False
        assert "start_new_session" not in kwargs and "preexec_fn" not in kwargs
        assert gates.c99.ENABLE_ENV not in kwargs["env"]
        kwargs["stderr"].write(stderr.encode())
        return subprocess.CompletedProcess(command, returncode)

    monkeypatch.setenv(gates.c99.ENABLE_ENV, "ambient-must-be-removed")
    monkeypatch.setattr(subprocess, "run", run)
    if accept:
        assert gates._process(["mock-native"], tmp_path / "native", error=error)["returncode"] == returncode
    else:
        with pytest.raises(ValueError):
            gates._process(["mock-native"], tmp_path / "native", error=error)
    assert json.loads((tmp_path / "native/process.json").read_text())["returncode"] == returncode


def test_fresh_frontends_use_exact_scoped_flags_and_full_comparison(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    calls = []

    def application(*args: Any, **kwargs: Any) -> list[str]:
        calls.append((args, kwargs))
        return ["same0", "same1", "repaired" if kwargs["c99_frontend_repair"] else "original"]

    def compare(baseline: list[str], candidate: list[str], left: Path, right: Path) -> dict[str, bool]:
        assert baseline == ["same0", "same1", "original"] and candidate == ["same0", "same1", "repaired"]
        assert left.name == "baseline" and right.name == "candidate"
        return {"all_regions_compared": True}

    monkeypatch.setattr(gates.recorder, "application_fir", application)
    monkeypatch.setattr(gates.c99, "compare_frontends", compare)
    row = gates._child(
        {
            "kind": "frontend",
            "artifact": str(tmp_path),
            "build": {"opt": "opt", "baseline_plugin": "phi.so", "candidate_plugin": "candidate.so"},
        },
        tmp_path,
    )
    assert row["disabled_regions_byte_identical"] is True and row["source_complete"] is False
    assert [call[1]["c99_frontend_repair"] for call in calls] == [False, False, True]
    assert all(
        call[0][3] == "polybench_gemm"
        and call[1]["complete"] is True
        and call[1]["frontend_flags"] == gates.c99.FRONTEND_FLAGS
        for call in calls
    )


@pytest.mark.parametrize(
    "fault",
    [
        None,
        "enabled-reference",
        "disabled-reference",
        "extra-region",
        "missing-region",
        "trailing-error",
        "missing-closure",
        "wrong-address",
        "untyped",
        "unchanged-selected",
        "reversed-regions",
    ],
)
def test_unrelated_control_keeps_reference_and_exercises_valid_selected_definition(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, fault: str | None
) -> None:
    reference = tmp_path / "artifact/analysis/gemv.ll"
    reference.parent.mkdir(parents=True)
    original = 'target datalayout = "e-p:64:64"\ndefine void @gemv() { ret void }\n'
    reference.write_text(original)
    monkeypatch.setattr(gates.recorder, "REFERENCE_ANALYSIS_SHA256", {"gemv": digest(reference)})
    original_fir = "original unrelated GEMV\n"
    monkeypatch.setattr(gates.recorder, "REFERENCE_FIR_SHA256", {"gemv": gates.recorder.sha256_text(original_fir)})
    selected_fir = "\n".join(
        [
            "%body = λ ptr 1 double %C, i32 %j .",
            "  %n64 = zext i32 %n to i64",
            "  %row64 = zext i32 %row to i64",
            "  %reproduction.c99.offset.0 = add nsw i64 %row.offset, %j64",
            "  %element = getelementptr inbounds double, ptr %C, i64 %reproduction.c99.offset.0",
            "",
        ]
    )
    commands = []

    def process(command: list[str], directory: Path, **kwargs: Any) -> dict[str, Any]:
        commands.append((command, kwargs))
        enabled = kwargs.get("enabled") == "1"
        regions = [original_fir, selected_fir if enabled else "original selected untyped loop\n"]
        if fault == ("enabled-reference" if enabled else "disabled-reference"):
            regions[0] = "changed reference\n"
        if enabled:
            if fault == "extra-region":
                regions.append("unaccounted function\n")
            elif fault == "missing-region":
                regions.pop()
            elif fault == "missing-closure":
                regions[1] = regions[1].replace("  %row64 = zext i32 %row to i64\n", "")
            elif fault == "wrong-address":
                regions[1] = regions[1].replace("ptr %C, i64", "ptr %B, i64")
            elif fault == "untyped":
                regions[1] = regions[1].replace("ptr 1 double %C", "ptr %C")
            elif fault == "unchanged-selected":
                regions[1] = "original selected untyped loop\n"
            elif fault == "reversed-regions":
                regions.reverse()
        text = "".join(f"REV Start\n{region}REV End\n" for region in regions)
        if enabled and fault == "trailing-error":
            text += "LLVM ERROR: a real native failure\n"
        directory.mkdir()
        stderr = directory / "stderr.log"
        stderr.write_text(text)
        return {"stderr": str(stderr), "returncode": 0, "command": command}

    monkeypatch.setattr(gates, "_process", process)
    output = tmp_path / "gate"
    output.mkdir()
    request = {
        "kind": "selection",
        "name": "unrelated",
        "artifact": str(reference.parents[1]),
        "build": {"opt": "mock-opt", "candidate_plugin": "candidate.so"},
    }
    if fault:
        with pytest.raises(ValueError):
            gates._child(request, output)
    else:
        result = gates._child(request, output)
        assert result["classification"] == "unrelated-unchanged-selected-repaired"
        assert result["composition"]["function_order"] == ["gemv", gates.c99.FUNCTION]
        assert result["region_sha256"][0][0] == result["region_sha256"][1][0]
    positive = (gates.c99.SUPPORT / "speq_c99_fixture.ll").read_text()
    definition = positive[positive.index("define void @guarded_stride(") :]
    assert (output / "input.ll").read_text() == original + definition.replace(
        "@guarded_stride(", f"@{gates.c99.FUNCTION}(", 1
    )
    assert len(commands) == 2 and commands[0][0] == commands[1][0]
    assert [kwargs.get("enabled") for _, kwargs in commands] == ["1", None]


def test_empty_selected_control_remains_a_domain_rejection(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    source = "define void @gemv() { ret void }\n"
    monkeypatch.setattr(gates.recorder, "read_verified", lambda *_: source)
    calls = []

    def process(command: list[str], output: Path, **kwargs: Any) -> dict[str, Any]:
        calls.append(kwargs)
        assert Path(command[-2]).read_text() == source + f"define void @{gates.c99.FUNCTION}() {{ ret void }}\n"
        return {"returncode": -6}

    monkeypatch.setattr(gates, "_process", process)
    result = gates._child(
        {
            "kind": "selection",
            "name": "empty",
            "artifact": str(tmp_path),
            "build": {"opt": "mock-opt", "candidate_plugin": "candidate.so"},
        },
        tmp_path,
    )
    assert result["classification"] == "selection-rejection"
    assert calls == [{"enabled": "1", "error": "REV C99 address domain: selected function has no chained GEP"}]
