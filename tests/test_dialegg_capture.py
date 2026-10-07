"""DialEgg native invocation boundaries, source output contracts, and guarded replay capture."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from scripts import dialegg_capture as complete
from scripts.reproduction_process import PilotProcessResult


@pytest.mark.parametrize(
    "stdout,returncode,success",
    [
        ("(Chosen 2)\n(Chosen 1)\n", 0, True),
        ("(Chosen 2)\n", 0, False),
        ("(Chosen 2)\n(Chosen 1)\n(Extra)\n", 0, False),
        ("(Chosen\n 2)\n(Chosen 1)\n", 0, False),
        ("(Chosen 2)\n(Chosen 1)\n", 1, False),
        ("(union a b)\n(Chosen 1)\n", 0, False),
    ],
)
def test_native_delegate_preserves_real_ordered_responses_and_rejects_bad_contracts(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, stdout: str, returncode: int, success: bool
) -> None:
    raw = tmp_path / "invocation-0.egg"
    raw.write_text("(extract second)\n(extract first)\n")
    backend = tmp_path / "engine"
    backend.write_text("synthetic engine identity")

    def execute(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[Any]:
        assert command == [str(backend), str(raw)]
        assert "start_new_session" not in kwargs
        kwargs["stdout"].write(stdout.encode())
        kwargs["stderr"].write(b"retained native diagnostic\n")
        return subprocess.CompletedProcess(command, returncode)

    monkeypatch.setattr(complete.subprocess, "run", execute)
    out, err = tmp_path / "stdout", tmp_path / "stderr"
    assert complete.delegate_backend(backend, raw, out, err) == (0 if success else 1)
    manifest = json.loads(raw.with_suffix(".json").read_text())
    assert manifest["status"] == ("complete" if success else "failed")
    assert out.read_text() == stdout
    assert err.read_text() == "retained native diagnostic\n"
    assert manifest["extract_requests"] == [["(", "extract", "second", ")"], ["(", "extract", "first", ")"]]
    assert manifest["stdout_sha256"] == hashlib.sha256(stdout.encode()).hexdigest()


@pytest.mark.parametrize("mismatch", [False, True])
@pytest.mark.parametrize("cost_logs", [False, True])
def test_completed_native_parent_requires_actual_replay_outputs_including_zero_root_helpers(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mismatch: bool, cost_logs: bool
) -> None:
    source = tmp_path / "source"
    (source / "src").mkdir(parents=True)
    (source / "src/base.egg").write_text(
        "(datatype Op (Real) (Wrong))\n(function type-of (Op) Type)\n(function dims (Type) IntVec)"
    )
    inputs = source / "bench/vector_norm"
    inputs.mkdir(parents=True)
    (inputs / "vector_norm.mlir").write_text("module {}")
    (inputs / "vector_norm.egg").write_text('(include "src/base.egg")')
    output = tmp_path / "output"
    output.mkdir()
    binary = tmp_path / "frontend/egg-opt-complete"
    binary.parent.mkdir()
    monkeypatch.setattr(complete, "prepare_complete_dialegg", lambda *_: (binary, {}))
    commands: list[list[str]] = []

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: Any) -> PilotProcessResult:
        assert kwargs["require_guard"]
        commands.append(command)
        out, err = Path(str(prefix) + ".out"), Path(str(prefix) + ".err")
        out.write_text("")
        err.write_text("")
        if any(arg.startswith("DIALEGG_CAPTURE_DIR=") for arg in command):
            calls = Path(next(arg.split("=", 1)[1] for arg in command if arg.startswith("DIALEGG_CAPTURE_DIR=")))
            for index, suffix in enumerate(("", "(extract root)\n")):
                raw = calls / f"invocation-{index}.egg"
                raw.write_text('(include "src/base.egg")\n(let root (Real))\n(union root (Wrong))\n(run 1)\n' + suffix)
                raw.with_suffix(".json").write_text(
                    json.dumps(
                        {
                            "status": "complete",
                            **({"extract_costs": [1] if index else []} if cost_logs else {}),
                            "output_count": index,
                            "extract_requests": [["(", "extract", "root", ")"]] if index else [],
                            "output_terms": [["(", "Real", ")"]] if index else [],
                        }
                    )
                )
            Path(command[-1]).write_text("module { /* optimized */ }")
        elif command[0].endswith("mlir-opt"):
            Path(command[-1]).write_text("module { /* verified */ }")
        else:
            program = Path(command[-1]).read_text()
            assert ("(check " in program) == (cost_logs and "(extract " in program)
            if "(extract " in program:
                out.write_text("(Wrong)\n" if mismatch else "(Real)\n")
                if cost_logs:
                    assert command[:2] == ["env", "RUST_LOG=egglog::extract=debug"]
                    err.write_text("Best cost for the extract root: 1\n")
        return PilotProcessResult("success", 0, 0.0, 0, out, err, None)

    monkeypatch.setattr(complete, "run_bounded_command", run)
    args = argparse.Namespace(
        dialegg_source=source,
        llvm18_prefix=tmp_path,
        native_egglog=tmp_path / "native",
        egglog=tmp_path / "replay",
        timeout_sec=30,
    )
    case = "dialegg-runtime-vector_norm-eqsat"
    row = complete.capture_complete_dialegg(args, [case], output)["cases"][case]
    assert row["source_complete"]
    assert row["source_completion"]["status"] == "complete"
    assert row["ordinary_compatible"] == (not mismatch or cost_logs)
    assert row["status"] == ("ordinary-validation-failed" if mismatch and not cost_logs else "reproduced")
    assert row["materialization"] == {"complete": True, "expected_sessions": 2, "materialized_sessions": 2}
    assert len(row["workloads"]) == (0 if mismatch and not cost_logs else 2)
    assert row["invocations"][0]["output_contract"]["zero_root_helper"]
    if cost_logs:
        assert row["invocations"][1]["cost_validation"] == {
            "native_costs": [1],
            "replay_costs": [1],
            "exact_terms": not mismatch,
        }
    assert len(commands) == 3  # parent and both independent replays


def test_guard_preflight_refusal_is_durable_and_never_a_success(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    def refuse(*args: Any, **kwargs: Any) -> Any:
        raise ValueError("resource guard refused to launch: test refusal")

    monkeypatch.setattr(complete, "run_bounded_command", refuse)
    result = complete.run_complete_command(["never-launched"], tmp_path, tmp_path / "preflight", 30)
    assert result.status == "resource-stopped"
    assert result.returncode is None
    assert "resource guard refused" in result.stderr_path.read_text()


def test_low_disk_space_does_not_block_ordinary_replay(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(shutil, "disk_usage", lambda _: SimpleNamespace(free=0))
    result = complete.run_complete_command(
        [sys.executable, "-c", "print('completed')"], tmp_path, tmp_path / "low-disk", 10
    )
    assert result.status == "success"
    assert result.stdout_path.read_text() == "completed\n"


@pytest.mark.parametrize("logged_term", ["(Chosen 2)", "(Chosen 999)"])
def test_native_cost_logs_are_enabled_and_bound_to_the_exact_response(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, logged_term: str
) -> None:
    raw, backend = tmp_path / "invocation.egg", tmp_path / "backend"
    raw.write_text("(extract root)")
    backend.write_text("synthetic engine")

    def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[Any]:
        assert kwargs["env"]["RUST_LOG"] == "info"
        kwargs["stdout"].write(b"(Chosen 2)\n")
        kwargs["stderr"].write(f"[INFO ] extracted with cost 2: {logged_term}\n".encode())
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(complete.subprocess, "run", run)
    assert complete.delegate_backend(backend, raw, tmp_path / "stdout", tmp_path / "stderr") == 0
    manifest = json.loads(raw.with_suffix(".json").read_text())
    if logged_term == "(Chosen 2)":
        assert manifest["extract_costs"] == [2]
    else:
        assert "extract_costs" not in manifest and "cost_evidence_unavailable" in manifest


@pytest.mark.parametrize("root", ["root", "(reproduction_root_0)", "(Cons (Child 1) (Nil))"])
@pytest.mark.parametrize("variants", ["", " 0"])
def test_best_extraction_accepts_existing_value_handles_and_expressions(root: str, variants: str) -> None:
    source = f"(extract {root}{variants})\n(extract second)\n"
    assert complete.validate_extract_output(source, "(Chosen 1)\n(Chosen 2)\n", line_protocol=True) == [
        ["(", "Chosen", "1", ")"],
        ["(", "Chosen", "2", ")"],
    ]
    with pytest.raises(ValueError, match="count"):
        complete.validate_extract_output(source, "(Chosen 1)\n")
    with pytest.raises(ValueError, match="one output line"):
        complete.validate_extract_output(source, "(Chosen\n1)\n(Chosen 2)\n", line_protocol=True)


@pytest.mark.parametrize("arguments", ["", "root 1", "(root) 1", "(root) 0 extra", "root other", "(root) (other)"])
def test_best_extraction_rejects_multiple_roots_or_nonzero_variants(arguments: str) -> None:
    with pytest.raises(ValueError, match="unsupported source extraction contract"):
        complete.validate_extract_output(f"(extract {arguments})", "(Chosen)\n")
