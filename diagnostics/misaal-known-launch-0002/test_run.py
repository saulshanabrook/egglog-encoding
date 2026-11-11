"""Prepared real safety fixtures are tested here without executing children."""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path

import pytest

spec = importlib.util.spec_from_file_location("misaal_known_launch_native_fixture", Path(__file__).with_name("run.py"))
assert spec is not None and spec.loader is not None
diagnostic = importlib.util.module_from_spec(spec)
spec.loader.exec_module(diagnostic)


def test_materialize_freezes_source_fixture_and_tools_without_spawning(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = tmp_path / "DSLInstructionUtils.py"
    source.write_text("pinned fixture source")
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    monkeypatch.setattr(diagnostic.groups, "SOURCE_SHA256", digest)
    monkeypatch.setattr(
        diagnostic.subprocess, "Popen", lambda *_a, **_kw: pytest.fail("materialization must not spawn")
    )
    output = tmp_path / "evidence"
    record = diagnostic.materialize(source, output)
    assert record["status"] == "materialized-unrun"
    assert record["inputs"][str(source)] == digest
    assert record["cases"] == [] and "no Racket/Rosette" in record["scope"]
    for mode in diagnostic.CASES:
        assert json.loads((output / mode / "fixture.json").read_text()) == {"mode": mode}
        assert hashlib.sha256((output / mode / "fixture.rkt").read_bytes()).hexdigest() == record["fixture_sha256"]
    with pytest.raises(FileExistsError):
        diagnostic.materialize(source, output)


def test_materialize_rejects_changed_original_source(tmp_path: Path) -> None:
    source = tmp_path / "DSLInstructionUtils.py"
    source.write_text("not the native pinned function")
    with pytest.raises(ValueError, match="exact pinned"):
        diagnostic.materialize(source, tmp_path / "evidence")
    assert not (tmp_path / "evidence").exists()


def test_real_fixture_contains_resistant_grandchild_and_aggregate_allocations() -> None:
    source = diagnostic.RACKET_STAND_IN
    assert "signal.signal(signal.SIGTERM, signal.SIG_IGN)" in source
    assert 'subprocess.Popen([sys.executable, __file__, "grandchild"])' in source
    assert "128 * 1024**2" in source
    assert "start_new_session" not in source  # Racket/solver descendants retain the registered group.


def test_fixture_uses_exact_full_module_function_code(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    from types import SimpleNamespace

    source = tmp_path / "checkout/lib/utils/DSLInstructionUtils.py"
    source.parent.mkdir(parents=True)
    source.write_text(
        "import subprocess\n"
        "class HelperCompletedProcess:\n"
        "    def __init__(self, returncode=1): self.returncode=returncode\n"
        "def run_command_child_processes(cmd, timeout=5):\n"
        "    proc=subprocess.Popen(cmd, start_new_session=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)\n"
        "    proc.wait(timeout=timeout)\n"
        "    return HelperCompletedProcess(proc.returncode)\n"
    )
    monkeypatch.setattr(diagnostic.groups, "SOURCE_SHA256", hashlib.sha256(source.read_bytes()).hexdigest())
    output = tmp_path / "evidence"
    diagnostic.materialize(source, output)
    monkeypatch.setenv("PATH", "unchanged original PATH")
    monkeypatch.setattr(diagnostic.groups.shutil, "which", lambda _: str(output / "bin/racket"))
    calls = []

    def launch(command: list, endpoint: Path, python: str, **kwargs: object) -> object:
        calls.append((command, endpoint, python, kwargs))
        return SimpleNamespace(returncode=7, wait=lambda **_kw: None)

    monkeypatch.setattr(diagnostic.groups, "launch_registered", launch)
    monkeypatch.setattr(diagnostic.time, "sleep", lambda _: None)
    monkeypatch.setattr(
        diagnostic.subprocess, "Popen", lambda *_a, **_k: pytest.fail("native fixture must remain mocked")
    )
    case = output / "return-code"
    assert diagnostic.child("return-code", source, case, tmp_path / "socket") == 0
    assert calls[0][0] == ["racket", str(case / "fixture.rkt")]
    assert json.loads((case / "source-result.json").read_text()) == {"returncode": 7, "parent_alive": True}


def test_fixture_retains_failing_phase_and_traceback_through_successful_cleanup(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from types import SimpleNamespace

    source = tmp_path / "source.py"
    source.write_text("pinned mock")
    monkeypatch.setattr(diagnostic.groups, "SOURCE_SHA256", hashlib.sha256(source.read_bytes()).hexdigest())
    events = []
    registry = SimpleNamespace(endpoint=tmp_path / "socket", closed=False, sample=lambda _: 0)

    def close() -> None:
        events.append("registry close")
        registry.closed = True

    registry.close = close
    monkeypatch.setattr(diagnostic.groups, "RacketGroups", lambda _: registry)
    monkeypatch.setattr(
        diagnostic.subprocess,
        "Popen",
        lambda *_a, **_k: SimpleNamespace(
            kill=lambda: events.append("bystander kill"), wait=lambda: events.append("bystander wait")
        ),
    )

    def denied(*_a: object, **_kw: object) -> object:
        raise PermissionError(1, "fixture exact failing site")

    monkeypatch.setattr(diagnostic, "run_bounded_command", denied)
    record = diagnostic.run_diagnostic(source, tmp_path / "results")
    assert record["status"] == "failure"
    assert record["failure_phase"] == "return-code: guarded native fixture"
    assert "PermissionError" in record["traceback"] and "fixture exact failing site" in record["traceback"]
    assert events == ["registry close", "bystander kill", "bystander wait"]
