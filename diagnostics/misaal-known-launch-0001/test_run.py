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
