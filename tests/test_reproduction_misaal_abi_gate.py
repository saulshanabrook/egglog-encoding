"""Durable source-script generation and mocked guarded execution; never native jobs."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from scripts import reproduction_misaal_abi_gate as gate
from tests.test_reproduction_misaal_patterns import (
    _PAPER_PARAMETER_SOURCE,
    _RACKET_COND_SOURCE,
)


@pytest.fixture
def prepared(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    """Reuse verbatim source excerpts already verified against retained source hashes."""
    checkout = tmp_path / "checkout"
    source = checkout / "lib/patterns/PatternUtils.py"
    source.parent.mkdir(parents=True)
    source.write_text(_PAPER_PARAMETER_SOURCE + '\nraise RuntimeError("module population imports must not run")\n')
    oracle = (gate.FIXTURES / "c098-ordinary-depth2.rkt").read_text()
    header = oracle.split("(define param-test-cases", 1)[0][:-1]
    helper = checkout / gate.SOURCE
    helper.parent.mkdir(parents=True)
    helper.write_text(f"HYDRIDE_HEADER = {header!r}\n" + _RACKET_COND_SOURCE + '\nraise RuntimeError("no imports")\n')
    source_pins = {
        str(path.relative_to(checkout)): hashlib.sha256(path.read_bytes()).hexdigest() for path in (source, helper)
    }
    monkeypatch.setattr(gate, "EXPORT_SOURCE_SHA256", source_pins)
    return {"checkout": checkout, "output": tmp_path / "abi-programs"}


def test_captured_fixture_is_exact_source_diagnostic() -> None:
    original = gate.FIXTURES / "ki4k2nlc.rkt"
    assert hashlib.sha256(original.read_bytes()).hexdigest() == gate.CAPTURED_SHA256
    assert original.read_bytes().count(b"(TESTS ") == 28
    assert original.read_bytes().count(b"(synthesize-param-expression param-test-cases 2 3 (list ) #f)") == 1
    provenance = json.loads((gate.FIXTURES / "provenance.json").read_text())
    assert provenance["files"] == gate.FIXTURE_SHA256
    assert provenance["admitted"] is False and "not benchmark" in provenance["scope"]


def test_offline_generation_uses_source_and_exact_paper_bytes(prepared: dict[str, Any]) -> None:
    source_files = [path for path in prepared["checkout"].rglob("*") if path.is_file()]
    before = {path: path.read_bytes() for path in source_files}
    manifest = gate.prepare_programs(prepared["checkout"], prepared["output"])
    assert set(manifest["programs"]) == {
        "ordinary-depth2",
        "general-depth1",
    }
    for name in ("ordinary-depth2", "general-depth1"):
        assert (
            Path(manifest["programs"][name]["path"]).read_bytes() == (gate.FIXTURES / f"c098-{name}.rkt").read_bytes()
        )
    assert all(path.read_bytes() == contents for path, contents in before.items())
    assert all(program["expected_exit"] == 0 for program in manifest["programs"].values())
    with pytest.raises(ValueError, match="fresh"):
        gate.prepare_programs(prepared["checkout"], prepared["output"])
