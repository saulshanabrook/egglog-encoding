"""Durable source-script generation and mocked guarded execution; never native jobs."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from scripts import reproduction_misaal_abi_gate as gate
from tests.test_reproduction_misaal_patterns import (
    _CURRENT_PARAMETER_SOURCE,
    _PARAMETER_RACKET_SOURCE,
    _RACKET_COND_SOURCE,
)


@pytest.fixture
def prepared(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    """Reuse verbatim source excerpts already verified against retained source hashes."""
    checkout = tmp_path / "checkout"
    source = checkout / "lib/patterns/PatternUtils.py"
    source.parent.mkdir(parents=True)
    source.write_text(_CURRENT_PARAMETER_SOURCE + '\nraise RuntimeError("module population imports must not run")\n')
    racket_source = checkout / "misaal/synthesis/param_abstract.rkt"
    racket_source.parent.mkdir(parents=True)
    racket_source.write_text(_PARAMETER_RACKET_SOURCE)
    oracle = (gate.FIXTURES / "c098-ordinary-depth2.rkt").read_text()
    header = oracle.split("(define param-test-cases", 1)[0][:-1]
    helper = checkout / gate.SOURCE
    helper.parent.mkdir(parents=True)
    helper.write_text(f"HYDRIDE_HEADER = {header!r}\n" + _RACKET_COND_SOURCE + '\nraise RuntimeError("no imports")\n')
    source_pins = {
        str(path.relative_to(checkout)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in (source, racket_source)
    }
    monkeypatch.setattr(gate.adaptation, "PARAMETER_ABI_SOURCE_SHA256", source_pins)
    monkeypatch.setattr(gate, "SOURCE_SHA256", hashlib.sha256(helper.read_bytes()).hexdigest())
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
        "ordinary-depth2-unadapted",
        "general-depth1-unadapted",
    }
    for name in ("ordinary-depth2", "general-depth1"):
        assert (
            Path(manifest["programs"][name]["path"]).read_bytes() == (gate.FIXTURES / f"c098-{name}.rkt").read_bytes()
        )
        unchanged = Path(manifest["programs"][name + "-unadapted"]["path"]).read_text()
        assert ("(list 1) #t)" if name.startswith("general") else "(list 1) #f)") in unchanged
    assert all(path.read_bytes() == contents for path, contents in before.items())
    assert manifest["adaptation_receipt"]["parameter_abi"]["status"] == "complete"
    with pytest.raises(ValueError, match="fresh"):
        gate.prepare_programs(prepared["checkout"], prepared["output"])
