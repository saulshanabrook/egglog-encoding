"""The canary preparer changes one request field and retains every binding."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from scripts import reproduction_prepare_misaal_pattern_canary as canary


@pytest.fixture
def source(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[Path, dict[str, Any], dict[str, Any]]:
    requests = tmp_path / "original/requests"
    requests.mkdir(parents=True)
    source = tmp_path / "source/lib/patterns"
    source.mkdir(parents=True)
    request = {
        "case_id": canary.CASE,
        "source": "benchmarks/hexagon/halide/blur3x3",
        "configuration": {"target": "hexagon"},
        "revision": "44ff893445d664cd87f52b08a138260ed2015ba8",
        "checkout": str(tmp_path / "source"),
        "environment": {"UNCHANGED": "value"},
        "source_hashes": {"input": "source-hash"},
        "generator_sha256": "generator-hash",
        "pattern_cache_contract": {"environment": "MISAAL_PATTERN_CACHE_DIR", "generation": "unchanged"},
        "identity_paths": ["source-identity"],
        "hvx_link_contract": {"opaque": "unchanged"},
    }
    (requests / f"{canary.CASE}.json").write_text(json.dumps(request))
    settings = {
        "revision": request["revision"],
        "paths": {"requests": str(requests), "egglog": "bound-engine"},
        "identity_paths": ["retained-settings-identity"],
        "timeout_sec": 300,
        "configuration_blockers": [],
    }
    path = requests.parent / "settings.json"
    path.write_text(json.dumps({"misaal": settings, "another-family": {"unchanged": True}}))
    monkeypatch.setattr(canary, "verified_request", lambda path: json.loads(path.read_text()))
    return path, request, settings


def test_immutable_subset_and_provenance(source: tuple[Path, dict[str, Any], dict[str, Any]], tmp_path: Path) -> None:
    path, original, original_settings = source
    original_bytes = path.read_bytes()
    output = tmp_path / "canary"
    receipt = canary.prepare_pattern_canary(path, output, root=tmp_path)
    request = json.loads((output / f"requests/{canary.CASE}.json").read_text())
    assert request.pop("pattern_deduplication") == "exact-render-last-v1"
    assert request == original
    settings = json.loads((output / "settings.json").read_text())["misaal"]
    assert settings["paths"].pop("requests") == str(output / "requests")
    assert settings["identity_paths"].pop() == str(output / "provenance.json")
    expected = json.loads(json.dumps(original_settings))
    expected["paths"].pop("requests")
    assert settings == expected
    assert path.read_bytes() == original_bytes == (output / "original-settings.json").read_bytes()
    assert list((output / "requests").iterdir()) == [output / f"requests/{canary.CASE}.json"]
    assert receipt["status"] == "request-prepared" and receipt["native_execution"] is False
    assert all(hashlib.sha256((output / p).read_bytes()).hexdigest() == sha for p, sha in receipt["artifacts"].items())
    assert not list(output.rglob("*.pickle"))
    with pytest.raises(FileExistsError):
        canary.prepare_pattern_canary(path, output, root=tmp_path)


@pytest.mark.parametrize("change", ["wrong-case", "already-flagged", "warm-environment", "warm-source"])
def test_invalid_original_refused(
    source: tuple[Path, dict[str, Any], dict[str, Any]], tmp_path: Path, change: str
) -> None:
    path, request, settings = source
    if change == "wrong-case":
        request["case_id"] = "different"
    elif change == "already-flagged":
        request["pattern_deduplication"] = canary.CONTRACT
    elif change == "warm-environment":
        request["environment"]["MISAAL_PATTERN_CACHE_DIR"] = "warm"
    else:
        (Path(request["checkout"]) / "lib/patterns/halide.pickle").write_text("not loaded")
    (Path(settings["paths"]["requests"]) / f"{canary.CASE}.json").write_text(json.dumps(request))
    with pytest.raises(ValueError):
        canary.prepare_pattern_canary(path, tmp_path / "canary", root=tmp_path)
    assert not (tmp_path / "canary").exists()
