"""Project selected paper metadata without collecting or preparing source inputs."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from benchmarking.figures import _figure_inventory

ROOT = Path(__file__).resolve().parents[1]


def corpus_fixture(root: Path) -> dict[str, Any]:
    directory = root / "benchmarks/corpus"
    corpus: dict[str, Any] = {"sources": {}, "cases": [], "workloads": []}
    sources = [
        ("math", (ROOT / "egglog-experimental/tests/math-microbenchmark-rational.egg").read_bytes()),
        ("eggcc", b"(datatype Expr (A))\n(let root (A))\n(extract root)\n"),
        ("hardboiled", b"(datatype Expr (B))\n(let root (B))\n(extract root)\n"),
    ]
    for family, source in sources:
        file = f"{family}/{family}-call-01.egg"
        path = directory / file
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(source)
        corpus["workloads"].append(
            {
                "file": file,
                "sha256": "sha256:" + hashlib.sha256(source).hexdigest(),
                "facts_sha256": "",
                "aliases": [{"case": family, "order": 0}],
            }
        )
        corpus["cases"].append(
            {
                "id": family,
                "family": family,
                "status": "ready",
                "workloads": [file],
                "reason": None,
            }
        )
    corpus["cases"].append(
        {
            "id": "missing-source",
            "family": "misaal",
            "status": "blocked",
            "workloads": [],
            "reason": "Source dependency is unavailable",
        }
    )
    (directory / "manifest.json").write_text(json.dumps(corpus))
    return corpus


def test_inventory_keeps_source_blockers_separate(tmp_path: Path) -> None:
    corpus = corpus_fixture(tmp_path)
    inventory = _figure_inventory(tmp_path, 300)
    assert len(inventory["workloads"]) == 3
    assert inventory["unavailable_cases"][0]["reason"] == "Source dependency is unavailable"
    assert inventory["workloads"][0]["file_sha256"] == corpus["workloads"][0]["sha256"]
    assert not (tmp_path / ".reports.jsonl").exists()
    assert not (tmp_path / "benchmarks/local/figure-inventory.json").exists()
    corpus["cases"][-1]["reason"] = "New source evidence"
    (tmp_path / "benchmarks/corpus/manifest.json").write_text(json.dumps(corpus))
    assert _figure_inventory(tmp_path, 300)["unavailable_cases"][0]["reason"] == "New source evidence"


def test_strict_metadata_is_identity_bound_and_can_be_cleared(tmp_path: Path) -> None:
    corpus = corpus_fixture(tmp_path)
    item = corpus["workloads"][0]
    outcome = {
        "file_sha256": item["sha256"],
        "fact_directory_sha256": "",
        "binary_sha256": "sha256:engine",
        "timeout_sec": 300,
        "disequality_encoding": "nee",
        "kind": "validation",
        "policy": "proof-testing-v1",
        "status": "failure",
        "reason": "Strict replay failed",
    }
    path = tmp_path / "benchmarks/corpus/.local/outcomes.json"
    path.parent.mkdir()
    path.write_text(json.dumps([outcome]))
    assert _figure_inventory(tmp_path, 300)["workloads"][0]["validation_failures"] == {
        "sha256:engine/300/nee": "Strict replay failed",
    }
    assert _figure_inventory(tmp_path, 120)["workloads"][0]["validation_failures"] == {}
    path.write_text(json.dumps([outcome, {**outcome, "status": "success"}]))
    assert _figure_inventory(tmp_path, 300)["workloads"][0]["validation_failures"] == {}


def test_metadata_only_validates_selected_corpus_inputs(tmp_path: Path) -> None:
    from benchmarking.models import FileSpec

    corpus = corpus_fixture(tmp_path)
    item = corpus["workloads"][0]
    directory = tmp_path / "benchmarks/corpus"
    item["aliases"].append({"case": "eggcc", "order": 1})
    corpus["cases"][1]["workloads"].append(item["file"])
    manifest = directory / "manifest.json"
    manifest.write_text(json.dumps(corpus))
    published = manifest.read_bytes()
    (directory / corpus["workloads"][1]["file"]).unlink()
    selected = FileSpec(item["file"], (directory / item["file"]).resolve(), item["sha256"])
    inventory = _figure_inventory(tmp_path, 300, [selected])
    assert len(inventory["workloads"]) == 1
    assert inventory["workloads"][0]["label"] == "math"
    assert inventory["workloads"][0]["family"] == "math"
    assert manifest.read_bytes() == published
    with pytest.raises(ValueError, match="unregistered"):
        _figure_inventory(tmp_path, 300, [FileSpec(item["file"], selected.absolute_path, "changed")])
    # Matching another published file's bytes does not authorize replacing
    # this path's pinned workload identity.
    with pytest.raises(ValueError, match="unregistered"):
        _figure_inventory(
            tmp_path, 300, [FileSpec(item["file"], selected.absolute_path, corpus["workloads"][1]["sha256"])]
        )
    assert (
        _figure_inventory(tmp_path, 300, [FileSpec("custom.egg", tmp_path / "custom.egg", "custom")])["workloads"] == []
    )
