"""Catalog metadata cannot silently omit selected inputs or invent measurements."""

from __future__ import annotations

import json
from dataclasses import asdict
from pathlib import Path
from typing import Any

from benchmarking.admission import PilotPolicy, pilot_identity
from benchmarking.figure_inventory import figure_inventory, write_inventory
from benchmarking.suites import resolve_suite


def catalog(root: Path, cases: list[dict[str, Any]]) -> None:
    (root / "benchmarks").mkdir(exist_ok=True)
    (root / "benchmarks/catalog.json").write_text(json.dumps({"families": {"eggcc": {}}, "cases": cases}))


def case(name: str, paths: list[str], **extra: Any) -> dict[str, Any]:
    return {"id": name, "family": "eggcc", "source": "source", "status": "captured", "workloads": paths, **extra}


def test_partial_capture_keeps_original_call_numbers_and_missing_selected_inputs(tmp_path: Path) -> None:
    (tmp_path / "b.egg").write_text("(datatype E (B))")
    (tmp_path / "c.egg").write_text("(datatype E (C))")
    catalog(
        tmp_path,
        [
            case(
                "partial",
                ["a.egg", "b.egg", "c.egg"],
                invocations=[{"index": index, "workload": f"{name}.egg"} for index, name in enumerate("abc")],
            )
        ],
    )
    rows = figure_inventory(tmp_path)["workloads"]
    assert {row["label"] for row in rows} == {"partial / call 1", "partial / call 2", "partial / call 3"}
    missing = next(row for row in rows if not row["file_sha256"])
    assert missing["label"] == "partial / call 1"
    assert missing["unavailable_reason"]


def test_missing_selected_file_does_not_disappear_when_old_exports_are_excluded(tmp_path: Path) -> None:
    catalog(
        tmp_path,
        [
            case(
                "missing",
                ["old.egg", "missing.egg"],
                benchmark_selection={
                    "workloads": ["missing.egg"],
                    "reason": "Omit setup call",
                },
            )
        ],
    )
    data = figure_inventory(tmp_path)
    assert len(data["workloads"]) == 1
    assert data["workloads"][0]["file_sha256"] == ""
    assert data["exclusions"][0]["paths"] == ["old.egg"]


def test_aliases_share_identity_and_changed_inputs_update_metadata_without_observations(tmp_path: Path) -> None:
    path = tmp_path / "input.egg"
    path.write_text("(datatype E (A))")
    catalog(tmp_path, [case("a", ["input.egg"]), case("b", ["input.egg"])])
    destination = tmp_path / "metadata.json"
    write_inventory(tmp_path, destination)
    before = destination.stat().st_mtime_ns
    original = json.loads(destination.read_text())
    assert len(original["workloads"]) == 1
    assert [alias["case"] for alias in original["workloads"][0]["aliases"]] == ["a", "b"]
    write_inventory(tmp_path, destination)
    assert destination.stat().st_mtime_ns == before
    path.write_text("(datatype E (B))")
    write_inventory(tmp_path, destination, 480)
    changed = json.loads(destination.read_text())
    assert changed["workloads"][0]["file_sha256"] != original["workloads"][0]["file_sha256"]
    assert changed["timeout_sec"] == 480
    assert not any(name in destination.read_text() for name in ("wall_sec", "samples", "mean", "max_rss_bytes"))
    assert not (tmp_path / ".reports.jsonl").exists()


def test_strict_evidence_requires_full_policy_and_only_applies_to_egglog(tmp_path: Path) -> None:
    (tmp_path / "input.egg").write_text("(datatype E (A))")
    catalog(tmp_path, [case("math-growth-011", ["input.egg"], family="math-growth")])
    selection = resolve_suite("expanded", tmp_path)
    identity = pilot_identity(
        selection.files[0], "math-growth", {"egglog": "egglog-binary", "egg": "egg-binary"}, PilotPolicy(300), tmp_path
    )
    failure = {"identity": identity, "status": "failure", "reason": "proof-testing: invalid"}
    stale = {"identity": {**identity, "policy": {**asdict(PilotPolicy(300)), "version": 0}}, "status": "admitted"}
    evidence = tmp_path / "benchmarks/local/pilot.jsonl"
    evidence.parent.mkdir()
    evidence.write_text("\n".join(json.dumps(row) for row in (failure, stale)))
    failures = figure_inventory(tmp_path)["workloads"][0]["validation_failures"]
    assert failures == {"egglog-binary/300": "Strict proof validation failed"}
    assert figure_inventory(tmp_path, 480)["workloads"][0]["validation_failures"] == {}
    evidence.write_text(evidence.read_text() + "\n" + json.dumps({"identity": identity, "status": "admitted"}))
    assert figure_inventory(tmp_path)["workloads"][0]["validation_failures"] == {}
