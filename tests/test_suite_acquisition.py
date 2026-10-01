"""Keep capture accounting independent from successful replay preparation."""

import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from benchmarking import suites
from scripts import suite_acquisition


def test_inventory_refresh_preserves_enriched_cases_and_out_of_scope_families() -> None:
    existing: dict[str, Any] = {
        "families": {"eggcc": {"revision": "same"}, "luminal": {"revision": "old"}},
        "cases": [
            {"id": "e", "family": "eggcc", "source": "a", "status": "captured", "workloads": ["a.egg"]},
            {"id": "l", "family": "luminal", "source": "l", "status": "captured", "workloads": ["l.egg"]},
        ],
    }
    fresh = {
        "families": {"eggcc": {"revision": "same"}, "luminal": {"revision": "changed"}},
        "cases": [
            {"id": "e", "family": "eggcc", "source": "a", "status": "blocked", "workloads": []},
            {"id": "new", "family": "eggcc", "source": "b", "status": "blocked", "workloads": []},
        ],
    }
    result = suite_acquisition.reconcile_inventory(existing, fresh, ("eggcc",))
    assert result["families"]["luminal"] == existing["families"]["luminal"]
    assert result["cases"][:2] == existing["cases"]
    assert result["cases"][2]["id"] == "new"


def test_inventory_revision_change_retains_old_evidence_but_invalidates_capture() -> None:
    old = {"id": "e", "family": "eggcc", "source": "a", "status": "captured", "workloads": ["a.egg"]}
    existing = {"families": {"eggcc": {"revision": "old"}}, "cases": [old]}
    fresh = {
        "families": {"eggcc": {"revision": "new"}},
        "cases": [{"id": "e", "family": "eggcc", "source": "a", "status": "blocked", "workloads": []}],
    }
    result = suite_acquisition.reconcile_inventory(existing, fresh, ("eggcc",))
    assert result["cases"][0]["status"] == "blocked"
    assert result["cases"][0]["workloads"] == []
    assert result["cases"][0]["previous_capture"]["case"] == old
    assert result["cases"][0]["previous_capture"]["revision"] == "old"


def test_partial_capture_retains_raw_order_and_only_prepared_replays(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(suite_acquisition, "ROOT", tmp_path)
    (tmp_path / "first.egg").write_text("; no eligible proof query\n")
    (tmp_path / "second.egg").write_text("; derived replay\n")
    catalog: dict[str, Any] = {
        "families": {"dialegg": {"revision": "pinned"}},
        "cases": [
            {"id": "dialegg-input", "family": "dialegg", "source": "input.mlir", "status": "blocked", "workloads": []},
        ],
    }
    path = tmp_path / "capture.json"
    path.write_text(
        json.dumps(
            {
                "cases": {
                    "dialegg-input": {
                        "status": "blocked",
                        "reason": "one call lacks an oracle",
                        "source_sha256": "source-hash",
                        "workloads": ["second.egg"],
                        "invocations": [
                            {"index": 0, "raw": "first.egg", "status": "blocked", "reason": "no query"},
                            {"index": 1, "raw": "second.egg", "workload": "second.egg", "status": "captured"},
                        ],
                    }
                }
            }
        )
    )
    suite_acquisition.import_captures(catalog, [path])
    case = catalog["cases"][0]
    assert case["workloads"] == ["second.egg"]
    assert case["status"] == "captured"
    assert case["reason"] == "one call lacks an oracle"
    assert [call["index"] for call in case["invocations"]] == [0, 1]
    assert not case["capture_complete"]
    captured = json.loads(path.read_text())
    captured["cases"]["dialegg-input"]["invocations"][0]["sha256"] = case["invocations"][0]["sha256"]
    path.write_text(json.dumps(captured))
    (tmp_path / "first.egg").write_text("changed after capture")
    with pytest.raises(ValueError, match="raw invocation changed"):
        suite_acquisition.import_captures(catalog, [path])


def test_persistent_engine_fragments_do_not_become_separate_workloads(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(suite_acquisition, "ROOT", tmp_path)
    (tmp_path / "seed.egg").write_text("seed")
    (tmp_path / "run.egg").write_text("run")
    (tmp_path / "replay.egg").write_text("seed\nrun")
    catalog: dict[str, Any] = {
        "families": {"churchroad": {"revision": "pinned"}},
        "cases": [
            {
                "id": "churchroad-input",
                "family": "churchroad",
                "source": "input.v",
                "status": "blocked",
                "workloads": [],
            },
        ],
    }
    path = tmp_path / "capture.json"
    path.write_text(
        json.dumps(
            [
                {
                    "id": "churchroad-input",
                    "revision": "pinned",
                    "status": "phase-prefix",
                    "engine_sessions": 1,
                    "raw_invocations": ["seed.egg", "run.egg"],
                    "workloads": ["replay.egg"],
                    "source_sha256": "source-hash",
                    "reason": "external synthesis unavailable",
                }
            ]
        )
    )
    suite_acquisition.import_captures(catalog, [path])
    case = catalog["cases"][0]
    assert case["workloads"] == ["replay.egg"]
    assert "invocations" not in case
    assert len(case["ordered_calls"]) == 2
    assert case["ordered_calls"][0]["sha256"] == hashlib.sha256(b"seed").hexdigest()
    assert not case["capture_complete"]


def test_reimport_preserves_source_selection_and_does_not_admit_new_helpers(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(suite_acquisition, "ROOT", tmp_path)
    (tmp_path / "kernel.egg").write_text("(check (= 1 1))\n")
    (tmp_path / "helper.egg").write_text("(let x 1)\n")
    selection = {"workloads": ["kernel.egg"], "reason": "Retain the complete computation"}
    catalog: dict[str, Any] = {
        "families": {"dialegg": {"revision": "pinned"}},
        "cases": [{"id": "input", "family": "dialegg", "source": "input", "benchmark_selection": selection}],
    }
    capture = tmp_path / "capture.json"
    capture.write_text(
        json.dumps(
            [
                {
                    "id": "input",
                    "revision": "pinned",
                    "status": "captured",
                    "source_sha256": "source-hash",
                    "workloads": ["kernel.egg", "helper.egg"],
                    "raw_invocations": ["kernel.egg", "helper.egg"],
                }
            ]
        )
    )
    suite_acquisition.import_captures(catalog, [capture])
    assert catalog["cases"][0]["benchmark_selection"] == selection
    assert catalog["cases"][0]["workloads"] == ["kernel.egg", "helper.egg"]
    (tmp_path / "benchmarks").mkdir()
    (tmp_path / "benchmarks/catalog.json").write_text(json.dumps(catalog))
    resolved = suites.resolve_suite("dialegg", tmp_path, include_normal_only=True)
    assert [file.display_path for file in resolved.files] == ["kernel.egg"]
    assert resolved.source_exclusions == {"input": ("helper.egg",)}


def test_split_speq_retains_extraction_variants_and_pushed_scope_boundaries() -> None:
    source = "(datatype E (Seed))\n"
    for name, variants in (("first", 0), ("second", 2), ("third", 0), ("fourth", 1)):
        source += (
            f";; Preserved artifact workload: {name}\n"
            f"(push 1)\n(let ${name} (Seed))\n(run 3)\n(extract ${name} {variants})\n(pop 1)\n"
        )
    replays = suite_acquisition.split_speq(source)
    assert list(replays) == ["first", "second", "third", "fourth"]
    assert "(extract $second 2)\n(pop 1)" in replays["second"]
    assert all(text.count("(push 1)") == text.count("(pop 1)") == 1 for text in replays.values())
    assert all("(datatype E (Seed))" in text and "(check " not in text for text in replays.values())
