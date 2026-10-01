"""Verify complete-source admission and deduplicated standalone corpus aliases."""

import json
from pathlib import Path

import pytest

from benchmarking.targets import sha256_file
from scripts.reproduction_corpus import write_corpus


def validated_row(root: Path, case: str, source: str = "(check (= 1 1))\n") -> dict:
    attempt = root / case
    attempt.mkdir()
    replay = attempt / "workload.egg"
    replay.write_text(source)
    (attempt / "stage.json").write_text('{"status": "success"}\n')
    return {
        "id": case,
        "family": "eggcc",
        "source": f"benchmarks/{case}.bril",
        "scope": "required",
        "configuration": {"optimizer": "statewalk"},
        "outcome": {
            "status": "success",
            "stage": "validate",
            "attempt": str(attempt),
            "workloads": [str(replay)],
            "capture_stage": {"status": "success"},
            "validations": [
                {
                    "replay": str(replay),
                    "replay_sha256": sha256_file(replay),
                    "status": "success",
                    "output_contract_passed": True,
                }
            ],
        },
    }


def test_corpus_deduplicates_bytes_preserves_aliases_and_failures(tmp_path: Path) -> None:
    first, alias = validated_row(tmp_path, "first"), validated_row(tmp_path, "alias")
    blocked = {**first, "id": "blocked", "outcome": {"status": "blocked", "reason": "later parent failed"}}
    corpus = tmp_path / "corpus"
    manifest = write_corpus([first, blocked, alias], corpus)
    assert len(list(corpus.glob("*.egg"))) == 1
    assert [item["case"] for item in manifest["workloads"][0]["aliases"]] == ["first", "alias"]
    assert manifest["cases"][1]["workloads"] == []
    assert manifest["cases"][1]["reason"] == "later parent failed"
    before = {path: path.stat().st_mtime_ns for path in corpus.iterdir()}
    assert write_corpus([first, blocked, alias], corpus) == manifest
    assert before == {path: path.stat().st_mtime_ns for path in corpus.iterdir()}
    assert json.loads((corpus / "manifest.json").read_text()) == manifest


@pytest.mark.parametrize("failure", ["failed-parent", "changed", "missing-check", "facts"])
def test_corpus_rejects_unvalidated_or_changed_replays(tmp_path: Path, failure: str) -> None:
    row = validated_row(tmp_path, "case")
    outcome = row["outcome"]
    if failure == "failed-parent":
        outcome["capture_stage"]["status"] = "blocked"
    elif failure == "changed":
        Path(outcome["workloads"][0]).write_text("(check (= 2 2))")
    elif failure == "missing-check":
        outcome["validations"][0]["output_contract_passed"] = False
    else:
        outcome["validations"][0]["facts_sha256"] = "sha256:unbound-facts"
    with pytest.raises(ValueError):
        write_corpus([row], tmp_path / "corpus")
    assert not (tmp_path / "corpus/manifest.json").exists()


def test_capture_only_is_visible_but_unpublished(tmp_path: Path) -> None:
    row = validated_row(tmp_path, "case")
    row["outcome"]["stage"] = "complete"
    manifest = write_corpus([row], tmp_path / "corpus")
    assert manifest["workloads"] == []
    assert manifest["cases"][0]["status"] == "pending"
    assert "standalone validation stage" in manifest["cases"][0]["reason"]


def test_complete_materialization_can_pass_separate_validation(tmp_path: Path) -> None:
    row = validated_row(tmp_path, "case")
    row["outcome"]["capture_stage"]["status"] = "ordinary-validation-pending"
    assert len(write_corpus([row], tmp_path / "corpus")["workloads"]) == 1


def test_stale_identity_stays_visible_without_a_replay(tmp_path: Path) -> None:
    row = validated_row(tmp_path, "case")
    row["outcome"] = {"status": "pending", "reason": "source identity changed", "historical": row["outcome"]}
    manifest = write_corpus([row], tmp_path / "corpus")
    assert manifest["workloads"] == []
    assert manifest["cases"][0]["status"] == "pending"


def test_modified_published_bytes_are_not_silently_overwritten(tmp_path: Path) -> None:
    row = validated_row(tmp_path, "case")
    directory = tmp_path / "corpus"
    manifest = write_corpus([row], directory)
    stored = directory / manifest["workloads"][0]["file"]
    stored.write_text("changed")
    with pytest.raises(ValueError, match="stored corpus bytes changed"):
        write_corpus([row], directory)
    assert stored.read_text() == "changed"
