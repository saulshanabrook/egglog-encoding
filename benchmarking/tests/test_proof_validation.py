"""Remote proof replay evidence cannot become a performance observation."""

from __future__ import annotations

import json
from copy import deepcopy
from dataclasses import replace
from pathlib import Path
from typing import Any

import pytest

from benchmarking.models import BenchmarkEndpoint, FileSpec
from benchmarking.proof_validation import (
    is_semantic_proof_failure,
    read_proof_source_bindings,
    read_proof_validation,
    select_remote_proof_validation,
)

from .report_fixtures import make_target


@pytest.mark.parametrize(
    ("process_status", "semantic"),
    [
        ("failure", True),
        ("success", True),
        ("timed-out", False),
        ("memory-limited", False),
        ("resource-limited", False),
        ("stack-overflow", False),
        ("infrastructure-unavailable", False),
    ],
)
def test_only_actual_checker_failure_vetoes_production_cost(process_status: str, semantic: bool) -> None:
    evidence = {"status": "failed", "observation": {"status": process_status}}
    assert is_semantic_proof_failure(evidence) is semantic


@pytest.fixture
def replay() -> dict[str, Any]:
    return {
        "validation_schema_version": 1,
        "kind": "proof-validation-replay",
        "started_at": "2026-11-12T00:00:00Z",
        "production_binary_sha256": "sha256:bin",
        "source_git_sha": "abc123",
        "file_sha256": "sha256:file",
        "production_treatment": "proof-extraction",
        "checked_treatment": "proof-testing",
        "threads": 4,
        "requested_threads": 4,
        "status": "success",
        "error_message": None,
        "proof_summary": {
            "schema_version": 1,
            "success": True,
            "check_requests": 1,
            "extraction_requests": 2,
            "produced_certificates": 3,
            "verified_certificates": 3,
        },
        "validator": {
            "host": "whale",
            "binary_sha256": "sha256:linux-binary",
            "source_git_sha": "abc123",
            "command": ["egglog-experimental", "--proof-testing", "--proof-summary", "summary.json"],
            "log_path": "validation.log",
            "timeout_sec": 1500,
            "memory_limit_bytes": 32 * 1024**3,
        },
    }


def test_remote_replay_preserves_distinct_validator_provenance_without_timing(
    tmp_path: Path, replay: dict[str, Any]
) -> None:
    path = tmp_path / "validation.jsonl"
    assert read_proof_validation(path) == ()
    path.write_text(json.dumps(replay) + "\n")
    before = path.read_bytes()
    endpoint = BenchmarkEndpoint(make_target().row, "sha256:bin", "proof-extraction", threads=4)
    file = FileSpec("input.egg", tmp_path / "input.egg", "sha256:file")
    result = select_remote_proof_validation(read_proof_validation(path), endpoint, file)
    assert result is not None and result["status"] == "passed"
    assert result["validator"]["binary_sha256"] == "sha256:linux-binary"
    assert result["validator"]["memory_limit_bytes"] != endpoint.memory_limit_bytes
    assert "not an exported local certificate" in result["scope"]
    assert "wall_sec" not in result["observation"] and path.read_bytes() == before
    replay["wall_sec"] = 123
    path.write_text(json.dumps(replay))
    with pytest.raises(ValueError, match="performance measurements"):
        read_proof_validation(path)


def test_frozen_source_receipt_survives_later_python_only_target_commits(
    tmp_path: Path, replay: dict[str, Any]
) -> None:
    receipt = tmp_path / "receipt.json"
    receipt.write_text(json.dumps({"binary_sha256": "sha256:bin", "compiled_source_sha": "abc123"}))
    target = replace(make_target().row, git_sha="later-python-commit")
    endpoint = BenchmarkEndpoint(target, "sha256:bin", "proof-extraction", threads=4)
    file = FileSpec("input.egg", tmp_path / "input.egg", "sha256:file")
    result = select_remote_proof_validation(
        (replay,), endpoint, file, source_bindings=read_proof_source_bindings(receipt)
    )
    assert result is not None and result["status"] == "passed"
    assert result["production_source_git_sha"] == "abc123"
    receipt.write_text(json.dumps({"binary_sources": {"sha256:bin": "wrong-rust-source"}}))
    result = select_remote_proof_validation(
        (replay,), endpoint, file, source_bindings=read_proof_source_bindings(receipt)
    )
    assert result is not None and result["status"] == "unknown"


def test_delegated_lmfao_replay_preserves_local_timing_rows_and_skips_local_checker(
    tmp_path: Path, replay: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking import collection
    from benchmarking.lmfao import optimizer
    from benchmarking.reports.store import ReportStore
    from benchmarking.targets import sha256_file

    from .report_fixtures import make_record

    source = tmp_path / "proof.egg"
    source.write_text("(check (= 1 1))\n")
    store = ReportStore(tmp_path / "timings.jsonl")
    target = make_target(binary_path=tmp_path / "frozen-engine")
    for index, mode in enumerate(optimizer.REPLAY_MODES):
        store.append(
            make_record(
                index,
                started_at=f"2026-11-12T00:00:0{index}Z",
                treatment=mode,
                file_sha256=sha256_file(source),
                timeout_sec=900,
                threads=4,
                requested_threads=4,
                wall_sec=2,
                max_rss_bytes=1024**2,
            )
        )
    before = store.path.read_bytes()

    def forbidden(*_args: Any, **_kwargs: Any) -> Any:
        pytest.fail("delegated cached replay launched a local process")

    monkeypatch.setattr(optimizer, "validate_proof_requests", forbidden)
    monkeypatch.setattr(collection, "run_process", forbidden)
    observed = optimizer.OptimizerCollection({}, {}, store, target)
    evidence_path = tmp_path / "remote-validation.jsonl"
    result = optimizer.collect_replays(observed, source, 1, 900, 16 * 1024**3, 192, 4, proof_validation=evidence_path)
    assert observed.report["proof_replay_validation"]["status"] == "pending"
    assert result["slotted-proof-extraction"]["process_seconds"]["mean"]["point"] == 2
    replay.update(
        file_sha256=sha256_file(source),
        production_treatment="slotted-proof-extraction",
        checked_treatment="slotted-proof-testing",
    )
    evidence_path.write_text(json.dumps(replay) + "\n")
    assert (
        optimizer.collect_replays(observed, source, 1, 900, 16 * 1024**3, 192, 4, proof_validation=evidence_path)
        == result
    )
    evidence = observed.report["proof_replay_validation"]
    assert evidence["status"] == "passed" and evidence["local_evidence"]["status"] == "pending"
    assert store.path.read_bytes() == before and store.row_count == 2


@pytest.mark.parametrize(
    "field",
    (
        "production_binary_sha256",
        "file_sha256",
        "production_treatment",
        "checked_treatment",
        "threads",
        "requested_threads",
    ),
)
def test_remote_replay_cannot_certify_another_profile(tmp_path: Path, replay: dict[str, Any], field: str) -> None:
    endpoint = BenchmarkEndpoint(make_target().row, "sha256:bin", "proof-extraction", threads=4)
    file = FileSpec("input.egg", tmp_path / "input.egg", "sha256:file")
    replay[field] = "different" if isinstance(replay[field], str) else 1
    assert select_remote_proof_validation((replay,), endpoint, file) is None


@pytest.mark.parametrize("failure", ("source", "validator-source", "partial", "empty", "no-summary", "process-failure"))
def test_remote_replay_requires_source_binding_and_actual_verified_counters(
    tmp_path: Path, replay: dict[str, Any], failure: str
) -> None:
    endpoint = BenchmarkEndpoint(make_target().row, "sha256:bin", "proof-extraction", threads=4)
    file = FileSpec("input.egg", tmp_path / "input.egg", "sha256:file")
    old = deepcopy(replay)
    replay["started_at"] = "2026-11-12T00:00:01Z"
    if failure == "source":
        replay["source_git_sha"] = "other"
    elif failure == "validator-source":
        replay["validator"]["source_git_sha"] = "other"
    elif failure == "partial":
        replay["proof_summary"]["verified_certificates"] = 2
    elif failure == "empty":
        replay["proof_summary"]["produced_certificates"] = replay["proof_summary"]["verified_certificates"] = 0
    elif failure == "no-summary":
        replay["proof_summary"] = None
    else:
        replay["status"], replay["error_message"] = "failure", "certificate rejected"
    result = select_remote_proof_validation((old, replay), endpoint, file)
    assert result is not None and result["status"] in ("failed", "unknown")
    assert result["issue"]
