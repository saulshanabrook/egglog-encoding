"""Test deterministic paper run manifests and exclusive result directories."""

from __future__ import annotations

import math
from datetime import UTC, datetime
from pathlib import Path

import pytest

from paper_benchmarking.jsonio import serialize_json_document, serialize_json_line
from paper_benchmarking.models import CommandSpec, ProcessLane
from paper_benchmarking.results import ResultStore, read_run_records
from paper_benchmarking.runner import build_run_manifest

from .paper_fixtures import fake_artifact_cache


def test_run_manifest_is_deterministic_for_fixed_provenance(tmp_path: Path) -> None:
    input_path = tmp_path / "input.txt"
    input_path.write_text("paper input\n", encoding="utf-8")
    command = CommandSpec(
        label="local",
        argv=("/bin/echo", "ok"),
        cwd=tmp_path,
        timeout_sec=5,
        env={"PAPER_MODE": "test"},
    )
    lane = ProcessLane(
        evaluation="math",
        name="fake",
        observations=(command,),
        input_paths=(input_path,),
        versions={"fake": "1.0"},
    )
    artifact = fake_artifact_cache(tmp_path / "artifact-cache")

    def manifest() -> dict[str, object]:
        return build_run_manifest(
            run_id="fixed-run",
            preset="quick",
            evaluations=("math",),
            lanes=(lane,),
            artifact=artifact,
            invocation_argv=("paper_bench.py", "run", "quick", "math"),
            invocation_cwd=tmp_path,
            environment={"PATH": "/bin", "UNRECORDED_SECRET": "not persisted"},
            created_at=datetime(2026, 8, 5, 12, 0, tzinfo=UTC),
            machine={"machine": "test", "system": "TestOS"},
            repository={"git_sha": "1" * 40, "is_dirty": False, "root": "/repo", "status": []},
        )

    first = manifest()
    second = manifest()

    assert serialize_json_document(first) == serialize_json_document(second)
    invocation = first["invocation"]
    assert isinstance(invocation, dict)
    assert invocation["env"] == {"PATH": "/bin"}
    assert first["versions"] == {"harness_schema_version": 1, "python": None}


def test_result_store_never_overwrites_a_run_directory(tmp_path: Path) -> None:
    ResultStore.create(tmp_path, "fixed-run")

    with pytest.raises(FileExistsError):
        ResultStore.create(tmp_path, "fixed-run")


def test_run_record_reader_ignores_an_unframed_final_row(tmp_path: Path) -> None:
    path = tmp_path / "runs.jsonl"
    path.write_bytes(b'{"sequence":1}\n{"sequence":2}')

    assert read_run_records(path) == [{"sequence": 1}]


def test_json_serialization_rejects_nonfinite_values() -> None:
    with pytest.raises(ValueError, match="Out of range float values"):
        serialize_json_line({"wall_sec": math.nan})
