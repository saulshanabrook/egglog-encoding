"""Check the shared grouped snapshot and atomic refresh."""

from __future__ import annotations

import json
import os
from pathlib import Path

import pytest

from benchmarking.reports import grouped
from benchmarking.reports.store import CacheKey, ReportStore, parse_grouped_report, serialize_grouped_report

from .report_fixtures import make_record, write_report


def test_grouped_snapshot_keeps_all_samples_and_derives_current_engine_labels(tmp_path: Path) -> None:
    path = tmp_path / "report.jsonl"
    records = [
        make_record(0, started_at="2026-09-30T00:00:03Z", binary_sha256="sha256:old", target_label="current"),
        make_record(1, started_at="2026-09-30T00:00:02Z", target_label="current", status="failure"),
        make_record(2, started_at="2026-09-30T00:00:04Z", target_label="current", status="timed-out"),
        make_record(3, started_at="2026-09-30T00:00:04Z", target_label="other"),
        make_record(4, started_at="2026-09-30T00:00:01Z", treatment="proofs"),
        make_record(
            5, started_at="2026-09-30T00:00:05Z", binary_sha256="sha256:egg", treatment="egg", target_label="current"
        ),
        make_record(6, started_at="2026-09-30T00:00:06Z", timeout_sec=60),
    ]
    write_report(path, *records)
    report = ReportStore(path).grouped_report()
    by_key = {CacheKey(**group["key"]): group for group in report.data["groups"]}
    key = CacheKey("sha256:bin", "sha256:file", "off", 120)

    assert [sample["row_index"] for sample in by_key[key]["samples"]] == [1, 2, 3]
    assert [sample["status"] for sample in by_key[key]["samples"]] == ["failure", "timed-out", "success"]
    assert by_key[key]["labels"] == ["current", "other"]
    assert by_key[CacheKey("sha256:bin", "sha256:file", "proofs", 120)]["labels"] == ["current", "other"]
    assert by_key[CacheKey("sha256:old", "sha256:file", "off", 120)]["labels"] == []
    assert by_key[CacheKey("sha256:egg", "sha256:file", "egg", 120)]["labels"] == ["current"]
    assert [row.row_index for row in report.latest_records(key, 2)] == [2, 3]
    assert len(report.records) == len(records)
    for group in report.data["groups"]:
        for sample in group["samples"]:
            assert {name: value for name, value in sample.items() if name != "row_index"} == records[
                sample["row_index"]
            ]

    encoded = serialize_grouped_report(report)
    restored = parse_grouped_report(encoded, str(path))
    assert restored.data == report.data
    assert restored.latest_records(key, 2) == report.latest_records(key, 2)
    assert serialize_grouped_report(ReportStore(path).grouped_report()) == encoded


@pytest.mark.parametrize("field", ["grouped_schema_version", "report_schema_version"])
def test_grouped_codec_rejects_incompatible_versions(tmp_path: Path, field: str) -> None:
    data = json.loads(serialize_grouped_report(ReportStore(tmp_path / "empty.jsonl").grouped_report()))
    data[field] = 0
    with pytest.raises(ValueError, match="unsupported.*schema version"):
        parse_grouped_report(json.dumps(data), "empty.jsonl")


def test_grouped_refresh_is_atomic_and_leaves_unchanged_files_untouched(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = tmp_path / "report.jsonl"
    write_report(path, make_record(0, started_at="2026-09-30T00:00:00Z"))
    os.utime(path, ns=(1_000_000_000, 1_000_000_000))
    before = path.stat()
    store = ReportStore(path)
    destination = grouped.grouped_report_path(path)
    grouped.write_grouped_report(store.grouped_report(), destination)
    os.utime(destination, ns=(2_000_000_000, 2_000_000_000))
    original = destination.read_bytes()
    grouped_before = destination.stat()

    grouped.write_grouped_report(store.grouped_report(), destination)

    assert path.stat().st_mtime_ns == before.st_mtime_ns
    assert path.stat().st_ino == before.st_ino
    assert destination.stat().st_mtime_ns == grouped_before.st_mtime_ns
    assert destination.stat().st_ino == grouped_before.st_ino
    store.append(make_record(1, started_at="2026-09-30T00:00:01Z"))

    def fail_replace(_source: object, _destination: object) -> None:
        raise PermissionError("cannot publish")

    monkeypatch.setattr(grouped.os, "replace", fail_replace)
    with pytest.raises(PermissionError, match="cannot publish"):
        grouped.write_grouped_report(store.grouped_report(), destination)
    assert destination.read_bytes() == original
    assert not list(tmp_path.glob(f".{destination.name}.*"))


def test_grouped_path_is_a_distinct_sibling(tmp_path: Path) -> None:
    assert grouped.grouped_report_path(tmp_path / ".reports.jsonl") == tmp_path / ".reports-grouped.json"
    assert grouped.grouped_report_path(tmp_path / "foo.jsonl") == tmp_path / "foo-grouped.json"
    assert grouped.grouped_report_path(tmp_path / "foo.json") == tmp_path / "foo.json-grouped.json"
