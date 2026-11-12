"""Test JSONL persistence, indexing, cache selection, and schema failures."""

from __future__ import annotations

import json
from pathlib import Path
from typing import cast

import pytest

from benchmarking.models import Status
from benchmarking.native_memory import NATIVE_LIMIT_BYTES
from benchmarking.reports.store import (
    CacheKey,
    ReportRecord,
    ReportStore,
    RulesetTimingRecord,
    TimingSummaryRecord,
    parse_report_record,
)

from .report_fixtures import make_record, make_ruleset_timing, make_timing_summary, write_report


@pytest.mark.parametrize(
    ("status", "wall", "old_timeout", "timeout", "expected"),
    [
        ("success", 121.0, 120, 120, True),
        ("success", None, 120, 300, True),
        ("success", 50.0, 300, 120, True),
        ("success", 121.0, 300, 120, True),
        ("success", None, 300, 120, True),
        ("timed-out", None, 120, 120, True),
        ("timed-out", None, 120, 300, False),
        ("failure", 50.0, 120, 300, True),
    ],
)
def test_timeout_selection_preserves_success_and_failure_provenance(
    tmp_path: Path, status: Status, wall: float | None, old_timeout: int, timeout: int, expected: bool
) -> None:
    record = make_record(0, started_at="2026-10-27T00:00:00Z", status=status, wall_sec=wall, timeout_sec=old_timeout)
    path = tmp_path / "report.jsonl"
    write_report(path, record)
    before = path.read_bytes()
    store = ReportStore(path)
    key = CacheKey("sha256:bin", "sha256:file", "off")
    selected = store.latest_records(key, 1, timeout, NATIVE_LIMIT_BYTES)
    assert bool(selected) is expected
    assert [r.row_index for r in store.grouped_report().latest_records(key, 1, timeout, NATIVE_LIMIT_BYTES)] == [
        r.row_index for r in selected
    ]
    assert path.read_bytes() == before


@pytest.mark.parametrize(
    ("status", "old_cap", "cap", "expected"),
    [
        ("success", None, None, True),
        ("success", None, 10, True),
        ("success", 8, None, True),
        ("success", 8, 10, True),
        ("success", 10, 8, True),
        ("memory-limited", 8, 8, True),
        ("memory-limited", 8, 10, False),
        ("memory-limited", 10, 8, True),
        ("memory-limited", 8, None, False),
        ("failure", 8, 10, True),
        ("timed-out", 8, 10, True),
    ],
)
def test_memory_guards_reuse_successes_and_retry_only_memory_failures(
    tmp_path: Path, status: Status, old_cap: int | None, cap: int | None, expected: bool
) -> None:
    record = make_record(0, started_at="2026-10-27T00:00:00Z", status=status, memory_limit_bytes=old_cap)
    path = tmp_path / "report.jsonl"
    write_report(path, record)
    before = path.read_bytes()
    store = ReportStore(path)
    key = CacheKey("sha256:bin", "sha256:file", "off")
    selected = store.latest_records(key, 1, 120, cap)
    assert bool(selected) is expected
    assert [row.row_index for row in store.grouped_report().latest_records(key, 1, 120, cap)] == [
        row.row_index for row in selected
    ]
    assert path.read_bytes() == before


def test_runtime_contract_changes_require_a_report_schema_bump() -> None:
    import hashlib

    from benchmarking import engines, native_memory
    from benchmarking.reports.store import REPORT_SCHEMA_VERSION

    contract = {
        "treatments": {
            name: [spec.binary_name, spec.flags, spec.input_suffix, spec.timing_summary, spec.allocator_limit]
            for name, spec in engines.TREATMENT_SPECS.items()
        },
        "egglog_flags": engines.EGGLOG_FLAGS,
        "process_environment": engines.PROCESS_ENV,
        "allocator_environment": native_memory.NATIVE_ALLOCATOR_ENV,
        "parameter_arguments": engines.NATIVE_PARAMETER_ARGUMENTS,
        "math_arguments": engines.MATH_WORKLOAD_ARGUMENTS,
    }
    digest = hashlib.sha256(json.dumps(contract, sort_keys=True).encode()).hexdigest()
    assert (REPORT_SCHEMA_VERSION, digest) == (
        11,
        "eda29f84222724b0d9a780ad3460f95f1c3a982efaacea03efd624f0f221b9f8",
    ), "Bump the report schema version and update this contract digest"


def test_raised_timeout_does_not_retry_control_failure(tmp_path: Path) -> None:
    record = make_record(0, started_at="2026-10-27T00:00:00Z", status="failure")
    record["error_message"] = "process-group cleanup failed: denied"
    store = ReportStore(tmp_path / "report.jsonl")
    store.append(record)
    assert len(store.latest_records(CacheKey("sha256:bin", "sha256:file", "off"), 1, 300, NATIVE_LIMIT_BYTES)) == 1


def test_missing_report_is_an_empty_store_without_creating_files(tmp_path: Path) -> None:
    report = tmp_path / "nested" / "report.jsonl"

    ReportStore(report)

    assert not report.parent.exists()


def test_append_is_immediately_queryable(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    record = make_record(0, started_at="2026-07-15T12:00:00Z", target_label="current")
    store = ReportStore(report)

    store.append(record)
    pointer = store.find_label_pointer("current")

    assert pointer is not None
    assert pointer.binary_sha256 == record["binary_sha256"]
    raw = json.loads(report.read_text(encoding="utf-8"))
    assert raw == record
    assert "row_index" not in raw


def test_label_pointers_select_the_latest_binary_for_each_engine(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-15T12:00:00Z",
            target_label="current",
            binary_sha256="sha256:egglog",
            treatment="off",
        ),
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            target_label="current",
            binary_sha256="sha256:egg",
            treatment="egg",
        ),
    )
    store = ReportStore(report)
    egglog = store.find_label_pointer("current", "egglog-experimental")
    egg = store.find_label_pointer("current", "egg-math-benchmark")
    latest = store.find_label_pointer("current")

    assert egglog is not None and egglog.binary_sha256 == "sha256:egglog"
    assert egg is not None and egg.binary_sha256 == "sha256:egg"
    assert latest is not None and latest.binary_sha256 == "sha256:egg"


def test_append_indexes_the_exact_record_it_persists(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    record = make_record(0, started_at="2026-07-15T12:00:00Z", wall_sec=2.5)
    key = CacheKey("sha256:bin", "sha256:file", "off")
    store = ReportStore(report)

    store.append(record)
    persisted = parse_report_record(report.read_bytes())
    current = store.latest_records(key, 1, 120, NATIVE_LIMIT_BYTES)[0].record
    reopened = ReportStore(report)

    assert current == persisted == reopened.latest_records(key, 1, 120, NATIVE_LIMIT_BYTES)[0].record
    assert store.records == reopened.records == (persisted,)
    assert current["wall_sec"] == 2.5


def test_report_path_metacharacters_are_literal_not_a_glob(tmp_path: Path) -> None:
    report = tmp_path / "a'quoted[?*].jsonl"
    sibling = tmp_path / "a?.jsonl"
    write_report(report, make_record(0, started_at="2026-07-15T12:00:00Z"))
    write_report(
        sibling,
        make_record(1, started_at="2026-07-15T12:00:01Z", binary_sha256="sha256:sibling"),
    )

    records = ReportStore(report).records

    assert [record["binary_sha256"] for record in records] == ["sha256:bin"]


def test_typed_dict_schema_and_nested_values_round_trip(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    record = make_record(
        0,
        started_at="2026-07-15T12:00:00Z",
        max_rss_bytes=1234,
        timing_summary=make_timing_summary(
            make_ruleset_timing(
                "rules/λ",
                search_ns=6,
                apply_ns=5,
                execution_ns=4,
                merge_ns=7,
            ),
            native_rebuild_ns=3,
        ),
    )

    ReportStore(report).append(record)
    loaded = parse_report_record(report.read_bytes())

    assert loaded == record
    assert set(loaded) == set(ReportRecord.__annotations__)
    summary = cast(TimingSummaryRecord, loaded["timing_summary"])
    assert tuple(summary) == tuple(TimingSummaryRecord.__annotations__)
    rulesets = cast(list[RulesetTimingRecord], summary["rulesets"])
    assert all(tuple(ruleset) == tuple(RulesetTimingRecord.__annotations__) for ruleset in rulesets)
    assert rulesets == [
        {
            "name": "rules/λ",
            "role": "program",
            "assembly_ns": 0,
            "search_ns": 6,
            "apply_ns": 5,
            "execution_ns": 4,
            "merge_ns": 7,
        }
    ]
    assert summary["native_rebuild_ns"] == 3


@pytest.mark.parametrize("schema_version", [None, 2], ids=["missing", "wrong"])
def test_incompatible_report_schema_fails_during_load(tmp_path: Path, schema_version: int | None) -> None:
    report = tmp_path / "report.jsonl"
    current = make_record(0, started_at="2026-07-15T12:00:00Z")
    old = cast(dict[str, object], make_record(1, started_at="2026-07-15T12:00:01Z"))
    if schema_version is None:
        del old["report_schema_version"]
    else:
        old["report_schema_version"] = schema_version
    report.write_text(f"{json.dumps(current)}\n{json.dumps(old)}\n", encoding="utf-8")

    with pytest.raises(ValueError, match=r"invalid or incompatible benchmark report.*recompute"):
        ReportStore(report)


@pytest.mark.parametrize("mixed", [False, True], ids=["old", "mixed"])
def test_incompatible_report_shapes_fail_during_load(tmp_path: Path, mixed: bool) -> None:
    report = tmp_path / "report.jsonl"
    current = make_record(0, started_at="2026-07-15T12:00:00Z")
    old = cast(dict[str, object], make_record(1, started_at="2026-07-15T12:00:01Z"))
    timing = cast(dict[str, object], old["timing_summary"])
    timing["schema_version"] = 2
    records = (current, old) if mixed else (old,)
    report.write_text("".join(f"{json.dumps(record)}\n" for record in records), encoding="utf-8")

    with pytest.raises(ValueError, match=r"invalid or incompatible benchmark report.*recompute"):
        ReportStore(report)


def test_success_without_timing_summary_is_an_incompatible_report(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    row = make_record(0, started_at="2026-07-15T12:00:00Z")
    row["timing_summary"] = None
    report.write_text(f"{json.dumps(row)}\n", encoding="utf-8")

    with pytest.raises(ValueError, match=r"invalid or incompatible benchmark report.*recompute"):
        ReportStore(report)


def test_bulk_status_selection_uses_all_cache_dimensions_and_jsonl_tie_order(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        make_record(0, started_at="2026-07-15T12:00:00Z", status="failure"),
        make_record(1, started_at="2026-07-15T12:00:01Z", status="timed-out"),
        make_record(2, started_at="2026-07-15T12:00:01Z"),
        make_record(
            3,
            started_at="2026-07-15T12:00:02Z",
            file_sha256="sha256:other",
        ),
    )
    exact = CacheKey("sha256:bin", "sha256:file", "off")
    other_file = CacheKey(
        "sha256:bin",
        "sha256:other",
        "off",
    )

    store = ReportStore(report)
    selected = {
        key: tuple(row.record["status"] for row in store.latest_records(key, 2, 120, NATIVE_LIMIT_BYTES))
        for key in (exact, other_file)
    }

    assert selected[exact] == ("timed-out", "success")
    assert selected[other_file] == ("success",)


def test_completed_samples_are_reused_below_a_recorded_resource_exclusion(tmp_path: Path) -> None:
    from benchmarking.models import Exclusion, FileSpec
    from benchmarking.reports.store import select_observations

    from .report_fixtures import make_endpoint

    store = ReportStore(tmp_path / "report.jsonl")
    store.append(
        make_record(0, started_at="2026-10-27T00:00:00Z", memory_limit_bytes=None, timeout_sec=900, wall_sec=300)
    )
    from dataclasses import replace

    endpoint = replace(make_endpoint(), memory_limit_bytes=1024)
    file = FileSpec(
        "file.egg",
        tmp_path / "file.egg",
        "sha256:file",
        exclusions=(
            Exclusion("resource", "recorded allocation limit", "probe", memory_limit_bytes=NATIVE_LIMIT_BYTES),
        ),
    )
    selected = select_observations(store, endpoint, file, 1, 1)
    assert selected.issue is None and selected.exclusion is None
    assert [row.row_index for row in selected.rows] == [0]
