"""Test JSONL persistence, indexing, cache selection, and schema failures."""

from __future__ import annotations

import json
from pathlib import Path
from typing import cast

import pytest

from benchmarking import models
from benchmarking.reports.records import (
    ReportRecord,
    RulesetTimingRecord,
    TimingSummaryRecord,
    parse_report_record,
)
from benchmarking.reports.store import ReportStore

from .conftest import make_record, make_ruleset_timing, make_timing_summary, write_report


def test_missing_report_is_an_empty_store_without_sidecar_artifacts(tmp_path: Path) -> None:
    report = tmp_path / "nested" / "report.jsonl"

    store = ReportStore(report)

    assert store.successful_estimate_aggregates() == ()
    assert report.read_text(encoding="utf-8") == ""
    assert list(report.parent.iterdir()) == [report]


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


def test_append_indexes_the_exact_record_it_persists(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    record = make_record(0, started_at="2026-07-15T12:00:00Z", wall_sec=2.5)
    key = models.EstimateKey("sha256:bin", "sha256:file", "off", 120)
    store = ReportStore(report)

    store.append(record)
    persisted = parse_report_record(report.read_bytes())
    current = store.latest_records(key, 1)[0].record
    reopened = ReportStore(report)

    assert current == persisted == reopened.latest_records(key, 1)[0].record
    assert store.records == reopened.records == (persisted,)
    assert current["wall_sec"] == 2.5
    assert store.successful_estimate_aggregates() == reopened.successful_estimate_aggregates()


def test_report_path_metacharacters_are_literal_not_a_glob(tmp_path: Path) -> None:
    report = tmp_path / "a'quoted[?*].jsonl"
    sibling = tmp_path / "a?.jsonl"
    write_report(report, make_record(0, started_at="2026-07-15T12:00:00Z"))
    write_report(
        sibling,
        make_record(1, started_at="2026-07-15T12:00:01Z", binary_sha256="sha256:sibling"),
    )

    aggregates = ReportStore(report).successful_estimate_aggregates()

    assert [aggregate.key.binary_sha256 for aggregate in aggregates] == ["sha256:bin"]


def test_historical_estimates_are_grouped_as_counts_and_sums(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        make_record(0, started_at="2026-07-15T12:00:00Z", wall_sec=1.5),
        make_record(1, started_at="2026-07-15T12:00:01Z", wall_sec=2.5),
        make_record(2, started_at="2026-07-15T12:00:02Z", status="failure", wall_sec=100.0),
        make_record(3, started_at="2026-07-15T12:00:03Z", status="timed-out"),
        make_record(4, started_at="2026-07-15T12:00:04Z", timeout_sec=60, wall_sec=7.0),
    )

    aggregates = ReportStore(report).successful_estimate_aggregates()

    assert [
        (aggregate.key.timeout_sec, aggregate.sample_count, aggregate.total_wall_sec) for aggregate in aggregates
    ] == [(60, 1, 7.0), (120, 2, 4.0)]


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
                unattributed_ns=4,
                merge_ns=7,
                rebuild_ns=3,
            )
        ),
    )

    ReportStore(report).append(record)
    loaded = parse_report_record(report.read_bytes())

    assert loaded == record
    assert tuple(loaded) == tuple(ReportRecord.__annotations__)
    summary = cast(TimingSummaryRecord, loaded["timing_summary"])
    assert tuple(summary) == tuple(TimingSummaryRecord.__annotations__)
    rulesets = cast(list[RulesetTimingRecord], summary["rulesets"])
    assert tuple(rulesets[0]) == tuple(RulesetTimingRecord.__annotations__)


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
    timing["schema_version"] = 1
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
            fact_directory_sha256="sha256:other-facts",
        ),
    )
    exact = models.EstimateKey("sha256:bin", "sha256:file", "off", 120)
    other_facts = models.EstimateKey(
        "sha256:bin",
        "sha256:file",
        "off",
        120,
        fact_directory_sha256="sha256:other-facts",
    )

    selected = ReportStore(report).selected_statuses_for_keys((exact, other_facts), 2)

    assert selected[exact] == ("timed-out", "success")
    assert selected[other_facts] == ("success",)
