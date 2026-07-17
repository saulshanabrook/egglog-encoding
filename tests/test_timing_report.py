"""Verify phase and top-ruleset report semantics."""

from __future__ import annotations

from pathlib import Path

from benchmarking import models
from benchmarking.reports.catalog import (
    ReportCatalog,
    ReportCell,
    ReportMessage,
    ReportOptions,
    ReportRow,
    ReportTable,
)
from benchmarking.reports.comparison import build_report_catalog, format_duration, report_file_labels
from benchmarking.reports.records import ReportRecord
from benchmarking.reports.store import ReportStore

from .conftest import make_endpoint, make_record, make_ruleset_timing, make_timing_summary, write_report


def test_phase_report_uses_split_means_and_wall_residual(tmp_path: Path) -> None:
    report_path = tmp_path / "phases.jsonl"
    baseline = make_endpoint(binary_sha256="sha256:base", treatment="off")
    candidate = make_endpoint(binary_sha256="sha256:candidate", treatment="proofs")
    file = models.FileSpec("nested/file.egg", tmp_path / "file.egg", "sha256:file")
    records: list[ReportRecord] = []
    cases = (
        (baseline, 1.0, make_ruleset_timing(search_ns=600_000_000, apply_ns=300_000_000)),
        (
            candidate,
            1.2,
            make_ruleset_timing(
                search_ns=700_000_000,
                apply_ns=200_000_000,
                merge_ns=100_000_000,
                rebuild_ns=100_000_000,
            ),
        ),
    )
    for endpoint, wall_sec, timing in cases:
        records.append(
            make_record(
                len(records),
                started_at=f"2026-07-17T12:00:0{len(records)}Z",
                binary_sha256=endpoint.target.binary_sha256,
                backend=endpoint.backend,
                treatment=endpoint.treatment,
                wall_sec=wall_sec,
                timing_summary=make_timing_summary(timing),
            )
        )
    write_report(report_path, *records)
    comparison = models.ComparisonSpec(baseline, candidate, (file,), 1, 120)

    catalog = build_report_catalog(ReportStore(report_path), comparison, ReportOptions("phases"))

    table = _only_table(catalog, "phases")
    rows = {_cell(row, table, "phase").raw: row for row in table.rows}
    assert _cell(rows["search"], table, "baseline").raw == 600_000_000.0
    assert _cell(rows["apply"], table, "candidate").raw == 200_000_000.0
    assert _cell(rows["other"], table, "baseline").raw == -200_000_000.0
    assert _cell(rows["other"], table, "baseline").display == "!-200 ms"
    assert _cell(rows["other"], table, "candidate").display == "100 ms"


def test_rulesets_are_union_ranked_and_fixed_to_top_ten(tmp_path: Path) -> None:
    report_path = tmp_path / "rulesets.jsonl"
    baseline = make_endpoint(binary_sha256="sha256:base", treatment="off")
    candidate = make_endpoint(binary_sha256="sha256:candidate", treatment="proofs")
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")

    common_baseline = tuple(
        make_ruleset_timing(f"rule-{index:02d}", search_ns=(index + 1) * 1_000_000) for index in range(11)
    )
    common_candidate = tuple(
        make_ruleset_timing(f"rule-{index:02d}", search_ns=(index + 2) * 1_000_000) for index in range(11)
    )
    removed = make_ruleset_timing("removed", search_ns=1_000_000_000)
    added = make_ruleset_timing("added", search_ns=1_200_000_000)
    records = (
        make_record(
            0,
            started_at="2026-07-17T12:00:00Z",
            binary_sha256=baseline.target.binary_sha256,
            treatment=baseline.treatment,
            wall_sec=4.0,
            timing_summary=make_timing_summary(*common_baseline, removed),
        ),
        make_record(
            1,
            started_at="2026-07-17T12:00:01Z",
            binary_sha256=candidate.target.binary_sha256,
            treatment=candidate.treatment,
            wall_sec=4.0,
            timing_summary=make_timing_summary(*common_candidate, added),
        ),
    )
    write_report(report_path, *records)
    comparison = models.ComparisonSpec(baseline, candidate, (file,), 1, 120)

    catalog = build_report_catalog(ReportStore(report_path), comparison, ReportOptions("rulesets"))

    table = _only_table(catalog, "rulesets")
    names = tuple(_cell(row, table, "ruleset").display for row in table.rows)
    assert len(table.rows) == 10
    assert {"added", "removed"} <= set(names)
    assert "Showing 10 of 13 rulesets" in (table.caption or "")
    added_row = next(row for row in table.rows if _cell(row, table, "ruleset").display == "added")
    removed_row = next(row for row in table.rows if _cell(row, table, "ruleset").display == "removed")
    assert _cell(added_row, table, "baseline").display == "—"
    assert _cell(removed_row, table, "candidate").display == "—"
    assert _cell(added_row, table, "ratio").display == "—"


def test_failed_file_uses_dashes_and_ruleset_status_message(tmp_path: Path) -> None:
    report_path = tmp_path / "failed.jsonl"
    baseline = make_endpoint(binary_sha256="sha256:base", treatment="off")
    candidate = make_endpoint(binary_sha256="sha256:candidate", treatment="proofs")
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    records = (
        make_record(
            0,
            started_at="2026-07-17T12:00:00Z",
            binary_sha256=baseline.target.binary_sha256,
            treatment=baseline.treatment,
        ),
        make_record(
            1,
            started_at="2026-07-17T12:00:01Z",
            binary_sha256=candidate.target.binary_sha256,
            treatment=candidate.treatment,
            status="timed-out",
        ),
    )
    write_report(report_path, *records)
    comparison = models.ComparisonSpec(baseline, candidate, (file,), 1, 120)

    catalog = build_report_catalog(ReportStore(report_path), comparison, ReportOptions("rulesets"))

    phase_table = _only_table(catalog, "phases")
    assert all(_cell(row, phase_table, "candidate").display == "—" for row in phase_table.rows)
    ruleset_section = next(section for section in catalog.sections if section.id == "rulesets")
    assert isinstance(ruleset_section.blocks[0], ReportMessage)
    assert "timeout row selected" in ruleset_section.blocks[0].text


def test_duration_units_and_file_labels_are_compact() -> None:
    assert format_duration(None) == "—"
    assert format_duration(999) == "999 ns"
    assert format_duration(12_500) == "12.5 us"
    assert format_duration(1_250_000) == "1.25 ms"
    assert format_duration(1_250_000_000) == "1.25 s"

    files = (
        models.FileSpec("left/shared.egg", Path("/left/shared.egg"), "sha256:left"),
        models.FileSpec("right/shared.egg", Path("/right/shared.egg"), "sha256:right"),
    )
    assert tuple(report_file_labels(files).values()) == ("left/shared.egg", "right/shared.egg")


def _only_table(catalog: ReportCatalog, section_id: str) -> ReportTable:
    section = next(section for section in catalog.sections if section.id == section_id)
    tables = tuple(block for block in section.blocks if isinstance(block, ReportTable))
    assert len(tables) == 1
    return tables[0]


def _cell(row: ReportRow, table: ReportTable, column_id: str) -> ReportCell:
    index = next(index for index, column in enumerate(table.columns) if column.id == column_id)
    return row.cells[index]
