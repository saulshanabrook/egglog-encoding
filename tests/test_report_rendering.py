"""Snapshot the pair report's shared Markdown and human-scale Rich output."""

from __future__ import annotations

from pathlib import Path
from typing import cast

from rich.cells import cell_len
from rich.console import Console
from syrupy.assertion import SnapshotAssertion

from benchmarking import models
from benchmarking.reports.catalog import ReportOptions
from benchmarking.reports.comparison import build_report_catalog
from benchmarking.reports.database import ReportDatabase
from benchmarking.reports.records import ReportRecord
from benchmarking.reports.render import render_markdown_report_document, render_rich_report_document

from .conftest import make_endpoint, make_record, make_ruleset_timing, make_timing_summary, write_report


def test_realistic_pair_report_markdown_snapshot(tmp_path: Path, snapshot: SnapshotAssertion) -> None:
    report_path, comparison = _pair_case(tmp_path)
    with ReportDatabase(report_path) as database:
        catalog = build_report_catalog(database, comparison, ReportOptions("rulesets"))

    markdown = render_markdown_report_document(catalog)
    stable = markdown.replace(str(report_path), "/tmp/benchmark-report.duckdb")

    assert stable == snapshot
    assert tuple(section.id for section in catalog.sections) == (
        "selection",
        "summary",
        "files",
        "phases",
        "rulesets",
    )
    assert "| Baseline | baseline | abc123 | no | main | off |" in markdown
    assert "| Candidate | candidate | abc123 | no | dd | proofs |" in markdown
    assert "1.066x [0.983, 1.157]" in markdown
    assert "1.0100s [0.8829, 1.1371]" in markdown


def test_rich_report_is_readable_at_realistic_widths(tmp_path: Path) -> None:
    report_path, comparison = _pair_case(tmp_path)
    with ReportDatabase(report_path) as database:
        catalog = build_report_catalog(database, comparison, ReportOptions("rulesets"))

    for width in (80, 119, 120, 160):
        console = Console(record=True, width=width, color_system=None)
        console.print(render_rich_report_document(catalog, width))
        rendered = console.export_text()

        assert rendered.count("Warning: detailed Rich report") == (1 if width < 120 else 0)
        assert max(cell_len(line) for line in rendered.splitlines()) <= width
        assert rendered.index("Phase comparison") < rendered.rindex("Benchmark summary")
        assert "math.egg" in rendered
        assert "rewrite.egg" in rendered


def test_detail_level_is_cumulative(tmp_path: Path) -> None:
    report_path, comparison = _pair_case(tmp_path)
    expected = {
        "summary": ("selection", "summary"),
        "files": ("selection", "summary", "files"),
        "phases": ("selection", "summary", "files", "phases"),
        "rulesets": ("selection", "summary", "files", "phases", "rulesets"),
    }

    for detail, section_ids in expected.items():
        with ReportDatabase(report_path) as database:
            catalog = build_report_catalog(
                database,
                comparison,
                ReportOptions(cast(models.DetailLevel, detail)),
            )
        assert tuple(section.id for section in catalog.sections) == section_ids


def test_one_file_summary_removes_redundant_wall_and_rss_tails(tmp_path: Path) -> None:
    report_path, comparison = _pair_case(tmp_path)
    one_file = models.ComparisonSpec(
        comparison.baseline,
        comparison.candidate,
        comparison.files[:1],
        comparison.rounds,
        comparison.timeout_sec,
    )
    with ReportDatabase(report_path) as database:
        catalog = build_report_catalog(database, one_file)

    markdown = render_markdown_report_document(catalog)

    assert markdown.count("| Wall time |") == 1
    assert "| Wall time | Suite (1 file) | math.egg |" in markdown
    assert markdown.count("| Peak RSS |") == 1
    assert "| Peak RSS | Only file | math.egg |" in markdown


def test_one_round_report_keeps_point_estimates_without_ci_brackets(tmp_path: Path) -> None:
    report_path, comparison = _pair_case(tmp_path)
    one_round = models.ComparisonSpec(
        comparison.baseline,
        comparison.candidate,
        comparison.files,
        1,
        comparison.timeout_sec,
    )
    with ReportDatabase(report_path) as database:
        catalog = build_report_catalog(database, one_round)

    summary = render_markdown_report_document(catalog).partition("## Benchmark summary")[2]

    assert "point only" in summary
    assert "[" not in summary


def test_missing_rss_is_one_explicit_unavailable_summary(tmp_path: Path) -> None:
    report_path = tmp_path / "no-rss.duckdb"
    file = models.FileSpec("benchmarks/file.egg", tmp_path / "file.egg", "sha256:file")
    baseline = make_endpoint(target_label="baseline", binary_sha256="sha256:baseline", treatment="off")
    candidate = make_endpoint(target_label="candidate", binary_sha256="sha256:candidate", treatment="proofs")
    write_report(
        report_path,
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
        ),
    )
    comparison = models.ComparisonSpec(baseline, candidate, (file,), 1, 120)
    with ReportDatabase(report_path) as database:
        catalog = build_report_catalog(database, comparison)

    markdown = render_markdown_report_document(catalog)

    assert markdown.count("| Peak RSS |") == 1
    assert "| Peak RSS | Unavailable | — | — | incomplete: peak RSS unavailable |" in markdown


def _pair_case(tmp_path: Path) -> tuple[Path, models.ComparisonSpec]:
    report_path = tmp_path / "pair.duckdb"
    files = (
        models.FileSpec("benchmarks/math.egg", tmp_path / "math.egg", "sha256:file-math"),
        models.FileSpec("benchmarks/rewrite.egg", tmp_path / "rewrite.egg", "sha256:file-rewrite"),
    )
    baseline = make_endpoint(
        target_label="baseline",
        binary_sha256="sha256:baseline",
        backend="main",
        treatment="off",
    )
    candidate = make_endpoint(
        target_label="candidate",
        binary_sha256="sha256:candidate",
        backend="dd",
        treatment="proofs",
    )
    records: list[ReportRecord] = []
    endpoint_cases = (
        (baseline, (1.0, 2.0), (100_000_000, 130_000_000)),
        (candidate, (0.8, 2.4), (95_000_000, 150_000_000)),
    )
    for endpoint, wall_times, rss_values in endpoint_cases:
        for file_order, file in enumerate(files):
            for round_index in range(2):
                wall = wall_times[file_order] + 0.02 * round_index
                records.append(
                    make_record(
                        len(records),
                        started_at=f"2026-07-17T12:00:{len(records):02d}Z",
                        binary_sha256=endpoint.target.binary_sha256,
                        file_sha256=file.sha256,
                        backend=endpoint.backend,
                        treatment=endpoint.treatment,
                        target_label=endpoint.target.row.label,
                        wall_sec=wall,
                        max_rss_bytes=rss_values[file_order] + round_index * 1_000_000,
                        timing_summary=make_timing_summary(
                            make_ruleset_timing(
                                "simplify",
                                search_ns=int(wall * 300_000_000),
                                apply_ns=int(wall * 120_000_000),
                                merge_ns=80_000_000,
                                rebuild_ns=30_000_000,
                            ),
                            make_ruleset_timing(
                                "finish",
                                search_ns=int(wall * 100_000_000),
                                apply_ns=int(wall * 60_000_000),
                                merge_ns=20_000_000,
                                rebuild_ns=10_000_000,
                            ),
                        ),
                    )
                )
    write_report(report_path, *records)
    return report_path, models.ComparisonSpec(baseline, candidate, files, 2, 120)
