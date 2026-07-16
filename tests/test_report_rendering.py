"""Snapshot the deterministic Markdown report document and section ordering."""

from __future__ import annotations

from pathlib import Path

from rich.cells import cell_len
from rich.console import Console
from syrupy.assertion import SnapshotAssertion

from benchmarking import models
from benchmarking.reports.database import ReportDatabase
from benchmarking.reports.records import ReportRecord
from benchmarking.reports.render import render_markdown_report_document, render_rich_report_document
from benchmarking.reports.results import ReportTableData, TargetView
from benchmarking.reports.summary import ReportDocument, build_report_document
from benchmarking.reports.timing import (
    CompactTimingRow,
    CompactTimingTable,
    DetailedTimingBlock,
    RulesetTimingRow,
    TimingReport,
)

from .conftest import make_record, make_ruleset_timing, make_timing_summary, write_report


def test_markdown_report_document_snapshot(snapshot: SnapshotAssertion) -> None:
    target = _target()
    table = ReportTableData(
        title="main: per-file wall time",
        headers=("File", "proofs"),
        rows=(("integer_math.egg", "[1.0000s, 1.2000s]"),),
        caption="Within-target wall-time estimates.",
        alignments=("left", "right"),
    )
    timing = TimingReport(
        compact=(
            CompactTimingTable(
                "integer_math.egg",
                (
                    CompactTimingRow(
                        "main",
                        "main/proofs",
                        "450 ms",
                        "200 ms",
                        "100 ms",
                        "50.0 ms",
                        "300 ms",
                        "1.10 s",
                        "success",
                    ),
                ),
            ),
        ),
        detailed=(),
    )
    summary = ReportTableData(
        title="main: proof overhead summary",
        headers=("Metric", "Ratio", "Result"),
        rows=(("wall proofs/off", "1.250x", "unclear"),),
        alignments=("left", "right", "left"),
    )
    document = ReportDocument(
        report_path="/tmp/report.jsonl",
        rounds=2,
        targets=(target,),
        command_argv=("--phase-timings", "egglog/tests/integer_math.egg"),
        targets_table=ReportTableData(
            "Targets",
            ("Role", "Label", "Git", "Dirty", "Binary", "Path"),
            (("target", "main", "123456789abc", "no", "abcdef012345", "/checkout"),),
        ),
        comparisons=(),
        diagnostics=(table,),
        timing=timing,
        summary=(summary,),
    )

    markdown = render_markdown_report_document(document)

    assert markdown == snapshot
    assert markdown.index("## Engine Timing") < markdown.index("## Benchmark Summary")
    for width in (80, 119, 120, 160):
        console = Console(record=True, width=width, color_system=None)
        console.print(render_rich_report_document(document, width))
        rich = console.export_text()
        assert rich.count("Warning:") == (1 if width < 120 else 0)
        assert rich.index("Engine timing") < rich.index("Benchmark summary")
        assert max(cell_len(line) for line in rich.splitlines()) <= width


def test_report_document_uses_bulk_database_results_and_same_run_timing(tmp_path: Path) -> None:
    report_path = tmp_path / "report.jsonl"
    records: list[ReportRecord] = []
    cases: tuple[tuple[models.Treatment, float, int], ...] = (("off", 1.0, 100), ("proofs", 1.5, 125))
    for treatment, wall_sec, rss in cases:
        for round_index in range(2):
            records.append(
                make_record(
                    len(records),
                    started_at=f"2026-07-15T12:00:0{len(records)}Z",
                    treatment=treatment,
                    wall_sec=wall_sec + round_index * 0.1,
                    max_rss_bytes=rss,
                    timing_summary=make_timing_summary(
                        make_ruleset_timing(
                            treatment,
                            search_ns=int(wall_sec * 350_000_000),
                            apply_ns=int(wall_sec * 150_000_000),
                            merge_ns=100_000_000,
                            rebuild_ns=50_000_000,
                        )
                    ),
                )
            )
    write_report(report_path, *records)
    target = _target_with_binary("sha256:bin")
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec(files=(file,), treatments=("off", "proofs"), rounds=2, timeout_sec=120)

    with ReportDatabase(report_path) as database:
        document = build_report_document(database, (target,), spec, phase_timings=True)

    assert [table.title for table in document.diagnostics] == [
        "main: overhead ratios",
        "main: per-file wall time",
        "main: per-file peak RSS",
    ]
    assert document.diagnostics[0].rows == (("file.egg", "[0.728x, 3.930x]"),)
    assert document.timing is not None
    assert [row.search for row in document.timing.compact[0].rows] == ["350 ms", "525 ms"]
    assert [row.apply for row in document.timing.compact[0].rows] == ["150 ms", "225 ms"]
    assert document.summary[-1].title == "main: proof overhead summary"


def test_database_built_multi_target_backend_markdown_snapshot(tmp_path: Path, snapshot: SnapshotAssertion) -> None:
    """Lock the complete Markdown UX to realistic queried report data."""

    report_path = tmp_path / "report.jsonl"
    targets = (
        _labeled_target("baseline", "sha256:baseline"),
        _labeled_target("candidate", "sha256:candidate"),
    )
    cells: tuple[tuple[models.Backend, models.Treatment], ...] = (
        ("main", "term"),
        ("main", "proofs"),
        ("dd", "term"),
        ("dd", "proofs"),
    )
    records: list[ReportRecord] = []
    for target_order, target in enumerate(targets):
        for cell_order, (backend, treatment) in enumerate(cells):
            for round_index in range(2):
                wall_sec = 0.80 + 0.08 * target_order + 0.15 * cell_order + 0.02 * round_index
                records.append(
                    make_record(
                        len(records),
                        started_at=f"2026-07-15T12:00:{len(records):02d}Z",
                        binary_sha256=target.binary_sha256,
                        backend=backend,
                        treatment=treatment,
                        wall_sec=wall_sec,
                        max_rss_bytes=120_000_000 + 5_000_000 * target_order + 2_000_000 * cell_order,
                        timing_summary=make_timing_summary(
                            make_ruleset_timing(
                                "simplify arithmetic and containers",
                                search_ns=int(wall_sec * 220_000_000),
                                apply_ns=int(wall_sec * 80_000_000),
                                merge_ns=45_000_000,
                                rebuild_ns=20_000_000,
                            ),
                            make_ruleset_timing(
                                f"{backend} {treatment} finishing rules",
                                search_ns=int(wall_sec * 120_000_000),
                                apply_ns=int(wall_sec * 60_000_000),
                                merge_ns=25_000_000,
                                rebuild_ns=10_000_000,
                            ),
                        ),
                    )
                )
    write_report(report_path, *records)
    file = models.FileSpec("benchmarks/integer_math.egg", tmp_path / "integer_math.egg", "sha256:file")
    spec = models.BenchmarkSpec(
        files=(file,),
        treatments=("term", "proofs"),
        rounds=2,
        timeout_sec=120,
        backends=("main", "dd"),
    )

    with ReportDatabase(report_path) as database:
        document = build_report_document(
            database,
            targets,
            spec,
            command_argv=(
                "--target",
                "baseline=main",
                "--target",
                "candidate=HEAD",
                "--backend",
                "main,dd",
                "--treatments",
                "term,proofs",
                "--phase-timings",
                "benchmarks/integer_math.egg",
            ),
            phase_timings=True,
        )
        comparison_keys = {
            tuple(row)
            for row in database._connection.execute(
                """
                SELECT
                    baseline_target_order,
                    baseline_cell_order,
                    candidate_target_order,
                    candidate_cell_order
                FROM scope_comparisons
                """
            ).fetchall()
        }

    markdown = render_markdown_report_document(document)
    stable_markdown = markdown.replace(str(report_path), "/tmp/benchmark-report.jsonl")
    assert stable_markdown == snapshot
    assert markdown.index("## Engine Timing") < markdown.index("## Benchmark Summary")
    assert "| baseline | main/term |" in markdown
    assert "| candidate | dd/proofs |" in markdown
    assert comparison_keys == {
        (0, 0, 1, 0),
        (0, 1, 1, 1),
        (0, 2, 1, 2),
        (0, 3, 1, 3),
        (0, 0, 0, 1),
        (0, 2, 0, 3),
        (0, 0, 0, 2),
        (0, 1, 0, 3),
        (1, 0, 1, 1),
        (1, 2, 1, 3),
        (1, 0, 1, 2),
        (1, 1, 1, 3),
    }
    for width in (119, 120):
        console = Console(record=True, width=width, color_system=None)
        console.print(render_rich_report_document(document, width))
        rich = console.export_text()
        assert rich.count("Warning:") == (1 if width < 120 else 0)
        assert "main/term" in rich
        assert "dd/proofs" in rich
        assert rich.index("Engine timing") < rich.index("Benchmark summary")
        assert max(cell_len(line) for line in rich.splitlines()) <= width


def test_database_built_report_surfaces_invalid_cells_and_omits_empty_rss(tmp_path: Path) -> None:
    """Keep invalid selection and no-RSS behavior visible through the full query path."""

    report_path = tmp_path / "report.jsonl"
    records = (
        make_record(0, started_at="2026-07-15T12:00:00Z", treatment="off", max_rss_bytes=None),
        make_record(1, started_at="2026-07-15T12:00:01Z", treatment="off", max_rss_bytes=None),
        make_record(2, started_at="2026-07-15T12:00:02Z", treatment="proofs", max_rss_bytes=None),
        make_record(
            3,
            started_at="2026-07-15T12:00:03Z",
            status="timed-out",
            treatment="proofs",
            wall_sec=None,
            max_rss_bytes=None,
        ),
    )
    write_report(report_path, *records)
    target = _target_with_binary("sha256:bin")
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec(files=(file,), treatments=("off", "proofs"), rounds=2, timeout_sec=120)

    with ReportDatabase(report_path) as database:
        document = build_report_document(database, (target,), spec, phase_timings=True)

    all_tables = (*document.comparisons, *document.diagnostics, *document.summary)
    assert not any("peak RSS" in table.title for table in all_tables)
    assert any(value.startswith("invalid:") for table in all_tables for row in table.rows for value in row)
    assert document.timing is not None
    proofs_row = next(row for row in document.timing.compact[0].rows if row.cell == "main/proofs")
    assert "timeout" in proofs_row.status


def test_rich_report_treats_dynamic_names_as_literal_text() -> None:
    target_label = "target [red]literal[/red] x[/blue]"
    file_label = "file [blue]literal[/blue] y[/green].egg"
    ruleset_label = "rules [green]literal[/green] z[/red]"
    target = TargetView(
        0,
        "candidate",
        target_label,
        ".",
        "/checkout/[target]",
        "HEAD",
        "a" * 40,
        False,
        "sha256:abcdef0123456789",
    )
    timing = TimingReport(
        compact=(
            CompactTimingTable(
                file_label,
                (
                    CompactTimingRow(
                        target_label,
                        "main/proofs",
                        "1.00 ms",
                        "2.00 ms",
                        "3.00 ms",
                        "4.00 ms",
                        "5.00 ms",
                        "15.0 ms",
                        "success",
                    ),
                ),
            ),
        ),
        detailed=(
            DetailedTimingBlock(
                f"{file_label} · main/proofs · {target_label}",
                (
                    RulesetTimingRow(
                        ruleset_label,
                        "10.0 ms",
                        "66.7%",
                        "1.00 ms",
                        "2.00 ms",
                        "500 us",
                        "3.00 ms",
                        "4.00 ms",
                    ),
                ),
            ),
        ),
    )
    ordinary_title = "ordinary [cyan]title[/cyan] q[/bold]"
    document = ReportDocument(
        report_path="/tmp/[report].jsonl",
        rounds=1,
        targets=(target,),
        command_argv=None,
        targets_table=ReportTableData("Targets", ("Role",), (("target",),)),
        comparisons=(),
        diagnostics=(ReportTableData(ordinary_title, ("File",), ((file_label,),)),),
        timing=timing,
        summary=(),
    )
    console = Console(record=True, width=240, color_system=None)

    console.print(render_rich_report_document(document, 240))

    rendered = console.export_text()
    for literal in (target_label, file_label, ruleset_label, ordinary_title, "/tmp/[report].jsonl"):
        assert literal in rendered
    assert "candidate" in rendered


def _target() -> TargetView:
    return TargetView(
        0,
        "target",
        "main",
        ".",
        "/checkout",
        "HEAD",
        "123456789abcdef",
        False,
        "sha256:abcdef0123456789",
    )


def _target_with_binary(binary_sha256: str) -> models.ResolvedTarget:
    request = models.TargetRequest("main=.", ".", "main")
    row = models.TargetRow(".", "/checkout", "HEAD", "123456789abcdef", False, "main")
    return models.ResolvedTarget(request, row, binary_sha256, None)


def _labeled_target(label: str, binary_sha256: str) -> models.ResolvedTarget:
    request = models.TargetRequest(f"{label}=.", ".", label)
    git_sha = ("1" if label == "baseline" else "2") * 40
    row = models.TargetRow(".", f"/checkout/{label}", "HEAD", git_sha, False, label)
    return models.ResolvedTarget(request, row, binary_sha256, None)
