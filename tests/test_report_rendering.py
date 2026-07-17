"""Snapshot the pair report's shared Markdown and human-scale Rich output."""

from __future__ import annotations

from pathlib import Path
from typing import cast

from pytest import MonkeyPatch
from rich.cells import cell_len
from rich.console import Console
from rich.rule import Rule
from syrupy.assertion import SnapshotAssertion

from benchmarking import models
from benchmarking.reports.catalog import ReportCatalog, ReportMessage, ReportTable, report_id
from benchmarking.reports.presentation import (
    build_report_catalog,
    format_duration,
    report_file_labels,
)
from benchmarking.reports.render import render_markdown_report_document, render_rich_report_document
from benchmarking.reports.store import ReportRecord, ReportStore

from .report_fixtures import make_endpoint, make_record, make_ruleset_timing, make_timing_summary, write_report


def test_report_ids_encode_parts_unambiguously() -> None:
    assert report_id("target", "ab", "c") != report_id("target", "a", "bc")


def test_realistic_pair_report_markdown_snapshot(tmp_path: Path, snapshot: SnapshotAssertion) -> None:
    report_path, comparison = _pair_case(tmp_path)
    catalog = build_report_catalog(ReportStore(report_path), comparison, "rulesets")

    markdown = render_markdown_report_document(catalog)
    stable = markdown.replace(str(report_path), "/tmp/benchmark-report.jsonl")

    assert stable == snapshot
    _assert_catalog_invariants(catalog)
    assert tuple(section.id for section in catalog.sections) == (
        "selection",
        "summary",
        "files",
        "phases",
        "rulesets",
    )
    assert "| Baseline | baseline | abc123 | main | off |" in markdown
    assert "| Candidate | candidate | abc123 | dd | proofs |" in markdown
    assert "0.983–1.16x" in markdown
    assert "883 ms–1.14 s" not in markdown
    assert "0.883–1.14 s" in markdown


def test_selection_uses_backend_and_treatment_from_the_comparison(tmp_path: Path) -> None:
    baseline = make_endpoint(target_label="main/off", binary_sha256="sha256:shared", backend="main", treatment="off")
    candidate = make_endpoint(target_label="DD/term", binary_sha256="sha256:shared", backend="dd", treatment="term")
    comparison = models.ComparisonSpec(
        baseline,
        candidate,
        (models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file"),),
        1,
        120,
    )

    markdown = render_markdown_report_document(build_report_catalog(ReportStore(tmp_path / "report.jsonl"), comparison))

    assert "| Baseline | main/off | abc123 | main | off |" in markdown
    assert "| Candidate | DD/term | abc123 | dd | term |" in markdown


def test_shared_formatters_keep_compact_units_and_unambiguous_paths() -> None:
    assert tuple(format_duration(value) for value in (None, 999, 12_500, 1_250_000, 1_250_000_000)) == (
        "—",
        "999 ns",
        "12.5 us",
        "1.25 ms",
        "1.25 s",
    )
    files = (
        models.FileSpec("left/shared.egg", Path("/left/shared.egg"), "sha256:left"),
        models.FileSpec("right/shared.egg", Path("/right/shared.egg"), "sha256:right"),
    )
    assert tuple(report_file_labels(files).values()) == ("left/shared.egg", "right/shared.egg")


def test_rich_report_is_readable_at_realistic_widths(tmp_path: Path) -> None:
    report_path, comparison = _six_file_pair_case(tmp_path)
    catalog = build_report_catalog(ReportStore(report_path), comparison, "rulesets")

    for width in (80, 119, 120, 160, 200):
        console = Console(record=True, width=width, color_system=None)
        console.print(render_rich_report_document(catalog, width))
        rendered = console.export_text()

        assert rendered.count("Warning: detailed Rich report") == (1 if width < 120 else 0)
        assert max(cell_len(line) for line in rendered.splitlines()) <= width
        rule_lines = tuple(line for line in rendered.splitlines() if "─" in line)
        assert len(rule_lines) == 5
        assert all(
            any(title in line for line in rule_lines)
            for title in ("Ruleset comparison", "Phase comparison", "Per-file results", "Comparison", "Summary —")
        )
        assert rendered.index("Ruleset comparison") < rendered.index("Phase comparison")
        assert rendered.index("Phase comparison") < rendered.index("Per-file results")
        assert rendered.index("Per-file results") < rendered.index("Comparison")
        assert rendered.index("Comparison") < rendered.rindex("Summary —")
        assert "…" not in rendered
        assert "Per-file wall time" not in rendered
        assert "Benchmark summary" not in rendered
        assert "math.egg" in rendered
        assert "pointer-analysis-small.egg" in rendered
        assert "herbie.egg" in rendered

    document = render_rich_report_document(catalog, 120)
    rules = tuple(renderable for renderable in document.renderables if isinstance(renderable, Rule))
    assert len(rules) == 5
    assert all(rule.style == "green" for rule in rules)


def test_realistic_six_file_rich_120_snapshot(
    tmp_path: Path,
    monkeypatch: MonkeyPatch,
    snapshot: SnapshotAssertion,
) -> None:
    report_path, comparison = _six_file_pair_case(tmp_path)
    monkeypatch.chdir(tmp_path)
    catalog = build_report_catalog(ReportStore(Path(report_path.name)), comparison, "rulesets")
    console = Console(record=True, width=120, color_system=None)

    console.print(render_rich_report_document(catalog, 120))
    rendered = console.export_text()

    assert rendered == snapshot
    assert rendered.count("Ruleset comparison —") == 6
    assert rendered.count("Phase comparison —") == 6
    assert "Warning: detailed Rich report" not in rendered
    assert "…" not in rendered


def test_detail_level_is_cumulative(tmp_path: Path) -> None:
    report_path, comparison = _pair_case(tmp_path)
    expected = {
        "summary": ("selection", "summary"),
        "files": ("selection", "summary", "files"),
        "phases": ("selection", "summary", "files", "phases"),
        "rulesets": ("selection", "summary", "files", "phases", "rulesets"),
    }

    for detail, section_ids in expected.items():
        catalog = build_report_catalog(
            ReportStore(report_path),
            comparison,
            cast(models.DetailLevel, detail),
        )
        assert tuple(section.id for section in catalog.sections) == section_ids


def test_phase_detail_has_one_six_row_table_per_file_and_one_guide(tmp_path: Path) -> None:
    report_path, comparison = _pair_case(tmp_path)
    catalog = build_report_catalog(ReportStore(report_path), comparison, "phases")

    section = next(section for section in catalog.sections if section.id == "phases")
    assert isinstance(section.blocks[0], ReportMessage)
    tables = tuple(block for block in section.blocks if isinstance(block, ReportTable))
    assert len(tables) == len(comparison.files)
    expected_columns = ("phase", "baseline", "candidate", "delta", "wall_delta")
    assert all(tuple(column.id for column in table.columns) == expected_columns for table in tables)
    assert all(len(table.rows) == 6 for table in tables)


def test_negative_outside_residual_keeps_an_explicit_warning(tmp_path: Path) -> None:
    report_path = tmp_path / "negative-residual.jsonl"
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    baseline = make_endpoint(binary_sha256="sha256:baseline", treatment="off")
    candidate = make_endpoint(binary_sha256="sha256:candidate", treatment="proofs")
    write_report(
        report_path,
        make_record(
            0,
            started_at="2026-07-17T12:00:00Z",
            binary_sha256=baseline.target.binary_sha256,
            treatment=baseline.treatment,
            wall_sec=1.0,
            timing_summary=make_timing_summary(
                make_ruleset_timing(
                    search_ns=1_200_000_000,
                    apply_ns=0,
                    merge_ns=0,
                    rebuild_ns=0,
                )
            ),
        ),
        make_record(
            1,
            started_at="2026-07-17T12:00:01Z",
            binary_sha256=candidate.target.binary_sha256,
            treatment=candidate.treatment,
            wall_sec=1.2,
            timing_summary=make_timing_summary(
                make_ruleset_timing(
                    search_ns=1_100_000_000,
                    apply_ns=0,
                    merge_ns=0,
                    rebuild_ns=0,
                )
            ),
        ),
    )
    comparison = models.ComparisonSpec(baseline, candidate, (file,), 1, 120)

    markdown = render_markdown_report_document(build_report_catalog(ReportStore(report_path), comparison, "phases"))

    assert "!-200 ms · -20.0%" in markdown
    assert "! marks a negative residual" in markdown


def test_ruleset_display_distinguishes_absent_from_measured_zero(tmp_path: Path) -> None:
    report_path = tmp_path / "ruleset-presence.jsonl"
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    baseline = make_endpoint(binary_sha256="sha256:baseline", treatment="off")
    candidate = make_endpoint(binary_sha256="sha256:candidate", treatment="proofs")
    write_report(
        report_path,
        make_record(
            0,
            started_at="2026-07-17T12:00:00Z",
            binary_sha256=baseline.target.binary_sha256,
            treatment=baseline.treatment,
            timing_summary=make_timing_summary(
                make_ruleset_timing("measured-zero", search_ns=0, apply_ns=0, merge_ns=0, rebuild_ns=0),
                make_ruleset_timing("removed", search_ns=10, apply_ns=0, merge_ns=0, rebuild_ns=0),
            ),
        ),
        make_record(
            1,
            started_at="2026-07-17T12:00:01Z",
            binary_sha256=candidate.target.binary_sha256,
            treatment=candidate.treatment,
            timing_summary=make_timing_summary(
                make_ruleset_timing("measured-zero", search_ns=5, apply_ns=0, merge_ns=0, rebuild_ns=0),
                make_ruleset_timing("added", search_ns=20, apply_ns=0, merge_ns=0, rebuild_ns=0),
            ),
        ),
    )
    comparison = models.ComparisonSpec(baseline, candidate, (file,), 1, 120)

    markdown = render_markdown_report_document(build_report_catalog(ReportStore(report_path), comparison, "rulesets"))

    assert "| measured-zero | 0 ns | 5.00 ns | +5.00 ns |" in markdown
    assert "| added | — | 20.0 ns | +20.0 ns |" in markdown


def test_one_file_summary_removes_redundant_wall_and_rss_tails(tmp_path: Path) -> None:
    report_path, comparison = _pair_case(tmp_path)
    one_file = models.ComparisonSpec(
        comparison.baseline,
        comparison.candidate,
        comparison.files[:1],
        comparison.rounds,
        comparison.timeout_sec,
    )
    catalog = build_report_catalog(ReportStore(report_path), one_file)

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
    catalog = build_report_catalog(ReportStore(report_path), one_round)

    summary = render_markdown_report_document(catalog).partition("## Summary —")[2]

    assert "point only" in summary
    assert "[" not in summary


def test_missing_rss_is_one_explicit_unavailable_summary(tmp_path: Path) -> None:
    report_path = tmp_path / "no-rss.jsonl"
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
    catalog = build_report_catalog(ReportStore(report_path), comparison)

    markdown = render_markdown_report_document(catalog)

    assert markdown.count("| Peak RSS |") == 1
    assert "| Peak RSS | Unavailable | — | — | incomplete: peak RSS unavailable |" in markdown


def test_timed_out_file_has_missing_phase_cells_and_ruleset_status(tmp_path: Path) -> None:
    report_path = tmp_path / "timed-out.jsonl"
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    baseline = make_endpoint(binary_sha256="sha256:baseline", treatment="off")
    candidate = make_endpoint(binary_sha256="sha256:candidate", treatment="proofs")
    write_report(
        report_path,
        make_record(0, started_at="2026-07-17T12:00:00Z", binary_sha256="sha256:baseline"),
        make_record(
            1,
            started_at="2026-07-17T12:00:01Z",
            binary_sha256="sha256:candidate",
            treatment="proofs",
            status="timed-out",
        ),
    )
    comparison = models.ComparisonSpec(baseline, candidate, (file,), 1, 120)

    catalog = build_report_catalog(ReportStore(report_path), comparison, "rulesets")
    phase_section = next(section for section in catalog.sections if section.id == "phases")
    phase_table = next(block for block in phase_section.blocks if isinstance(block, ReportTable))
    candidate_column = next(index for index, column in enumerate(phase_table.columns) if column.id == "candidate")
    assert all(row.cells[candidate_column].display == "—" for row in phase_table.rows)
    ruleset_section = next(section for section in catalog.sections if section.id == "rulesets")
    assert isinstance(ruleset_section.blocks[0], ReportMessage)
    assert ruleset_section.blocks[0].text == "Status: timeout row selected"


def _pair_case(tmp_path: Path) -> tuple[Path, models.ComparisonSpec]:
    report_path = tmp_path / "pair.jsonl"
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


def _six_file_pair_case(tmp_path: Path) -> tuple[Path, models.ComparisonSpec]:
    report_path = tmp_path / "six-files.jsonl"
    names = (
        "math.egg",
        "eggcc-extract.egg",
        "pointer-analysis-small.egg",
        "hardboiled.egg",
        "luminal.egg",
        "herbie.egg",
    )
    files = tuple(
        models.FileSpec(f"benchmarks/{name}", tmp_path / name, f"sha256:file-{index}")
        for index, name in enumerate(names)
    )
    baseline = make_endpoint(target_label="old", binary_sha256="sha256:old", treatment="off")
    candidate = make_endpoint(target_label="new", binary_sha256="sha256:new", treatment="proofs")
    records: list[ReportRecord] = []
    for endpoint_order, endpoint in enumerate((baseline, candidate)):
        for file_order, file in enumerate(files):
            baseline_wall = 1.0 + file_order * 0.5
            wall_factor = 1.0 if endpoint_order == 0 else 0.8 + file_order * 0.1
            for round_index in range(2):
                timing_factor = (1.0 + round_index * 0.02) * (1.0 + endpoint_order * (file_order - 2.5) * 0.04)
                rulesets = tuple(
                    make_ruleset_timing(
                        f"ruleset-{ruleset_order:02d}",
                        search_ns=int((ruleset_order + 1) * (file_order + 1) * 2_000_000 * timing_factor),
                        apply_ns=int((ruleset_order + 1) * (file_order + 1) * 1_000_000 * timing_factor),
                        unattributed_ns=int((ruleset_order + 1) * 200_000 * timing_factor),
                        merge_ns=int((ruleset_order + 1) * 500_000 * timing_factor),
                        rebuild_ns=int((ruleset_order + 1) * 250_000 * timing_factor),
                    )
                    for ruleset_order in range(12)
                )
                records.append(
                    make_record(
                        len(records),
                        started_at=f"2026-07-17T12:{len(records):02d}:00Z",
                        binary_sha256=endpoint.target.binary_sha256,
                        file_sha256=file.sha256,
                        treatment=endpoint.treatment,
                        target_label=endpoint.target.row.label,
                        wall_sec=baseline_wall * wall_factor + round_index * 0.01,
                        max_rss_bytes=(100 + file_order * 20 + endpoint_order * 10 + round_index) * 1_000_000,
                        timing_summary=make_timing_summary(*rulesets),
                    )
                )
    write_report(report_path, *records)
    return report_path, models.ComparisonSpec(baseline, candidate, files, 2, 120)


def _assert_catalog_invariants(catalog: ReportCatalog) -> None:
    """Check trusted catalog construction once at the realistic boundary."""

    section_ids = [section.id for section in catalog.sections]
    block_ids = [block.id for section in catalog.sections for block in section.blocks]
    assert len(section_ids) == len(set(section_ids))
    assert len(block_ids) == len(set(block_ids))
    for section in catalog.sections:
        for block in section.blocks:
            if not isinstance(block, ReportTable):
                continue
            column_ids = [column.id for column in block.columns]
            row_ids = [row.id for row in block.rows]
            assert len(column_ids) == len(set(column_ids))
            assert len(row_ids) == len(set(row_ids))
            assert all(len(row.cells) == len(block.columns) for row in block.rows)
