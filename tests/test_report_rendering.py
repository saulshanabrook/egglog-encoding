"""Snapshot the pair report's shared Markdown and human-scale Rich output."""

from __future__ import annotations

from pathlib import Path
from typing import cast

from pytest import MonkeyPatch
from rich import box
from rich.cells import cell_len
from rich.console import Console
from rich.rule import Rule
from syrupy.assertion import SnapshotAssertion

from benchmarking import models
from benchmarking.reports.analysis import PhaseValues
from benchmarking.reports.catalog import ReportCatalog, ReportMessage, ReportTable, report_id
from benchmarking.reports.presentation import (
    _important_phase_changes,
    build_report_catalog,
    format_duration,
    report_file_labels,
)
from benchmarking.reports.render import render_markdown_report_document, render_rich_report_document, render_rich_table
from benchmarking.reports.store import ReportRecord, ReportStore
from benchmarking.workloads import DEFAULT_WORKLOADS

from .report_fixtures import (
    make_endpoint,
    make_record,
    make_ruleset_timing,
    make_target,
    make_timing_summary,
    write_report,
)


def _header_positions(lines: list[str], labels: tuple[str, ...]) -> list[tuple[int, ...]]:
    return [tuple(line.index(label) for label in labels) for line in lines if all(label in line for label in labels)]


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
    assert "| Baseline | baseline | abc123 | off |" in markdown
    assert "| Candidate | candidate | abc123 | proofs |" in markdown
    assert "0.983–1.16x" in markdown
    assert "883 ms–1.14 s" not in markdown
    assert "0.883–1.14 s" in markdown


def test_selection_uses_treatment_from_the_comparison(tmp_path: Path) -> None:
    baseline = make_endpoint(target_label="off", binary_sha256="sha256:shared", treatment="off")
    candidate = make_endpoint(target_label="term", binary_sha256="sha256:shared", treatment="term")
    comparison = models.ComparisonSpec(
        baseline,
        candidate,
        (models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file"),),
        1,
        120,
    )

    markdown = render_markdown_report_document(build_report_catalog(ReportStore(tmp_path / "report.jsonl"), comparison))

    assert "| Baseline | off | abc123 | off |" in markdown
    assert "| Candidate | term | abc123 | term |" in markdown


def test_selection_warns_when_same_engine_binary_and_treatment_both_change(tmp_path: Path) -> None:
    comparison = models.ComparisonSpec(
        models.BenchmarkEndpoint(make_target(binary_sha256="sha256:before"), "off"),
        models.BenchmarkEndpoint(make_target(binary_sha256="sha256:after"), "proofs"),
        (models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file"),),
        1,
        120,
    )

    markdown = render_markdown_report_document(build_report_catalog(ReportStore(tmp_path / "report.jsonl"), comparison))

    assert "This comparison changes both target and treatment" in markdown


def test_selection_does_not_treat_cross_engine_binary_difference_as_target_change(tmp_path: Path) -> None:
    original = make_target(binary_sha256="sha256:egglog")
    target = models.ResolvedTarget(
        original.request,
        original.row,
        original.binary_sha256,
        original.binary_path,
        (
            models.EngineBinary("egglog", "sha256:egglog", None),
            models.EngineBinary("egg", "sha256:egg", None),
        ),
        "egglog",
    )
    comparison = models.ComparisonSpec(
        models.BenchmarkEndpoint(target, "egg-proofs"),
        models.BenchmarkEndpoint(target, "proofs"),
        (models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file"),),
        1,
        120,
    )

    markdown = render_markdown_report_document(build_report_catalog(ReportStore(tmp_path / "report.jsonl"), comparison))

    assert "This comparison changes both target and treatment" not in markdown


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
    ellipsis_count: int | None = None

    for width in (80, 119, 120, 160, 200):
        console = Console(record=True, width=width, color_system=None)
        console.print(render_rich_report_document(catalog, width))
        rendered = console.export_text()

        assert rendered.count("Warning: detailed Rich report") == (1 if width < 120 else 0)
        assert max(cell_len(line) for line in rendered.splitlines()) <= width
        rule_lines = tuple(line for line in rendered.splitlines() if "─" in line)
        assert all(
            any(title in line for line in rule_lines)
            for title in (
                "Ruleset drivers",
                "Slowdown decomposition",
                "Per-file results",
                "Comparison",
                "Summary —",
            )
        )
        assert rendered.index("Ruleset drivers") < rendered.index("Slowdown decomposition")
        assert rendered.index("Slowdown decomposition") < rendered.index("Per-file results")
        assert rendered.index("Per-file results") < rendered.index("Comparison")
        assert rendered.index("Comparison") < rendered.rindex("Summary —")
        if ellipsis_count is None:
            ellipsis_count = rendered.count("…")
            assert ellipsis_count > 0
        else:
            assert rendered.count("…") == ellipsis_count
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
    assert rendered.count("Ruleset drivers —") == 6
    assert rendered.count("Slowdown decomposition") >= 1
    assert "Warning: detailed Rich report" not in rendered
    assert "Other (7 more source rulesets)" in rendered


def test_repeated_rich_table_schemas_share_column_positions(tmp_path: Path) -> None:
    report_path, comparison = _six_file_pair_case(tmp_path)
    catalog = build_report_catalog(ReportStore(report_path), comparison, "rulesets")

    for width in (120, 160, 200):
        console = Console(record=True, width=width, color_system=None)
        console.print(render_rich_report_document(catalog, width))
        lines = console.export_text().splitlines()

        ruleset_positions = _header_positions(lines, ("Driver", "Δ", "Wall share", "Important phase changes"))
        assert len(ruleset_positions) == len(comparison.files)
        assert len(set(ruleset_positions)) == 1

        result_positions = _header_positions(
            lines, ("File", "Baseline (95% CI)", "Candidate (95% CI)", "Ratio (95% CI)", "Result")
        )
        assert len(result_positions) == 2
        assert len(set(result_positions)) == 1


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


def test_all_rich_tables_use_one_compact_style(tmp_path: Path) -> None:
    report_path, comparison = _pair_case(tmp_path)
    catalog = build_report_catalog(ReportStore(report_path), comparison, "rulesets")
    tables = [
        render_rich_table(block)
        for section in catalog.sections
        for block in section.blocks
        if isinstance(block, ReportTable)
    ]

    assert tables
    assert all(table.box is box.SIMPLE_HEAVY and not table.show_lines for table in tables)


def test_phase_detail_has_additive_parent_and_generated_breakdown_tables(tmp_path: Path) -> None:
    report_path, comparison = _pair_case(tmp_path)
    catalog = build_report_catalog(ReportStore(report_path), comparison, "phases")

    section = next(section for section in catalog.sections if section.id == "phases")
    tables = tuple(block for block in section.blocks if isinstance(block, ReportTable))
    assert len(tables) == 2
    table, generated = tables
    assert tuple(column.id for column in table.columns) == (
        "file",
        "wall_delta",
        "typecheck",
        "frontend",
        "program",
        "equality",
        "commands",
        "residual",
    )
    assert len(table.rows) == len(comparison.files) + 1
    assert table.rows[0].cells[0].display == "Suite total (2 files)"
    assert [row.cells[0].display for row in table.rows[1:]] == ["math.egg", "rewrite.egg"]
    assert table.columns[3].label == "Frontend"
    assert table.columns[4].label == "Program"
    assert table.columns[5].label == "Equality"
    assert tuple(column.id for column in generated.columns) == (
        "file",
        "generated_phase",
        "delta",
        "wall_share",
    )
    assert len(generated.rows) == 4 * len(table.rows)
    assert [row.cells[1].display for row in generated.rows[:4]] == [
        "Construct",
        "Signatures",
        "Resolve/cache",
        "Lower/materialize",
    ]
    assert generated.caption is not None and "generated portion of Frontend" in generated.caption
    assert table.caption is not None and "candidate − baseline" in table.caption
    assert all("%" in cell.display.partition("  ")[0] for cell in table.rows[0].cells[2:])
    assert all(sum("◆" in cell.display for cell in row.cells[2:]) == 1 for row in table.rows)
    assert table.rows[0].cells[2].tone == "muted"
    assert table.rows[0].cells[4].tone == "emphasis"
    assert table.rows[1].cells[1].tone == "positive"
    assert table.rows[1].cells[4].tone == "emphasis"
    assert table.rows[1].cells[7].tone == "positive"


def test_generated_breakdown_preserves_signed_submillisecond_deltas(tmp_path: Path) -> None:
    report_path = tmp_path / "generated-units.jsonl"
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
                frontend_generated_signatures_ns=3_000,
                frontend_generated_lower_ns=5_000_000,
            ),
        ),
        make_record(
            1,
            started_at="2026-07-17T12:00:01Z",
            binary_sha256=candidate.target.binary_sha256,
            treatment=candidate.treatment,
            wall_sec=1.01,
            timing_summary=make_timing_summary(
                frontend_generated_construct_ns=125,
                frontend_generated_signatures_ns=500,
                frontend_generated_resolve_ns=1_250_000,
            ),
        ),
    )
    comparison = models.ComparisonSpec(baseline, candidate, (file,), 1, 120)

    catalog = build_report_catalog(ReportStore(report_path), comparison, "phases")
    section = next(section for section in catalog.sections if section.id == "phases")
    generated = tuple(block for block in section.blocks if isinstance(block, ReportTable))[1]
    file_rows = generated.rows[4:]

    assert [row.cells[1].display for row in file_rows] == [
        "Construct",
        "Signatures",
        "Resolve/cache",
        "Lower/materialize",
    ]
    assert [row.cells[2].raw for row in file_rows] == [125.0, -2_500.0, 1_250_000.0, -5_000_000.0]
    assert all(row.cells[2].raw != 0 for row in file_rows)
    assert [row.cells[2].display for row in file_rows] == [
        "+125 ns",
        "-2.50 us",
        "+1.25 ms",
        "-5.00 ms",
    ]


def test_default_ten_file_markdown_and_rich_include_generated_breakdown(tmp_path: Path) -> None:
    report_path = tmp_path / "default-ten.jsonl"
    files = tuple(
        models.FileSpec(workload.file, tmp_path / Path(workload.file).name, f"sha256:file-{index}")
        for index, workload in enumerate(DEFAULT_WORKLOADS)
    )
    assert len(files) == 10
    baseline = make_endpoint(binary_sha256="sha256:baseline", treatment="off")
    candidate = make_endpoint(binary_sha256="sha256:candidate", treatment="proofs")
    records: list[ReportRecord] = []
    for endpoint_order, endpoint in enumerate((baseline, candidate)):
        for file_order, file in enumerate(files):
            records.append(
                make_record(
                    len(records),
                    started_at=f"2026-07-17T12:{len(records):02d}:00Z",
                    binary_sha256=endpoint.target.binary_sha256,
                    file_sha256=file.sha256,
                    treatment=endpoint.treatment,
                    wall_sec=1.0 + endpoint_order * 0.01,
                    timing_summary=make_timing_summary(
                        frontend_generated_construct_ns=(endpoint_order + file_order) * 100,
                        frontend_generated_signatures_ns=(endpoint_order + file_order) * 1_000,
                        frontend_generated_resolve_ns=(endpoint_order + file_order) * 1_000_000,
                        frontend_generated_lower_ns=(endpoint_order + file_order) * 10_000_000,
                    ),
                )
            )
    write_report(report_path, *records)
    comparison = models.ComparisonSpec(baseline, candidate, files, 1, 120)

    catalog = build_report_catalog(ReportStore(report_path), comparison, "phases")
    section = next(section for section in catalog.sections if section.id == "phases")
    generated = tuple(block for block in section.blocks if isinstance(block, ReportTable))[1]
    markdown = render_markdown_report_document(catalog)
    console = Console(record=True, width=120, color_system=None)
    console.print(render_rich_report_document(catalog, 120))
    rich = console.export_text()

    assert len(generated.rows) == 44
    assert [row.cells[1].display for row in generated.rows] == [
        label for _ in range(11) for label in ("Construct", "Signatures", "Resolve/cache", "Lower/materialize")
    ]
    assert "### Generated frontend breakdown" in markdown
    assert all(Path(workload.file).name in markdown for workload in DEFAULT_WORKLOADS)
    assert "Generated frontend breakdown" in rich
    assert "Warning: detailed Rich report" not in rich
    assert max(cell_len(line) for line in rich.splitlines()) <= 120


def test_ruleset_detail_unfolds_program_and_equality_with_explicit_children(tmp_path: Path) -> None:
    report_path, comparison = _pair_case(tmp_path)
    catalog = build_report_catalog(ReportStore(report_path), comparison, "rulesets")

    section = next(section for section in catalog.sections if section.id == "rulesets")
    guide = section.blocks[0]
    assert isinstance(guide, ReportMessage)
    assert "Parent rows exactly match" in guide.text
    assert "one global Native rebuild replaced row" in guide.text
    assert "top 5 plus an exact per-group Other" in guide.text
    assert "↳ marks children" in guide.text
    assert "max(1 ms, 10% of |row Δ|)" in guide.text

    math = next(
        block for block in section.blocks if isinstance(block, ReportTable) and block.title.endswith("math.egg")
    )
    rewrite = next(
        block for block in section.blocks if isinstance(block, ReportTable) and block.title.endswith("rewrite.egg")
    )
    assert tuple(column.id for column in math.columns) == ("driver", "delta", "share", "important_phases")
    assert math.columns[2].label == "Wall share"
    assert [row.cells[0].display for row in math.rows] == [
        "Program rules — own work",
        "↳ simplify",
        "↳ finish",
        "Equality/rebuild — net",
    ]
    assert math.rows[0].cells[0].tone == "emphasis"
    assert math.rows[0].cells[1].tone == "positive"
    assert math.rows[0].cells[3].display == "◆ Search -80.0 ms; Apply -36.0 ms"
    assert math.rows[0].cells[2].display == "+58.0%"
    assert math.rows[1].cells[2].display == ""
    assert math.rows[3].cells[0].tone == "emphasis"
    assert math.rows[3].cells[3].display == "0 ns"
    assert math.caption is not None and "Program + Equality account for +58.0%" in math.caption
    assert rewrite.rows[0].cells[1].tone == "default"


def test_ruleset_edges_label_empty_names_and_break_equal_deltas_by_name(tmp_path: Path) -> None:
    report_path = tmp_path / "ruleset-ties.jsonl"
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    baseline = make_endpoint(binary_sha256="sha256:baseline", treatment="off")
    candidate = make_endpoint(binary_sha256="sha256:candidate", treatment="proofs")
    unchanged = make_ruleset_timing("unchanged", search_ns=0, apply_ns=0, merge_ns=0)
    tied_names = ("zeta", "beta", "eta", "delta", "gamma", "alpha", "epsilon")
    write_report(
        report_path,
        make_record(
            0,
            started_at="2026-07-17T12:00:00Z",
            binary_sha256=baseline.target.binary_sha256,
            timing_summary=make_timing_summary(unchanged, native_rebuild_ns=0),
        ),
        make_record(
            1,
            started_at="2026-07-17T12:00:01Z",
            binary_sha256=candidate.target.binary_sha256,
            treatment="proofs",
            wall_sec=1.2,
            timing_summary=make_timing_summary(
                *(make_ruleset_timing(name, search_ns=10_000_000, apply_ns=0, merge_ns=0) for name in tied_names),
                make_ruleset_timing("", role="equality", search_ns=1_000_000, apply_ns=0, merge_ns=0),
                unchanged,
                native_rebuild_ns=0,
            ),
        ),
    )
    comparison = models.ComparisonSpec(baseline, candidate, (file,), 1, 120)

    catalog = build_report_catalog(ReportStore(report_path), comparison, "rulesets")
    section = next(section for section in catalog.sections if section.id == "rulesets")
    table = next(block for block in section.blocks if isinstance(block, ReportTable))
    default_ruleset = next(row for row in table.rows if row.cells[0].display == "↳ <default ruleset>")

    assert default_ruleset.cells[0].raw == ""
    assert [row.cells[0].display for row in table.rows[:8]] == [
        "Program rules — own work",
        "↳ alpha",
        "↳ beta",
        "↳ delta",
        "↳ epsilon",
        "↳ eta",
        "↳ Other (2 more source rulesets)",
        "Equality/rebuild — net",
    ]
    assert table.rows[6].cells[1].display == "+20.0 ms"


def test_ratio_tones_use_green_for_improvements_and_dim_unclear_results(tmp_path: Path) -> None:
    report_path, comparison = _pair_case(tmp_path)
    catalog = build_report_catalog(ReportStore(report_path), comparison)
    summary = next(section for section in catalog.sections if section.id == "summary")
    table = next(block for block in summary.blocks if isinstance(block, ReportTable))
    expected = {
        "higher": "default",
        "invalid": "error",
        "lower": "positive",
        "point_only": "muted",
        "unclear": "muted",
    }

    for row in table.rows:
        result = row.cells[4].raw
        assert isinstance(result, str)
        assert row.cells[3].tone == expected[result]
        assert row.cells[4].tone == expected[result]


def test_negative_residual_keeps_an_explicit_warning(tmp_path: Path) -> None:
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
                ),
                native_rebuild_ns=0,
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
                ),
                native_rebuild_ns=0,
            ),
        ),
    )
    comparison = models.ComparisonSpec(baseline, candidate, (file,), 1, 120)

    markdown = render_markdown_report_document(build_report_catalog(ReportStore(report_path), comparison, "phases"))

    assert "!◆ +150%  +300 ms" in markdown
    assert "! means an endpoint's mean residual is negative" in markdown


def test_important_phase_changes_use_the_documented_deterministic_threshold() -> None:
    phases = PhaseValues(500_000, 10_000_000, 3_000_000, 2_000_000, 4_000_000, 500_000)

    assert _important_phase_changes(phases) == (
        "◆ Search +10.0 ms; Apply +3.00 ms; Execution +2.00 ms; Merge +4.00 ms; …"
    )


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
    phase_table, generated = tuple(block for block in phase_section.blocks if isinstance(block, ReportTable))
    assert len(phase_table.rows) == 2
    assert all(cell.display == "—" for row in phase_table.rows for cell in row.cells[1:])
    assert len(generated.rows) == 8
    assert [row.cells[1].display for row in generated.rows] == [
        label for _ in range(2) for label in ("Construct", "Signatures", "Resolve/cache", "Lower/materialize")
    ]
    assert all(row.cells[2].display == row.cells[3].display == "—" for row in generated.rows)
    ruleset_section = next(section for section in catalog.sections if section.id == "rulesets")
    status = next(
        block
        for block in ruleset_section.blocks
        if isinstance(block, ReportMessage) and block.title == "Ruleset drivers — file.egg"
    )
    assert status.text == "Status: timeout row selected"
    summary_section = next(section for section in catalog.sections if section.id == "summary")
    summary_table = next(block for block in summary_section.blocks if isinstance(block, ReportTable))
    invalid = next(row for row in summary_table.rows if row.cells[4].raw == "invalid")
    assert invalid.cells[3].tone == "error"
    assert invalid.cells[4].tone == "error"


def _pair_case(tmp_path: Path) -> tuple[Path, models.ComparisonSpec]:
    report_path = tmp_path / "pair.jsonl"
    files = (
        models.FileSpec("benchmarks/math.egg", tmp_path / "math.egg", "sha256:file-math"),
        models.FileSpec("benchmarks/rewrite.egg", tmp_path / "rewrite.egg", "sha256:file-rewrite"),
    )
    baseline = make_endpoint(
        target_label="baseline",
        binary_sha256="sha256:baseline",
        treatment="off",
    )
    candidate = make_endpoint(
        target_label="candidate",
        binary_sha256="sha256:candidate",
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
                            ),
                            make_ruleset_timing(
                                "finish",
                                search_ns=int(wall * 100_000_000),
                                apply_ns=int(wall * 60_000_000),
                                merge_ns=20_000_000,
                            ),
                            native_rebuild_ns=40_000_000,
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
                        execution_ns=int((ruleset_order + 1) * 200_000 * timing_factor),
                        merge_ns=int((ruleset_order + 1) * 500_000 * timing_factor),
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
                        timing_summary=make_timing_summary(
                            *rulesets,
                            native_rebuild_ns=sum(
                                int((ruleset_order + 1) * 250_000 * timing_factor) for ruleset_order in range(12)
                            ),
                        ),
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
