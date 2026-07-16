"""Snapshot timing serialization and exercise realistic Rich terminal widths."""

from __future__ import annotations

from pathlib import Path

from rich.cells import cell_len
from rich.console import Console
from syrupy.assertion import SnapshotAssertion

from benchmarking import models
from benchmarking.reports.render import render_markdown_timing, render_rich_timing
from benchmarking.reports.results import CompactTimingView, RulesetTimingView
from benchmarking.reports.timing import build_timing_report, format_duration, format_share


def test_duration_and_share_formatting() -> None:
    assert format_duration(0) == "0 ns"
    assert format_duration(999) == "999 ns"
    assert format_duration(1_500) == "1.50 us"
    assert format_duration(2_500_000) == "2.50 ms"
    assert format_duration(3_250_000_000) == "3.25 s"
    assert format_duration(-2_500_000, attribution=True) == "!-2.50 ms"
    assert format_share(None) == "—"
    assert format_share(0.0005) == "<0.1%"


def test_markdown_compact_and_detailed_report(snapshot: SnapshotAssertion) -> None:
    targets = (_target("baseline", "sha256:baseline"), _target("candidate", "sha256:candidate"))
    spec = _spec()
    compact = (
        _compact(0, 0, 500_000, 200_000, 150_000, 150_000, 1_250_000, unattributed_ns=50_000),
        _compact(1, 0, 400_000, 120_000, 110_000, 120_000, 900_000, unattributed_ns=30_000),
        _compact(0, 1, issue="timeout row selected"),
        _compact(1, 1, 700_000, 300_000, 200_000, 300_000, 1_400_000, unattributed_ns=40_000),
    )
    rulesets = (
        _ruleset(
            0,
            0,
            0,
            "",
            450_000,
            150_000,
            100_000,
            50_000,
            1_050_000,
            770_000,
            unattributed_ns=20_000,
        ),
        _ruleset(1, 0, 0, "", 0, 0, 0, 0, 750_000, 770_000),
        _ruleset(
            0,
            0,
            1,
            "simplify|nested",
            70_000,
            30_000,
            50_000,
            100_000,
            1_050_000,
            700_000,
            unattributed_ns=30_000,
        ),
        _ruleset(1, 0, 1, "simplify|nested", 350_000, 150_000, 100_000, 100_000, 750_000, 700_000),
        _ruleset(0, 0, 2, "candidate-only", None, None, None, None, 1_000_000, 50_000),
        _ruleset(1, 0, 2, "candidate-only", 15_000, 5_000, 10_000, 20_000, 750_000, 50_000),
        _ruleset(1, 1, 0, "proof extraction", 700_000, 300_000, 200_000, 300_000, 1_500_000, 1_500_000),
    )

    report = build_timing_report(
        compact,
        rulesets,
        targets,
        spec,
        detailed=True,
        file_labels=("integer_math.egg",),
    )

    assert render_markdown_timing(report) == snapshot


def test_view_order_preserves_absent_rows_and_recorded_zeroes() -> None:
    targets = (_target("baseline", "sha256:baseline"), _target("candidate", "sha256:candidate"))
    spec = _spec(treatments=("proofs",))
    compact = (
        _compact(0, 0, 5, 3, 1, 1, 20, treatment="proofs"),
        _compact(1, 0, 10, 8, 1, 1, 30, treatment="proofs"),
    )
    rulesets = (
        _ruleset(0, 0, 0, "candidate-only", None, None, None, None, 10, 20, treatment="proofs"),
        _ruleset(1, 0, 0, "candidate-only", 10, 8, 1, 1, 20, 20, treatment="proofs"),
        _ruleset(0, 0, 1, "baseline-only", 5, 3, 1, 1, 10, 10, treatment="proofs"),
        _ruleset(1, 0, 1, "baseline-only", None, None, None, None, 20, 10, treatment="proofs"),
        _ruleset(0, 0, 2, "recorded-zero", 0, 0, 0, 0, 10, 0, treatment="proofs"),
        _ruleset(1, 0, 2, "recorded-zero", 0, 0, 0, 0, 20, 0, treatment="proofs"),
    )

    report = build_timing_report(compact, rulesets, targets, spec, detailed=True)

    baseline, candidate = report.detailed
    assert [row.ruleset for row in baseline.rows] == ["candidate-only", "baseline-only", "recorded-zero"]
    assert [row.ruleset for row in candidate.rows] == ["candidate-only", "baseline-only", "recorded-zero"]
    assert baseline.rows[0].total == "—"
    assert candidate.rows[1].total == "—"
    assert baseline.rows[2].total == "0 ns"
    assert candidate.rows[2].total == "0 ns"


def test_rich_timing_warns_exactly_once_below_120_and_always_renders() -> None:
    targets = (_target("a-long-baseline-target", "sha256:baseline"), _target("candidate", "sha256:candidate"))
    spec = _spec(treatments=("proofs",))
    compact = (
        _compact(0, 0, 5, 3, 1, 1, 20, treatment="proofs"),
        _compact(1, 0, 10, 8, 1, 1, 30, treatment="proofs"),
    )
    rulesets = (
        _ruleset(0, 0, 0, "a very long ruleset name that may fold", 5, 3, 1, 1, 10, 20, treatment="proofs"),
        _ruleset(1, 0, 0, "a very long ruleset name that may fold", 0, 0, 0, 0, 20, 20, treatment="proofs"),
        _ruleset(0, 0, 1, "other", 0, 0, 0, 0, 10, 20, treatment="proofs"),
        _ruleset(1, 0, 1, "other", 10, 8, 1, 1, 20, 20, treatment="proofs"),
    )
    report = build_timing_report(compact, rulesets, targets, spec, detailed=True)

    for width in (80, 119, 120, 160):
        console = Console(record=True, width=width, color_system=None)
        console.print(render_rich_timing(report, width))
        output = console.export_text()
        assert output.count("Warning:") == (1 if width < 120 else 0)
        assert max(cell_len(line) for line in output.splitlines()) <= width
        assert "Engine timing" in output
        assert "Detailed timing" in output
        assert "Unattributed" in output


def test_default_six_file_compact_report_stays_bounded_at_realistic_widths() -> None:
    target = _target("main", "sha256:main")
    files = tuple(
        models.FileSpec(
            f"benchmarks/case-{file_order}.egg", Path(f"/tmp/case-{file_order}.egg"), f"sha256:{file_order}"
        )
        for file_order in range(6)
    )
    spec = models.BenchmarkSpec(files=files, treatments=("off", "term", "proofs"), rounds=6, timeout_sec=120)
    compact = tuple(
        _compact(
            0,
            cell_order,
            700_000,
            300_000,
            250_000,
            250_000,
            2_000_000,
            file_order=file_order,
            treatment=treatment,
        )
        for file_order in range(6)
        for cell_order, treatment in enumerate(spec.treatments)
    )
    rulesets = tuple(
        _ruleset(
            0,
            cell_order,
            0,
            "rules",
            700_000,
            300_000,
            250_000,
            250_000,
            1_500_000,
            1_500_000,
            file_order=file_order,
            treatment=treatment,
        )
        for file_order in range(6)
        for cell_order, treatment in enumerate(spec.treatments)
    )
    report = build_timing_report(compact, rulesets, (target,), spec, detailed=False)

    for width in (80, 119, 120, 160):
        console = Console(record=True, width=width, color_system=None)
        console.print(render_rich_timing(report, width))
        lines = console.export_text().splitlines()
        assert sum("Warning:" in line for line in lines) == (1 if width < 120 else 0)
        assert max(map(cell_len, lines)) <= width
        assert len(lines) <= 70

    markdown = render_markdown_timing(report)
    assert markdown.count("### benchmarks/case-") == 6
    assert markdown.count("| main | main/") == 18


def _compact(
    target_order: int,
    cell_order: int,
    search_ns: float | None = None,
    apply_ns: float | None = None,
    merge_ns: float | None = None,
    rebuild_ns: float | None = None,
    wall_ns: float | None = None,
    *,
    file_order: int = 0,
    treatment: models.Treatment = "off",
    issue: str | None = None,
    unattributed_ns: float | None = None,
) -> CompactTimingView:
    pre_merge = None
    ruleset_total = None
    outside_rulesets = None
    other = None
    if issue is None:
        assert search_ns is not None and apply_ns is not None
        assert merge_ns is not None and rebuild_ns is not None and wall_ns is not None
        unattributed_ns = 0 if unattributed_ns is None else unattributed_ns
        pre_merge = search_ns + apply_ns + unattributed_ns
        ruleset_total = pre_merge + merge_ns + rebuild_ns
        outside_rulesets = wall_ns - ruleset_total
        other = wall_ns - search_ns - apply_ns - merge_ns - rebuild_ns
    return CompactTimingView(
        target_order,
        file_order,
        cell_order,
        "main",
        treatment,
        search_ns,
        apply_ns,
        None if search_ns is None or apply_ns is None else search_ns + apply_ns,
        unattributed_ns,
        pre_merge,
        merge_ns,
        rebuild_ns,
        ruleset_total,
        outside_rulesets,
        other,
        wall_ns,
        wall_ns is not None,
        "available" if issue is None else "invalid",
        issue,
    )


def _ruleset(
    target_order: int,
    cell_order: int,
    ruleset_order: int,
    name: str,
    search_ns: float | None,
    apply_ns: float | None,
    merge_ns: float | None,
    rebuild_ns: float | None,
    denominator_ns: float | None,
    maximum_target_total: float,
    *,
    file_order: int = 0,
    treatment: models.Treatment = "off",
    unattributed_ns: float | None = None,
) -> RulesetTimingView:
    phases = (search_ns, apply_ns, unattributed_ns, merge_ns, rebuild_ns)
    if all(phase is None for phase in phases):
        search_and_apply = None
        pre_merge = None
        total = None
        has_samples = False
    else:
        assert search_ns is not None
        assert apply_ns is not None
        assert merge_ns is not None
        assert rebuild_ns is not None
        unattributed_ns = 0 if unattributed_ns is None else unattributed_ns
        search_and_apply = search_ns + apply_ns
        pre_merge = search_and_apply + unattributed_ns
        total = pre_merge + merge_ns + rebuild_ns
        has_samples = True
    return RulesetTimingView(
        file_order,
        cell_order,
        ruleset_order,
        target_order,
        "main",
        treatment,
        name,
        search_ns,
        apply_ns,
        search_and_apply,
        unattributed_ns,
        pre_merge,
        merge_ns,
        rebuild_ns,
        total,
        maximum_target_total,
        denominator_ns,
        has_samples,
        "available",
        None if total is None or not denominator_ns else total / denominator_ns,
    )


def _target(label: str, binary_sha256: str) -> models.ResolvedTarget:
    request = models.TargetRequest(f"{label}=.", ".", label)
    row = models.TargetRow(".", "/checkout", "HEAD", binary_sha256[-12:], False, label)
    return models.ResolvedTarget(request, row, binary_sha256, None)


def _spec(*, treatments: tuple[models.Treatment, ...] = ("off", "proofs")) -> models.BenchmarkSpec:
    file = models.FileSpec("path/to/integer_math.egg", Path("/tmp/integer_math.egg"), "sha256:file")
    return models.BenchmarkSpec(files=(file,), treatments=treatments, rounds=2, timeout_sec=120)
