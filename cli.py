"""Terminal rendering of benchmark reports with Rich.

Lays out the values from ``tables.py`` as Rich tables/trees and maps result
statuses to Rich styles. All numbers and formatting come from ``tables.py``.
"""

from __future__ import annotations

from collections.abc import Sequence

from pandera.typing import DataFrame
from rich import box
from rich.console import Console
from rich.markup import escape
from rich.table import Table
from rich.text import Text
from rich.tree import Tree

from models import (
    BenchmarkSpec,
    CellMap,
    RatioSummary,
    ReportDestination,
    ResolvedTarget,
    TargetCellMaps,
    Treatment,
)
from report_frame import ReportFrame
from tables import (
    PROOF_OVERHEAD_CAPTION,
    TARGET_PEAK_RSS_CAPTION,
    TARGET_WALL_TIME_CAPTION,
    comparison_result,
    format_bytes_summary,
    format_percent_change,
    format_ratio_summary,
    format_seconds_summary,
    format_wall_time_change,
    format_worst_file,
    geometric_mean_ratio,
    lower_is_better_result,
    proof_gate_result,
    ratio_pairs,
    ratio_specs,
    ratio_summary,
    suite_ratio,
    summary_pairs,
    target_cell_summaries,
    target_rss_cell_summaries,
    target_treatment_file_cells,
    treatment_file_cells,
    worst_file_ratio,
)

RESULT_STYLES = {
    "descriptive": "dim",
    "established": "green",
    "faster": "green",
    "invalid": "bold red",
    "less": "green",
    "more": "red",
    "not established": "red",
    "point only": "dim",
    "slower": "red",
    "unclear": "yellow",
}


def result_style(status: str) -> str:
    return RESULT_STYLES.get(status, "")


def styled_status(status: str, text: str | None = None) -> Text:
    return Text(text or status, style=result_style(status))


def format_comparison_result(summary: RatioSummary) -> Text:
    result = comparison_result(summary)
    if result == "invalid" and summary.issue is not None:
        return styled_status(result, f"invalid: {summary.issue}")
    return styled_status(result)


def format_lower_is_better_result(summary: RatioSummary) -> Text:
    result = lower_is_better_result(summary)
    if result == "invalid" and summary.issue is not None:
        return styled_status(result, f"invalid: {summary.issue}")
    return styled_status(result)


def format_proof_gate_result(summary: RatioSummary) -> Text:
    status, text = proof_gate_result(summary)
    return styled_status(status, text)


def report_table(title: str, *, caption: str | None = None, show_lines: bool = False) -> Table:
    return Table(
        title=title,
        title_style="bold",
        caption=caption,
        caption_style="dim",
        caption_justify="left",
        header_style="bold",
        box=box.SIMPLE_HEAVY,
        show_lines=show_lines,
    )


def render_report(
    console: Console,
    report_destination: ReportDestination,
    rows: DataFrame[ReportFrame],
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    console.rule("[bold]Benchmark report[/bold]")
    console.print(f"Report: [bold]{escape(report_destination.display_path)}[/bold]")
    console.print(f"Selected rows per cell: [bold]{spec.rounds}[/bold]")

    render_targets_tree(console, targets)

    cell_maps = {target: target_cell_summaries(rows, target, spec) for target in targets}
    rss_cell_maps = {target: target_rss_cell_summaries(rows, target, spec) for target in targets}
    if len(targets) > 1:
        render_per_file_wall_time_change(console, cell_maps, targets, spec)
        render_per_file_peak_rss_change(console, rss_cell_maps, targets, spec)

    for target in targets:
        render_target_diagnostics(console, cell_maps[target], rss_cell_maps[target], target, spec)

    render_benchmark_summary(console, cell_maps, rss_cell_maps, targets, spec)


def render_targets_tree(console: Console, targets: Sequence[ResolvedTarget]) -> None:
    tree = Tree("[bold]Targets[/bold]", guide_style="dim")
    for index, target in enumerate(targets):
        role = "target"
        if len(targets) > 1:
            role = "baseline" if index == 0 else "candidate"
        dirty = "dirty" if target.row.is_dirty else "clean"
        binary = target.binary_sha256.removeprefix("sha256:")[:12]
        branch = tree.add(f"[bold]{role}[/bold] {escape(target.display_label)}")
        branch.add(f"source: {escape(target.row.source)}")
        branch.add(f"git: {target.row.git_sha[:12]} ({dirty})")
        if target.row.git_ref != "HEAD":
            branch.add(f"ref: {escape(target.row.git_ref)}")
        branch.add(f"binary: {binary}")
        branch.add(f"path: {escape(target.row.path)}")
    console.print(tree)


def render_per_file_wall_time_change(
    console: Console,
    cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    baseline = targets[0]
    for target in targets[1:]:
        table = report_table(
            f"Per-file wall-time change vs {baseline.display_label}: {target.display_label}",
            caption=TARGET_WALL_TIME_CAPTION,
        )
        table.add_column("File")
        table.add_column("Treatment")
        table.add_column("Time ratio", no_wrap=True)
        table.add_column("Wall-time change", no_wrap=True)
        table.add_column("Result")
        for file_spec in spec.files:
            for treatment_index, treatment in enumerate(spec.treatments):
                ratio = ratio_summary(
                    cell_maps[baseline][(file_spec.sha256, treatment)],
                    cell_maps[target][(file_spec.sha256, treatment)],
                )
                table.add_row(
                    file_spec.display_path if treatment_index == 0 else "",
                    treatment,
                    format_ratio_summary(ratio),
                    format_wall_time_change(ratio),
                    format_comparison_result(ratio),
                    end_section=treatment_index == len(spec.treatments) - 1,
                )
        console.print(table)


def render_per_file_peak_rss_change(
    console: Console,
    rss_cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    baseline = targets[0]
    baseline_has_rss = any(cell.samples for cell in rss_cell_maps[baseline].values())
    for target in targets[1:]:
        if not baseline_has_rss and not any(cell.samples for cell in rss_cell_maps[target].values()):
            continue
        table = report_table(
            f"Per-file peak RSS change vs {baseline.display_label}: {target.display_label}",
            caption=TARGET_PEAK_RSS_CAPTION,
        )
        table.add_column("File")
        table.add_column("Treatment")
        table.add_column("RSS ratio", no_wrap=True)
        table.add_column("RSS change", no_wrap=True)
        table.add_column("Result")
        for file_spec in spec.files:
            for treatment_index, treatment in enumerate(spec.treatments):
                ratio = ratio_summary(
                    rss_cell_maps[baseline][(file_spec.sha256, treatment)],
                    rss_cell_maps[target][(file_spec.sha256, treatment)],
                )
                table.add_row(
                    file_spec.display_path if treatment_index == 0 else "",
                    treatment,
                    format_ratio_summary(ratio),
                    format_percent_change(ratio),
                    format_lower_is_better_result(ratio),
                    end_section=treatment_index == len(spec.treatments) - 1,
                )
        console.print(table)


def render_benchmark_summary(
    console: Console,
    cell_maps: TargetCellMaps,
    rss_cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    console.rule("[bold]Benchmark summary[/bold]")
    if len(targets) == 1:
        render_single_target_summary(console, cell_maps[targets[0]], rss_cell_maps[targets[0]], targets[0], spec)
    else:
        render_multi_target_summary(console, cell_maps, rss_cell_maps, targets, spec)


def render_single_target_summary(
    console: Console,
    cell_map: CellMap,
    rss_cell_map: CellMap,
    target: ResolvedTarget,
    spec: BenchmarkSpec,
) -> None:
    table = report_table(f"{target.display_label}: proof overhead summary", caption=PROOF_OVERHEAD_CAPTION)
    table.add_column("Metric")
    table.add_column("Ratio", no_wrap=True)
    table.add_column("Change", no_wrap=True)
    table.add_column("Worst file")
    table.add_column("Worst ratio", no_wrap=True)
    table.add_column("Result")
    if "off" in spec.treatments and "proofs" in spec.treatments:
        add_within_target_wall_summary_row(table, cell_map, spec, "off", "proofs", "wall proofs/off")
        add_within_target_rss_summary_row(table, rss_cell_map, spec, "off", "proofs", "peak RSS proofs/off")
    else:
        table.add_row("no proof baseline", "-", "-", "-", "-", styled_status("descriptive", "select off and proofs"))
    if "term" in spec.treatments and "proofs" in spec.treatments:
        add_within_target_rss_summary_row(table, rss_cell_map, spec, "term", "proofs", "peak RSS proofs/term")
    console.print(table)


def add_within_target_wall_summary_row(
    table: Table,
    cell_map: CellMap,
    spec: BenchmarkSpec,
    baseline_treatment: Treatment,
    candidate_treatment: Treatment,
    label: str,
) -> None:
    file_cells = treatment_file_cells(cell_map, spec, baseline_treatment, candidate_treatment)
    pairs = summary_pairs(file_cells)
    summary = suite_ratio(pairs)
    geometric = geometric_mean_ratio(pairs)
    worst_file, worst = worst_file_ratio(ratio_pairs(file_cells))
    table.add_row(
        label,
        format_ratio_summary(summary),
        format_percent_change(summary),
        format_worst_file(worst_file),
        format_ratio_summary(worst),
        format_proof_gate_result(summary)
        if baseline_treatment == "off" and candidate_treatment == "proofs"
        else format_comparison_result(summary),
    )
    table.add_row(
        f"{label} geomean",
        format_ratio_summary(geometric),
        format_percent_change(geometric),
        "-",
        "-",
        styled_status("descriptive", "descriptive"),
    )


def add_within_target_rss_summary_row(
    table: Table,
    rss_cell_map: CellMap,
    spec: BenchmarkSpec,
    baseline_treatment: Treatment,
    candidate_treatment: Treatment,
    label: str,
) -> None:
    file_cells = treatment_file_cells(rss_cell_map, spec, baseline_treatment, candidate_treatment)
    pairs = summary_pairs(file_cells)
    summary = suite_ratio(pairs)
    worst_file, worst = worst_file_ratio(ratio_pairs(file_cells))
    table.add_row(
        label,
        format_ratio_summary(summary),
        format_percent_change(summary),
        format_worst_file(worst_file),
        format_ratio_summary(worst),
        format_lower_is_better_result(summary),
    )


def render_multi_target_summary(
    console: Console,
    cell_maps: TargetCellMaps,
    rss_cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    baseline = targets[0]
    wall_table = report_table(
        f"Wall-time summary vs {baseline.display_label}",
        caption=TARGET_WALL_TIME_CAPTION,
    )
    wall_table.add_column("Target")
    wall_table.add_column("Treatment")
    wall_table.add_column("Wall-time change", no_wrap=True)
    wall_table.add_column("Geomean", no_wrap=True)
    wall_table.add_column("Worst file")
    wall_table.add_column("Worst ratio", no_wrap=True)
    wall_table.add_column("Result")
    for target in targets[1:]:
        for treatment in spec.treatments:
            file_cells = target_treatment_file_cells(cell_maps[baseline], cell_maps[target], spec, treatment)
            pairs = summary_pairs(file_cells)
            suite = suite_ratio(pairs)
            geometric = geometric_mean_ratio(pairs)
            worst_file, worst = worst_file_ratio(ratio_pairs(file_cells))
            wall_table.add_row(
                target.display_label,
                treatment,
                format_wall_time_change(suite),
                format_ratio_summary(geometric),
                format_worst_file(worst_file),
                format_ratio_summary(worst),
                format_comparison_result(suite),
            )
    console.print(wall_table)

    rss_table = report_table(
        f"Peak RSS summary vs {baseline.display_label}",
        caption=TARGET_PEAK_RSS_CAPTION,
    )
    rss_table.add_column("Target")
    rss_table.add_column("Treatment")
    rss_table.add_column("RSS change", no_wrap=True)
    rss_table.add_column("Geomean", no_wrap=True)
    rss_table.add_column("Worst file")
    rss_table.add_column("Worst ratio", no_wrap=True)
    rss_table.add_column("Result")
    for target in targets[1:]:
        for treatment in spec.treatments:
            file_cells = target_treatment_file_cells(rss_cell_maps[baseline], rss_cell_maps[target], spec, treatment)
            pairs = summary_pairs(file_cells)
            summary = suite_ratio(pairs)
            geometric = geometric_mean_ratio(pairs)
            worst_file, worst = worst_file_ratio(ratio_pairs(file_cells))
            rss_table.add_row(
                target.display_label,
                treatment,
                format_percent_change(summary),
                format_ratio_summary(geometric),
                format_worst_file(worst_file),
                format_ratio_summary(worst),
                format_lower_is_better_result(summary),
            )
    console.print(rss_table)


def render_target_diagnostics(
    console: Console,
    cell_map: CellMap,
    rss_cell_map: CellMap,
    target: ResolvedTarget,
    spec: BenchmarkSpec,
) -> None:
    render_overhead_ratios(console, cell_map, target, spec)

    means_table = report_table(
        f"{target.display_label}: per-file wall time",
        caption="Within-target wall-time estimates. These are not target-vs-baseline ratios.",
    )
    means_table.add_column("File")
    for treatment in spec.treatments:
        means_table.add_column(treatment, no_wrap=True)
    means_rows: list[tuple[list[str], str]] = []
    has_mean_issues = False
    for file_spec in spec.files:
        issue_parts: list[str] = []
        row_values = [file_spec.display_path]
        for treatment in spec.treatments:
            cell = cell_map[(file_spec.sha256, treatment)]
            row_values.append(format_seconds_summary(cell))
            if cell.issue is not None:
                issue_parts.append(f"{treatment}: {cell.issue}")
        issue_text = "; ".join(issue_parts)
        has_mean_issues = has_mean_issues or bool(issue_text)
        means_rows.append((row_values, issue_text))
    if has_mean_issues:
        means_table.add_column("Issue")
    for row_values, issue_text in means_rows:
        if has_mean_issues:
            row_values.append(issue_text)
        means_table.add_row(*row_values)
    console.print(means_table)

    render_peak_rss_diagnostics(console, rss_cell_map, target, spec)


def render_overhead_ratios(
    console: Console,
    cell_map: CellMap,
    target: ResolvedTarget,
    spec: BenchmarkSpec,
) -> None:
    ratio_columns = ratio_specs(spec.treatments)
    if not ratio_columns:
        return
    ratio_table = report_table(
        f"{target.display_label}: overhead ratios",
        caption="Within-target treatment ratios. These are not target-vs-baseline wall-time change.",
    )
    ratio_table.add_column("File")
    for _, _, ratio_name in ratio_columns:
        ratio_table.add_column(ratio_name, no_wrap=True)
    for file_spec in spec.files:
        row_values = [file_spec.display_path]
        for baseline_treatment, candidate_treatment, _ in ratio_columns:
            ratio = ratio_summary(
                cell_map[(file_spec.sha256, baseline_treatment)],
                cell_map[(file_spec.sha256, candidate_treatment)],
            )
            row_values.append(format_ratio_summary(ratio))
        ratio_table.add_row(*row_values)
    console.print(ratio_table)


def render_peak_rss_diagnostics(
    console: Console,
    rss_cell_map: CellMap,
    target: ResolvedTarget,
    spec: BenchmarkSpec,
) -> None:
    if not any(cell.samples for cell in rss_cell_map.values()):
        return
    rss_table = report_table(
        f"{target.display_label}: per-file peak RSS",
        caption="Within-target peak resident set size estimates. These are separate from wall-time ratios.",
    )
    rss_table.add_column("File")
    for treatment in spec.treatments:
        rss_table.add_column(treatment, no_wrap=True)
    rss_rows: list[tuple[list[str], str]] = []
    has_rss_issues = False
    for file_spec in spec.files:
        issue_parts: list[str] = []
        row_values = [file_spec.display_path]
        for treatment in spec.treatments:
            cell = rss_cell_map[(file_spec.sha256, treatment)]
            row_values.append(format_bytes_summary(cell))
            if cell.issue is not None:
                issue_parts.append(f"{treatment}: {cell.issue}")
        issue_text = "; ".join(issue_parts)
        has_rss_issues = has_rss_issues or bool(issue_text)
        rss_rows.append((row_values, issue_text))
    if has_rss_issues:
        rss_table.add_column("Issue")
    for row_values, issue_text in rss_rows:
        if has_rss_issues:
            row_values.append(issue_text)
        rss_table.add_row(*row_values)
    console.print(rss_table)
