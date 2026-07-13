"""Report tables: the neutral table/cell model, value formatting, result
classification, and the builders that turn analysis summaries into ReportTables.
Consumed by cli.py (terminal) and the eval-live consumer. No pandera at runtime.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING

from analysis import (
    geometric_mean_ratio,
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
from models import (
    BenchmarkSpec,
    CellMap,
    CellSummary,
    FileSpec,
    RatioSummary,
    ResolvedTarget,
    ResultStatus,
    TargetCellMaps,
    Treatment,
)

if TYPE_CHECKING:
    from pandera.typing import DataFrame

    from report_frame import ReportFrame


TARGET_WALL_TIME_CAPTION = (
    "Ratio is target / baseline. Values below 1x are faster; above 1x are slower. "
    "Wall-time change is derived from the ratio; negative is faster. Intervals are 95% CIs."
)


TARGET_PEAK_RSS_CAPTION = (
    "Ratio is target / baseline. Values below 1x use less peak RSS; above 1x use more. "
    "RSS change is derived from the ratio; negative uses less memory. Intervals are 95% CIs."
)


PROOF_OVERHEAD_CAPTION = "Within-target proof overhead. This is separate from target-vs-baseline wall-time change."


def format_estimate_or_interval(
    point: float | None,
    low: float | None,
    high: float | None,
    suffix: str,
    digits: int,
) -> str:
    if point is None:
        return "-"
    point_text = f"{point:.{digits}f}{suffix}"
    if low is None or high is None:
        return point_text
    return f"[{low:.{digits}f}{suffix}, {high:.{digits}f}{suffix}]"


def format_seconds_summary(summary: CellSummary) -> str:
    return format_estimate_or_interval(summary.mean, summary.ci_low, summary.ci_high, "s", 4)


def format_bytes(value: float | None) -> str:
    if value is None:
        return "-"
    units = ("B", "KiB", "MiB", "GiB")
    amount = float(value)
    unit = units[0]
    for unit in units:
        if amount < 1024 or unit == units[-1]:
            break
        amount /= 1024
    if unit == "B":
        return f"{int(amount)} B"
    return f"{amount:.1f} {unit}"


def format_bytes_summary(summary: CellSummary) -> str:
    if summary.mean is None:
        return "-"
    point_text = format_bytes(summary.mean)
    if summary.ci_low is None or summary.ci_high is None:
        return point_text
    return f"[{format_bytes(summary.ci_low)}, {format_bytes(summary.ci_high)}]"


def format_ratio_summary(summary: RatioSummary) -> str:
    return format_estimate_or_interval(summary.point, summary.ci_low, summary.ci_high, "x", 3)


def format_wall_time_change(summary: RatioSummary) -> str:
    return format_percent_change(summary)


def format_percent_change(summary: RatioSummary) -> str:
    point = None if summary.point is None else (summary.point - 1.0) * 100.0
    low = None if summary.ci_low is None else (summary.ci_low - 1.0) * 100.0
    high = None if summary.ci_high is None else (summary.ci_high - 1.0) * 100.0
    return format_estimate_or_interval(point, low, high, "%", 1)


def format_worst_file(file_spec: FileSpec | None) -> str:
    return "-" if file_spec is None else file_spec.display_path


def comparison_result(summary: RatioSummary) -> ResultStatus:
    if summary.point is None:
        return "invalid"
    if summary.ci_low is None or summary.ci_high is None:
        return "point only"
    if summary.ci_high < 1:
        return "faster"
    if summary.ci_low > 1:
        return "slower"
    return "unclear"


def lower_is_better_result(summary: RatioSummary) -> ResultStatus:
    if summary.point is None:
        return "invalid"
    if summary.ci_low is None or summary.ci_high is None:
        return "point only"
    if summary.ci_high < 1:
        return "less"
    if summary.ci_low > 1:
        return "more"
    return "unclear"


def proof_gate_result(summary: RatioSummary) -> tuple[ResultStatus, str]:
    if summary.point is None:
        return ("invalid", f"invalid: {summary.issue or 'unavailable'}")
    if summary.ci_high is None:
        return ("point only", "point only")
    if summary.ci_high < 2:
        return ("established", "<2x established")
    return ("not established", "<2x not established")


@dataclass(frozen=True)
class Cell:
    text: str
    status: ResultStatus | None = None


@dataclass(frozen=True)
class Column:
    label: str
    numeric: bool = False  # CLI: no_wrap
    drop_if_empty: bool = False


@dataclass(frozen=True)
class ReportTable:
    web_name: str
    caption: str | None
    columns: tuple[Column, ...]
    rows: tuple[dict[str, Cell], ...]
    cli_title: Callable[[str | None], str]  # group label (or None) -> CLI title
    cli_section: str = "diagnostic"  # CLI placement: "change" | "diagnostic" | "summary"
    group_by: str | None = None  # column the CLI drops when splitting into per-group tables
    group_keys: tuple[str, ...] = ()  # per-row grouping identity (parallel to rows); CLI groups on this
    merge: str | None = None


def _comparison_cell(ratio: RatioSummary) -> Cell:
    result = comparison_result(ratio)
    if result == "invalid" and ratio.issue is not None:
        return Cell(f"invalid: {ratio.issue}", "invalid")
    return Cell(result, result)


def _lower_is_better_cell(ratio: RatioSummary) -> Cell:
    result = lower_is_better_result(ratio)
    if result == "invalid" and ratio.issue is not None:
        return Cell(f"invalid: {ratio.issue}", "invalid")
    return Cell(result, result)


def _proof_gate_cell(ratio: RatioSummary) -> Cell:
    status, text = proof_gate_result(ratio)
    return Cell(text, status)


def _change_table(
    cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    *,
    rss: bool,
) -> ReportTable | None:
    if len(targets) < 2:
        return None
    baseline = targets[0]
    if rss:
        baseline_has = any(cell.samples for cell in cell_maps[baseline].values())
    ratio_label, change_label = ("RSS ratio", "RSS change") if rss else ("Time ratio", "Wall-time change")
    rows: list[dict[str, Cell]] = []
    group_keys: list[str] = []
    for target in targets[1:]:
        if rss and not baseline_has and not any(cell.samples for cell in cell_maps[target].values()):
            continue
        for file_spec in spec.files:
            for treatment in spec.treatments:
                ratio = ratio_summary(
                    cell_maps[baseline][(file_spec.sha256, treatment)],
                    cell_maps[target][(file_spec.sha256, treatment)],
                )
                change = format_percent_change(ratio) if rss else format_wall_time_change(ratio)
                result = _lower_is_better_cell(ratio) if rss else _comparison_cell(ratio)
                rows.append(
                    {
                        "Target": Cell(target.display_label),
                        "File": Cell(file_spec.display_path),
                        "Treatment": Cell(treatment),
                        ratio_label: Cell(format_ratio_summary(ratio)),
                        change_label: Cell(change),
                        "Result": result,
                    }
                )
                group_keys.append(target.binary_sha256)
    if not rows:
        return None
    columns = (
        Column("Target"),
        Column("File"),
        Column("Treatment"),
        Column(ratio_label, numeric=True),
        Column(change_label, numeric=True),
        Column("Result"),
    )
    kind = "peak RSS" if rss else "wall-time"
    caption = TARGET_PEAK_RSS_CAPTION if rss else TARGET_WALL_TIME_CAPTION
    return ReportTable(
        web_name=f"Per-file {kind} change",
        caption=caption,
        columns=columns,
        rows=tuple(rows),
        cli_title=lambda t: f"Per-file {kind} change vs {baseline.display_label}: {t}",
        cli_section="change",
        group_by="Target",
        group_keys=tuple(group_keys),
        merge="File",
    )


def _overhead_table(
    cell_maps: TargetCellMaps, targets: Sequence[ResolvedTarget], spec: BenchmarkSpec
) -> ReportTable | None:
    ratio_columns = ratio_specs(spec.treatments)
    if not ratio_columns:
        return None
    rows: list[dict[str, Cell]] = []
    group_keys: list[str] = []
    for target in targets:
        cell_map = cell_maps[target]
        for file_spec in spec.files:
            row = {"Target": Cell(target.display_label), "File": Cell(file_spec.display_path)}
            for baseline_treatment, candidate_treatment, ratio_name in ratio_columns:
                ratio = ratio_summary(
                    cell_map[(file_spec.sha256, baseline_treatment)],
                    cell_map[(file_spec.sha256, candidate_treatment)],
                )
                row[ratio_name] = Cell(format_ratio_summary(ratio))
            rows.append(row)
            group_keys.append(target.binary_sha256)
    columns = (Column("Target"), Column("File")) + tuple(Column(name, numeric=True) for _, _, name in ratio_columns)
    return ReportTable(
        web_name="Overhead ratios",
        caption="Within-target treatment ratios. These are not target-vs-baseline wall-time change.",
        columns=columns,
        rows=tuple(rows),
        cli_title=lambda t: f"{t}: overhead ratios",
        group_by="Target",
        group_keys=tuple(group_keys),
    )


def _means_table(
    cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    *,
    rss: bool,
) -> ReportTable | None:
    format_cell = format_bytes_summary if rss else format_seconds_summary
    rows: list[dict[str, Cell]] = []
    group_keys: list[str] = []
    for target in targets:
        cell_map = cell_maps[target]
        if rss and not any(cell.samples for cell in cell_map.values()):
            continue
        for file_spec in spec.files:
            issues: list[str] = []
            row = {"Target": Cell(target.display_label), "File": Cell(file_spec.display_path)}
            for treatment in spec.treatments:
                cell = cell_map[(file_spec.sha256, treatment)]
                row[treatment] = Cell(format_cell(cell))
                if cell.issue is not None:
                    issues.append(f"{treatment}: {cell.issue}")
            row["Issue"] = Cell("; ".join(issues))
            rows.append(row)
            group_keys.append(target.binary_sha256)
    if not rows:
        return None
    columns = (
        (Column("Target"), Column("File"))
        + tuple(Column(t, numeric=True) for t in spec.treatments)
        + (Column("Issue", drop_if_empty=True),)
    )
    kind = "peak RSS" if rss else "wall time"
    caption = (
        "Within-target peak resident set size estimates. These are separate from wall-time ratios."
        if rss
        else "Within-target wall-time estimates. These are not target-vs-baseline ratios."
    )
    return ReportTable(
        web_name=f"Per-file {kind}",
        caption=caption,
        columns=columns,
        rows=tuple(rows),
        cli_title=lambda t: f"{t}: per-file {kind}",
        group_by="Target",
        group_keys=tuple(group_keys),
    )


def _wall_summary_rows(
    cell_map: CellMap, spec: BenchmarkSpec, baseline_treatment: Treatment, candidate_treatment: Treatment, label: str
) -> list[dict[str, Cell]]:
    file_cells = treatment_file_cells(cell_map, spec, baseline_treatment, candidate_treatment)
    pairs = summary_pairs(file_cells)
    summary = suite_ratio(pairs)
    geometric = geometric_mean_ratio(pairs)
    worst_file, worst = worst_file_ratio(ratio_pairs(file_cells))
    result = (
        _proof_gate_cell(summary)
        if baseline_treatment == "off" and candidate_treatment == "proofs"
        else _comparison_cell(summary)
    )
    return [
        {
            "Metric": Cell(label),
            "Ratio": Cell(format_ratio_summary(summary)),
            "Change": Cell(format_percent_change(summary)),
            "Worst file": Cell(format_worst_file(worst_file)),
            "Worst ratio": Cell(format_ratio_summary(worst)),
            "Result": result,
        },
        {
            "Metric": Cell(f"{label} geomean"),
            "Ratio": Cell(format_ratio_summary(geometric)),
            "Change": Cell(format_percent_change(geometric)),
            "Worst file": Cell("-"),
            "Worst ratio": Cell("-"),
            "Result": Cell("descriptive", "descriptive"),
        },
    ]


def _rss_summary_row(
    rss_cell_map: CellMap,
    spec: BenchmarkSpec,
    baseline_treatment: Treatment,
    candidate_treatment: Treatment,
    label: str,
) -> dict[str, Cell]:
    file_cells = treatment_file_cells(rss_cell_map, spec, baseline_treatment, candidate_treatment)
    pairs = summary_pairs(file_cells)
    summary = suite_ratio(pairs)
    worst_file, worst = worst_file_ratio(ratio_pairs(file_cells))
    return {
        "Metric": Cell(label),
        "Ratio": Cell(format_ratio_summary(summary)),
        "Change": Cell(format_percent_change(summary)),
        "Worst file": Cell(format_worst_file(worst_file)),
        "Worst ratio": Cell(format_ratio_summary(worst)),
        "Result": _lower_is_better_cell(summary),
    }


def _proof_summary_table(
    cell_maps: TargetCellMaps, rss_cell_maps: TargetCellMaps, targets: Sequence[ResolvedTarget], spec: BenchmarkSpec
) -> ReportTable:
    target = targets[0]
    cell_map = cell_maps[target]
    rss_cell_map = rss_cell_maps[target]
    rows: list[dict[str, Cell]] = []
    if "off" in spec.treatments and "proofs" in spec.treatments:
        rows.extend(_wall_summary_rows(cell_map, spec, "off", "proofs", "wall proofs/off"))
        rows.append(_rss_summary_row(rss_cell_map, spec, "off", "proofs", "peak RSS proofs/off"))
    else:
        rows.append(
            {
                "Metric": Cell("no proof baseline"),
                "Ratio": Cell("-"),
                "Change": Cell("-"),
                "Worst file": Cell("-"),
                "Worst ratio": Cell("-"),
                "Result": Cell("select off and proofs", "descriptive"),
            }
        )
    if "term" in spec.treatments and "proofs" in spec.treatments:
        rows.append(_rss_summary_row(rss_cell_map, spec, "term", "proofs", "peak RSS proofs/term"))
    columns = (
        Column("Metric"),
        Column("Ratio", numeric=True),
        Column("Change", numeric=True),
        Column("Worst file"),
        Column("Worst ratio", numeric=True),
        Column("Result"),
    )
    return ReportTable(
        web_name="Proof overhead summary",
        caption=PROOF_OVERHEAD_CAPTION,
        columns=columns,
        rows=tuple(rows),
        cli_title=lambda _: f"{target.display_label}: proof overhead summary",
        cli_section="summary",
    )


def _target_summary_table(
    cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    *,
    rss: bool,
) -> ReportTable:
    baseline = targets[0]
    change_label = "RSS change" if rss else "Wall-time change"
    rows: list[dict[str, Cell]] = []
    for target in targets[1:]:
        for treatment in spec.treatments:
            file_cells = target_treatment_file_cells(cell_maps[baseline], cell_maps[target], spec, treatment)
            pairs = summary_pairs(file_cells)
            summary = suite_ratio(pairs)
            geometric = geometric_mean_ratio(pairs)
            worst_file, worst = worst_file_ratio(ratio_pairs(file_cells))
            change = format_percent_change(summary) if rss else format_wall_time_change(summary)
            result = _lower_is_better_cell(summary) if rss else _comparison_cell(summary)
            rows.append(
                {
                    "Target": Cell(target.display_label),
                    "Treatment": Cell(treatment),
                    change_label: Cell(change),
                    "Geomean": Cell(format_ratio_summary(geometric)),
                    "Worst file": Cell(format_worst_file(worst_file)),
                    "Worst ratio": Cell(format_ratio_summary(worst)),
                    "Result": result,
                }
            )
    columns = (
        Column("Target"),
        Column("Treatment"),
        Column(change_label, numeric=True),
        Column("Geomean", numeric=True),
        Column("Worst file"),
        Column("Worst ratio", numeric=True),
        Column("Result"),
    )
    kind = "Peak RSS" if rss else "Wall-time"
    caption = TARGET_PEAK_RSS_CAPTION if rss else TARGET_WALL_TIME_CAPTION
    return ReportTable(
        web_name=f"{kind} summary",
        caption=caption,
        columns=columns,
        rows=tuple(rows),
        cli_title=lambda _: f"{kind} summary vs {baseline.display_label}",
        cli_section="summary",
    )


def build_report_tables(
    rows: DataFrame[ReportFrame],
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    *,
    validate: bool = True,
) -> list[ReportTable]:
    """Build every report table once, from a single computation of the cell maps.

    To add a table, write a builder and append it here — the CLI (by
    ``cli_section``) and the eval-live web/dump both pick it up automatically.
    ``None`` entries (a table that does not apply to this data) are dropped.
    """
    cell_maps = {t: target_cell_summaries(rows, t, spec, validate=validate) for t in targets}
    rss_cell_maps = {t: target_rss_cell_summaries(rows, t, spec, validate=validate) for t in targets}
    multi = len(targets) > 1
    candidates = [
        _change_table(cell_maps, targets, spec, rss=False),
        _change_table(rss_cell_maps, targets, spec, rss=True),
        _overhead_table(cell_maps, targets, spec),
        _means_table(cell_maps, targets, spec, rss=False),
        _means_table(rss_cell_maps, targets, spec, rss=True),
        None if multi else _proof_summary_table(cell_maps, rss_cell_maps, targets, spec),
        _target_summary_table(cell_maps, targets, spec, rss=False) if multi else None,
        _target_summary_table(rss_cell_maps, targets, spec, rss=True) if multi else None,
    ]
    return [table for table in candidates if table is not None]
