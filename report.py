"""Report tables: the neutral table/cell model, value formatting, result
classification, and the builders that turn analysis summaries into ReportTables.
Consumed by cli.py (terminal) and the eval-live consumer. No pandera at runtime.
"""

from __future__ import annotations

import shlex
from collections.abc import Callable, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING

from analysis import (
    backend_treatment_file_cells,
    best_file_ratio,
    count_better_files,
    geometric_mean_ratio,
    ratio_pairs,
    ratio_specs_for_backend,
    ratio_summary,
    suite_ratio,
    suite_total_mean,
    summary_pairs,
    target_cell_summaries,
    target_rss_cell_summaries,
    target_treatment_file_cells,
    treatment_file_cells,
    worst_file_ratio,
)
from models import (
    Backend,
    BenchmarkSpec,
    CellMap,
    CellSummary,
    FileSpec,
    RatioSummary,
    ReportDestination,
    ResolvedTarget,
    ResultStatus,
    TargetCellMaps,
    Treatment,
    backend_spec,
    benchmark_cells,
    shared_backend_treatments,
    supported_treatments,
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


BACKEND_WALL_TIME_CAPTION = (
    "Ratio is candidate backend / baseline backend for the same target and treatment. "
    "Values below 1x are faster; above 1x are slower. Intervals are 95% CIs."
)


BACKEND_PEAK_RSS_CAPTION = (
    "Ratio is candidate backend / baseline backend for the same target and treatment. "
    "Values below 1x use less peak RSS; above 1x use more. Intervals are 95% CIs."
)


PROOF_OVERHEAD_CAPTION = "Within-backend proof overhead. This is separate from target-vs-baseline wall-time change."


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


def display_backend(backend: Backend) -> str:
    return backend_spec(backend).display_name


def format_better_file_count(count: tuple[int, int]) -> str:
    better, total = count
    if total == 0:
        return "-"
    return f"{better}/{total}"


def format_seconds_value(value: float | None) -> str:
    return "-" if value is None else f"{value:.4f}s"


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


def _cell_label(spec: BenchmarkSpec, backend: Backend, treatment: Treatment) -> str:
    return treatment if len(spec.backends) == 1 else f"{backend}/{treatment}"


def _metric_label(spec: BenchmarkSpec, backend: Backend, label: str) -> str:
    return label if len(spec.backends) == 1 else f"{backend} {label}"


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
    multi_backend = len(spec.backends) > 1
    if rss:
        baseline_has = any(cell.samples for cell in cell_maps[baseline].values())
    ratio_label, change_label = ("RSS ratio", "RSS change") if rss else ("Time ratio", "Wall-time change")
    rows: list[dict[str, Cell]] = []
    group_keys: list[str] = []
    for target in targets[1:]:
        if rss and not baseline_has and not any(cell.samples for cell in cell_maps[target].values()):
            continue
        for file_spec in spec.files:
            for cell in benchmark_cells(spec):
                ratio = ratio_summary(
                    cell_maps[baseline][(file_spec.sha256, cell.backend, cell.treatment)],
                    cell_maps[target][(file_spec.sha256, cell.backend, cell.treatment)],
                )
                change = format_percent_change(ratio) if rss else format_wall_time_change(ratio)
                result = _lower_is_better_cell(ratio) if rss else _comparison_cell(ratio)
                row: dict[str, Cell] = {"Target": Cell(target.display_label), "File": Cell(file_spec.display_path)}
                if multi_backend:
                    row["Backend"] = Cell(display_backend(cell.backend))
                row["Treatment"] = Cell(cell.treatment)
                row[ratio_label] = Cell(format_ratio_summary(ratio))
                row[change_label] = Cell(change)
                row["Result"] = result
                rows.append(row)
                group_keys.append(target.binary_sha256)
    if not rows:
        return None
    columns: tuple[Column, ...] = (Column("Target"), Column("File"))
    if multi_backend:
        columns += (Column("Backend"),)
    columns += (
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


def _backend_change_table(
    cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    *,
    rss: bool,
) -> ReportTable | None:
    """Per-file candidate-backend-vs-baseline-backend change, per target."""
    if len(spec.backends) < 2:
        return None
    baseline_backend = spec.backends[0]
    ratio_label, change_label = ("RSS ratio", "RSS change") if rss else ("Time ratio", "Wall-time change")
    rows: list[dict[str, Cell]] = []
    group_keys: list[str] = []
    for target in targets:
        cell_map = cell_maps[target]
        if rss and not any(cell.samples for cell in cell_map.values()):
            continue
        for candidate_backend in spec.backends[1:]:
            treatments = shared_backend_treatments(spec, baseline_backend, candidate_backend)
            for treatment in treatments:
                file_cells = backend_treatment_file_cells(
                    cell_map, spec, baseline_backend, candidate_backend, treatment
                )
                for file_spec, baseline_cell, candidate_cell in file_cells:
                    ratio = ratio_summary(baseline_cell, candidate_cell)
                    change = format_percent_change(ratio) if rss else format_wall_time_change(ratio)
                    result = _lower_is_better_cell(ratio) if rss else _comparison_cell(ratio)
                    rows.append(
                        {
                            "Target": Cell(target.display_label),
                            "Backend": Cell(
                                f"{display_backend(candidate_backend)} vs {display_backend(baseline_backend)}"
                            ),
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
        Column("Backend"),
        Column("File"),
        Column("Treatment"),
        Column(ratio_label, numeric=True),
        Column(change_label, numeric=True),
        Column("Result"),
    )
    kind = "peak RSS" if rss else "wall-time"
    caption = BACKEND_PEAK_RSS_CAPTION if rss else BACKEND_WALL_TIME_CAPTION
    return ReportTable(
        web_name=f"Per-file backend {kind} change",
        caption=caption,
        columns=columns,
        rows=tuple(rows),
        cli_title=lambda t: f"Per-file backend {kind} change: {t}",
        cli_section="change",
        group_by="Target",
        group_keys=tuple(group_keys),
        merge="Backend",
    )


def _overhead_table(
    cell_maps: TargetCellMaps, targets: Sequence[ResolvedTarget], spec: BenchmarkSpec
) -> ReportTable | None:
    multi_backend = len(spec.backends) > 1
    ratio_columns: list[tuple[Backend, Treatment, Treatment, str]] = []
    for backend in spec.backends:
        for baseline_treatment, candidate_treatment, ratio_name in ratio_specs_for_backend(spec, backend):
            label = _metric_label(spec, backend, ratio_name)
            ratio_columns.append((backend, baseline_treatment, candidate_treatment, label))
    if not ratio_columns:
        return None
    rows: list[dict[str, Cell]] = []
    group_keys: list[str] = []
    for target in targets:
        cell_map = cell_maps[target]
        for file_spec in spec.files:
            row = {"Target": Cell(target.display_label), "File": Cell(file_spec.display_path)}
            for backend, baseline_treatment, candidate_treatment, label in ratio_columns:
                ratio = ratio_summary(
                    cell_map[(file_spec.sha256, backend, baseline_treatment)],
                    cell_map[(file_spec.sha256, backend, candidate_treatment)],
                )
                row[label] = Cell(format_ratio_summary(ratio))
            rows.append(row)
            group_keys.append(target.binary_sha256)
    columns = (Column("Target"), Column("File")) + tuple(Column(label, numeric=True) for *_, label in ratio_columns)
    caption = (
        "Within-backend treatment ratios. These are not target-vs-baseline wall-time change."
        if multi_backend
        else "Within-target treatment ratios. These are not target-vs-baseline wall-time change."
    )
    return ReportTable(
        web_name="Overhead ratios",
        caption=caption,
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
    cells = benchmark_cells(spec)
    rows: list[dict[str, Cell]] = []
    group_keys: list[str] = []
    for target in targets:
        cell_map = cell_maps[target]
        if rss and not any(cell.samples for cell in cell_map.values()):
            continue
        for file_spec in spec.files:
            issues: list[str] = []
            row = {"Target": Cell(target.display_label), "File": Cell(file_spec.display_path)}
            for cell in cells:
                label = _cell_label(spec, cell.backend, cell.treatment)
                summary = cell_map[(file_spec.sha256, cell.backend, cell.treatment)]
                row[label] = Cell(format_cell(summary))
                if summary.issue is not None:
                    issues.append(f"{label}: {summary.issue}")
            row["Issue"] = Cell("; ".join(issues))
            rows.append(row)
            group_keys.append(target.binary_sha256)
    if not rows:
        return None
    columns = (
        (Column("Target"), Column("File"))
        + tuple(Column(_cell_label(spec, cell.backend, cell.treatment), numeric=True) for cell in cells)
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
    cell_map: CellMap,
    spec: BenchmarkSpec,
    backend: Backend,
    baseline_treatment: Treatment,
    candidate_treatment: Treatment,
    label: str,
) -> list[dict[str, Cell]]:
    file_cells = treatment_file_cells(cell_map, spec, backend, baseline_treatment, candidate_treatment)
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
    backend: Backend,
    baseline_treatment: Treatment,
    candidate_treatment: Treatment,
    label: str,
) -> dict[str, Cell]:
    file_cells = treatment_file_cells(rss_cell_map, spec, backend, baseline_treatment, candidate_treatment)
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
    for backend in spec.backends:
        supported = supported_treatments(backend)
        has_off = "off" in spec.treatments and "off" in supported
        has_term = "term" in spec.treatments and "term" in supported
        has_proofs = "proofs" in spec.treatments and "proofs" in supported
        if has_off and has_proofs:
            rows.extend(
                _wall_summary_rows(
                    cell_map, spec, backend, "off", "proofs", _metric_label(spec, backend, "wall proofs/off")
                )
            )
            rows.append(
                _rss_summary_row(
                    rss_cell_map, spec, backend, "off", "proofs", _metric_label(spec, backend, "peak RSS proofs/off")
                )
            )
        elif len(spec.backends) == 1:
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
        if has_term and has_proofs:
            rows.append(
                _rss_summary_row(
                    rss_cell_map, spec, backend, "term", "proofs", _metric_label(spec, backend, "peak RSS proofs/term")
                )
            )
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
    multi_backend = len(spec.backends) > 1
    change_label = "RSS change" if rss else "Wall-time change"
    rows: list[dict[str, Cell]] = []
    for target in targets[1:]:
        for cell in benchmark_cells(spec):
            file_cells = target_treatment_file_cells(
                cell_maps[baseline], cell_maps[target], spec, cell.backend, cell.treatment
            )
            pairs = summary_pairs(file_cells)
            summary = suite_ratio(pairs)
            geometric = geometric_mean_ratio(pairs)
            worst_file, worst = worst_file_ratio(ratio_pairs(file_cells))
            change = format_percent_change(summary) if rss else format_wall_time_change(summary)
            result = _lower_is_better_cell(summary) if rss else _comparison_cell(summary)
            row: dict[str, Cell] = {"Target": Cell(target.display_label)}
            if multi_backend:
                row["Backend"] = Cell(display_backend(cell.backend))
            row["Treatment"] = Cell(cell.treatment)
            row[change_label] = Cell(change)
            row["Geomean"] = Cell(format_ratio_summary(geometric))
            row["Worst file"] = Cell(format_worst_file(worst_file))
            row["Worst ratio"] = Cell(format_ratio_summary(worst))
            row["Result"] = result
            rows.append(row)
    columns: tuple[Column, ...] = (Column("Target"),)
    if multi_backend:
        columns += (Column("Backend"),)
    columns += (
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


@dataclass(frozen=True)
class MetricSpec:
    title: str
    caption: str
    file_count_heading: str
    format_total: Callable[[float | None], str]
    format_change: Callable[[RatioSummary], str]
    format_result: Callable[[RatioSummary], Cell]
    rss: bool = False
    omit_without_samples: bool = False


def _backend_summary_table(
    cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    metric: MetricSpec,
) -> ReportTable | None:
    """Candidate-backend-vs-baseline-backend summary across all targets."""
    if len(spec.backends) < 2:
        return None
    baseline_backend = spec.backends[0]
    multi_target = len(targets) > 1
    rows: list[dict[str, Cell]] = []
    for target in targets:
        cell_map = cell_maps[target]
        if metric.omit_without_samples and not any(cell.samples for cell in cell_map.values()):
            continue
        for candidate_backend in spec.backends[1:]:
            treatments = shared_backend_treatments(spec, baseline_backend, candidate_backend)
            for treatment in treatments:
                file_cells = backend_treatment_file_cells(
                    cell_map, spec, baseline_backend, candidate_backend, treatment
                )
                pairs = summary_pairs(file_cells)
                summary = suite_ratio(pairs)
                geometric = geometric_mean_ratio(pairs)
                ratio_list = ratio_pairs(file_cells)
                best_file, best = best_file_ratio(ratio_list)
                baseline_total = suite_total_mean([b for _, b, _ in file_cells])
                candidate_total = suite_total_mean([c for _, _, c in file_cells])
                row: dict[str, Cell] = {}
                if multi_target:
                    row["Target"] = Cell(target.display_label)
                row["Backend"] = Cell(display_backend(candidate_backend))
                row["Mode"] = Cell(treatment)
                row[f"{display_backend(baseline_backend)} total"] = Cell(metric.format_total(baseline_total))
                row["Candidate total"] = Cell(metric.format_total(candidate_total))
                row["Ratio"] = Cell(format_ratio_summary(summary))
                row["Change"] = Cell(metric.format_change(summary))
                row["File geomean"] = Cell(format_ratio_summary(geometric))
                row[metric.file_count_heading] = Cell(format_better_file_count(count_better_files(ratio_list)))
                row["Best file"] = Cell(format_worst_file(best_file))
                row["Best ratio"] = Cell(format_ratio_summary(best))
                row["Best result"] = metric.format_result(best)
                rows.append(row)
    if not rows:
        return None
    columns: tuple[Column, ...] = ()
    if multi_target:
        columns += (Column("Target"),)
    columns += (
        Column("Backend"),
        Column("Mode"),
        Column(f"{display_backend(baseline_backend)} total", numeric=True),
        Column("Candidate total", numeric=True),
        Column("Ratio", numeric=True),
        Column("Change", numeric=True),
        Column("File geomean", numeric=True),
        Column(metric.file_count_heading, numeric=True),
        Column("Best file"),
        Column("Best ratio", numeric=True),
        Column("Best result"),
    )
    if len(spec.backends) == 2:
        candidate = display_backend(spec.backends[1])
        title = f"{candidate} vs {display_backend(baseline_backend)} {metric.title}"
    else:
        title = f"Backend {metric.title} summary vs {display_backend(baseline_backend)}"
    return ReportTable(
        web_name=title,
        caption=metric.caption,
        columns=columns,
        rows=tuple(rows),
        cli_title=lambda _: title,
        cli_section="summary",
    )


def _backend_summary_tables(
    cell_maps: TargetCellMaps,
    rss_cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> list[ReportTable]:
    if len(spec.backends) < 2:
        return []
    wall_metric = MetricSpec(
        title="wall time",
        caption=BACKEND_WALL_TIME_CAPTION,
        file_count_heading="Faster files",
        format_total=format_seconds_value,
        format_change=format_wall_time_change,
        format_result=_comparison_cell,
    )
    rss_metric = MetricSpec(
        title="peak RSS",
        caption=BACKEND_PEAK_RSS_CAPTION,
        file_count_heading="Lower-RSS files",
        format_total=format_bytes,
        format_change=format_percent_change,
        format_result=_lower_is_better_cell,
        rss=True,
        omit_without_samples=True,
    )
    tables = [_backend_summary_table(cell_maps, targets, spec, wall_metric)]
    tables.append(_backend_summary_table(rss_cell_maps, targets, spec, rss_metric))
    return [table for table in tables if table is not None]


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
    candidates: list[ReportTable | None] = [
        _change_table(cell_maps, targets, spec, rss=False),
        _change_table(rss_cell_maps, targets, spec, rss=True),
        _backend_change_table(cell_maps, targets, spec, rss=False),
        _backend_change_table(rss_cell_maps, targets, spec, rss=True),
        _overhead_table(cell_maps, targets, spec),
        _means_table(cell_maps, targets, spec, rss=False),
        _means_table(rss_cell_maps, targets, spec, rss=True),
    ]
    candidates.extend(_backend_summary_tables(cell_maps, rss_cell_maps, targets, spec))
    candidates.extend(
        [
            None if multi else _proof_summary_table(cell_maps, rss_cell_maps, targets, spec),
            _target_summary_table(cell_maps, targets, spec, rss=False) if multi else None,
            _target_summary_table(rss_cell_maps, targets, spec, rss=True) if multi else None,
        ]
    )
    return [table for table in candidates if table is not None]


def markdown_escape_cell(value: str) -> str:
    return (
        value.replace("\\", "\\\\")
        .replace("|", "\\|")
        .replace("\r\n", "<br>")
        .replace("\r", "<br>")
        .replace("\n", "<br>")
    )


def _visible_columns(table: ReportTable) -> list[Column]:
    visible: list[Column] = []
    for column in table.columns:
        if column.drop_if_empty and all(not row.get(column.label, Cell("")).text for row in table.rows):
            continue
        visible.append(column)
    return visible


def render_markdown_table(table: ReportTable, *, heading_level: int = 3) -> str:
    columns = _visible_columns(table)
    heading = "#" * heading_level
    lines = [f"{heading} {table.web_name}", ""]
    lines.append("| " + " | ".join(markdown_escape_cell(column.label) for column in columns) + " |")
    lines.append("| " + " | ".join("---:" if column.numeric else "---" for column in columns) + " |")
    for row in table.rows:
        cells = [markdown_escape_cell(row.get(column.label, Cell("")).text) for column in columns]
        lines.append("| " + " | ".join(cells) + " |")
    if table.caption:
        lines.append("")
        lines.append(f"_{markdown_escape_cell(table.caption)}_")
    return "\n".join(lines)


def benchmark_command_block(command_argv: Sequence[str]) -> str:
    return "```shell\n$ ./bench.py " + shlex.join(command_argv) + "\n```"


def _targets_markdown(targets: Sequence[ResolvedTarget]) -> str:
    lines = ["## Targets", "", "| Role | Label | Git ref | Dirty | Binary |", "| --- | --- | --- | --- | --- |"]
    for index, target in enumerate(targets):
        role = "baseline" if index == 0 else "candidate"
        lines.append(
            "| "
            + " | ".join(
                markdown_escape_cell(value)
                for value in (
                    role,
                    target.display_label,
                    target.row.git_ref,
                    "yes" if target.row.is_dirty else "no",
                    target.binary_sha256.removeprefix("sha256:")[:16],
                )
            )
            + " |"
        )
    return "\n".join(lines)


def render_markdown_report(
    report_destination: ReportDestination,
    rows: DataFrame[ReportFrame],
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    command_argv: Sequence[str] | None = None,
) -> str:
    """Full markdown report rendered from the same ReportTable catalog the CLI and web use."""
    parts: list[str] = []
    if command_argv is not None:
        parts.append(benchmark_command_block(command_argv))
    parts.append(
        f"# Benchmark Report\n\nReport: `{report_destination.display_path}`  \nSelected rows per cell: {spec.rounds}"
    )
    parts.append(_targets_markdown(targets))
    for table in build_report_tables(rows, targets, spec):
        parts.append(render_markdown_table(table))
    return "\n\n".join(part for part in parts if part)
