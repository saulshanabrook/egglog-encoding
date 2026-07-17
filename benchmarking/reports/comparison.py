"""Build the renderer-neutral catalog for one baseline/candidate comparison.

DuckDB owns sample selection, statistics, result classification, phase
pairing, ruleset union, deltas, ratios, and top-ten ranking. This module only
maps those typed rows into the fixed selection-summary-files-phases-rulesets
catalog and formats values for Rich, Markdown, and live adapters.
"""

from __future__ import annotations

import math
from collections.abc import Sequence
from pathlib import Path

from scipy import stats

from ..models import ComparisonSpec, DetailLevel, FileSpec
from .catalog import (
    CellTone,
    ReportBlock,
    ReportCatalog,
    ReportCell,
    ReportColumn,
    ReportMessage,
    ReportOptions,
    ReportRow,
    ReportSection,
    ReportTable,
    TableAlignment,
    TableLayout,
    report_id,
    text_cell,
)
from .database import ReportDatabase
from .results import (
    EndpointView,
    FileComparisonView,
    MetricName,
    PairReportViewData,
    PhaseComparisonView,
    RatioSummary,
    ResultClass,
    RulesetComparisonView,
    SummaryView,
)

NULL = "—"
DEFAULT_RULESET = "<default ruleset>"
DETAIL_ORDER: dict[DetailLevel, int] = {
    "summary": 0,
    "files": 1,
    "phases": 2,
    "rulesets": 3,
}
RATIO_DIRECTION = "candidate / baseline; below 1 is faster or uses less RSS, while above 1 is slower or uses more RSS"
PHASE_CAPTION = (
    "Delta is candidate − baseline. Phase values are descriptive means without confidence intervals. Other is "
    "wall time minus Search, Apply, Merge, and Rebuild; a leading ! means recorded phase totals exceed wall time."
)
RULESET_CAPTION = "Ruleset totals are descriptive means without confidence intervals."


def build_report_catalog(
    database: ReportDatabase,
    comparison: ComparisonSpec,
    options: ReportOptions | None = None,
) -> ReportCatalog:
    """Query one SQL-owned pair analysis and build its complete catalog."""

    options = ReportOptions() if options is None else options
    t_critical = None if comparison.rounds < 2 else float(stats.t.ppf(0.975, comparison.rounds - 1))
    database.install_scope(comparison, t_critical)
    views = database.report_view_data(options.detail)
    file_labels = report_file_labels(comparison.files)

    sections = [
        _selection_section(database.display_path, comparison, views.endpoints, file_labels),
        _summary_section(comparison, views.summary, file_labels),
    ]
    if _includes(options.detail, "files"):
        sections.append(_files_section(views.files, comparison, file_labels))
    if _includes(options.detail, "phases"):
        sections.append(_phases_section(views.phases, comparison, file_labels))
    if _includes(options.detail, "rulesets"):
        sections.append(_rulesets_section(views, comparison, file_labels))
    return ReportCatalog(tuple(sections))


def _includes(detail: DetailLevel, requested: DetailLevel) -> bool:
    return DETAIL_ORDER[detail] >= DETAIL_ORDER[requested]


def _selection_section(
    report_path: str,
    comparison: ComparisonSpec,
    endpoints: Sequence[EndpointView],
    file_labels: dict[FileSpec, str],
) -> ReportSection:
    endpoint_rows = tuple(
        _row(
            report_id("row", "selection", endpoint.endpoint_role, _endpoint_id(endpoint)),
            text_cell(endpoint.endpoint_role, endpoint.endpoint_role.title()),
            endpoint.target_label,
            text_cell(endpoint.target_git_sha, endpoint.target_git_sha[:12]),
            text_cell(endpoint.target_is_dirty, "yes" if endpoint.target_is_dirty else "no"),
            endpoint.backend,
            endpoint.treatment,
        )
        for endpoint in endpoints
    )
    endpoint_table = _table(
        report_id("table", "selection", "endpoints"),
        "Endpoints",
        ("role", "target", "git", "dirty", "backend", "treatment"),
        ("Role", "Target", "Git", "Dirty", "Backend", "Treatment"),
        endpoint_rows,
    )
    selected_files = "; ".join(_file_with_facts(file, file_labels[file]) for file in comparison.files)
    run_table = _table(
        report_id("table", "selection", "run"),
        "Run",
        ("setting", "value"),
        ("Setting", "Value"),
        (
            _row(report_id("row", "selection", "ratio"), "Ratio", RATIO_DIRECTION),
            _row(
                report_id("row", "selection", "files"),
                "Files",
                f"{len(comparison.files)}: {selected_files}",
            ),
            _row(
                report_id("row", "selection", "rounds"),
                "Rounds",
                f"{comparison.rounds} per endpoint/file",
            ),
            _row(
                report_id("row", "selection", "timeout"),
                "Timeout",
                f"{comparison.timeout_sec} s per run",
            ),
            _row(report_id("row", "selection", "report"), "Report", report_path),
        ),
    )
    blocks: list[ReportBlock] = [endpoint_table, run_table]
    changed = (
        comparison.baseline.target.binary_sha256 != comparison.candidate.target.binary_sha256,
        comparison.baseline.backend != comparison.candidate.backend,
        comparison.baseline.treatment != comparison.candidate.treatment,
    )
    if sum(changed) > 1:
        blocks.append(
            ReportMessage(
                report_id("message", "selection", "joint-comparison"),
                None,
                "This comparison changes more than one of target, backend, and treatment. Its ratios describe "
                "the joint endpoint change and do not isolate one cause.",
                tone="warning",
            )
        )
    return ReportSection("selection", "Comparison", tuple(blocks))


def _endpoint_id(endpoint: EndpointView) -> str:
    return report_id("endpoint", endpoint.binary_sha256, endpoint.backend, endpoint.treatment)


def _file_with_facts(file: FileSpec, label: str) -> str:
    if file.fact_directory is None:
        return label
    return f"{label} (facts: {file.fact_directory})"


def _summary_section(
    comparison: ComparisonSpec,
    rows: Sequence[SummaryView],
    file_labels: dict[FileSpec, str],
) -> ReportSection:
    selected = _deduplicate_summary_rows(rows, len(comparison.files))
    report_rows: list[ReportRow] = []
    for row, scope in selected:
        if row.summary_kind == "suite":
            file_display = (
                file_labels[comparison.files[0]] if len(comparison.files) == 1 else f"{len(comparison.files)} files"
            )
        elif row.file_order is None:
            file_display = NULL
        else:
            file_display = file_labels[comparison.files[row.file_order]]
        report_rows.append(
            _row(
                report_id("row", "summary", row.metric, scope),
                text_cell(row.metric, _metric_label(row.metric)),
                text_cell(scope, _scope_label(scope, len(comparison.files))),
                file_display,
                _ratio_cell(row.ratio),
                _result_cell(row.result_class, row.issue, rss=row.metric == "max_rss_bytes"),
            )
        )
    table = _table(
        report_id("table", "summary"),
        "Benchmark summary",
        ("metric", "scope", "file", "ratio", "result"),
        ("Metric", "Scope", "File(s)", "Ratio (95% CI)", "Result"),
        tuple(report_rows),
        alignments=("left", "left", "left", "right", "left"),
    )
    return ReportSection("summary", "Benchmark summary", (table,))


def _deduplicate_summary_rows(
    rows: Sequence[SummaryView],
    file_count: int,
) -> tuple[tuple[SummaryView, str], ...]:
    suite = next(row for row in rows if row.summary_kind == "suite")
    result: list[tuple[SummaryView, str]] = [(suite, "suite")]
    for metric in ("wall_sec", "max_rss_bytes"):
        tails = [row for row in rows if row.metric == metric and row.summary_kind != "suite"]
        if len(tails) != 2:
            raise ValueError(f"expected lowest and highest summary rows for {metric}")
        low, high = tails
        if low.file_order == high.file_order:
            if metric == "wall_sec" and file_count == 1:
                # The fixed-suite wall row is the selected file in this case.
                continue
            if low.file_order is None:
                scope = "unavailable"
            elif file_count == 1:
                scope = "only"
            else:
                scope = "only-comparable"
            result.append((low, scope))
        else:
            result.extend(((low, "low"), (high, "high")))
    return tuple(result)


def _scope_label(scope: str, file_count: int) -> str:
    labels = {
        "suite": "Suite (1 file)" if file_count == 1 else "Suite total",
        "low": "Lowest-ratio file",
        "high": "Highest-ratio file",
        "only": "Only file",
        "only-comparable": "Only comparable file",
        "unavailable": "Unavailable",
    }
    return labels[scope]


def _files_section(
    rows: Sequence[FileComparisonView],
    comparison: ComparisonSpec,
    file_labels: dict[FileSpec, str],
) -> ReportSection:
    tables: list[ReportBlock] = []
    for metric in ("wall_sec", "max_rss_bytes"):
        metric_rows = tuple(row for row in rows if row.metric == metric)
        if metric == "max_rss_bytes" and not any(
            row.baseline_mean is not None or row.candidate_mean is not None for row in metric_rows
        ):
            tables.append(
                ReportMessage(
                    report_id("message", "files", metric),
                    "Per-file peak RSS",
                    "Peak RSS is unavailable for the selected endpoints.",
                    tone="muted",
                )
            )
            continue
        tables.append(
            _table(
                report_id("table", "files", metric),
                "Per-file wall time" if metric == "wall_sec" else "Per-file peak RSS",
                ("file", "baseline", "candidate", "ratio", "result"),
                ("File", "Baseline (95% CI)", "Candidate (95% CI)", "Ratio (95% CI)", "Result"),
                tuple(
                    _row(
                        report_id(
                            "row",
                            "files",
                            metric,
                            comparison.files[row.file_order].sha256,
                            comparison.files[row.file_order].fact_directory_sha256,
                        ),
                        file_labels[comparison.files[row.file_order]],
                        _estimate_cell(
                            row.baseline_mean,
                            row.baseline_ci_low,
                            row.baseline_ci_high,
                            rss=metric == "max_rss_bytes",
                        ),
                        _estimate_cell(
                            row.candidate_mean,
                            row.candidate_ci_low,
                            row.candidate_ci_high,
                            rss=metric == "max_rss_bytes",
                        ),
                        _ratio_cell(row.ratio),
                        _result_cell(row.result_class, row.issue, rss=metric == "max_rss_bytes"),
                    )
                    for row in metric_rows
                ),
                alignments=("left", "right", "right", "right", "left"),
                layout="wide",
            )
        )
    return ReportSection("files", "Per-file results", tuple(tables))


def _phases_section(
    rows: Sequence[PhaseComparisonView],
    comparison: ComparisonSpec,
    file_labels: dict[FileSpec, str],
) -> ReportSection:
    table = _table(
        report_id("table", "phases"),
        "Phase comparison",
        ("benchmark", "phase", "baseline", "candidate", "delta", "ratio"),
        ("File", "Phase", "Baseline", "Candidate", "Delta", "Ratio"),
        tuple(
            _row(
                report_id(
                    "row",
                    "phases",
                    comparison.files[row.file_order].sha256,
                    comparison.files[row.file_order].fact_directory_sha256,
                    row.phase,
                ),
                file_labels[comparison.files[row.file_order]],
                text_cell(row.phase, row.phase.title()),
                text_cell(
                    row.baseline_ns,
                    format_duration(row.baseline_ns, attribution=row.phase == "other"),
                ),
                text_cell(
                    row.candidate_ns,
                    format_duration(row.candidate_ns, attribution=row.phase == "other"),
                ),
                text_cell(row.delta_ns, format_duration(row.delta_ns)),
                text_cell(row.point, _format_point_ratio(row.point)),
            )
            for row in rows
        ),
        caption=PHASE_CAPTION,
        alignments=("left", "left", "right", "right", "right", "right"),
        collapse_repeats=frozenset({"benchmark"}),
        layout="wide",
    )
    return ReportSection("phases", "Phase comparison", (table,))


def _rulesets_section(
    views: PairReportViewData,
    comparison: ComparisonSpec,
    file_labels: dict[FileSpec, str],
) -> ReportSection:
    by_file: dict[int, list[RulesetComparisonView]] = {}
    for row in views.rulesets:
        by_file.setdefault(row.file_order, []).append(row)
    file_issues = {
        row.file_order: row.issue for row in views.files if row.metric == "wall_sec" and row.issue is not None
    }
    blocks: list[ReportBlock] = []
    for file_order, file in enumerate(comparison.files):
        title = f"Ruleset comparison — {file_labels[file]}"
        rulesets = by_file.get(file_order, [])
        if not rulesets:
            issue = file_issues.get(file_order)
            blocks.append(
                ReportMessage(
                    report_id("message", "rulesets", file.sha256, file.fact_directory_sha256),
                    title,
                    f"Status: {issue}" if issue is not None else "No rulesets recorded.",
                )
            )
            continue
        count = rulesets[0].ruleset_count
        caption = RULESET_CAPTION
        if count > 10:
            caption = (
                f"Showing 10 of {count} rulesets, ranked by absolute candidate − baseline total-time difference. "
                + caption
            )
        blocks.append(
            _table(
                report_id("table", "rulesets", file.sha256, file.fact_directory_sha256),
                title,
                ("ruleset", "baseline", "candidate", "delta", "ratio"),
                ("Ruleset", "Baseline total", "Candidate total", "Delta", "Ratio"),
                tuple(
                    _row(
                        report_id("row", "rulesets", file.sha256, file.fact_directory_sha256, row.name),
                        text_cell(row.name, DEFAULT_RULESET if row.name == "" else row.name),
                        text_cell(row.baseline_total_ns, format_duration(row.baseline_total_ns)),
                        text_cell(row.candidate_total_ns, format_duration(row.candidate_total_ns)),
                        text_cell(row.delta_ns, format_duration(row.delta_ns)),
                        text_cell(row.point, _format_point_ratio(row.point)),
                    )
                    for row in rulesets
                ),
                caption=caption,
                alignments=("left", "right", "right", "right", "right"),
                layout="wide",
            )
        )
    return ReportSection("rulesets", "Ruleset comparison", tuple(blocks))


def report_file_labels(files: Sequence[FileSpec]) -> dict[FileSpec, str]:
    """Return shortest unambiguous labels, including fact directories."""

    labels = {file: Path(file.display_path).name for file in files}
    by_basename: dict[str, list[FileSpec]] = {}
    for file in files:
        by_basename.setdefault(labels[file], []).append(file)
    for group in by_basename.values():
        paths = tuple(dict.fromkeys(file.display_path for file in group))
        if len(paths) == 1:
            continue
        max_depth = max(len(Path(path).parts) for path in paths)
        path_labels: dict[str, str] = {}
        for depth in range(2, max_depth + 1):
            candidates = {path: str(Path(*Path(path).parts[-depth:])) for path in paths}
            if len(set(candidates.values())) == len(paths):
                path_labels = candidates
                break
        if not path_labels:
            path_labels = {path: path for path in paths}
        for file in group:
            labels[file] = path_labels[file.display_path]
    by_label: dict[str, list[FileSpec]] = {}
    for file in files:
        by_label.setdefault(labels[file], []).append(file)
    for label, group in by_label.items():
        if len(group) == 1:
            continue
        fact_labels = {
            file: file.fact_directory.name if file.fact_directory is not None else "no-facts" for file in group
        }
        if len(set(fact_labels.values())) != len(group):
            fact_labels = {
                file: str(file.fact_directory) if file.fact_directory is not None else "no-facts" for file in group
            }
        for file in group:
            labels[file] = f"{label}:{fact_labels[file]}"
    return labels


def format_duration(value_ns: float | None, *, attribution: bool = False) -> str:
    """Format nanoseconds with three significant digits and a local unit."""

    if value_ns is None:
        return NULL
    prefix = "!" if attribution and value_ns < 0 else ""
    magnitude = abs(value_ns)
    if magnitude == 0:
        return "0 ns"
    if magnitude < 1_000:
        scaled, unit = value_ns, "ns"
    elif magnitude < 1_000_000:
        scaled, unit = value_ns / 1_000, "us"
    elif magnitude < 1_000_000_000:
        scaled, unit = value_ns / 1_000_000, "ms"
    else:
        scaled, unit = value_ns / 1_000_000_000, "s"
    return f"{prefix}{_three_significant_digits(scaled)} {unit}"


def _three_significant_digits(value: float) -> str:
    magnitude = abs(value)
    if magnitude == 0:
        return "0"
    decimal_places = max(0, 2 - math.floor(math.log10(magnitude)))
    return f"{value:.{decimal_places}f}"


def _metric_label(metric: MetricName) -> str:
    return "Wall time" if metric == "wall_sec" else "Peak RSS"


def _estimate_cell(
    point: float | None,
    low: float | None,
    high: float | None,
    *,
    rss: bool,
) -> ReportCell:
    if point is None:
        return text_cell(None, NULL)
    formatter = format_bytes if rss else format_seconds_value
    display = formatter(point)
    if low is not None and high is not None:
        display = _format_bytes_interval(point, low, high) if rss else f"{display} [{low:.4f}, {high:.4f}]"
    return text_cell(point, display)


def _ratio_cell(summary: RatioSummary) -> ReportCell:
    return text_cell(summary.point, format_ratio_summary(summary))


def format_ratio_summary(summary: RatioSummary) -> str:
    if summary.point is None:
        return NULL
    point = f"{summary.point:.3f}x"
    if summary.ci_low is None or summary.ci_high is None:
        return point
    return f"{point} [{summary.ci_low:.3f}, {summary.ci_high:.3f}]"


def _format_point_ratio(point: float | None) -> str:
    return NULL if point is None else f"{point:.3f}x"


def format_seconds_value(value: float) -> str:
    return f"{value:.4f}s"


def format_bytes(value: float) -> str:
    divisor, unit = _byte_unit(value)
    return _format_bytes_in_unit(value, divisor, unit, include_unit=True)


def _format_bytes_interval(point: float, low: float, high: float) -> str:
    divisor, unit = _byte_unit(max(abs(point), abs(low), abs(high)))
    point_text = _format_bytes_in_unit(point, divisor, unit, include_unit=True)
    low_text = _format_bytes_in_unit(low, divisor, unit, include_unit=False)
    high_text = _format_bytes_in_unit(high, divisor, unit, include_unit=False)
    return f"{point_text} [{low_text}, {high_text}]"


def _byte_unit(value: float) -> tuple[float, str]:
    units = ("B", "KiB", "MiB", "GiB")
    magnitude = abs(float(value))
    divisor = 1.0
    unit = units[0]
    for index, candidate in enumerate(units):
        unit = candidate
        divisor = 1024.0**index
        if magnitude / divisor < 1024 or candidate == units[-1]:
            break
    return divisor, unit


def _format_bytes_in_unit(value: float, divisor: float, unit: str, *, include_unit: bool) -> str:
    amount = value / divisor
    text = f"{int(amount)}" if unit == "B" else f"{amount:.1f}"
    return f"{text} {unit}" if include_unit else text


def _result_cell(result_class: ResultClass, issue: str | None, *, rss: bool) -> ReportCell:
    if result_class == "invalid":
        text = f"incomplete: {issue or 'unavailable'}"
    elif result_class == "point_only":
        text = "point only"
    elif result_class == "lower":
        text = "lower RSS" if rss else "faster"
    elif result_class == "higher":
        text = "higher RSS" if rss else "slower"
    elif result_class == "unclear":
        text = "CI includes 1"
    else:
        raise AssertionError(f"unknown result class: {result_class}")
    tones: dict[ResultClass, CellTone] = {
        "higher": "negative",
        "invalid": "error",
        "lower": "positive",
        "point_only": "muted",
        "unclear": "warning",
    }
    return text_cell(result_class, text, tone=tones[result_class])


def _table(
    table_id: str,
    title: str,
    column_ids: tuple[str, ...],
    labels: tuple[str, ...],
    rows: tuple[ReportRow, ...],
    *,
    caption: str | None = None,
    alignments: tuple[TableAlignment, ...] | None = None,
    collapse_repeats: frozenset[str] = frozenset(),
    layout: TableLayout = "standard",
) -> ReportTable:
    selected_alignments = alignments or tuple("left" for _ in labels)
    return ReportTable(
        table_id,
        title,
        tuple(
            ReportColumn(
                column_id,
                label,
                alignment,
                collapse_repeats=column_id in collapse_repeats,
            )
            for column_id, label, alignment in zip(column_ids, labels, selected_alignments, strict=True)
        ),
        rows,
        caption,
        layout,
    )


def _row(row_id: str, *values: ReportCell | str | int | float | bool | None) -> ReportRow:
    return ReportRow(row_id, tuple(value if isinstance(value, ReportCell) else text_cell(value) for value in values))
