"""Build the canonical benchmark presentation and format its values.

This module maps typed statistics from :mod:`benchmarking.reports.analysis`
into Comparison, Summary, Files, Phases, and Rulesets sections. It owns shared
labels, units, interval formatting, and result wording; Rich and Markdown only
serialize the resulting catalog.
"""

from __future__ import annotations

import math
from collections.abc import Sequence
from pathlib import Path

from ..models import BenchmarkEndpoint, ComparisonSpec, DetailLevel, FileSpec
from .analysis import (
    Estimate,
    FileComparisonView,
    MetricName,
    PairReportViewData,
    PhaseComparisonView,
    PhaseEstimate,
    PhaseName,
    RatioEstimate,
    ResultClass,
    RulesetComparisonView,
    SummaryView,
    analyze_pair,
)
from .catalog import (
    CellTone,
    ReportBlock,
    ReportCatalog,
    ReportCell,
    ReportColumn,
    ReportMessage,
    ReportRow,
    ReportSection,
    ReportTable,
    TableAlignment,
    report_id,
    text_cell,
)
from .store import ReportStore

NULL = "—"
DEFAULT_RULESET = "<default ruleset>"
DETAIL_ORDER: dict[DetailLevel, int] = {
    "summary": 0,
    "files": 1,
    "phases": 2,
    "rulesets": 3,
}
RATIO_DIRECTION = "Ratios are candidate / baseline; below 1 is lower and above 1 is higher."
PHASE_CAPTION = (
    "Endpoint cells show a 95% CI (or one-round point) and that phase's share of endpoint wall time. "
    "Delta is the signed candidate − baseline mean; Δ contribution is the phase's share of the wall-time "
    "change and may be negative or exceed 100% when phases offset. Execution overhead is stored per-ruleset "
    "unattributed time. Outside recorded rulesets is wall time minus all five recorded phases; ! marks a negative "
    "residual."
)
RULESET_CAPTION = (
    "Totals show a 95% CI or one-round point. S/A/Exec/M/R are signed candidate − baseline mean deltas for "
    "Search, Apply, Execution overhead (stored unattributed time), Merge, and Rebuild."
)

PHASE_LABELS: dict[PhaseName, str] = {
    "search": "Search",
    "apply": "Apply",
    "unattributed": "Execution overhead",
    "merge": "Merge",
    "rebuild": "Rebuild",
    "outside": "Outside recorded rulesets",
}


def build_report_catalog(
    store: ReportStore,
    comparison: ComparisonSpec,
    detail: DetailLevel = "summary",
) -> ReportCatalog:
    """Analyze one pair and build its complete presentation catalog."""

    views = analyze_pair(store, comparison, detail)
    file_labels = report_file_labels(comparison.files)

    sections = [
        _selection_section(store.display_path, comparison, file_labels),
        _summary_section(comparison, views.summary, file_labels),
    ]
    if _includes(detail, "files"):
        sections.append(_files_section(views.files, comparison, file_labels))
    if _includes(detail, "phases"):
        sections.append(_phases_section(views.phases, comparison, file_labels))
    if _includes(detail, "rulesets"):
        sections.append(_rulesets_section(views, comparison, file_labels))
    return ReportCatalog(tuple(sections))


def _includes(detail: DetailLevel, requested: DetailLevel) -> bool:
    return DETAIL_ORDER[detail] >= DETAIL_ORDER[requested]


def _selection_section(
    report_path: str,
    comparison: ComparisonSpec,
    file_labels: dict[FileSpec, str],
) -> ReportSection:
    endpoint_rows = tuple(
        _row(
            report_id(
                "row",
                "selection",
                role,
                report_id("endpoint", *endpoint.cache_identity),
            ),
            text_cell(role, role.title()),
            endpoint.target.display_label,
            text_cell(
                endpoint.target.row.git_sha,
                _git_display(endpoint.target.row.git_sha, endpoint.target.row.is_dirty),
            ),
            endpoint.backend,
            endpoint.treatment,
        )
        for role, endpoint in (("baseline", comparison.baseline), ("candidate", comparison.candidate))
    )
    endpoint_table = _table(
        report_id("table", "selection", "endpoints"),
        "Comparison",
        ("role", "target", "git", "backend", "treatment"),
        ("Role", "Target", "Git", "Backend", "Treatment"),
        endpoint_rows,
        caption=_comparison_caption(report_path, comparison, file_labels),
    )
    blocks: list[ReportBlock] = [endpoint_table]
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


def _git_display(git_sha: str, is_dirty: bool) -> str:
    suffix = " dirty" if is_dirty else ""
    return f"{git_sha[:12]}{suffix}"


def _comparison_caption(
    report_path: str,
    comparison: ComparisonSpec,
    file_labels: dict[FileSpec, str],
) -> str:
    selected_files = ", ".join(_file_with_facts(file, file_labels[file]) for file in comparison.files)
    return (
        f"{len(comparison.files)} file(s): {selected_files} · {comparison.rounds} round(s) per endpoint/file · "
        f"{comparison.timeout_sec} s timeout per run · Report: {report_path}"
    )


def _file_with_facts(file: FileSpec, label: str) -> str:
    if file.fact_directory is None:
        return label
    return f"{label} (facts: {file.fact_directory})"


def _summary_section(
    comparison: ComparisonSpec,
    rows: Sequence[SummaryView],
    file_labels: dict[FileSpec, str],
) -> ReportSection:
    title = f"Summary — {_endpoint_identity(comparison.candidate)} vs {_endpoint_identity(comparison.baseline)}"
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
                _result_cell(row.ratio.result_class, row.ratio.issue, rss=row.metric == "max_rss_bytes"),
            )
        )
    table = _table(
        report_id("table", "summary"),
        title,
        ("metric", "scope", "file", "ratio", "result"),
        ("Metric", "Scope", "File(s)", "Ratio (95% CI)", "Result"),
        tuple(report_rows),
        caption=RATIO_DIRECTION,
        alignments=("left", "left", "left", "right", "left"),
    )
    return ReportSection("summary", title, (table,))


def _endpoint_identity(endpoint: BenchmarkEndpoint) -> str:
    return f"{endpoint.target.display_label} {endpoint.backend}/{endpoint.treatment}"


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
            row.baseline.point is not None or row.candidate.point is not None for row in metric_rows
        ):
            tables.append(
                ReportMessage(
                    report_id("message", "files", metric),
                    "Peak RSS",
                    "Peak RSS is unavailable for the selected endpoints.",
                    tone="muted",
                )
            )
            continue
        tables.append(
            _table(
                report_id("table", "files", metric),
                "Wall time" if metric == "wall_sec" else "Peak RSS",
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
                        _estimate_cell(row.baseline, rss=metric == "max_rss_bytes"),
                        _estimate_cell(row.candidate, rss=metric == "max_rss_bytes"),
                        _ratio_cell(row.ratio),
                        _result_cell(row.ratio.result_class, row.ratio.issue, rss=metric == "max_rss_bytes"),
                    )
                    for row in metric_rows
                ),
                alignments=("left", "right", "right", "right", "left"),
            )
        )
    return ReportSection("files", "Per-file results", tuple(tables))


def _phases_section(
    rows: Sequence[PhaseComparisonView],
    comparison: ComparisonSpec,
    file_labels: dict[FileSpec, str],
) -> ReportSection:
    by_file: dict[int, list[PhaseComparisonView]] = {}
    for row in rows:
        by_file.setdefault(row.file_order, []).append(row)
    blocks: list[ReportBlock] = [
        ReportMessage(report_id("message", "phases", "guide"), None, PHASE_CAPTION, tone="muted")
    ]
    for file_order, file in enumerate(comparison.files):
        blocks.append(
            _table(
                report_id("table", "phases", file.sha256, file.fact_directory_sha256),
                f"Phase comparison — {file_labels[file]}",
                ("phase", "baseline", "candidate", "delta", "wall_delta"),
                ("Phase", "Baseline (95% CI · wall)", "Candidate (95% CI · wall)", "Delta", "Δ contribution"),
                tuple(_phase_row(row, file) for row in by_file[file_order]),
                alignments=("left", "right", "right", "right", "right"),
            )
        )
    return ReportSection("phases", "Phase comparison", tuple(blocks))


def _phase_row(row: PhaseComparisonView, file: FileSpec) -> ReportRow:
    return _row(
        report_id("row", "phases", file.sha256, file.fact_directory_sha256, row.phase),
        text_cell(row.phase, PHASE_LABELS[row.phase]),
        _phase_estimate_cell(row.baseline, attribution=row.phase == "outside"),
        _phase_estimate_cell(row.candidate, attribution=row.phase == "outside"),
        text_cell(row.delta_ns, format_duration(row.delta_ns, signed=True)),
        text_cell(row.wall_delta_contribution, _format_percent(row.wall_delta_contribution, signed=True)),
    )


def _rulesets_section(
    views: PairReportViewData,
    comparison: ComparisonSpec,
    file_labels: dict[FileSpec, str],
) -> ReportSection:
    by_file: dict[int, list[RulesetComparisonView]] = {}
    for row in views.rulesets:
        by_file.setdefault(row.file_order, []).append(row)
    file_issues = {
        row.file_order: row.ratio.issue
        for row in views.files
        if row.metric == "wall_sec" and row.ratio.issue is not None
    }
    blocks: list[ReportBlock] = []
    if views.rulesets:
        blocks.append(ReportMessage(report_id("message", "rulesets", "guide"), None, RULESET_CAPTION, tone="muted"))
    for file_order, file in enumerate(comparison.files):
        title = f"Ruleset comparison — {file_labels[file]}"
        rulesets = by_file.get(file_order, [])
        if not rulesets:
            issue = file_issues.get(file_order)
            status = f"Status: {issue}" if issue is not None else "No nonzero ruleset timing differences."
            blocks.append(
                ReportMessage(
                    report_id("message", "rulesets", file.sha256, file.fact_directory_sha256),
                    title,
                    status,
                )
            )
            continue
        count = rulesets[0].ruleset_count
        caption = None if count <= 10 else f"Showing 10 of {count} changed rulesets by absolute total delta."
        blocks.append(
            _table(
                report_id("table", "rulesets", file.sha256, file.fact_directory_sha256),
                title,
                (
                    "ruleset",
                    "baseline",
                    "candidate",
                    "delta",
                    "search_delta",
                    "apply_delta",
                    "execution_delta",
                    "merge_delta",
                    "rebuild_delta",
                ),
                ("Ruleset", "Baseline total", "Candidate total", "Total Δ", "S Δ", "A Δ", "Exec Δ", "M Δ", "R Δ"),
                tuple(
                    _row(
                        report_id("row", "rulesets", file.sha256, file.fact_directory_sha256, row.name),
                        text_cell(row.name, DEFAULT_RULESET if row.name == "" else row.name),
                        _duration_estimate_cell(row.baseline),
                        _duration_estimate_cell(row.candidate),
                        text_cell(row.delta.total, format_duration(row.delta.total, signed=True)),
                        text_cell(row.delta.phases.search, format_duration(row.delta.phases.search, signed=True)),
                        text_cell(row.delta.phases.apply, format_duration(row.delta.phases.apply, signed=True)),
                        text_cell(
                            row.delta.phases.unattributed,
                            format_duration(row.delta.phases.unattributed, signed=True),
                        ),
                        text_cell(row.delta.phases.merge, format_duration(row.delta.phases.merge, signed=True)),
                        text_cell(row.delta.phases.rebuild, format_duration(row.delta.phases.rebuild, signed=True)),
                    )
                    for row in rulesets
                ),
                caption=caption,
                alignments=("left", "right", "right", "right", "right", "right", "right", "right", "right"),
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


def format_duration(
    value_ns: float | None,
    *,
    attribution: bool = False,
    signed: bool = False,
) -> str:
    """Format nanoseconds with three significant digits and a local unit."""

    if value_ns is None:
        return NULL
    prefix = "!" if attribution and value_ns < 0 else ""
    divisor, unit = _duration_unit(abs(value_ns))
    return f"{prefix}{_format_scaled(value_ns / divisor, signed=signed)} {unit}"


def _format_duration_interval(
    point_ns: float | None,
    low_ns: float | None,
    high_ns: float | None,
    *,
    attribution: bool = False,
) -> str:
    if point_ns is None:
        return NULL
    if low_ns is None or high_ns is None:
        return format_duration(point_ns, attribution=attribution)
    divisor, unit = _duration_unit(max(abs(point_ns), abs(low_ns), abs(high_ns)))
    prefix = "!" if attribution and point_ns < 0 else ""
    return f"{prefix}{_format_scaled(low_ns / divisor)}–{_format_scaled(high_ns / divisor)} {unit}"


def _duration_unit(magnitude_ns: float) -> tuple[float, str]:
    if magnitude_ns < 1_000:
        return 1.0, "ns"
    if magnitude_ns < 1_000_000:
        return 1_000.0, "us"
    if magnitude_ns < 1_000_000_000:
        return 1_000_000.0, "ms"
    return 1_000_000_000.0, "s"


def _format_scaled(value: float, *, signed: bool = False) -> str:
    prefix = "+" if signed and value > 0 else ""
    return f"{prefix}{_three_significant_digits(value)}"


def _three_significant_digits(value: float) -> str:
    magnitude = abs(value)
    if magnitude == 0:
        return "0"
    decimal_places = max(0, 2 - math.floor(math.log10(magnitude)))
    return f"{value:.{decimal_places}f}"


def _metric_label(metric: MetricName) -> str:
    return "Wall time" if metric == "wall_sec" else "Peak RSS"


def _estimate_cell(
    estimate: Estimate,
    *,
    rss: bool,
) -> ReportCell:
    point, low, high = estimate
    if point is None:
        return text_cell(None, NULL)
    if rss:
        display = format_bytes(point) if low is None or high is None else _format_bytes_interval(point, low, high)
    else:
        display = _format_duration_interval(
            point * 1_000_000_000.0,
            None if low is None else low * 1_000_000_000.0,
            None if high is None else high * 1_000_000_000.0,
        )
    return text_cell(point, display)


def _duration_estimate_cell(estimate: Estimate | None) -> ReportCell:
    if estimate is None:
        return text_cell(None, NULL)
    return text_cell(estimate.point, _format_duration_interval(*estimate))


def _phase_estimate_cell(
    phase: PhaseEstimate,
    *,
    attribution: bool,
) -> ReportCell:
    duration = _format_duration_interval(*phase.timing, attribution=attribution)
    display = duration if phase.wall_share is None else f"{duration} · {_format_percent(phase.wall_share)}"
    point = phase.timing.point
    tone: CellTone = "warning" if attribution and point is not None and point < 0 else "default"
    return text_cell(point, display, tone=tone)


def _ratio_cell(ratio: RatioEstimate) -> ReportCell:
    return text_cell(ratio.estimate.point, format_ratio_summary(ratio))


def format_ratio_summary(ratio: RatioEstimate) -> str:
    estimate = ratio.estimate
    if estimate.point is None:
        return NULL
    point = f"{_three_significant_digits(estimate.point)}x"
    if estimate.ci_low is None or estimate.ci_high is None:
        return point
    return f"{_three_significant_digits(estimate.ci_low)}–{_three_significant_digits(estimate.ci_high)}x"


def _format_percent(value: float | None, *, signed: bool = False) -> str:
    if value is None:
        return NULL
    prefix = "+" if signed and value > 0 else ""
    return f"{prefix}{_three_significant_digits(value * 100)}%"


def format_bytes(value: float) -> str:
    divisor, unit = _byte_unit(value)
    return _format_bytes_in_unit(value, divisor, unit, include_unit=True)


def _format_bytes_interval(point: float, low: float, high: float) -> str:
    divisor, unit = _byte_unit(max(abs(point), abs(low), abs(high)))
    low_text = _format_bytes_in_unit(low, divisor, unit, include_unit=False)
    high_text = _format_bytes_in_unit(high, divisor, unit, include_unit=False)
    return f"{low_text}–{high_text} {unit}"


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
) -> ReportTable:
    selected_alignments = alignments or tuple("left" for _ in labels)
    return ReportTable(
        table_id,
        title,
        tuple(
            ReportColumn(column_id, label, alignment)
            for column_id, label, alignment in zip(column_ids, labels, selected_alignments, strict=True)
        ),
        rows,
        caption,
    )


def _row(row_id: str, *values: ReportCell | str | int | float | bool | None) -> ReportRow:
    return ReportRow(row_id, tuple(value if isinstance(value, ReportCell) else text_cell(value) for value in values))
