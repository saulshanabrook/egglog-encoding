"""Build the canonical benchmark presentation and format its values.

This module maps typed statistics from :mod:`benchmarking.reports.analysis`
into Comparison, Summary, Files, Mechanisms, and Rulesets sections. It owns shared
labels, units, interval formatting, and result wording; Rich and Markdown only
serialize the resulting catalog.
"""

from __future__ import annotations

import math
from collections.abc import Sequence
from pathlib import Path

from ..engines import TREATMENT_SPECS
from ..models import BenchmarkEndpoint, ComparisonSpec, DetailLevel, FileSpec
from .analysis import (
    RULESET_PHASES,
    Estimate,
    FileComparisonView,
    FileTimingBreakdown,
    MetricName,
    PhaseValues,
    RatioEstimate,
    ResultClass,
    RulesetGroup,
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
RULESET_CONTRIBUTOR_LIMIT = 5
DETAIL_ORDER: dict[DetailLevel, int] = {
    "summary": 0,
    "files": 1,
    "phases": 2,
    "rulesets": 3,
}
RESULT_TONES: dict[ResultClass, CellTone] = {
    "higher": "default",
    "invalid": "error",
    "lower": "positive",
    "point_only": "muted",
    "unclear": "muted",
}
RATIO_DIRECTION = "Ratios are candidate / baseline; below 1 is lower and above 1 is higher."
DECOMPOSITION_CAPTION = (
    "The Suite total row sums each selected file's candidate − baseline mean; file rows are per-file mean deltas. "
    "Each mechanism cell is its share of that row's wall-time change followed by its signed mean time change. "
    "Frontend includes parsing, other lowering, and declaration/install commands. Program rules includes every "
    "phase of source-origin rulesets except rebuild. Equality/rebuild combines encoded maintenance rulesets with "
    "native rebuild tails. Commands includes actions/input, checks, and other schedules. Shares may be negative or "
    "exceed 100% when mechanisms offset. ◆ and bold type mark each row's largest absolute share; contributions below "
    "5% are dimmed and improvements are green in Rich and interactive reports. Signed values carry the same "
    "information without styling. Residual is wall time minus every recorded leaf; ! means an endpoint's mean "
    "residual is negative."
)
RULESET_CAPTION = (
    "Each panel unfolds the Program and Equality cells from the decomposition. Parent rows exactly match those "
    "cells and alone show wall share. Program children contain only source-rule Assembly, Search, Apply, Execution, "
    "and Merge; Equality children contain every encoded maintenance ruleset plus one global Native rebuild replaced "
    "row. ↳ marks children in every format. Zero children are hidden. Source children are ranked by absolute own-work "
    f"Δ (top {RULESET_CONTRIBUTOR_LIMIT} plus an exact per-group Other); every nonzero maintenance child is shown. "
    "Important phases include every |phase Δ| ≥ max(1 ms, 10% of |row Δ|), always include the dominant phase (◆), "
    "and appear in Assembly, Search, Apply, Execution, Merge, Rebuild order; … marks omitted nonzero phases."
)


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
        sections.append(_phases_section(views.timing, comparison, file_labels))
    if _includes(detail, "rulesets"):
        sections.append(_rulesets_section(views.timing, comparison, file_labels))
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
            endpoint.treatment,
        )
        for role, endpoint in (("baseline", comparison.baseline), ("candidate", comparison.candidate))
    )
    endpoint_table = _table(
        report_id("table", "selection", "endpoints"),
        "Comparison",
        ("role", "target", "git", "treatment"),
        ("Role", "Target", "Git", "Treatment"),
        endpoint_rows,
        caption=_comparison_caption(report_path, comparison, file_labels),
    )
    blocks: list[ReportBlock] = [endpoint_table]
    baseline_engine = TREATMENT_SPECS[comparison.baseline.treatment].engine
    candidate_engine = TREATMENT_SPECS[comparison.candidate.treatment].engine
    target_changed = (
        comparison.baseline.target.row.git_sha,
        comparison.baseline.target.row.is_dirty,
        comparison.baseline.target.display_label,
    ) != (
        comparison.candidate.target.row.git_sha,
        comparison.candidate.target.row.is_dirty,
        comparison.candidate.target.display_label,
    ) or (
        baseline_engine == candidate_engine
        and comparison.baseline.target.binary_sha256_for(comparison.baseline.treatment)
        != comparison.candidate.target.binary_sha256_for(comparison.candidate.treatment)
    )
    changed = (target_changed, comparison.baseline.treatment != comparison.candidate.treatment)
    if sum(changed) > 1:
        blocks.append(
            ReportMessage(
                report_id("message", "selection", "joint-comparison"),
                None,
                "This comparison changes both target and treatment. Its ratios describe "
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
    return f"{endpoint.target.display_label} {endpoint.treatment}"


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
    rows: Sequence[FileTimingBreakdown],
    comparison: ComparisonSpec,
    file_labels: dict[FileSpec, str],
) -> ReportSection:
    report_rows = []
    for row in rows:
        if row.file_order is None:
            row_id = report_id("row", "phases", "suite")
            file_count = len(comparison.files)
            label = f"Suite total ({file_count} {'file' if file_count == 1 else 'files'})"
        else:
            file = comparison.files[row.file_order]
            row_id = report_id("row", "phases", file.sha256, file.fact_directory_sha256)
            label = file_labels[file]
        deltas = row.mechanism_deltas
        wall_delta = row.wall_delta_ns
        shares = tuple(
            None if delta is None or wall_delta is None or wall_delta == 0 else delta / wall_delta for delta in deltas
        )
        comparable = [index for index, share in enumerate(shares) if share is not None]
        leader = max(comparable, key=lambda index: abs(shares[index] or 0.0), default=None)
        if leader is not None and shares[leader] == 0.0:
            leader = None
        mechanism_cells = tuple(
            _slowdown_cell(
                delta,
                shares[index],
                leader=index == leader,
                warning=row.residual_warning and index == len(deltas) - 1,
            )
            for index, delta in enumerate(deltas)
        )
        report_rows.append(
            _row(
                row_id,
                text_cell(row.file_order, label),
                text_cell(
                    row.wall_delta_ns,
                    _format_delta_ms(row.wall_delta_ns),
                    tone=_delta_tone(row.wall_delta_ns),
                ),
                *mechanism_cells,
            )
        )
    table = _table(
        report_id("table", "phases", "decomposition"),
        "Slowdown decomposition",
        ("file", "wall_delta", "typecheck", "frontend", "program", "equality", "commands", "residual"),
        (
            "File",
            "Wall Δ",
            "Typecheck",
            "Frontend",
            "Program",
            "Equality",
            "Commands",
            "Residual",
        ),
        tuple(report_rows),
        caption=DECOMPOSITION_CAPTION,
        alignments=("left", "right", "right", "right", "right", "right", "right", "right"),
    )
    return ReportSection("phases", "Slowdown decomposition", (table,))


def _slowdown_cell(
    delta_ns: float | None,
    slowdown_share: float | None,
    *,
    leader: bool,
    warning: bool,
) -> ReportCell:
    duration = _format_delta_ms(delta_ns)
    share = _format_percent(slowdown_share, signed=True)
    marker = "◆ " if leader else ""
    display = NULL if delta_ns is None else f"{marker}{share}  {duration}"
    if warning:
        display = f"!{display}"
    return text_cell(
        slowdown_share,
        display,
        tone=_delta_tone(delta_ns, share=slowdown_share, emphasis=leader, warning=warning),
    )


def _delta_tone(
    delta_ns: float | None,
    *,
    share: float | None = None,
    emphasis: bool = False,
    warning: bool = False,
) -> CellTone:
    """Apply the report's anomaly-first styling policy to one signed delta."""

    if warning:
        return "warning"
    if emphasis:
        return "emphasis"
    if share is not None and abs(share) < 0.05:
        return "muted"
    if delta_ns is not None and delta_ns < 0:
        return "positive"
    if delta_ns == 0:
        return "muted"
    return "default"


def _rulesets_section(
    timing: Sequence[FileTimingBreakdown],
    comparison: ComparisonSpec,
    file_labels: dict[FileSpec, str],
) -> ReportSection:
    by_file = {row.file_order: row for row in timing if row.file_order is not None}
    blocks: list[ReportBlock] = [
        ReportMessage(report_id("message", "rulesets", "guide"), None, RULESET_CAPTION, tone="muted")
    ]
    for file_order, file in enumerate(comparison.files):
        title = f"Ruleset drivers — {file_labels[file]}"
        breakdown = by_file.get(file_order)
        if breakdown is None or breakdown.issue is not None:
            status = f"Status: {breakdown.issue}" if breakdown is not None else "Timing unavailable."
            blocks.append(
                ReportMessage(
                    report_id("message", "rulesets", file.sha256, file.fact_directory_sha256),
                    title,
                    status,
                )
            )
            continue
        program = sorted(breakdown.program.rulesets, key=lambda row: (-abs(row.phases.total), row.name))
        maintenance = sorted(breakdown.equality.rulesets, key=lambda row: (-abs(row.phases.total), row.name))
        wall_delta = breakdown.wall_delta_ns
        coverage = (
            None
            if wall_delta is None or wall_delta == 0
            else (breakdown.program.phases.total + breakdown.equality.phases.total) / wall_delta
        )
        coverage_text = (
            "Program + Equality coverage is unavailable because wall time did not change."
            if coverage is None
            else (
                f"Program + Equality account for {_format_percent(coverage, signed=True)} "
                "of this file's wall-time change."
            )
        )
        source_count = len(program)
        source_shown = min(source_count, RULESET_CONTRIBUTOR_LIMIT)
        source_text = f"Source rules shown: {source_shown}/{source_count}"
        source_text += " plus exact Other." if source_count > source_shown else "."
        maintenance_count = len(maintenance)
        maintenance_text = (
            "Maintenance rules shown: none."
            if maintenance_count == 0
            else f"Maintenance rules shown: {maintenance_count}/{maintenance_count}."
        )
        caption = f"{coverage_text} {source_text} {maintenance_text}"
        report_rows = [
            _ruleset_report_row(
                file,
                "aggregate",
                "program",
                "",
                source_count,
                breakdown.program.phases,
                breakdown.wall_delta_ns,
            )
        ]
        report_rows.extend(
            _ruleset_report_row(
                file,
                "ruleset",
                "program",
                ruleset.name,
                1,
                ruleset.phases,
                breakdown.wall_delta_ns,
            )
            for ruleset in program[:RULESET_CONTRIBUTOR_LIMIT]
        )
        if len(program) > RULESET_CONTRIBUTOR_LIMIT:
            omitted = tuple(program[RULESET_CONTRIBUTOR_LIMIT:])
            report_rows.append(
                _ruleset_report_row(
                    file,
                    "other",
                    "program",
                    "",
                    len(omitted),
                    RulesetGroup(omitted).phases,
                    breakdown.wall_delta_ns,
                )
            )
        report_rows.append(
            _ruleset_report_row(
                file,
                "aggregate",
                "equality",
                "",
                maintenance_count,
                breakdown.equality.phases,
                breakdown.wall_delta_ns,
            )
        )
        report_rows.extend(
            _ruleset_report_row(
                file,
                "ruleset",
                "equality",
                ruleset.name,
                1,
                ruleset.phases,
                breakdown.wall_delta_ns,
            )
            for ruleset in maintenance
        )
        if breakdown.equality.native_rebuild_delta_ns != 0:
            report_rows.append(
                _ruleset_report_row(
                    file,
                    "native_rebuild",
                    "equality",
                    "",
                    0,
                    PhaseValues(0, 0, 0, 0, 0, breakdown.equality.native_rebuild_delta_ns),
                    breakdown.wall_delta_ns,
                )
            )
        blocks.append(
            _table(
                report_id("table", "rulesets", file.sha256, file.fact_directory_sha256),
                title,
                ("driver", "delta", "share", "important_phases"),
                ("Driver", "Δ", "Wall share", "Important phase changes"),
                tuple(report_rows),
                caption=caption,
                alignments=("left", "right", "right", "left"),
            )
        )
    return ReportSection("rulesets", "Ruleset drivers", tuple(blocks))


def _ruleset_report_row(
    file: FileSpec,
    kind: str,
    mechanism: str,
    name: str,
    ruleset_count: int,
    phases: PhaseValues,
    wall_delta: float | None,
) -> ReportRow:
    parent = kind == "aggregate"
    share = None if not parent or wall_delta is None or wall_delta == 0 else phases.total / wall_delta
    tone = _delta_tone(phases.total, share=share)
    if kind == "aggregate":
        label = "Program rules — own work" if mechanism == "program" else "Equality/rebuild — net"
    elif kind == "native_rebuild":
        label = "↳ Native rebuild replaced"
    elif kind == "other":
        label = f"↳ Other ({ruleset_count} more source rulesets)"
    else:
        label = f"↳ {DEFAULT_RULESET if name == '' else name}"
    return _row(
        report_id(
            "row",
            "rulesets",
            file.sha256,
            file.fact_directory_sha256,
            kind,
            mechanism,
            name,
        ),
        text_cell(name, label, tone="emphasis" if parent else "default"),
        text_cell(phases.total, format_duration(phases.total, signed=True), tone=tone),
        text_cell(share, _format_percent(share, signed=True) if parent else "", tone=tone),
        text_cell(_important_phase_changes(phases), tone=tone),
    )


def _important_phase_changes(phases: PhaseValues) -> str:
    changed = [index for index, value in enumerate(phases) if value != 0]
    if not changed:
        return "0 ns"
    dominant = max(changed, key=lambda index: abs(phases[index]))
    threshold = max(1_000_000.0, abs(phases.total) * 0.1)
    included = {index for index in changed if abs(phases[index]) >= threshold}
    included.add(dominant)
    parts = [
        f"{'◆ ' if index == dominant else ''}{RULESET_PHASES[index].title()} "
        f"{format_duration(phases[index], signed=True)}"
        for index in range(len(RULESET_PHASES))
        if index in included
    ]
    if any(index not in included for index in changed):
        parts.append("…")
    return "; ".join(parts)


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
    signed: bool = False,
) -> str:
    """Format nanoseconds with three significant digits and a local unit."""

    if value_ns is None:
        return NULL
    divisor, unit = _duration_unit(abs(value_ns))
    return f"{_format_scaled(value_ns / divisor, signed=signed)} {unit}"


def _format_delta_ms(value_ns: float | None) -> str:
    if value_ns is None:
        return NULL
    return f"{_format_scaled(value_ns / 1_000_000.0, signed=True)} ms"


def _format_duration_interval(
    point_ns: float | None,
    low_ns: float | None,
    high_ns: float | None,
) -> str:
    if point_ns is None:
        return NULL
    if low_ns is None or high_ns is None:
        return format_duration(point_ns)
    divisor, unit = _duration_unit(max(abs(point_ns), abs(low_ns), abs(high_ns)))
    return f"{_format_scaled(low_ns / divisor)}–{_format_scaled(high_ns / divisor)} {unit}"


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


def _ratio_cell(ratio: RatioEstimate) -> ReportCell:
    # Retain the point for sorting/filtering while keeping the visible CI cell compact.
    return text_cell(ratio.estimate.point, format_ratio_summary(ratio), tone=RESULT_TONES[ratio.result_class])


def format_ratio_summary(ratio: RatioEstimate) -> str:
    """Show CI bounds when available, otherwise the point, to keep cells compact."""

    estimate = ratio.estimate
    if estimate.point is None:
        return NULL
    if estimate.ci_low is not None and estimate.ci_high is not None:
        return f"{_three_significant_digits(estimate.ci_low)}–{_three_significant_digits(estimate.ci_high)}x"
    return f"{_three_significant_digits(estimate.point)}x"


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
    return text_cell(result_class, text, tone=RESULT_TONES[result_class])


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
