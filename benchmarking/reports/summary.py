"""Lay out renderer-neutral ordinary benchmark and optional timing reports.

This module chooses comparison coordinates, report sections, columns, captions,
and human wording. DuckDB views own statistics, result classifications,
best/worst selection, rollups, and timing aggregation; ``database`` returns
their typed rows. Timing-specific table assembly belongs in ``timing``, while
Rich/Markdown syntax and terminal behavior belong in ``render``.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from dataclasses import dataclass
from pathlib import Path

from scipy import stats

from ..models import (
    Backend,
    BenchmarkSpec,
    FileSpec,
    ResolvedTarget,
    Treatment,
    backend_has_treatment,
    backend_spec,
    benchmark_cells,
    shared_backend_treatments,
)
from .database import ReportDatabase
from .results import (
    CellEstimateView,
    ComparisonRequest,
    ComparisonRollupView,
    FileRatioView,
    MetricName,
    RatioSummary,
    ReportTableData,
    ResultClass,
    TargetView,
)
from .timing import TimingReport, build_timing_report

ComparisonKey = tuple[int, int, int, int]

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
PROOF_OVERHEAD_CAPTION = "Within-backend proof overhead. This is not backend-vs-main performance."


@dataclass(frozen=True)
class MetricSpec:
    """Labels and text-formatting policy used only by summary tables."""

    title: str
    caption: str
    file_count_heading: str
    format_total: Callable[[float | None], str]
    format_change: Callable[[RatioSummary], str]
    format_result: Callable[[ResultClass, str | None], str]
    omit_without_samples: bool = False


@dataclass(frozen=True)
class ReportAnalysis:
    """Output-facing DuckDB view rows indexed by stable selector coordinates."""

    cells: dict[tuple[MetricName, int, int, int], CellEstimateView]
    file_ratios: dict[tuple[int, MetricName, int], FileRatioView]
    comparisons: dict[tuple[int, MetricName], ComparisonRollupView]
    comparison_orders: dict[ComparisonKey, int]

    def cell(self, metric: MetricName, target: int, file: int, cell: int) -> CellEstimateView:
        return self.cells[(metric, target, file, cell)]

    def comparison(
        self,
        metric: MetricName,
        baseline_target: int,
        baseline_cell: int,
        candidate_target: int,
        candidate_cell: int,
    ) -> ComparisonRollupView:
        key = (baseline_target, baseline_cell, candidate_target, candidate_cell)
        comparison_order = self.comparison_orders[key]
        return self.comparisons[(comparison_order, metric)]

    def file_ratio(self, comparison: ComparisonRollupView, file_order: int) -> FileRatioView:
        return self.file_ratios[(comparison.comparison_order, comparison.metric, file_order)]


@dataclass(frozen=True)
class ReportDocument:
    """Renderer-neutral sections for one complete benchmark report."""

    report_path: str
    rounds: int
    targets: tuple[TargetView, ...]
    command_argv: tuple[str, ...] | None
    targets_table: ReportTableData
    comparisons: tuple[ReportTableData, ...]
    diagnostics: tuple[ReportTableData, ...]
    timing: TimingReport | None
    summary: tuple[ReportTableData, ...]


def build_report_document(
    database: ReportDatabase,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    command_argv: Sequence[str] | None = None,
    *,
    phase_timings: bool = False,
    detailed_timing: bool = False,
) -> ReportDocument:
    """Query all selected results once and assemble report sections."""

    selected_targets = tuple(targets)
    t_critical = None if spec.rounds < 2 else float(stats.t.ppf(0.975, spec.rounds - 1))
    database.install_scope(selected_targets, spec, t_critical)
    requests = _comparison_requests(selected_targets, spec)
    view_data = database.report_view_data(
        requests,
        include_timing=phase_timings or detailed_timing,
    )
    analysis = ReportAnalysis(
        cells={(row.metric, row.target_order, row.file_order, row.cell_order): row for row in view_data.cell_estimates},
        file_ratios={(row.comparison_order, row.metric, row.file_order): row for row in view_data.file_ratios},
        comparisons={(row.comparison_order, row.metric): row for row in view_data.comparison_rollups},
        comparison_orders={
            (
                request.baseline_target_order,
                request.baseline_cell_order,
                request.candidate_target_order,
                request.candidate_cell_order,
            ): request.comparison_order
            for request in requests
        },
    )
    file_labels = report_file_labels(spec.files)
    comparisons = comparison_tables(analysis, selected_targets, spec, file_labels)
    diagnostics = diagnostic_tables(analysis, selected_targets, spec, file_labels)
    summary = summary_tables(analysis, selected_targets, spec, file_labels)
    timing = None
    if phase_timings or detailed_timing:
        timing = build_timing_report(
            view_data.compact_timings,
            view_data.ruleset_timings,
            selected_targets,
            spec,
            detailed=detailed_timing,
            file_labels=tuple(file_labels[file] for file in spec.files),
        )
    return ReportDocument(
        report_path=database.display_path,
        rounds=spec.rounds,
        targets=view_data.targets,
        command_argv=None if command_argv is None else tuple(command_argv),
        targets_table=targets_table_data(view_data.targets),
        comparisons=comparisons,
        diagnostics=diagnostics,
        timing=timing,
        summary=summary,
    )


def _comparison_requests(targets: Sequence[ResolvedTarget], spec: BenchmarkSpec) -> tuple[ComparisonRequest, ...]:
    cells = benchmark_cells(spec)
    target_count = len(targets)
    keys: list[ComparisonKey] = []

    def add(key: ComparisonKey) -> None:
        if key not in keys:
            keys.append(key)

    for candidate_target in range(1, target_count):
        for cell_order in range(len(cells)):
            add((0, cell_order, candidate_target, cell_order))

    for target_order in range(target_count):
        for backend in spec.backends:
            for baseline_treatment, candidate_treatment, _label in ratio_specs_for_backend(spec, backend):
                add(
                    (
                        target_order,
                        _cell_order(spec, backend, baseline_treatment),
                        target_order,
                        _cell_order(spec, backend, candidate_treatment),
                    )
                )
        baseline_backend = spec.backends[0]
        for candidate_backend in spec.backends[1:]:
            for treatment in shared_backend_treatments(spec, baseline_backend, candidate_backend):
                add(
                    (
                        target_order,
                        _cell_order(spec, baseline_backend, treatment),
                        target_order,
                        _cell_order(spec, candidate_backend, treatment),
                    )
                )
    return tuple(ComparisonRequest(index, *key) for index, key in enumerate(keys))


def report_file_labels(files: Sequence[FileSpec]) -> dict[FileSpec, str]:
    """Return shortest unambiguous labels, including fact directories when needed."""

    labels = {file_spec: Path(file_spec.display_path).name for file_spec in files}
    by_basename: dict[str, list[FileSpec]] = {}
    for file_spec in files:
        by_basename.setdefault(labels[file_spec], []).append(file_spec)
    for group in by_basename.values():
        paths = tuple(dict.fromkeys(file_spec.display_path for file_spec in group))
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
        for file_spec in group:
            labels[file_spec] = path_labels[file_spec.display_path]
    by_label: dict[str, list[FileSpec]] = {}
    for file_spec in files:
        by_label.setdefault(labels[file_spec], []).append(file_spec)
    for label, group in by_label.items():
        if len(group) == 1:
            continue
        fact_labels = {
            file_spec: file_spec.fact_directory.name if file_spec.fact_directory is not None else "no-facts"
            for file_spec in group
        }
        if len(set(fact_labels.values())) != len(group):
            fact_labels = {
                file_spec: str(file_spec.fact_directory) if file_spec.fact_directory is not None else "no-facts"
                for file_spec in group
            }
        for file_spec in group:
            labels[file_spec] = f"{label}:{fact_labels[file_spec]}"
    return labels


def targets_table_data(targets: Sequence[TargetView]) -> ReportTableData:
    rows: list[tuple[str, ...]] = []
    for target in targets:
        git = target.target_git_sha[:12]
        if target.target_git_ref != "HEAD":
            git = f"{git} ({target.target_git_ref})"
        rows.append(
            _row(
                target.target_role,
                target.target_label,
                git,
                "yes" if target.target_is_dirty else "no",
                target.binary_sha256.removeprefix("sha256:")[:12],
                target.target_path,
            )
        )
    return ReportTableData("Targets", ("Role", "Label", "Git", "Dirty", "Binary", "Path"), tuple(rows))


def comparison_tables(
    analysis: ReportAnalysis,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
) -> tuple[ReportTableData, ...]:
    """Build target and backend per-file comparison sections."""

    tables: list[ReportTableData] = []
    if len(targets) > 1:
        tables.extend(_per_file_target_tables(analysis, targets, spec, file_labels, "wall_sec"))
        tables.extend(_per_file_target_tables(analysis, targets, spec, file_labels, "max_rss_bytes"))
    if len(spec.backends) > 1:
        tables.extend(_per_file_backend_tables(analysis, targets, spec, file_labels, "wall_sec"))
        tables.extend(_per_file_backend_tables(analysis, targets, spec, file_labels, "max_rss_bytes"))
    return tuple(tables)


def _per_file_target_tables(
    analysis: ReportAnalysis,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
    metric: MetricName,
) -> tuple[ReportTableData, ...]:
    baseline = targets[0]
    cells = benchmark_cells(spec)
    tables: list[ReportTableData] = []
    for target_order, target in enumerate(targets[1:], start=1):
        if metric == "max_rss_bytes" and not (
            _target_has_samples(analysis, metric, 0) or _target_has_samples(analysis, metric, target_order)
        ):
            continue
        rows: list[tuple[str, ...]] = []
        for file_order, file_spec in enumerate(spec.files):
            for cell_order, cell in enumerate(cells):
                comparison = analysis.comparison(metric, 0, cell_order, target_order, cell_order)
                ratio = analysis.file_ratio(comparison, file_order)
                rows.append(
                    _row(
                        file_labels[file_spec] if cell_order == 0 else "",
                        cell.backend,
                        cell.treatment,
                        format_ratio_summary(ratio.ratio),
                        format_percent_change(ratio.change),
                        _result_text(ratio.result_class, ratio.issue, rss=metric == "max_rss_bytes"),
                    )
                )
        if metric == "wall_sec":
            title = f"Per-file wall-time change vs {baseline.display_label}: {target.display_label}"
            headers = ("File", "Backend", "Treatment", "Time ratio", "Wall-time change", "Result")
            caption = TARGET_WALL_TIME_CAPTION
        else:
            title = f"Per-file peak RSS change vs {baseline.display_label}: {target.display_label}"
            headers = ("File", "Backend", "Treatment", "RSS ratio", "RSS change", "Result")
            caption = TARGET_PEAK_RSS_CAPTION
        tables.append(
            ReportTableData(
                title,
                headers,
                tuple(rows),
                caption,
                ("left", "left", "left", "right", "right", "left"),
            )
        )
    return tuple(tables)


def _per_file_backend_tables(
    analysis: ReportAnalysis,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
    metric: MetricName,
) -> tuple[ReportTableData, ...]:
    baseline_backend = spec.backends[0]
    baseline_name = backend_spec(baseline_backend).display_name
    tables: list[ReportTableData] = []
    for target_order, target in enumerate(targets):
        if metric == "max_rss_bytes" and not _target_has_samples(analysis, metric, target_order):
            continue
        rows: list[tuple[str, ...]] = []
        for file_order, file_spec in enumerate(spec.files):
            first = True
            for candidate_backend in spec.backends[1:]:
                for treatment in shared_backend_treatments(spec, baseline_backend, candidate_backend):
                    baseline_cell = _cell_order(spec, baseline_backend, treatment)
                    candidate_cell = _cell_order(spec, candidate_backend, treatment)
                    comparison = analysis.comparison(metric, target_order, baseline_cell, target_order, candidate_cell)
                    ratio = analysis.file_ratio(comparison, file_order)
                    rows.append(
                        _row(
                            file_labels[file_spec] if first else "",
                            candidate_backend,
                            treatment,
                            format_ratio_summary(ratio.ratio),
                            format_percent_change(ratio.change),
                            _result_text(ratio.result_class, ratio.issue, rss=metric == "max_rss_bytes"),
                        )
                    )
                    first = False
        if metric == "wall_sec":
            title = f"Per-file backend wall-time change vs {baseline_name}: {target.display_label}"
            headers = ("File", "Backend", "Treatment", "Time ratio", "Wall-time change", "Result")
            caption = BACKEND_WALL_TIME_CAPTION
        else:
            title = f"Per-file backend peak RSS change vs {baseline_name}: {target.display_label}"
            headers = ("File", "Backend", "Treatment", "RSS ratio", "RSS change", "Result")
            caption = BACKEND_PEAK_RSS_CAPTION
        tables.append(
            ReportTableData(
                title,
                headers,
                tuple(rows),
                caption,
                ("left", "left", "left", "right", "right", "left"),
            )
        )
    return tuple(tables)


def diagnostic_tables(
    analysis: ReportAnalysis,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
) -> tuple[ReportTableData, ...]:
    """Build within-target treatment ratios and per-file estimate tables."""

    tables: list[ReportTableData] = []
    for target_order, target in enumerate(targets):
        overhead = _overhead_ratios_table(analysis, target_order, target, spec, file_labels)
        if overhead is not None:
            tables.append(overhead)
        tables.append(_target_metric_table(analysis, target_order, target, spec, file_labels, "wall_sec"))
        if any(
            analysis.cell("max_rss_bytes", target_order, file_order, cell_order).has_samples
            for file_order in range(len(spec.files))
            for cell_order in range(len(benchmark_cells(spec)))
        ):
            tables.append(_target_metric_table(analysis, target_order, target, spec, file_labels, "max_rss_bytes"))
    return tuple(tables)


def _overhead_ratios_table(
    analysis: ReportAnalysis,
    target_order: int,
    target: ResolvedTarget,
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
) -> ReportTableData | None:
    ratios = {backend: ratio_specs_for_backend(spec, backend) for backend in spec.backends}
    if not any(ratios.values()):
        return None
    headers = ["File"]
    for backend in spec.backends:
        for _, _, ratio_name in ratios[backend]:
            headers.append(_backend_metric_label(spec, backend, ratio_name))
    rows: list[tuple[str, ...]] = []
    for file_order, file_spec in enumerate(spec.files):
        values = [file_labels[file_spec]]
        for backend in spec.backends:
            for baseline_treatment, candidate_treatment, _ in ratios[backend]:
                comparison = analysis.comparison(
                    "wall_sec",
                    target_order,
                    _cell_order(spec, backend, baseline_treatment),
                    target_order,
                    _cell_order(spec, backend, candidate_treatment),
                )
                values.append(format_ratio_summary(analysis.file_ratio(comparison, file_order).ratio))
        rows.append(tuple(values))
    return ReportTableData(
        f"{target.display_label}: overhead ratios",
        tuple(headers),
        tuple(rows),
        "Within-target treatment ratios. These are not target-vs-baseline wall-time change.",
        tuple("left" if index == 0 else "right" for index in range(len(headers))),
    )


def _target_metric_table(
    analysis: ReportAnalysis,
    target_order: int,
    target: ResolvedTarget,
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
    metric: MetricName,
) -> ReportTableData:
    cells = benchmark_cells(spec)
    headers = ["File", *(_cell_label(spec, cell.backend, cell.treatment) for cell in cells)]
    rows_with_issue: list[tuple[list[str], str]] = []
    for file_order, file_spec in enumerate(spec.files):
        values = [file_labels[file_spec]]
        issues: list[str] = []
        for cell_order, cell in enumerate(cells):
            summary = analysis.cell(metric, target_order, file_order, cell_order)
            values.append(_format_cell_summary(summary, rss=metric == "max_rss_bytes"))
            if summary.issue is not None:
                issues.append(f"{_cell_label(spec, cell.backend, cell.treatment)}: {summary.issue}")
        rows_with_issue.append((values, "; ".join(issues)))
    if any(issue for _, issue in rows_with_issue):
        headers.append("Issue")
    rows = tuple(tuple([*values, issue] if headers[-1] == "Issue" else values) for values, issue in rows_with_issue)
    if metric == "wall_sec":
        title = f"{target.display_label}: per-file wall time"
        caption = "Within-target wall-time estimates. These are not target-vs-baseline ratios."
    else:
        title = f"{target.display_label}: per-file peak RSS"
        caption = "Within-target peak resident set size estimates. These are separate from wall-time ratios."
    return ReportTableData(
        title,
        tuple(headers),
        rows,
        caption,
        tuple("left" if index == 0 or header == "Issue" else "right" for index, header in enumerate(headers)),
    )


def summary_tables(
    analysis: ReportAnalysis,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
) -> tuple[ReportTableData, ...]:
    """Build the final decision-oriented benchmark summary tables."""

    tables = list(_backend_summary_tables(analysis, targets, spec, file_labels))
    if len(targets) == 1:
        tables.append(_single_target_summary(analysis, targets[0], spec, file_labels))
    else:
        tables.extend(_multi_target_summaries(analysis, targets, spec, file_labels))
    return tuple(tables)


def _single_target_summary(
    analysis: ReportAnalysis,
    target: ResolvedTarget,
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
) -> ReportTableData:
    rows: list[tuple[str, ...]] = []
    for backend in spec.backends:
        has_off_proofs = backend_has_treatment(spec, backend, "off") and backend_has_treatment(spec, backend, "proofs")
        has_term_proofs = backend_has_treatment(spec, backend, "term") and backend_has_treatment(
            spec, backend, "proofs"
        )
        if has_off_proofs:
            rows.extend(
                _within_target_summary_rows(
                    analysis,
                    spec,
                    file_labels,
                    backend,
                    "off",
                    "proofs",
                    _backend_metric_label(spec, backend, "wall proofs/off"),
                    "wall_sec",
                    include_geomean=True,
                    proof_gate=True,
                )
            )
            rows.extend(
                _within_target_summary_rows(
                    analysis,
                    spec,
                    file_labels,
                    backend,
                    "off",
                    "proofs",
                    _backend_metric_label(spec, backend, "peak RSS proofs/off"),
                    "max_rss_bytes",
                    include_geomean=False,
                )
            )
        elif has_term_proofs:
            rows.extend(
                _within_target_summary_rows(
                    analysis,
                    spec,
                    file_labels,
                    backend,
                    "term",
                    "proofs",
                    _backend_metric_label(spec, backend, "wall proofs/term"),
                    "wall_sec",
                    include_geomean=True,
                )
            )
        else:
            rows.append(
                _row(
                    _backend_metric_label(spec, backend, "no proof baseline"),
                    "-",
                    "-",
                    "-",
                    "-",
                    "select off and proofs",
                )
            )
        if has_term_proofs:
            rows.extend(
                _within_target_summary_rows(
                    analysis,
                    spec,
                    file_labels,
                    backend,
                    "term",
                    "proofs",
                    _backend_metric_label(spec, backend, "peak RSS proofs/term"),
                    "max_rss_bytes",
                    include_geomean=False,
                )
            )
    return ReportTableData(
        f"{target.display_label}: proof overhead summary",
        ("Metric", "Ratio", "Change", "Worst file", "Worst ratio", "Result"),
        tuple(rows),
        PROOF_OVERHEAD_CAPTION,
        ("left", "right", "right", "left", "right", "left"),
    )


def _within_target_summary_rows(
    analysis: ReportAnalysis,
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
    backend: Backend,
    baseline_treatment: Treatment,
    candidate_treatment: Treatment,
    label: str,
    metric: MetricName,
    *,
    include_geomean: bool,
    proof_gate: bool = False,
) -> tuple[tuple[str, ...], ...]:
    comparison = analysis.comparison(
        metric,
        0,
        _cell_order(spec, backend, baseline_treatment),
        0,
        _cell_order(spec, backend, candidate_treatment),
    )
    worst_file_order, worst = comparison.worst_file_order, comparison.worst
    result = (
        _proof_gate_result_text(comparison)
        if proof_gate
        else _result_text(comparison.suite_result_class, comparison.suite_issue, rss=metric == "max_rss_bytes")
    )
    rows = [
        _row(
            label,
            format_ratio_summary(comparison.suite),
            format_percent_change(comparison.suite_change),
            _format_file_order(worst_file_order, spec, file_labels),
            format_ratio_summary(worst),
            result,
        )
    ]
    if include_geomean:
        rows.append(
            _row(
                f"{label} geomean",
                format_ratio_summary(comparison.geometric_mean),
                format_percent_change(comparison.geometric_mean_change),
                "-",
                "-",
                "descriptive",
            )
        )
    return tuple(rows)


def _multi_target_summaries(
    analysis: ReportAnalysis,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
) -> tuple[ReportTableData, ReportTableData]:
    baseline = targets[0]
    wall_rows: list[tuple[str, ...]] = []
    rss_rows: list[tuple[str, ...]] = []
    for target_order, target in enumerate(targets[1:], start=1):
        for cell_order, cell in enumerate(benchmark_cells(spec)):
            wall = analysis.comparison("wall_sec", 0, cell_order, target_order, cell_order)
            worst_file, worst = wall.worst_file_order, wall.worst
            wall_rows.append(
                _row(
                    target.display_label,
                    cell.backend,
                    cell.treatment,
                    format_percent_change(wall.suite_change),
                    format_ratio_summary(wall.geometric_mean),
                    _format_file_order(worst_file, spec, file_labels),
                    format_ratio_summary(worst),
                    _result_text(wall.suite_result_class, wall.suite_issue),
                )
            )
            rss = analysis.comparison("max_rss_bytes", 0, cell_order, target_order, cell_order)
            rss_worst_file, rss_worst = rss.worst_file_order, rss.worst
            rss_rows.append(
                _row(
                    target.display_label,
                    cell.backend,
                    cell.treatment,
                    format_percent_change(rss.suite_change),
                    format_ratio_summary(rss.geometric_mean),
                    _format_file_order(rss_worst_file, spec, file_labels),
                    format_ratio_summary(rss_worst),
                    _result_text(rss.suite_result_class, rss.suite_issue, rss=True),
                )
            )
    return (
        ReportTableData(
            f"Wall-time summary vs {baseline.display_label}",
            (
                "Target",
                "Backend",
                "Treatment",
                "Wall-time change",
                "Geomean",
                "Worst file",
                "Worst ratio",
                "Result",
            ),
            tuple(wall_rows),
            TARGET_WALL_TIME_CAPTION,
            ("left", "left", "left", "right", "right", "left", "right", "left"),
        ),
        ReportTableData(
            f"Peak RSS summary vs {baseline.display_label}",
            ("Target", "Backend", "Treatment", "RSS change", "Geomean", "Worst file", "Worst ratio", "Result"),
            tuple(rss_rows),
            TARGET_PEAK_RSS_CAPTION,
            ("left", "left", "left", "right", "right", "left", "right", "left"),
        ),
    )


def _backend_summary_tables(
    analysis: ReportAnalysis,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
) -> tuple[ReportTableData, ...]:
    if len(spec.backends) <= 1:
        return ()
    metrics: tuple[tuple[MetricName, MetricSpec], ...] = (
        (
            "wall_sec",
            MetricSpec(
                "wall time",
                BACKEND_WALL_TIME_CAPTION,
                "Faster files",
                format_seconds_value,
                format_percent_change,
                _wall_result_text,
            ),
        ),
        (
            "max_rss_bytes",
            MetricSpec(
                "peak RSS",
                BACKEND_PEAK_RSS_CAPTION,
                "Lower-RSS files",
                format_bytes,
                format_percent_change,
                _rss_result_text,
                True,
            ),
        ),
    )
    return tuple(
        _backend_summary_table(analysis, targets, spec, file_labels, metric, policy)
        for metric, policy in metrics
        if not policy.omit_without_samples or _has_samples(analysis, metric)
    )


def _backend_summary_table(
    analysis: ReportAnalysis,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
    metric: MetricName,
    policy: MetricSpec,
) -> ReportTableData:
    baseline_backend = spec.backends[0]
    baseline_name = backend_spec(baseline_backend).display_name
    candidate_name = backend_spec(spec.backends[1]).display_name if len(spec.backends) == 2 else "Candidate"
    title = (
        f"{candidate_name} vs {baseline_name} {policy.title}"
        if len(spec.backends) == 2
        else f"Backend {policy.title} summary vs {baseline_name}"
    )
    ratio_heading = f"{candidate_name}/{baseline_name}"
    baseline_total_heading = f"{baseline_name} total"
    candidate_total_heading = f"{candidate_name} total"
    headers = ["Target"] if len(targets) > 1 else []
    headers.extend(
        (
            "Backend",
            "Mode",
            baseline_total_heading,
            candidate_total_heading,
            ratio_heading,
            "Change",
            "File geomean",
            policy.file_count_heading,
            "Best file",
            "Best ratio",
            "Best result",
        )
    )
    rows: list[tuple[str, ...]] = []
    for target_order, target in enumerate(targets):
        for candidate_backend in spec.backends[1:]:
            for treatment in shared_backend_treatments(spec, baseline_backend, candidate_backend):
                baseline_cell = _cell_order(spec, baseline_backend, treatment)
                candidate_cell = _cell_order(spec, candidate_backend, treatment)
                comparison = analysis.comparison(metric, target_order, baseline_cell, target_order, candidate_cell)
                best_file, best = comparison.best_file_order, comparison.best
                values: list[object] = [target.display_label] if len(targets) > 1 else []
                values.extend(
                    (
                        candidate_backend,
                        treatment,
                        policy.format_total(comparison.baseline_total),
                        policy.format_total(comparison.candidate_total),
                        format_ratio_summary(comparison.suite),
                        policy.format_change(comparison.suite_change),
                        format_ratio_summary(comparison.geometric_mean),
                        _format_better_count(comparison),
                        _format_file_order(best_file, spec, file_labels),
                        format_ratio_summary(best),
                        policy.format_result(comparison.best_result_class, comparison.best_issue),
                    )
                )
                rows.append(_row(*values))
    right = {
        baseline_total_heading,
        candidate_total_heading,
        ratio_heading,
        "Change",
        "File geomean",
        policy.file_count_heading,
        "Best ratio",
    }
    return ReportTableData(
        title,
        tuple(headers),
        tuple(rows),
        policy.caption,
        tuple("right" if header in right else "left" for header in headers),
    )


def ratio_specs(treatments: Sequence[Treatment]) -> tuple[tuple[Treatment, Treatment, str], ...]:
    specs: list[tuple[Treatment, Treatment, str]] = []
    if "off" in treatments and "term" in treatments:
        specs.append(("off", "term", "term/off"))
    if "off" in treatments and "proofs" in treatments:
        specs.append(("off", "proofs", "proofs/off"))
    if "term" in treatments and "proofs" in treatments:
        specs.append(("term", "proofs", "proofs/term"))
    return tuple(specs)


def ratio_specs_for_backend(spec: BenchmarkSpec, backend: Backend) -> tuple[tuple[Treatment, Treatment, str], ...]:
    return tuple(
        ratio
        for ratio in ratio_specs(spec.treatments)
        if backend_has_treatment(spec, backend, ratio[0]) and backend_has_treatment(spec, backend, ratio[1])
    )


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


def format_ratio_summary(summary: RatioSummary) -> str:
    return format_estimate_or_interval(summary.point, summary.ci_low, summary.ci_high, "x", 3)


def format_percent_change(summary: RatioSummary) -> str:
    point = None if summary.point is None else summary.point * 100.0
    low = None if summary.ci_low is None else summary.ci_low * 100.0
    high = None if summary.ci_high is None else summary.ci_high * 100.0
    return format_estimate_or_interval(point, low, high, "%", 1)


def format_seconds_value(value: float | None) -> str:
    return "-" if value is None else f"{value:.4f}s"


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
    return f"{int(amount)} B" if unit == "B" else f"{amount:.1f} {unit}"


def _format_cell_summary(summary: CellEstimateView, *, rss: bool) -> str:
    if summary.mean is None:
        return "-"
    if rss:
        point = format_bytes(summary.mean)
        if summary.ci_low is None or summary.ci_high is None:
            return point
        return f"[{format_bytes(summary.ci_low)}, {format_bytes(summary.ci_high)}]"
    return format_estimate_or_interval(summary.mean, summary.ci_low, summary.ci_high, "s", 4)


def _result_text(result_class: ResultClass, issue: str | None, *, rss: bool = False) -> str:
    """Translate a SQL-owned statistical classification into report wording."""

    if result_class == "invalid":
        return f"invalid: {issue or 'unavailable'}"
    if result_class == "point_only":
        return "point only"
    if result_class == "lower":
        return "less" if rss else "faster"
    if result_class == "higher":
        return "more" if rss else "slower"
    if result_class == "unclear":
        return "unclear"
    raise ValueError(f"unexpected ratio result class: {result_class}")


def _wall_result_text(result_class: ResultClass, issue: str | None) -> str:
    return _result_text(result_class, issue)


def _rss_result_text(result_class: ResultClass, issue: str | None) -> str:
    return _result_text(result_class, issue, rss=True)


def _proof_gate_result_text(summary: ComparisonRollupView) -> str:
    if summary.suite_result_class == "invalid":
        return f"invalid: {summary.suite_issue or 'unavailable'}"
    if summary.suite_result_class == "point_only":
        return "point only"
    return "<2x established" if summary.suite_ci_entirely_below_two else "<2x not established"


def _format_better_count(comparison: ComparisonRollupView) -> str:
    if comparison.comparable_file_count == 0:
        return "-"
    return f"{comparison.better_file_count}/{comparison.comparable_file_count}"


def _format_file_order(file_order: int | None, spec: BenchmarkSpec, file_labels: dict[FileSpec, str]) -> str:
    return "-" if file_order is None else file_labels[spec.files[file_order]]


def _cell_order(spec: BenchmarkSpec, backend: Backend, treatment: Treatment) -> int:
    for index, cell in enumerate(benchmark_cells(spec)):
        if cell.backend == backend and cell.treatment == treatment:
            return index
    raise ValueError(f"benchmark cell not selected: {backend}/{treatment}")


def _cell_label(spec: BenchmarkSpec, backend: Backend, treatment: Treatment) -> str:
    return treatment if len(spec.backends) == 1 else f"{backend}/{treatment}"


def _backend_metric_label(spec: BenchmarkSpec, backend: Backend, label: str) -> str:
    return label if len(spec.backends) == 1 else f"{backend} {label}"


def _has_samples(analysis: ReportAnalysis, metric: MetricName) -> bool:
    return any(key[0] == metric and value.has_samples for key, value in analysis.cells.items())


def _target_has_samples(analysis: ReportAnalysis, metric: MetricName, target_order: int) -> bool:
    return any(
        key[0] == metric and key[1] == target_order and value.has_samples for key, value in analysis.cells.items()
    )


def _row(*values: object) -> tuple[str, ...]:
    return tuple(str(value) for value in values)
