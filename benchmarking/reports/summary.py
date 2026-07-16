"""Build one complete renderer-neutral benchmark report catalog.

This module chooses comparison coordinates, report sections, columns, captions,
and human wording. DuckDB relations own statistics, result classifications,
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
from .catalog import (
    CellTone,
    ReportCatalog,
    ReportCell,
    ReportColumn,
    ReportOptions,
    ReportRow,
    ReportScope,
    ReportSection,
    ReportTable,
    TableAlignment,
    report_id,
    text_cell,
)
from .database import ReportDatabase
from .results import (
    CellEstimateView,
    ComparisonRequest,
    ComparisonRollupView,
    FileRatioView,
    MetricName,
    RatioSummary,
    ResultClass,
    TargetView,
)
from .timing import build_timing_sections

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
    omit_without_samples: bool = False


@dataclass(frozen=True)
class ReportAnalysis:
    """Output-facing DuckDB rows indexed by stable selector coordinates."""

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


def build_report_catalog(
    database: ReportDatabase,
    scope: ReportScope,
    options: ReportOptions | None = None,
) -> ReportCatalog:
    """Install one explicit scope, query its views, and assemble the shared catalog."""

    options = ReportOptions() if options is None else options
    selected_targets = scope.targets
    spec = scope.spec
    t_critical = None if spec.rounds < 2 else float(stats.t.ppf(0.975, spec.rounds - 1))
    requests = _comparison_requests(selected_targets, spec)
    database.install_scope(selected_targets, spec, t_critical, requests)
    view_data = database.report_view_data(include_timing=options.include_timing)
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
            ): comparison_order
            for comparison_order, request in enumerate(requests)
        },
    )
    file_labels = report_file_labels(spec.files)
    comparisons = comparison_tables(analysis, selected_targets, spec, file_labels)
    diagnostics = diagnostic_tables(analysis, selected_targets, spec, file_labels)
    summary = summary_tables(analysis, selected_targets, spec, file_labels)
    sections: list[ReportSection] = [
        ReportSection("targets", None, (targets_table_data(view_data.targets),)),
    ]
    if comparisons:
        sections.append(ReportSection("comparisons", "Comparisons", comparisons))
    if diagnostics:
        sections.append(ReportSection("diagnostics", "Target Diagnostics", diagnostics))
    if options.include_timing:
        sections.extend(
            build_timing_sections(
                view_data.compact_timings,
                view_data.ruleset_timings,
                selected_targets,
                spec,
                detailed=options.detailed_timing,
                file_labels=tuple(file_labels[file] for file in spec.files),
            )
        )
    sections.append(ReportSection("summary", "Benchmark Summary", summary))
    return ReportCatalog(
        report_path=database.display_path,
        rounds=spec.rounds,
        command_argv=options.command_argv,
        sections=tuple(sections),
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
    return tuple(ComparisonRequest(*key) for key in keys)


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


def targets_table_data(targets: Sequence[TargetView]) -> ReportTable:
    rows: list[ReportRow] = []
    for target in targets:
        git = target.target_git_sha[:12]
        if target.target_git_ref != "HEAD":
            git = f"{git} ({target.target_git_ref})"
        rows.append(
            _row(
                report_id("target", target.binary_sha256),
                target.target_role,
                target.target_label,
                target.target_source,
                text_cell(target.target_git_sha, git),
                target.target_git_ref,
                text_cell(target.target_is_dirty, "yes" if target.target_is_dirty else "no"),
                text_cell(target.binary_sha256, target.binary_sha256.removeprefix("sha256:")[:12]),
                target.target_path,
            )
        )
    return ReportTable(
        report_id("table", "targets"),
        "Targets",
        (
            ReportColumn("role", "Role"),
            ReportColumn("label", "Label"),
            ReportColumn("source", "Source", visible=False),
            ReportColumn("git", "Git"),
            ReportColumn("git_ref", "Git ref", visible=False),
            ReportColumn("dirty", "Dirty"),
            ReportColumn("binary", "Binary"),
            ReportColumn("path", "Path"),
        ),
        tuple(rows),
        layout="target-tree",
    )


def comparison_tables(
    analysis: ReportAnalysis,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
) -> tuple[ReportTable, ...]:
    """Build target and backend per-file comparison sections."""

    tables: list[ReportTable] = []
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
) -> tuple[ReportTable, ...]:
    baseline = targets[0]
    cells = benchmark_cells(spec)
    tables: list[ReportTable] = []
    for target_order, target in enumerate(targets[1:], start=1):
        if metric == "max_rss_bytes" and not (
            _target_has_samples(analysis, metric, 0) or _target_has_samples(analysis, metric, target_order)
        ):
            continue
        rows: list[ReportRow] = []
        for file_order, file_spec in enumerate(spec.files):
            for cell_order, cell in enumerate(cells):
                comparison = analysis.comparison(metric, 0, cell_order, target_order, cell_order)
                ratio = analysis.file_ratio(comparison, file_order)
                rows.append(
                    _row(
                        report_id(
                            "comparison",
                            "target",
                            metric,
                            target.binary_sha256,
                            file_spec.sha256,
                            file_spec.fact_directory_sha256,
                            cell.backend,
                            cell.treatment,
                        ),
                        file_labels[file_spec],
                        cell.backend,
                        cell.treatment,
                        _ratio_cell(ratio.ratio),
                        _percent_cell(ratio.change),
                        _result_cell(ratio.result_class, ratio.issue, rss=metric == "max_rss_bytes"),
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
            _table(
                report_id("table", "comparison", "target", metric, baseline.binary_sha256, target.binary_sha256),
                title,
                ("file", "backend", "treatment", "ratio", "change", "result"),
                headers,
                tuple(rows),
                caption,
                ("left", "left", "left", "right", "right", "left"),
                collapse_repeats=frozenset({"file"}),
            )
        )
    return tuple(tables)


def _per_file_backend_tables(
    analysis: ReportAnalysis,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
    metric: MetricName,
) -> tuple[ReportTable, ...]:
    baseline_backend = spec.backends[0]
    baseline_name = backend_spec(baseline_backend).display_name
    tables: list[ReportTable] = []
    for target_order, target in enumerate(targets):
        if metric == "max_rss_bytes" and not _target_has_samples(analysis, metric, target_order):
            continue
        rows: list[ReportRow] = []
        for file_order, file_spec in enumerate(spec.files):
            for candidate_backend in spec.backends[1:]:
                for treatment in shared_backend_treatments(spec, baseline_backend, candidate_backend):
                    baseline_cell = _cell_order(spec, baseline_backend, treatment)
                    candidate_cell = _cell_order(spec, candidate_backend, treatment)
                    comparison = analysis.comparison(metric, target_order, baseline_cell, target_order, candidate_cell)
                    ratio = analysis.file_ratio(comparison, file_order)
                    rows.append(
                        _row(
                            report_id(
                                "comparison",
                                "backend",
                                metric,
                                target.binary_sha256,
                                file_spec.sha256,
                                file_spec.fact_directory_sha256,
                                candidate_backend,
                                treatment,
                            ),
                            file_labels[file_spec],
                            candidate_backend,
                            treatment,
                            _ratio_cell(ratio.ratio),
                            _percent_cell(ratio.change),
                            _result_cell(ratio.result_class, ratio.issue, rss=metric == "max_rss_bytes"),
                        )
                    )
        if metric == "wall_sec":
            title = f"Per-file backend wall-time change vs {baseline_name}: {target.display_label}"
            headers = ("File", "Backend", "Treatment", "Time ratio", "Wall-time change", "Result")
            caption = BACKEND_WALL_TIME_CAPTION
        else:
            title = f"Per-file backend peak RSS change vs {baseline_name}: {target.display_label}"
            headers = ("File", "Backend", "Treatment", "RSS ratio", "RSS change", "Result")
            caption = BACKEND_PEAK_RSS_CAPTION
        tables.append(
            _table(
                report_id("table", "comparison", "backend", metric, target.binary_sha256),
                title,
                ("file", "backend", "treatment", "ratio", "change", "result"),
                headers,
                tuple(rows),
                caption,
                ("left", "left", "left", "right", "right", "left"),
                collapse_repeats=frozenset({"file"}),
            )
        )
    return tuple(tables)


def diagnostic_tables(
    analysis: ReportAnalysis,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
) -> tuple[ReportTable, ...]:
    """Build within-target treatment ratios and per-file estimate tables."""

    tables: list[ReportTable] = []
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
) -> ReportTable | None:
    ratios = {backend: ratio_specs_for_backend(spec, backend) for backend in spec.backends}
    if not any(ratios.values()):
        return None
    headers = ["File"]
    column_ids = ["file"]
    for backend in spec.backends:
        for baseline_treatment, candidate_treatment, ratio_name in ratios[backend]:
            headers.append(_backend_metric_label(spec, backend, ratio_name))
            column_ids.append(f"ratio:{backend}:{baseline_treatment}:{candidate_treatment}")
    rows: list[ReportRow] = []
    for file_order, file_spec in enumerate(spec.files):
        values: list[ReportCell] = [text_cell(file_labels[file_spec])]
        for backend in spec.backends:
            for baseline_treatment, candidate_treatment, _ in ratios[backend]:
                comparison = analysis.comparison(
                    "wall_sec",
                    target_order,
                    _cell_order(spec, backend, baseline_treatment),
                    target_order,
                    _cell_order(spec, backend, candidate_treatment),
                )
                values.append(_ratio_cell(analysis.file_ratio(comparison, file_order).ratio))
        rows.append(
            ReportRow(
                report_id(
                    "overhead",
                    target.binary_sha256,
                    file_spec.sha256,
                    file_spec.fact_directory_sha256,
                ),
                tuple(values),
            )
        )
    return _table(
        report_id("table", "diagnostic", "overhead", target.binary_sha256),
        f"{target.display_label}: overhead ratios",
        tuple(column_ids),
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
) -> ReportTable:
    cells = benchmark_cells(spec)
    headers = ["File", *(_cell_label(spec, cell.backend, cell.treatment) for cell in cells)]
    column_ids = ["file", *(f"cell:{cell.backend}:{cell.treatment}" for cell in cells)]
    rows_with_issue: list[tuple[FileSpec, list[ReportCell], str]] = []
    for file_order, file_spec in enumerate(spec.files):
        values = [text_cell(file_labels[file_spec])]
        issues: list[str] = []
        for cell_order, cell in enumerate(cells):
            summary = analysis.cell(metric, target_order, file_order, cell_order)
            values.append(_cell_summary_cell(summary, rss=metric == "max_rss_bytes"))
            if summary.issue is not None:
                issues.append(f"{_cell_label(spec, cell.backend, cell.treatment)}: {summary.issue}")
        rows_with_issue.append((file_spec, values, "; ".join(issues)))
    has_issue = any(issue for _, _, issue in rows_with_issue)
    if has_issue:
        headers.append("Issue")
        column_ids.append("issue")
    rows = tuple(
        ReportRow(
            report_id("estimate", metric, target.binary_sha256, file_spec.sha256, file_spec.fact_directory_sha256),
            tuple([*values, text_cell(issue)] if has_issue else values),
        )
        for file_spec, values, issue in rows_with_issue
    )
    if metric == "wall_sec":
        title = f"{target.display_label}: per-file wall time"
        caption = "Within-target wall-time estimates. These are not target-vs-baseline ratios."
    else:
        title = f"{target.display_label}: per-file peak RSS"
        caption = "Within-target peak resident set size estimates. These are separate from wall-time ratios."
    return _table(
        report_id("table", "diagnostic", "estimate", metric, target.binary_sha256),
        title,
        tuple(column_ids),
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
) -> tuple[ReportTable, ...]:
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
) -> ReportTable:
    rows: list[ReportRow] = []
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
                    report_id("summary", "proof-overhead", backend, "unavailable"),
                    _backend_metric_label(spec, backend, "no proof baseline"),
                    text_cell(None, "-"),
                    text_cell(None, "-"),
                    text_cell(None, "-"),
                    text_cell(None, "-"),
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
    return _table(
        report_id("table", "summary", "proof-overhead", target.binary_sha256),
        f"{target.display_label}: proof overhead summary",
        ("metric", "ratio", "change", "worst_file", "worst_ratio", "result"),
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
) -> tuple[ReportRow, ...]:
    comparison = analysis.comparison(
        metric,
        0,
        _cell_order(spec, backend, baseline_treatment),
        0,
        _cell_order(spec, backend, candidate_treatment),
    )
    worst_file_order, worst = comparison.worst_file_order, comparison.worst
    result = (
        _proof_gate_cell(comparison)
        if proof_gate
        else _result_cell(comparison.suite_result_class, comparison.suite_issue, rss=metric == "max_rss_bytes")
    )
    rows = [
        _row(
            report_id("summary", backend, baseline_treatment, candidate_treatment, metric, "suite"),
            label,
            _ratio_cell(comparison.suite),
            _percent_cell(comparison.suite_change),
            _file_order_cell(worst_file_order, spec, file_labels),
            _ratio_cell(worst),
            result,
        )
    ]
    if include_geomean:
        rows.append(
            _row(
                report_id("summary", backend, baseline_treatment, candidate_treatment, metric, "geomean"),
                f"{label} geomean",
                _ratio_cell(comparison.geometric_mean),
                _percent_cell(comparison.geometric_mean_change),
                text_cell(None, "-"),
                text_cell(None, "-"),
                text_cell("descriptive", tone="muted"),
            )
        )
    return tuple(rows)


def _multi_target_summaries(
    analysis: ReportAnalysis,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    file_labels: dict[FileSpec, str],
) -> tuple[ReportTable, ReportTable]:
    baseline = targets[0]
    wall_rows: list[ReportRow] = []
    rss_rows: list[ReportRow] = []
    for target_order, target in enumerate(targets[1:], start=1):
        for cell_order, cell in enumerate(benchmark_cells(spec)):
            wall = analysis.comparison("wall_sec", 0, cell_order, target_order, cell_order)
            worst_file, worst = wall.worst_file_order, wall.worst
            wall_rows.append(
                _row(
                    report_id("summary", "target", "wall_sec", target.binary_sha256, cell.backend, cell.treatment),
                    target.display_label,
                    cell.backend,
                    cell.treatment,
                    _percent_cell(wall.suite_change),
                    _ratio_cell(wall.geometric_mean),
                    _file_order_cell(worst_file, spec, file_labels),
                    _ratio_cell(worst),
                    _result_cell(wall.suite_result_class, wall.suite_issue),
                )
            )
            rss = analysis.comparison("max_rss_bytes", 0, cell_order, target_order, cell_order)
            rss_worst_file, rss_worst = rss.worst_file_order, rss.worst
            rss_rows.append(
                _row(
                    report_id("summary", "target", "max_rss_bytes", target.binary_sha256, cell.backend, cell.treatment),
                    target.display_label,
                    cell.backend,
                    cell.treatment,
                    _percent_cell(rss.suite_change),
                    _ratio_cell(rss.geometric_mean),
                    _file_order_cell(rss_worst_file, spec, file_labels),
                    _ratio_cell(rss_worst),
                    _result_cell(rss.suite_result_class, rss.suite_issue, rss=True),
                )
            )
    return (
        _table(
            report_id("table", "summary", "target", "wall_sec", baseline.binary_sha256),
            f"Wall-time summary vs {baseline.display_label}",
            ("target", "backend", "treatment", "change", "geomean", "worst_file", "worst_ratio", "result"),
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
        _table(
            report_id("table", "summary", "target", "max_rss_bytes", baseline.binary_sha256),
            f"Peak RSS summary vs {baseline.display_label}",
            ("target", "backend", "treatment", "change", "geomean", "worst_file", "worst_ratio", "result"),
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
) -> tuple[ReportTable, ...]:
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
            ),
        ),
        (
            "max_rss_bytes",
            MetricSpec(
                "peak RSS",
                BACKEND_PEAK_RSS_CAPTION,
                "Lower-RSS files",
                format_bytes,
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
) -> ReportTable:
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
    rows: list[ReportRow] = []
    for target_order, target in enumerate(targets):
        for candidate_backend in spec.backends[1:]:
            for treatment in shared_backend_treatments(spec, baseline_backend, candidate_backend):
                baseline_cell = _cell_order(spec, baseline_backend, treatment)
                candidate_cell = _cell_order(spec, candidate_backend, treatment)
                comparison = analysis.comparison(metric, target_order, baseline_cell, target_order, candidate_cell)
                best_file, best = comparison.best_file_order, comparison.best
                values: list[ReportCell | str] = [target.display_label] if len(targets) > 1 else []
                values.extend(
                    (
                        candidate_backend,
                        treatment,
                        text_cell(comparison.baseline_total, policy.format_total(comparison.baseline_total)),
                        text_cell(comparison.candidate_total, policy.format_total(comparison.candidate_total)),
                        _ratio_cell(comparison.suite),
                        _percent_cell(comparison.suite_change),
                        _ratio_cell(comparison.geometric_mean),
                        _better_count_cell(comparison),
                        _file_order_cell(best_file, spec, file_labels),
                        _ratio_cell(best),
                        _result_cell(
                            comparison.best_result_class,
                            comparison.best_issue,
                            rss=metric == "max_rss_bytes",
                        ),
                    )
                )
                rows.append(
                    _row(
                        report_id(
                            "summary",
                            "backend",
                            metric,
                            target.binary_sha256,
                            candidate_backend,
                            treatment,
                        ),
                        *values,
                    )
                )
    right = {
        baseline_total_heading,
        candidate_total_heading,
        ratio_heading,
        "Change",
        "File geomean",
        policy.file_count_heading,
        "Best ratio",
    }
    column_ids = ["target"] if len(targets) > 1 else []
    column_ids.extend(
        (
            "backend",
            "mode",
            "baseline_total",
            "candidate_total",
            "ratio",
            "change",
            "geomean",
            "better_files",
            "best_file",
            "best_ratio",
            "result",
        )
    )
    return _table(
        report_id("table", "summary", "backend", metric, baseline_backend),
        title,
        tuple(column_ids),
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


def _cell_summary_cell(summary: CellEstimateView, *, rss: bool) -> ReportCell:
    return text_cell(summary.mean, _format_cell_summary(summary, rss=rss))


def _ratio_cell(summary: RatioSummary) -> ReportCell:
    return text_cell(summary.point, format_ratio_summary(summary))


def _percent_cell(summary: RatioSummary) -> ReportCell:
    return text_cell(summary.point, format_percent_change(summary))


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


def _result_cell(result_class: ResultClass, issue: str | None, *, rss: bool = False) -> ReportCell:
    tones: dict[ResultClass, CellTone] = {
        "available": "default",
        "higher": "negative",
        "interval": "default",
        "invalid": "error",
        "lower": "positive",
        "point_only": "muted",
        "unclear": "warning",
    }
    return text_cell(result_class, _result_text(result_class, issue, rss=rss), tone=tones[result_class])


def _proof_gate_result_text(summary: ComparisonRollupView) -> str:
    if summary.suite_result_class == "invalid":
        return f"invalid: {summary.suite_issue or 'unavailable'}"
    if summary.suite_result_class == "point_only":
        return "point only"
    return "<2x established" if summary.suite_ci_entirely_below_two else "<2x not established"


def _proof_gate_cell(summary: ComparisonRollupView) -> ReportCell:
    text = _proof_gate_result_text(summary)
    if summary.suite_result_class == "invalid":
        tone: CellTone = "error"
    elif summary.suite_result_class == "point_only":
        tone = "muted"
    else:
        tone = "positive" if summary.suite_ci_entirely_below_two else "negative"
    return text_cell(summary.suite_result_class, text, tone=tone)


def _format_better_count(comparison: ComparisonRollupView) -> str:
    if comparison.comparable_file_count == 0:
        return "-"
    return f"{comparison.better_file_count}/{comparison.comparable_file_count}"


def _better_count_cell(comparison: ComparisonRollupView) -> ReportCell:
    raw = None if comparison.comparable_file_count == 0 else comparison.better_file_count
    return text_cell(raw, _format_better_count(comparison))


def _format_file_order(file_order: int | None, spec: BenchmarkSpec, file_labels: dict[FileSpec, str]) -> str:
    return "-" if file_order is None else file_labels[spec.files[file_order]]


def _file_order_cell(file_order: int | None, spec: BenchmarkSpec, file_labels: dict[FileSpec, str]) -> ReportCell:
    return text_cell(file_order, _format_file_order(file_order, spec, file_labels))


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


def _row(
    row_id: str,
    *values: ReportCell | str | int | float | bool | None,
) -> ReportRow:
    return ReportRow(row_id, tuple(value if isinstance(value, ReportCell) else text_cell(value) for value in values))


def _table(
    table_id: str,
    title: str,
    column_ids: Sequence[str],
    headers: Sequence[str],
    rows: tuple[ReportRow, ...],
    caption: str | None = None,
    alignments: Sequence[TableAlignment] | None = None,
    *,
    collapse_repeats: frozenset[str] = frozenset(),
) -> ReportTable:
    selected_alignments: tuple[TableAlignment, ...] = (
        tuple("left" for _ in headers) if alignments is None else tuple(alignments)
    )
    columns = tuple(
        ReportColumn(
            column_id,
            header,
            alignment,
            collapse_repeats=column_id in collapse_repeats,
        )
        for column_id, header, alignment in zip(column_ids, headers, selected_alignments, strict=True)
    )
    return ReportTable(table_id, title, columns, rows, caption)
