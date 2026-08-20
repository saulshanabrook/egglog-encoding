"""Compute renderer-neutral statistics for one benchmark endpoint pair.

This module selects observations, estimates means and confidence intervals,
computes Fieller ratios, exhaustively attributes wall time, and partitions
ruleset work. Persistence lives in :mod:`benchmarking.reports.store`; all labels,
units, and presentation policy live in :mod:`benchmarking.reports.presentation`.
"""

from __future__ import annotations

import math
import statistics
from collections.abc import Iterable
from typing import Literal, NamedTuple, cast

from scipy import stats

from ..models import ComparisonSpec, DetailLevel
from .store import CacheKey, IndexedRecord, ReportStore

MetricName = Literal["wall_sec", "max_rss_bytes"]
ResultClass = Literal["higher", "invalid", "lower", "point_only", "unclear"]
SummaryKind = Literal["suite", "lowest_file", "highest_file"]
RulesetPhaseName = Literal["assembly", "search", "apply", "execution", "merge", "rebuild"]
RulesetMechanism = Literal["program", "equality"]
type _MetricKey = tuple[int, int, MetricName]
type _ObservationKey = tuple[int, int]

_METRICS: tuple[MetricName, ...] = ("wall_sec", "max_rss_bytes")
RULESET_PHASES: tuple[RulesetPhaseName, ...] = (
    "assembly",
    "search",
    "apply",
    "execution",
    "merge",
    "rebuild",
)


class Estimate(NamedTuple):
    """One point estimate and its optional confidence interval."""

    point: float | None
    ci_low: float | None
    ci_high: float | None


class RatioEstimate(NamedTuple):
    """One ratio estimate plus its interpretation and availability issue."""

    estimate: Estimate
    result_class: ResultClass
    issue: str | None


class PhaseValues(NamedTuple):
    """Six recorded timing components aggregated for one observation/ruleset."""

    assembly: float
    search: float
    apply: float
    execution: float
    merge: float
    rebuild: float

    @property
    def total(self) -> float:
        return math.fsum(self)


class SummaryView(NamedTuple):
    """One suite or per-file tail summary."""

    metric: MetricName
    summary_kind: SummaryKind
    file_order: int | None
    ratio: RatioEstimate


class FileComparisonView(NamedTuple):
    """One file/metric comparison."""

    file_order: int
    metric: MetricName
    baseline: Estimate
    candidate: Estimate
    ratio: RatioEstimate


class RulesetChange(NamedTuple):
    """One named ruleset's own-work phase changes."""

    name: str
    phases: PhaseValues


class RulesetGroup(NamedTuple):
    """One mechanism's named rulesets and optional global rebuild change."""

    rulesets: tuple[RulesetChange, ...]
    native_rebuild_delta_ns: float = 0.0

    @property
    def phases(self) -> PhaseValues:
        values = [math.fsum(ruleset.phases[index] for ruleset in self.rulesets) for index in range(len(RULESET_PHASES))]
        values[-1] += self.native_rebuild_delta_ns
        return PhaseValues(*values)


class FileTimingBreakdown(NamedTuple):
    """One canonical additive timing partition consumed by both timing views."""

    file_order: int | None
    wall_delta_ns: float | None
    typecheck_delta_ns: float
    frontend_delta_ns: float
    generated_construct_delta_ns: float
    generated_signatures_delta_ns: float
    generated_resolve_delta_ns: float
    generated_lower_delta_ns: float
    program: RulesetGroup
    equality: RulesetGroup
    commands_delta_ns: float
    residual_delta_ns: float
    residual_warning: bool
    issue: str | None

    @property
    def mechanism_deltas(self) -> tuple[float | None, ...]:
        if self.issue is not None:
            return (None,) * 6
        return (
            self.typecheck_delta_ns,
            self.frontend_delta_ns,
            self.program.phases.total,
            self.equality.phases.total,
            self.commands_delta_ns,
            self.residual_delta_ns,
        )


class PairReportViewData(NamedTuple):
    """Typed analysis collections requested by one cumulative detail level."""

    summary: tuple[SummaryView, ...]
    files: tuple[FileComparisonView, ...]
    timing: tuple[FileTimingBreakdown, ...]


class _MetricEstimate(NamedTuple):
    sample_count: int
    estimate: Estimate
    var_mean: float | None
    issue: str | None


class _TimingMean(NamedTuple):
    """One endpoint/file's direct means from the typed timing record."""

    typecheck_ns: float
    frontend_ns: float
    generated_construct_ns: float
    generated_signatures_ns: float
    generated_resolve_ns: float
    generated_lower_ns: float
    commands_ns: float
    rulesets: dict[tuple[RulesetMechanism, str], PhaseValues]
    native_rebuild_ns: float
    residual_ns: float | None


def analyze_pair(
    store: ReportStore,
    comparison: ComparisonSpec,
    detail: DetailLevel,
) -> PairReportViewData:
    """Return every presentation row requested for one exact endpoint pair."""

    observations = _selected_observations(store, comparison)
    issues = {key: _selection_issue(rows, comparison.rounds) for key, rows in observations.items()}
    t_critical = None if comparison.rounds < 2 else float(stats.t.ppf(0.975, comparison.rounds - 1))
    estimates = _metric_estimates(observations, issues, t_critical)
    file_rows = _file_comparisons(comparison, estimates, t_critical)
    summary = _summary_rows(comparison, estimates, file_rows, t_critical)

    if detail == "summary":
        return PairReportViewData(summary, (), ())
    if detail == "files":
        return PairReportViewData(summary, file_rows, ())

    timing = _timing_breakdowns(comparison, observations, issues, estimates)
    return PairReportViewData(summary, file_rows, timing)


def _selected_observations(
    store: ReportStore,
    comparison: ComparisonSpec,
) -> dict[_ObservationKey, tuple[IndexedRecord, ...]]:
    selected: dict[_ObservationKey, tuple[IndexedRecord, ...]] = {}
    for endpoint_order, endpoint in enumerate((comparison.baseline, comparison.candidate)):
        for file_order, file in enumerate(comparison.files):
            key = CacheKey.for_endpoint(endpoint, file, comparison.timeout_sec)
            selected[(endpoint_order, file_order)] = store.latest_records(key, comparison.rounds)
    return selected


def _selection_issue(rows: tuple[IndexedRecord, ...], rounds: int) -> str | None:
    if len(rows) < rounds:
        return f"missing {rounds - len(rows)} row(s)"
    statuses = tuple(row.record["status"] for row in rows)
    if "failure" in statuses:
        return "failure row selected"
    if "timed-out" in statuses:
        return "timeout row selected"
    return None


def _metric_estimates(
    observations: dict[_ObservationKey, tuple[IndexedRecord, ...]],
    issues: dict[_ObservationKey, str | None],
    t_critical: float | None,
) -> dict[_MetricKey, _MetricEstimate]:
    result: dict[_MetricKey, _MetricEstimate] = {}
    for (endpoint_order, file_order), rows in observations.items():
        for metric in _METRICS:
            values = [float(value) for row in rows if (value := row.record[metric]) is not None]
            issue = issues[(endpoint_order, file_order)]
            if issue is None and len(values) != len(rows):
                issue = "wall time unavailable" if metric == "wall_sec" else "peak RSS unavailable"
            result[(endpoint_order, file_order, metric)] = _sample_estimate(values, issue, t_critical)
    return result


def _file_comparisons(
    comparison: ComparisonSpec,
    estimates: dict[_MetricKey, _MetricEstimate],
    t_critical: float | None,
) -> tuple[FileComparisonView, ...]:
    rows: list[FileComparisonView] = []
    for file_order in range(len(comparison.files)):
        for metric in _METRICS:
            baseline = estimates[(0, file_order, metric)]
            candidate = estimates[(1, file_order, metric)]
            rows.append(
                FileComparisonView(
                    file_order,
                    metric,
                    baseline.estimate,
                    candidate.estimate,
                    _ratio_estimate(baseline, candidate, t_critical),
                )
            )
    return tuple(rows)


def _ratio_estimate(
    baseline: _MetricEstimate,
    candidate: _MetricEstimate,
    t_critical: float | None,
) -> RatioEstimate:
    baseline_mean = baseline.estimate.point
    candidate_mean = candidate.estimate.point
    issue = baseline.issue or candidate.issue
    if issue is not None:
        return RatioEstimate(Estimate(None, None, None), "invalid", issue)
    if baseline_mean is None or candidate_mean is None:
        return RatioEstimate(Estimate(None, None, None), "invalid", "estimate unavailable")
    if baseline_mean <= 0:
        return RatioEstimate(Estimate(None, None, None), "invalid", "baseline mean is not positive")

    point = candidate_mean / baseline_mean
    if min(baseline.sample_count, candidate.sample_count) < 2:
        return RatioEstimate(Estimate(point, None, None), "point_only", "CI undefined for n < 2")
    if baseline.var_mean is None or candidate.var_mean is None or t_critical is None:
        raise ValueError("multi-sample ratio is missing variance or its t critical value")
    critical_squared = t_critical * t_critical
    fieller_a = baseline_mean * baseline_mean - critical_squared * baseline.var_mean
    fieller_d = candidate_mean * candidate_mean - critical_squared * candidate.var_mean
    radicand = (baseline_mean * candidate_mean) ** 2 - fieller_a * fieller_d
    if fieller_a <= 0 or radicand < 0:
        return RatioEstimate(Estimate(point, None, None), "point_only", "Fieller interval undefined")
    center = baseline_mean * candidate_mean / fieller_a
    half_width = math.sqrt(radicand) / fieller_a
    ci_low = center - half_width
    ci_high = center + half_width
    return RatioEstimate(Estimate(point, ci_low, ci_high), _result_class(point, ci_low, ci_high), None)


def _result_class(point: float | None, ci_low: float | None, ci_high: float | None) -> ResultClass:
    if point is None:
        return "invalid"
    if ci_low is None or ci_high is None:
        return "point_only"
    if ci_high < 1.0:
        return "lower"
    if ci_low > 1.0:
        return "higher"
    return "unclear"


def _summary_rows(
    comparison: ComparisonSpec,
    estimates: dict[_MetricKey, _MetricEstimate],
    file_rows: tuple[FileComparisonView, ...],
    t_critical: float | None,
) -> tuple[SummaryView, ...]:
    baseline = [estimates[(0, order, "wall_sec")] for order in range(len(comparison.files))]
    candidate = [estimates[(1, order, "wall_sec")] for order in range(len(comparison.files))]
    first_issue = next(
        (
            issue
            for baseline_estimate, candidate_estimate in zip(baseline, candidate, strict=True)
            if (issue := baseline_estimate.issue or candidate_estimate.issue) is not None
        ),
        None,
    )
    sample_count = min(estimate.sample_count for estimate in baseline)
    suite_ratio = _ratio_estimate(
        _MetricEstimate(
            sample_count,
            Estimate(math.fsum(estimate.estimate.point or 0.0 for estimate in baseline), None, None),
            math.fsum(estimate.var_mean or 0.0 for estimate in baseline),
            first_issue,
        ),
        _MetricEstimate(
            sample_count,
            Estimate(math.fsum(estimate.estimate.point or 0.0 for estimate in candidate), None, None),
            math.fsum(estimate.var_mean or 0.0 for estimate in candidate),
            None,
        ),
        t_critical,
    )
    rows = [SummaryView("wall_sec", "suite", None, suite_ratio)]
    tail_specs: tuple[tuple[MetricName, SummaryKind], ...] = (
        ("wall_sec", "lowest_file"),
        ("wall_sec", "highest_file"),
        ("max_rss_bytes", "lowest_file"),
        ("max_rss_bytes", "highest_file"),
    )
    for metric, kind in tail_specs:
        metric_rows = tuple(row for row in file_rows if row.metric == metric)
        comparable = tuple(row for row in metric_rows if row.ratio.estimate.point is not None)
        selected: FileComparisonView | None
        if kind == "lowest_file":
            selected = min(comparable, key=lambda row: (row.ratio.estimate.point, row.file_order), default=None)
        else:
            selected = max(comparable, key=lambda row: (row.ratio.estimate.point, row.file_order), default=None)
        if selected is None:
            issue = (
                next(
                    (row.ratio.issue for row in metric_rows if row.ratio.estimate.point is None),
                    None,
                )
                or "no comparable files"
            )
            ratio = RatioEstimate(Estimate(None, None, None), "invalid", issue)
            file_order = None
        else:
            ratio = selected.ratio
            file_order = selected.file_order
        rows.append(SummaryView(metric, kind, file_order, ratio))
    return tuple(rows)


def _timing_breakdowns(
    comparison: ComparisonSpec,
    observations: dict[_ObservationKey, tuple[IndexedRecord, ...]],
    issues: dict[_ObservationKey, str | None],
    metric_estimates: dict[_MetricKey, _MetricEstimate],
) -> tuple[FileTimingBreakdown, ...]:
    means = _timing_means(observations, metric_estimates)
    files: list[FileTimingBreakdown] = []
    for file_order in range(len(comparison.files)):
        baseline = means[(0, file_order)]
        candidate = means[(1, file_order)]
        baseline_wall = metric_estimates[(0, file_order, "wall_sec")]
        candidate_wall = metric_estimates[(1, file_order, "wall_sec")]
        issue = issues[(0, file_order)] or issues[(1, file_order)] or baseline_wall.issue or candidate_wall.issue
        wall_delta_ns = (
            None
            if issue is not None or baseline_wall.estimate.point is None or candidate_wall.estimate.point is None
            else (candidate_wall.estimate.point - baseline_wall.estimate.point) * 1_000_000_000.0
        )
        residual_delta_ns = (
            0.0
            if baseline.residual_ns is None or candidate.residual_ns is None
            else candidate.residual_ns - baseline.residual_ns
        )
        files.append(
            FileTimingBreakdown(
                file_order,
                wall_delta_ns,
                candidate.typecheck_ns - baseline.typecheck_ns,
                candidate.frontend_ns - baseline.frontend_ns,
                candidate.generated_construct_ns - baseline.generated_construct_ns,
                candidate.generated_signatures_ns - baseline.generated_signatures_ns,
                candidate.generated_resolve_ns - baseline.generated_resolve_ns,
                candidate.generated_lower_ns - baseline.generated_lower_ns,
                _ruleset_group_delta(baseline, candidate, "program"),
                _ruleset_group_delta(baseline, candidate, "equality"),
                candidate.commands_ns - baseline.commands_ns,
                residual_delta_ns,
                (baseline.residual_ns is not None and baseline.residual_ns < 0)
                or (candidate.residual_ns is not None and candidate.residual_ns < 0),
                issue,
            )
        )

    suite_issue = next((row.issue for row in files if row.issue is not None), None)
    suite = FileTimingBreakdown(
        None,
        None if suite_issue is not None else math.fsum(cast(float, row.wall_delta_ns) for row in files),
        math.fsum(row.typecheck_delta_ns for row in files),
        math.fsum(row.frontend_delta_ns for row in files),
        math.fsum(row.generated_construct_delta_ns for row in files),
        math.fsum(row.generated_signatures_delta_ns for row in files),
        math.fsum(row.generated_resolve_delta_ns for row in files),
        math.fsum(row.generated_lower_delta_ns for row in files),
        _sum_ruleset_groups(row.program for row in files),
        _sum_ruleset_groups(row.equality for row in files),
        math.fsum(row.commands_delta_ns for row in files),
        math.fsum(row.residual_delta_ns for row in files),
        any(row.residual_warning for row in files),
        suite_issue,
    )
    return (suite, *files)


def _timing_means(
    observations: dict[_ObservationKey, tuple[IndexedRecord, ...]],
    metric_estimates: dict[_MetricKey, _MetricEstimate],
) -> dict[_ObservationKey, _TimingMean]:
    result: dict[_ObservationKey, _TimingMean] = {}
    for key, rows in observations.items():
        typecheck = 0.0
        frontend = 0.0
        generated_construct = 0.0
        generated_signatures = 0.0
        generated_resolve = 0.0
        generated_lower = 0.0
        commands = 0.0
        native_rebuild = 0.0
        rulesets: dict[tuple[RulesetMechanism, str], list[float]] = {}
        for row in rows:
            record = row.record
            if record["status"] != "success":
                continue
            summary = record["timing_summary"]
            if summary is None:
                raise ValueError("successful benchmark record is missing its timing summary")
            typecheck += summary["typecheck_ns"]
            generated_construct += summary["frontend_generated_construct_ns"]
            generated_signatures += summary["frontend_generated_signatures_ns"]
            generated_resolve += summary["frontend_generated_resolve_ns"]
            generated_lower += summary["frontend_generated_lower_ns"]
            frontend += (
                summary["frontend_parse_ns"]
                + summary["frontend_other_ns"]
                + summary["frontend_install_ns"]
                + summary["frontend_generated_construct_ns"]
                + summary["frontend_generated_signatures_ns"]
                + summary["frontend_generated_resolve_ns"]
                + summary["frontend_generated_lower_ns"]
            )
            commands += summary["commands_actions_ns"] + summary["commands_check_ns"] + summary["commands_other_ns"]
            native_rebuild += summary["native_rebuild_ns"]
            for timing in summary["rulesets"]:
                phase_sums = rulesets.setdefault((timing["role"], timing["name"]), [0.0] * 6)
                phase_sums[0] += timing["assembly_ns"]
                phase_sums[1] += timing["search_ns"]
                phase_sums[2] += timing["apply_ns"]
                phase_sums[3] += timing["execution_ns"]
                phase_sums[4] += timing["merge_ns"]

        denominator = len(rows) or 1
        ruleset_means = {
            key: PhaseValues(*(value / denominator for value in values)) for key, values in rulesets.items()
        }
        typecheck /= denominator
        frontend /= denominator
        generated_construct /= denominator
        generated_signatures /= denominator
        generated_resolve /= denominator
        generated_lower /= denominator
        commands /= denominator
        native_rebuild /= denominator
        recorded = (
            typecheck
            + frontend
            + commands
            + native_rebuild
            + math.fsum(phases.total for phases in ruleset_means.values())
        )
        wall = metric_estimates[(key[0], key[1], "wall_sec")].estimate.point
        result[key] = _TimingMean(
            typecheck,
            frontend,
            generated_construct,
            generated_signatures,
            generated_resolve,
            generated_lower,
            commands,
            ruleset_means,
            native_rebuild,
            None if wall is None else wall * 1_000_000_000.0 - recorded,
        )
    return result


def _ruleset_group_delta(
    baseline: _TimingMean,
    candidate: _TimingMean,
    mechanism: RulesetMechanism,
) -> RulesetGroup:
    names = sorted({name for role, name in baseline.rulesets.keys() | candidate.rulesets.keys() if role == mechanism})
    zero = PhaseValues(0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
    rulesets = []
    for name in names:
        baseline_phases = baseline.rulesets.get((mechanism, name), zero)
        candidate_phases = candidate.rulesets.get((mechanism, name), zero)
        phases = PhaseValues(
            *(candidate_phases[index] - baseline_phases[index] for index in range(len(RULESET_PHASES)))
        )
        if any(phases):
            rulesets.append(RulesetChange(name, phases))
    rebuild = candidate.native_rebuild_ns - baseline.native_rebuild_ns if mechanism == "equality" else 0.0
    return RulesetGroup(tuple(rulesets), rebuild)


def _sum_ruleset_groups(groups: Iterable[RulesetGroup]) -> RulesetGroup:
    """Combine file-level ruleset groups while preserving named phase totals."""

    phase_sums: dict[str, list[float]] = {}
    native_rebuild = 0.0
    for group in groups:
        native_rebuild += group.native_rebuild_delta_ns
        for ruleset in group.rulesets:
            values = phase_sums.setdefault(ruleset.name, [0.0] * len(RULESET_PHASES))
            for index, value in enumerate(ruleset.phases):
                values[index] += value
    rulesets = tuple(
        RulesetChange(name, PhaseValues(*values)) for name, values in sorted(phase_sums.items()) if any(values)
    )
    return RulesetGroup(rulesets, native_rebuild)


def _sample_estimate(
    values: list[float],
    issue: str | None,
    t_critical: float | None,
) -> _MetricEstimate:
    mean = statistics.fmean(values) if issue is None and values else None
    var_mean: float | None = None
    ci_low: float | None = None
    ci_high: float | None = None
    if mean is not None and len(values) >= 2:
        var_mean = statistics.variance(values) / len(values)
        if t_critical is None:
            raise ValueError("multi-sample estimate is missing its t critical value")
        half_width = t_critical * math.sqrt(var_mean)
        ci_low = mean - half_width
        ci_high = mean + half_width
    return _MetricEstimate(len(values), Estimate(mean, ci_low, ci_high), var_mean, issue)
