"""Compute renderer-neutral statistics for one benchmark endpoint pair.

This module selects observations, estimates means and confidence intervals,
computes Fieller ratios, exhaustively attributes wall time, and ranks changed
rulesets. Persistence lives in :mod:`benchmarking.reports.store`; all labels,
units, and presentation policy live in :mod:`benchmarking.reports.presentation`.
"""

from __future__ import annotations

import math
import statistics
from collections.abc import Iterable
from dataclasses import dataclass
from typing import Literal, NamedTuple

from scipy import stats

from ..models import ComparisonSpec, DetailLevel
from .store import CacheKey, IndexedRecord, ReportStore

MetricName = Literal["wall_sec", "max_rss_bytes"]
ResultClass = Literal["higher", "invalid", "lower", "point_only", "unclear"]
SummaryKind = Literal["suite", "lowest_file", "highest_file"]
PhaseName = Literal["search", "apply", "unattributed", "merge", "rebuild", "outside"]
RulesetPhaseName = Literal["search", "apply", "unattributed", "merge", "rebuild"]

type _MetricKey = tuple[int, int, MetricName]
type _ObservationKey = tuple[int, int]

_METRICS: tuple[MetricName, ...] = ("wall_sec", "max_rss_bytes")
_RULESET_PHASES: tuple[RulesetPhaseName, ...] = ("search", "apply", "unattributed", "merge", "rebuild")
_PHASES: tuple[PhaseName, ...] = (*_RULESET_PHASES, "outside")


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


class PhaseEstimate(NamedTuple):
    """One phase estimate and its share of endpoint wall time."""

    timing: Estimate
    wall_share: float | None


class PhaseValues(NamedTuple):
    """Five recorded timing components aggregated for one observation/ruleset."""

    search: float
    apply: float
    unattributed: float
    merge: float
    rebuild: float

    @property
    def total(self) -> float:
        return sum(self)

    def phase(self, name: RulesetPhaseName) -> float:
        if name == "search":
            return self.search
        if name == "apply":
            return self.apply
        if name == "unattributed":
            return self.unattributed
        if name == "merge":
            return self.merge
        return self.rebuild


class RulesetDelta(NamedTuple):
    """One exact total delta and its five timing-component deltas."""

    total: float
    phases: PhaseValues


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


class PhaseComparisonView(NamedTuple):
    """One exhaustive per-file wall-time phase comparison."""

    file_order: int
    phase: PhaseName
    baseline: PhaseEstimate
    candidate: PhaseEstimate
    delta_ns: float | None
    wall_delta_contribution: float | None


class RulesetComparisonView(NamedTuple):
    """One top absolute-total-delta ruleset with component deltas."""

    file_order: int
    ruleset_count: int
    name: str
    baseline: Estimate | None
    candidate: Estimate | None
    delta: RulesetDelta


class PairReportViewData(NamedTuple):
    """Typed analysis collections requested by one cumulative detail level."""

    summary: tuple[SummaryView, ...]
    files: tuple[FileComparisonView, ...]
    phases: tuple[PhaseComparisonView, ...]
    rulesets: tuple[RulesetComparisonView, ...]


class _MetricEstimate(NamedTuple):
    sample_count: int
    estimate: Estimate
    var_mean: float | None
    issue: str | None


@dataclass
class _RulesetSamples:
    """Sparse per-observation samples; omitted observations contribute zero."""

    total: list[float]
    phases: dict[RulesetPhaseName, list[float]]


@dataclass
class _TimingAggregate:
    """One-pass phase and ruleset samples for an endpoint/file selection."""

    observation_count: int
    phases: dict[PhaseName, list[float]]
    rulesets: dict[str, _RulesetSamples]


class _RankedRuleset(NamedTuple):
    """One changed ruleset before the per-file top-ten cutoff."""

    name: str
    baseline: _MetricEstimate | None
    candidate: _MetricEstimate | None
    delta: RulesetDelta


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
        return PairReportViewData(summary, (), (), ())
    if detail == "files":
        return PairReportViewData(summary, file_rows, (), ())

    timing = _timing_aggregates(observations)
    phases = _phase_comparisons(comparison, timing, issues, estimates, t_critical)
    if detail == "phases":
        return PairReportViewData(summary, file_rows, phases, ())
    rulesets = _ruleset_comparisons(comparison, timing, issues, t_critical)
    return PairReportViewData(summary, file_rows, phases, rulesets)


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
    if issue is None and (baseline_mean is None or candidate_mean is None):
        issue = "estimate unavailable"
    if issue is None and baseline_mean is not None and baseline_mean <= 0:
        issue = "baseline mean is not positive"
    if issue is not None:
        return RatioEstimate(Estimate(None, None, None), "invalid", issue)

    assert baseline_mean is not None and candidate_mean is not None
    point = candidate_mean / baseline_mean
    if min(baseline.sample_count, candidate.sample_count) < 2:
        return RatioEstimate(Estimate(point, None, None), "point_only", "CI undefined for n < 2")
    assert baseline.var_mean is not None
    assert candidate.var_mean is not None
    assert t_critical is not None
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


def _phase_comparisons(
    comparison: ComparisonSpec,
    timing: dict[_ObservationKey, _TimingAggregate],
    issues: dict[_ObservationKey, str | None],
    metric_estimates: dict[_MetricKey, _MetricEstimate],
    t_critical: float | None,
) -> tuple[PhaseComparisonView, ...]:
    estimates: dict[tuple[int, int, PhaseName], _MetricEstimate] = {}
    for (endpoint_order, file_order), aggregate in timing.items():
        for phase in _PHASES:
            issue = issues[(endpoint_order, file_order)]
            if phase == "outside" and issue is None:
                issue = metric_estimates[(endpoint_order, file_order, "wall_sec")].issue
            estimates[(endpoint_order, file_order, phase)] = _sample_estimate(
                aggregate.phases[phase],
                issue,
                t_critical,
            )

    result: list[PhaseComparisonView] = []
    for file_order in range(len(comparison.files)):
        baseline_wall = metric_estimates[(0, file_order, "wall_sec")].estimate.point
        candidate_wall = metric_estimates[(1, file_order, "wall_sec")].estimate.point
        wall_delta_ns = (
            None
            if baseline_wall is None or candidate_wall is None
            else (candidate_wall - baseline_wall) * 1_000_000_000.0
        )
        for phase in _PHASES:
            baseline = estimates[(0, file_order, phase)]
            candidate = estimates[(1, file_order, phase)]
            baseline_point = baseline.estimate.point
            candidate_point = candidate.estimate.point
            delta = None if baseline_point is None or candidate_point is None else candidate_point - baseline_point
            result.append(
                PhaseComparisonView(
                    file_order,
                    phase,
                    PhaseEstimate(
                        baseline.estimate,
                        _share(baseline_point, baseline_wall, scale=1_000_000_000.0),
                    ),
                    PhaseEstimate(
                        candidate.estimate,
                        _share(candidate_point, candidate_wall, scale=1_000_000_000.0),
                    ),
                    delta,
                    _share(delta, wall_delta_ns),
                )
            )
    return tuple(result)


def _timing_aggregates(
    observations: dict[_ObservationKey, tuple[IndexedRecord, ...]],
) -> dict[_ObservationKey, _TimingAggregate]:
    result: dict[_ObservationKey, _TimingAggregate] = {}
    for key, rows in observations.items():
        aggregate = _TimingAggregate(
            len(rows),
            {phase: [] for phase in _PHASES},
            {},
        )
        for row in rows:
            record = row.record
            if record["status"] != "success":
                continue
            summary = record["timing_summary"]
            assert summary is not None
            per_ruleset: dict[str, PhaseValues] = {}
            for ruleset in summary["rulesets"]:
                totals = PhaseValues(
                    float(ruleset["search_ns"]),
                    float(ruleset["apply_ns"]),
                    float(ruleset["unattributed_ns"]),
                    float(ruleset["merge_ns"]),
                    float(ruleset["rebuild_ns"]),
                )
                per_ruleset[ruleset["name"]] = _add_totals(per_ruleset.get(ruleset["name"], _ZERO_PHASE_TOTALS), totals)
            recorded = _sum_totals(per_ruleset.values())
            for phase in _RULESET_PHASES:
                aggregate.phases[phase].append(recorded.phase(phase))
            wall_sec = record["wall_sec"]
            if wall_sec is not None:
                aggregate.phases["outside"].append(wall_sec * 1_000_000_000.0 - recorded.total)
            for name, totals in per_ruleset.items():
                samples = aggregate.rulesets.setdefault(
                    name,
                    _RulesetSamples([], {phase: [] for phase in _RULESET_PHASES}),
                )
                samples.total.append(totals.total)
                for phase in _RULESET_PHASES:
                    samples.phases[phase].append(totals.phase(phase))
        result[key] = aggregate
    return result


_ZERO_PHASE_TOTALS = PhaseValues(0.0, 0.0, 0.0, 0.0, 0.0)


def _add_totals(left: PhaseValues, right: PhaseValues) -> PhaseValues:
    return PhaseValues(
        left.search + right.search,
        left.apply + right.apply,
        left.unattributed + right.unattributed,
        left.merge + right.merge,
        left.rebuild + right.rebuild,
    )


def _sum_totals(values: Iterable[PhaseValues]) -> PhaseValues:
    result = _ZERO_PHASE_TOTALS
    for value in values:
        result = _add_totals(result, value)
    return result


def _ruleset_comparisons(
    comparison: ComparisonSpec,
    timing: dict[_ObservationKey, _TimingAggregate],
    issues: dict[_ObservationKey, str | None],
    t_critical: float | None,
) -> tuple[RulesetComparisonView, ...]:
    result: list[RulesetComparisonView] = []
    for file_order in range(len(comparison.files)):
        if issues[(0, file_order)] is not None or issues[(1, file_order)] is not None:
            continue
        names = sorted({name for endpoint_order in (0, 1) for name in timing[(endpoint_order, file_order)].rulesets})
        comparisons: list[_RankedRuleset] = []
        for name in names:
            baseline = _ruleset_estimate(timing[(0, file_order)], name, None, t_critical)
            candidate = _ruleset_estimate(timing[(1, file_order)], name, None, t_critical)
            total_delta = _estimate_point(candidate) - _estimate_point(baseline)
            if total_delta == 0.0:
                continue
            delta = RulesetDelta(total_delta, _ruleset_phase_deltas(timing, file_order, name, t_critical))
            comparisons.append(_RankedRuleset(name, baseline, candidate, delta))
        comparisons.sort(key=lambda row: (-abs(row.delta.total), row.name))
        count = len(comparisons)
        for row in comparisons[:10]:
            result.append(
                RulesetComparisonView(
                    file_order,
                    count,
                    row.name,
                    None if row.baseline is None else row.baseline.estimate,
                    None if row.candidate is None else row.candidate.estimate,
                    row.delta,
                )
            )
    return tuple(result)


def _ruleset_estimate(
    aggregate: _TimingAggregate,
    name: str,
    phase: RulesetPhaseName | None,
    t_critical: float | None,
) -> _MetricEstimate | None:
    samples = aggregate.rulesets.get(name)
    if samples is None:
        return None
    observed = samples.total if phase is None else samples.phases[phase]
    values = [*observed, *(0.0 for _ in range(aggregate.observation_count - len(observed)))]
    return _sample_estimate(values, None, t_critical)


def _estimate_point(estimate: _MetricEstimate | None) -> float:
    return 0.0 if estimate is None or estimate.estimate.point is None else estimate.estimate.point


def _ruleset_phase_deltas(
    timing: dict[_ObservationKey, _TimingAggregate],
    file_order: int,
    name: str,
    t_critical: float | None,
) -> PhaseValues:
    def delta(phase: RulesetPhaseName) -> float:
        candidate = _ruleset_estimate(timing[(1, file_order)], name, phase, t_critical)
        baseline = _ruleset_estimate(timing[(0, file_order)], name, phase, t_critical)
        return _estimate_point(candidate) - _estimate_point(baseline)

    return PhaseValues(delta("search"), delta("apply"), delta("unattributed"), delta("merge"), delta("rebuild"))


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
        assert t_critical is not None
        half_width = t_critical * math.sqrt(var_mean)
        ci_low = mean - half_width
        ci_high = mean + half_width
    return _MetricEstimate(len(values), Estimate(mean, ci_low, ci_high), var_mean, issue)


def _share(numerator: float | None, denominator: float | None, *, scale: float = 1.0) -> float | None:
    if numerator is None or denominator is None or denominator == 0:
        return None
    return numerator / (denominator * scale)
