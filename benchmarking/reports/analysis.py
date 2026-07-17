"""Compute one renderer-neutral baseline/candidate benchmark comparison.

This module owns latest-observation status policy, Student-t estimates, Fieller
ratios, fixed-suite and tail summaries, phase residuals, and ruleset ranking.
Persistence and cache discovery stay in :mod:`benchmarking.reports.store`;
human-facing wording and formatting stay in ``comparison``.
"""

from __future__ import annotations

import math
import statistics
from dataclasses import dataclass
from typing import Literal, NamedTuple

from scipy import stats

from ..models import ComparisonSpec, DetailLevel, EstimateKey
from .records import RulesetTimingRecord
from .store import IndexedRecord, ReportStore

MetricName = Literal["wall_sec", "max_rss_bytes"]
ResultClass = Literal["higher", "invalid", "lower", "point_only", "unclear"]
SummaryKind = Literal["suite", "lowest_file", "highest_file"]
PhaseName = Literal["search", "apply", "merge", "rebuild", "other"]

type _MetricKey = tuple[int, int, MetricName]
type _ObservationKey = tuple[int, int]

_METRICS: tuple[MetricName, ...] = ("wall_sec", "max_rss_bytes")
_PHASES: tuple[PhaseName, ...] = ("search", "apply", "merge", "rebuild", "other")


@dataclass(frozen=True)
class RatioSummary:
    """Point estimate, confidence interval, and availability issue for a ratio."""

    point: float | None
    ci_low: float | None
    ci_high: float | None
    issue: str | None


class SummaryView(NamedTuple):
    """One suite or per-file tail summary."""

    metric: MetricName
    summary_kind: SummaryKind
    file_order: int | None
    point: float | None
    ci_low: float | None
    ci_high: float | None
    result_class: ResultClass
    issue: str | None

    @property
    def ratio(self) -> RatioSummary:
        """Return the candidate/baseline ratio represented by this row."""

        return RatioSummary(self.point, self.ci_low, self.ci_high, self.issue)


class FileComparisonView(NamedTuple):
    """One file/metric comparison."""

    file_order: int
    metric: MetricName
    baseline_mean: float | None
    baseline_ci_low: float | None
    baseline_ci_high: float | None
    candidate_mean: float | None
    candidate_ci_low: float | None
    candidate_ci_high: float | None
    point: float | None
    ci_low: float | None
    ci_high: float | None
    result_class: ResultClass
    issue: str | None

    @property
    def ratio(self) -> RatioSummary:
        """Return the candidate/baseline ratio represented by this row."""

        return RatioSummary(self.point, self.ci_low, self.ci_high, self.issue)


class PhaseComparisonView(NamedTuple):
    """One file/phase comparison."""

    file_order: int
    phase: PhaseName
    baseline_ns: float | None
    candidate_ns: float | None
    delta_ns: float | None
    point: float | None


class RulesetComparisonView(NamedTuple):
    """One top absolute-delta ruleset."""

    file_order: int
    ruleset_count: int
    name: str
    baseline_total_ns: float | None
    candidate_total_ns: float | None
    delta_ns: float
    point: float | None


@dataclass(frozen=True)
class PairReportViewData:
    """Typed analysis collections requested by one cumulative detail level."""

    summary: tuple[SummaryView, ...]
    files: tuple[FileComparisonView, ...]
    phases: tuple[PhaseComparisonView, ...]
    rulesets: tuple[RulesetComparisonView, ...]


@dataclass(frozen=True)
class _MetricEstimate:
    sample_count: int
    mean: float | None
    var_mean: float | None
    ci_low: float | None
    ci_high: float | None
    issue: str | None


@dataclass(frozen=True)
class _RatioEstimate:
    point: float | None
    ci_low: float | None
    ci_high: float | None
    result_class: ResultClass
    issue: str | None


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

    phases = _phase_comparisons(comparison, observations, issues)
    if detail == "phases":
        return PairReportViewData(summary, file_rows, phases, ())
    rulesets = _ruleset_comparisons(comparison, observations, issues)
    return PairReportViewData(summary, file_rows, phases, rulesets)


def _selected_observations(
    store: ReportStore,
    comparison: ComparisonSpec,
) -> dict[_ObservationKey, tuple[IndexedRecord, ...]]:
    selected: dict[_ObservationKey, tuple[IndexedRecord, ...]] = {}
    for endpoint_order, endpoint in enumerate((comparison.baseline, comparison.candidate)):
        for file_order, file in enumerate(comparison.files):
            key = EstimateKey.for_endpoint(endpoint, file, comparison.timeout_sec)
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
            mean = statistics.fmean(values) if issue is None else None
            var_mean: float | None = None
            ci_low: float | None = None
            ci_high: float | None = None
            if mean is not None and len(values) >= 2:
                var_mean = statistics.variance(values) / len(values)
                assert t_critical is not None
                half_width = t_critical * math.sqrt(var_mean)
                ci_low = mean - half_width
                ci_high = mean + half_width
            result[(endpoint_order, file_order, metric)] = _MetricEstimate(
                len(values),
                mean,
                var_mean,
                ci_low,
                ci_high,
                issue,
            )
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
            issue = baseline.issue if baseline.issue is not None else candidate.issue
            ratio = _ratio_estimate(
                baseline.mean,
                baseline.var_mean,
                candidate.mean,
                candidate.var_mean,
                baseline.sample_count,
                t_critical,
                issue,
            )
            rows.append(
                FileComparisonView(
                    file_order,
                    metric,
                    baseline.mean,
                    baseline.ci_low,
                    baseline.ci_high,
                    candidate.mean,
                    candidate.ci_low,
                    candidate.ci_high,
                    ratio.point,
                    ratio.ci_low,
                    ratio.ci_high,
                    ratio.result_class,
                    ratio.issue,
                )
            )
    return tuple(rows)


def _ratio_estimate(
    baseline_mean: float | None,
    baseline_var_mean: float | None,
    candidate_mean: float | None,
    candidate_var_mean: float | None,
    sample_count: int,
    t_critical: float | None,
    preliminary_issue: str | None,
) -> _RatioEstimate:
    issue = preliminary_issue
    if issue is None and (baseline_mean is None or candidate_mean is None):
        issue = "estimate unavailable"
    if issue is None and baseline_mean is not None and baseline_mean <= 0:
        issue = "baseline mean is not positive"
    if issue is not None:
        return _RatioEstimate(None, None, None, "invalid", issue)

    assert baseline_mean is not None and candidate_mean is not None
    point = candidate_mean / baseline_mean
    if sample_count < 2:
        return _RatioEstimate(point, None, None, "point_only", "CI undefined for n < 2")
    assert baseline_var_mean is not None
    assert candidate_var_mean is not None
    assert t_critical is not None
    critical_squared = t_critical * t_critical
    fieller_a = baseline_mean * baseline_mean - critical_squared * baseline_var_mean
    fieller_d = candidate_mean * candidate_mean - critical_squared * candidate_var_mean
    radicand = (baseline_mean * candidate_mean) ** 2 - fieller_a * fieller_d
    if fieller_a <= 0 or radicand < 0:
        return _RatioEstimate(point, None, None, "point_only", "Fieller interval undefined")
    center = baseline_mean * candidate_mean / fieller_a
    half_width = math.sqrt(radicand) / fieller_a
    ci_low = center - half_width
    ci_high = center + half_width
    return _RatioEstimate(point, ci_low, ci_high, _result_class(point, ci_low, ci_high), None)


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
    suite_ratio = _ratio_estimate(
        math.fsum(estimate.mean or 0.0 for estimate in baseline),
        math.fsum(estimate.var_mean or 0.0 for estimate in baseline),
        math.fsum(estimate.mean or 0.0 for estimate in candidate),
        math.fsum(estimate.var_mean or 0.0 for estimate in candidate),
        min(estimate.sample_count for estimate in baseline),
        t_critical,
        first_issue,
    )
    rows = [_summary_view("wall_sec", "suite", None, suite_ratio)]
    tail_specs: tuple[tuple[MetricName, SummaryKind], ...] = (
        ("wall_sec", "lowest_file"),
        ("wall_sec", "highest_file"),
        ("max_rss_bytes", "lowest_file"),
        ("max_rss_bytes", "highest_file"),
    )
    for metric, kind in tail_specs:
        metric_rows = tuple(row for row in file_rows if row.metric == metric)
        comparable = tuple(row for row in metric_rows if row.point is not None)
        selected: FileComparisonView | None
        if kind == "lowest_file":
            selected = min(comparable, key=lambda row: (row.point, row.file_order), default=None)
        else:
            selected = max(comparable, key=lambda row: (row.point, row.file_order), default=None)
        if selected is None:
            issue = next((row.issue for row in metric_rows if row.point is None), None) or "no comparable files"
            ratio = _RatioEstimate(None, None, None, "invalid", issue)
            file_order = None
        else:
            ratio = _RatioEstimate(
                selected.point,
                selected.ci_low,
                selected.ci_high,
                selected.result_class,
                selected.issue,
            )
            file_order = selected.file_order
        rows.append(_summary_view(metric, kind, file_order, ratio))
    return tuple(rows)


def _summary_view(
    metric: MetricName,
    kind: SummaryKind,
    file_order: int | None,
    ratio: _RatioEstimate,
) -> SummaryView:
    return SummaryView(
        metric,
        kind,
        file_order,
        ratio.point,
        ratio.ci_low,
        ratio.ci_high,
        ratio.result_class,
        ratio.issue,
    )


def _phase_comparisons(
    comparison: ComparisonSpec,
    observations: dict[_ObservationKey, tuple[IndexedRecord, ...]],
    issues: dict[_ObservationKey, str | None],
) -> tuple[PhaseComparisonView, ...]:
    means: dict[tuple[int, int, PhaseName], float | None] = {}
    for (endpoint_order, file_order), rows in observations.items():
        for phase in _PHASES:
            values = _phase_values(rows, phase)
            means[(endpoint_order, file_order, phase)] = (
                statistics.fmean(values) if issues[(endpoint_order, file_order)] is None and values else None
            )

    result: list[PhaseComparisonView] = []
    for file_order in range(len(comparison.files)):
        for phase in _PHASES:
            baseline = means[(0, file_order, phase)]
            candidate = means[(1, file_order, phase)]
            delta = None if baseline is None or candidate is None else candidate - baseline
            issue = issues[(0, file_order)] or issues[(1, file_order)]
            if issue is None and baseline is not None and baseline <= 0:
                issue = "baseline phase mean is not positive"
            if issue is None and candidate is not None and candidate < 0:
                issue = "candidate phase mean is negative"
            point = candidate / baseline if issue is None and baseline is not None and candidate is not None else None
            result.append(
                PhaseComparisonView(
                    file_order,
                    phase,
                    baseline,
                    candidate,
                    delta,
                    point,
                )
            )
    return tuple(result)


def _phase_values(rows: tuple[IndexedRecord, ...], phase: PhaseName) -> list[float]:
    values: list[float] = []
    for row in rows:
        record = row.record
        if record["status"] != "success":
            continue
        summary = record["timing_summary"]
        assert summary is not None
        rulesets = summary["rulesets"]
        recorded = {
            "search": sum(item["search_ns"] for item in rulesets),
            "apply": sum(item["apply_ns"] for item in rulesets),
            "merge": sum(item["merge_ns"] for item in rulesets),
            "rebuild": sum(item["rebuild_ns"] for item in rulesets),
        }
        if phase == "other":
            wall_sec = record["wall_sec"]
            if wall_sec is not None:
                values.append(wall_sec * 1_000_000_000.0 - sum(recorded.values()))
        else:
            values.append(float(recorded[phase]))
    return values


def _ruleset_comparisons(
    comparison: ComparisonSpec,
    observations: dict[_ObservationKey, tuple[IndexedRecord, ...]],
    issues: dict[_ObservationKey, str | None],
) -> tuple[RulesetComparisonView, ...]:
    result: list[RulesetComparisonView] = []
    for file_order in range(len(comparison.files)):
        if issues[(0, file_order)] is not None or issues[(1, file_order)] is not None:
            continue
        names = sorted(
            {
                ruleset["name"]
                for endpoint_order in (0, 1)
                for row in observations[(endpoint_order, file_order)]
                for ruleset in _rulesets(row)
            }
        )
        comparisons: list[tuple[str, float | None, float | None, float, float | None]] = []
        for name in names:
            baseline = _ruleset_mean(observations[(0, file_order)], name)
            candidate = _ruleset_mean(observations[(1, file_order)], name)
            delta = (candidate or 0.0) - (baseline or 0.0)
            point = candidate / baseline if baseline is not None and baseline > 0 and candidate is not None else None
            comparisons.append((name, baseline, candidate, delta, point))
        comparisons.sort(key=lambda row: (-abs(row[3]), row[0]))
        count = len(comparisons)
        for name, baseline, candidate, delta, point in comparisons[:10]:
            result.append(
                RulesetComparisonView(
                    file_order,
                    count,
                    name,
                    baseline,
                    candidate,
                    delta,
                    point,
                )
            )
    return tuple(result)


def _rulesets(row: IndexedRecord) -> list[RulesetTimingRecord]:
    summary = row.record["timing_summary"]
    return [] if summary is None else summary["rulesets"]


def _ruleset_mean(rows: tuple[IndexedRecord, ...], name: str) -> float | None:
    values: list[float] = []
    present = False
    for row in rows:
        matches = [_ruleset_total(ruleset) for ruleset in _rulesets(row) if ruleset["name"] == name]
        if matches:
            present = True
            values.extend(matches)
        else:
            values.append(0.0)
    return statistics.fmean(values) if present else None


def _ruleset_total(ruleset: RulesetTimingRecord) -> float:
    return float(
        ruleset["search_ns"]
        + ruleset["apply_ns"]
        + ruleset["unattributed_ns"]
        + ruleset["merge_ns"]
        + ruleset["rebuild_ns"]
    )
