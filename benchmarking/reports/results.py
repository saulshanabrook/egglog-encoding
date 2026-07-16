"""Define immutable typed contracts at the DuckDB query boundary.

The ``*View`` named tuples mirror the output columns in
``reports/sql/presentation.sql`` exactly; schema changes must update both
locations. Persisted mutable ``TypedDict`` shapes instead belong in
:mod:`benchmarking.reports.records`. The database constructs these values;
final table layout and display values belong in :mod:`benchmarking.reports.catalog`.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, NamedTuple

from ..models import EstimateKey, TargetRow, Treatment

MetricName = Literal["wall_sec", "max_rss_bytes"]
ResultClass = Literal["available", "higher", "interval", "invalid", "lower", "point_only", "unclear"]
TargetRole = Literal["baseline", "candidate", "target"]


@dataclass(frozen=True)
class RatioSummary:
    """Point estimate, confidence interval, and availability issue for a ratio."""

    point: float | None
    ci_low: float | None
    ci_high: float | None
    issue: str | None


@dataclass(frozen=True)
class CachedTarget:
    """Latest persisted target identity addressed by a user label."""

    row: TargetRow
    binary_sha256: str


@dataclass(frozen=True)
class EstimateAggregate:
    """Historical successful wall-time count and sum for one exact cache key."""

    key: EstimateKey
    sample_count: int
    total_wall_sec: float


@dataclass(frozen=True)
class ComparisonRequest:
    """Compare two scoped target/cell coordinates across every scoped file."""

    baseline_target_order: int
    baseline_cell_order: int
    candidate_target_order: int
    candidate_cell_order: int


class TargetView(NamedTuple):
    """One typed row from SQL ``presentation_targets``."""

    target_order: int
    target_role: TargetRole
    target_label: str
    target_source: str
    target_path: str
    target_git_ref: str
    target_git_sha: str
    target_is_dirty: bool
    binary_sha256: str


class CellEstimateView(NamedTuple):
    """One typed row from SQL ``presentation_cell_estimates``."""

    metric_order: int
    target_order: int
    file_order: int
    cell_order: int
    metric: MetricName
    backend: str
    treatment: Treatment
    sample_count: int
    has_samples: bool
    mean: float | None
    ci_low: float | None
    ci_high: float | None
    result_class: ResultClass
    issue: str | None


class FileRatioView(NamedTuple):
    """One typed row from SQL ``presentation_file_ratios``."""

    comparison_order: int
    metric_order: int
    file_order: int
    metric: MetricName
    baseline_target_order: int
    baseline_cell_order: int
    candidate_target_order: int
    candidate_cell_order: int
    baseline_sample_count: int
    candidate_sample_count: int
    has_samples: bool
    point: float | None
    ci_low: float | None
    ci_high: float | None
    change_fraction: float | None
    change_ci_low: float | None
    change_ci_high: float | None
    is_valid: bool
    ci_entirely_below_one: bool
    ci_entirely_above_one: bool
    result_class: ResultClass
    issue: str | None

    @property
    def ratio(self) -> RatioSummary:
        return RatioSummary(self.point, self.ci_low, self.ci_high, self.issue)

    @property
    def change(self) -> RatioSummary:
        return RatioSummary(self.change_fraction, self.change_ci_low, self.change_ci_high, self.issue)


class ComparisonRollupView(NamedTuple):
    """One typed row from SQL ``presentation_comparison_rollups``."""

    comparison_order: int
    metric_order: int
    metric: MetricName
    baseline_target_order: int
    baseline_cell_order: int
    candidate_target_order: int
    candidate_cell_order: int
    baseline_total: float | None
    candidate_total: float | None
    has_samples: bool
    suite_point: float | None
    suite_ci_low: float | None
    suite_ci_high: float | None
    suite_change_fraction: float | None
    suite_change_ci_low: float | None
    suite_change_ci_high: float | None
    suite_ci_entirely_below_two: bool
    suite_result_class: ResultClass
    suite_issue: str | None
    geometric_mean_point: float | None
    geometric_mean_change_fraction: float | None
    geometric_mean_result_class: ResultClass
    geometric_mean_issue: str | None
    file_count: int
    comparable_file_count: int
    better_file_count: int
    best_file_order: int | None
    best_point: float | None
    best_ci_low: float | None
    best_ci_high: float | None
    best_change_fraction: float | None
    best_result_class: ResultClass
    best_issue: str | None
    worst_file_order: int | None
    worst_point: float | None
    worst_ci_low: float | None
    worst_ci_high: float | None
    worst_change_fraction: float | None
    worst_result_class: ResultClass
    worst_issue: str | None

    @property
    def suite(self) -> RatioSummary:
        return RatioSummary(self.suite_point, self.suite_ci_low, self.suite_ci_high, self.suite_issue)

    @property
    def suite_change(self) -> RatioSummary:
        return RatioSummary(
            self.suite_change_fraction,
            self.suite_change_ci_low,
            self.suite_change_ci_high,
            self.suite_issue,
        )

    @property
    def geometric_mean(self) -> RatioSummary:
        return RatioSummary(self.geometric_mean_point, None, None, self.geometric_mean_issue)

    @property
    def geometric_mean_change(self) -> RatioSummary:
        return RatioSummary(self.geometric_mean_change_fraction, None, None, self.geometric_mean_issue)

    @property
    def best(self) -> RatioSummary:
        return RatioSummary(self.best_point, self.best_ci_low, self.best_ci_high, self.best_issue)

    @property
    def worst(self) -> RatioSummary:
        return RatioSummary(self.worst_point, self.worst_ci_low, self.worst_ci_high, self.worst_issue)


class CompactTimingView(NamedTuple):
    """One typed row from SQL ``presentation_compact_timings``."""

    target_order: int
    file_order: int
    cell_order: int
    backend: str
    treatment: Treatment
    search_ns: float | None
    apply_ns: float | None
    search_and_apply_ns: float | None
    unattributed_ns: float | None
    pre_merge_ns: float | None
    merge_ns: float | None
    rebuild_ns: float | None
    ruleset_total_ns: float | None
    outside_rulesets_ns: float | None
    other_ns: float | None
    wall_ns: float | None
    has_samples: bool
    result_class: ResultClass
    issue: str | None


class RulesetTimingView(NamedTuple):
    """One typed row from SQL ``presentation_ruleset_timings``.

    An aligned name that this target never emitted has ``has_samples=False``
    and nullable phase values; the enclosing benchmark result is still valid.
    """

    file_order: int
    cell_order: int
    ruleset_order: int
    target_order: int
    backend: str
    treatment: Treatment
    name: str
    search_ns: float | None
    apply_ns: float | None
    search_and_apply_ns: float | None
    unattributed_ns: float | None
    pre_merge_ns: float | None
    merge_ns: float | None
    rebuild_ns: float | None
    total_ns: float | None
    maximum_target_total: float
    result_ruleset_total_ns: float | None
    has_samples: bool
    result_class: ResultClass
    ruleset_share: float | None


@dataclass(frozen=True)
class ReportViewData:
    """Typed contents of every DuckDB report view consumed by Python."""

    targets: tuple[TargetView, ...]
    cell_estimates: tuple[CellEstimateView, ...]
    file_ratios: tuple[FileRatioView, ...]
    comparison_rollups: tuple[ComparisonRollupView, ...]
    compact_timings: tuple[CompactTimingView, ...]
    ruleset_timings: tuple[RulesetTimingView, ...]
