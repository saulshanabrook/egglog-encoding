"""Define immutable typed contracts at the DuckDB query boundary.

The ``*View`` named tuples mirror ``reports/sql/presentation.sql`` column for
column. Persisted DuckDB ``TypedDict`` shapes instead live in ``records``;
presentation layout and formatting live above this data boundary.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, NamedTuple

from ..models import Backend, EstimateKey, TargetRow, Treatment

MetricName = Literal["wall_sec", "max_rss_bytes"]
ResultClass = Literal["higher", "invalid", "lower", "point_only", "unclear"]
EndpointRole = Literal["baseline", "candidate"]
SummaryKind = Literal["suite", "lowest_file", "highest_file"]
PhaseName = Literal["search", "apply", "merge", "rebuild", "other"]


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
class CachedEndpoint:
    """One row-complete cached endpoint available to the live report."""

    row: TargetRow
    binary_sha256: str
    backend: Backend
    treatment: Treatment

    @property
    def cache_identity(self) -> tuple[str, Backend, Treatment]:
        """Return the report-key dimensions shared by every endpoint file."""

        return (self.binary_sha256, self.backend, self.treatment)


@dataclass(frozen=True)
class EstimateAggregate:
    """Historical successful wall-time count and sum for one exact cache key."""

    key: EstimateKey
    sample_count: int
    total_wall_sec: float


class EndpointView(NamedTuple):
    """One row from SQL ``presentation_endpoints``."""

    endpoint_order: int
    endpoint_role: EndpointRole
    target_label: str
    target_git_sha: str
    target_is_dirty: bool
    binary_sha256: str
    backend: Backend
    treatment: Treatment


class SummaryView(NamedTuple):
    """One suite or per-file tail row from ``presentation_summary``."""

    summary_order: int
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
    """One file/metric row from SQL ``presentation_files``."""

    file_order: int
    metric_order: int
    file_path: str
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
    """One file/phase row from SQL ``presentation_phases``."""

    file_order: int
    file_path: str
    phase_order: int
    phase: PhaseName
    baseline_ns: float | None
    candidate_ns: float | None
    delta_ns: float | None
    point: float | None


class RulesetComparisonView(NamedTuple):
    """One top absolute-delta ruleset from ``presentation_rulesets``."""

    file_order: int
    file_path: str
    ruleset_rank: int
    ruleset_count: int
    name: str
    baseline_total_ns: float | None
    candidate_total_ns: float | None
    delta_ns: float
    point: float | None


@dataclass(frozen=True)
class PairReportViewData:
    """Typed contents of the presentation views requested by one detail level."""

    endpoints: tuple[EndpointView, ...]
    summary: tuple[SummaryView, ...]
    files: tuple[FileComparisonView, ...]
    phases: tuple[PhaseComparisonView, ...]
    rulesets: tuple[RulesetComparisonView, ...]
