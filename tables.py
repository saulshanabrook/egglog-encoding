"""Benchmark table computation: row selection, statistics, formatting, results.

Pure compute shared by every renderer — means/CIs, Fieller ratios, string
formatters, and result classifiers (plain status strings, no styling), so the
terminal and eval-live views style them their own way. No pandera at runtime.
"""

from __future__ import annotations

import math
from collections.abc import Sequence
from typing import TYPE_CHECKING

import numpy as np
from scipy import stats

from models import (
    BenchmarkSpec,
    CellMap,
    CellSummary,
    EstimateKey,
    FileSpec,
    RatioSummary,
    ResolvedTarget,
    Treatment,
)

if TYPE_CHECKING:
    from pandera.typing import DataFrame

    from report_frame import ReportFrame

TARGET_WALL_TIME_CAPTION = (
    "Ratio is target / baseline. Values below 1x are faster; above 1x are slower. "
    "Wall-time change is derived from the ratio; negative is faster. Intervals are 95% CIs."
)
TARGET_PEAK_RSS_CAPTION = (
    "Ratio is target / baseline. Values below 1x use less peak RSS; above 1x use more. "
    "RSS change is derived from the ratio; negative uses less memory. Intervals are 95% CIs."
)
PROOF_OVERHEAD_CAPTION = "Within-target proof overhead. This is separate from target-vs-baseline wall-time change."


def selected_rows(
    rows: DataFrame[ReportFrame],
    key: EstimateKey,
    rounds: int,
    *,
    validate: bool = True,
) -> DataFrame[ReportFrame]:
    matches = rows.loc[
        rows["binary_sha256"].eq(key.binary_sha256)
        & rows["file_sha256"].eq(key.file_sha256)
        & rows["treatment"].eq(key.treatment)
        & rows["timeout_sec"].eq(key.timeout_sec)
    ]
    latest = matches.sort_values(["started_at", "row_index"], ascending=[False, False], kind="mergesort").head(rounds)
    selected = latest.sort_values(["started_at", "row_index"], kind="mergesort").reset_index(drop=True)
    if not validate:
        # Browser (Pyodide) recompute path: pandera is unavailable, and rows
        # were already validated Python-side, so skip re-validation.
        return selected
    from report_frame import validate_report_frame

    return validate_report_frame(selected)


def status_counts_for_rows(rows: DataFrame[ReportFrame]) -> dict[str, int]:
    return {str(status): int(count) for status, count in rows["status"].value_counts().sort_index().items()}


def estimate_key_for(
    target: ResolvedTarget,
    file_spec: FileSpec,
    treatment: Treatment,
    timeout_sec: int,
) -> EstimateKey:
    return EstimateKey(
        binary_sha256=target.binary_sha256,
        file_sha256=file_spec.sha256,
        treatment=treatment,
        timeout_sec=timeout_sec,
    )


def summarize_cell(rows: DataFrame[ReportFrame], rounds: int) -> CellSummary:
    return summarize_metric_cell(rows, rounds, "wall_sec", "missing wall_sec")


def summarize_rss_cell(rows: DataFrame[ReportFrame], rounds: int) -> CellSummary:
    return summarize_metric_cell(rows, rounds, "max_rss_bytes", "missing max_rss_bytes")


def summarize_metric_cell(
    rows: DataFrame[ReportFrame],
    rounds: int,
    column: str,
    missing_issue: str,
) -> CellSummary:
    status_counts = status_counts_for_rows(rows)
    if len(rows) < rounds:
        return CellSummary(
            rows=rows,
            samples=(),
            status_counts=status_counts,
            mean=None,
            ci_low=None,
            ci_high=None,
            issue=f"missing {rounds - len(rows)} row(s)",
        )
    if status_counts.get("failure", 0):
        return CellSummary(rows, (), status_counts, None, None, None, "failure row selected")
    if status_counts.get("timed-out", 0):
        return CellSummary(rows, (), status_counts, None, None, None, "timeout row selected")
    samples = tuple(float(value) for value in rows.loc[rows[column].notna(), column].tolist())
    if len(samples) != len(rows):
        return CellSummary(rows, (), status_counts, None, None, None, missing_issue)
    mean, ci_low, ci_high = mean_interval(samples)
    return CellSummary(rows, samples, status_counts, mean, ci_low, ci_high, None)


def mean_interval(samples: Sequence[float]) -> tuple[float, float | None, float | None]:
    mean = float(np.mean(samples))
    if len(samples) < 2:
        return (mean, None, None)
    variance = float(np.var(samples, ddof=1))
    t_critical = float(stats.t.ppf(0.975, len(samples) - 1))
    half_width = t_critical * math.sqrt(variance / len(samples))
    return (mean, mean - half_width, mean + half_width)


def ratio_summary(
    baseline: CellSummary,
    candidate: CellSummary,
) -> RatioSummary:
    if not baseline.ok:
        return RatioSummary(None, None, None, baseline.issue or "baseline unavailable")
    if not candidate.ok:
        return RatioSummary(None, None, None, candidate.issue or "candidate unavailable")
    return ratio_from_samples(baseline.samples, candidate.samples)


def ratio_from_samples(
    baseline_samples: Sequence[float],
    candidate_samples: Sequence[float],
) -> RatioSummary:
    if len(baseline_samples) != len(candidate_samples):
        return RatioSummary(None, None, None, "sample counts differ")
    if len(baseline_samples) < 1:
        return RatioSummary(None, None, None, "no samples")
    baseline_mean = float(np.mean(baseline_samples))
    candidate_mean = float(np.mean(candidate_samples))
    if baseline_mean <= 0:
        return RatioSummary(None, None, None, "baseline mean is not positive")
    point = candidate_mean / baseline_mean
    if len(baseline_samples) < 2:
        return RatioSummary(point, None, None, "CI undefined for n < 2")
    n = len(baseline_samples)
    var_baseline_mean = float(np.var(baseline_samples, ddof=1)) / n
    var_candidate_mean = float(np.var(candidate_samples, ddof=1)) / n
    interval = fieller_interval(
        baseline_mean,
        candidate_mean,
        var_baseline_mean,
        var_candidate_mean,
        df=n - 1,
    )
    if interval is None:
        return RatioSummary(point, None, None, "Fieller interval undefined")
    return RatioSummary(point, interval[0], interval[1], None)


def fieller_interval(
    baseline_mean: float,
    candidate_mean: float,
    baseline_mean_variance: float,
    candidate_mean_variance: float,
    df: int,
) -> tuple[float, float] | None:
    if baseline_mean <= 0 or df <= 0:
        return None
    t_critical = float(stats.t.ppf(0.975, df))
    a = baseline_mean**2 - t_critical**2 * baseline_mean_variance
    d = candidate_mean**2 - t_critical**2 * candidate_mean_variance
    radicand = (baseline_mean * candidate_mean) ** 2 - a * d
    if a <= 0 or radicand < 0:
        return None
    center = baseline_mean * candidate_mean / a
    half_width = math.sqrt(radicand) / a
    return (center - half_width, center + half_width)


def suite_ratio(
    file_cells: Sequence[tuple[CellSummary, CellSummary]],
) -> RatioSummary:
    if not file_cells:
        return RatioSummary(None, None, None, "no files")
    for baseline, candidate in file_cells:
        if not baseline.ok:
            return RatioSummary(None, None, None, baseline.issue or "baseline unavailable")
        if not candidate.ok:
            return RatioSummary(None, None, None, candidate.issue or "candidate unavailable")
    sample_count = len(file_cells[0][0].samples)
    if sample_count < 1:
        return RatioSummary(None, None, None, "no samples")
    if any(len(b.samples) != sample_count or len(c.samples) != sample_count for b, c in file_cells):
        return RatioSummary(None, None, None, "sample counts differ")

    baseline_means = [float(np.mean(b.samples)) for b, _ in file_cells]
    candidate_means = [float(np.mean(c.samples)) for _, c in file_cells]
    baseline_sum = float(sum(baseline_means))
    candidate_sum = float(sum(candidate_means))
    if baseline_sum <= 0:
        return RatioSummary(None, None, None, "baseline mean is not positive")
    point = candidate_sum / baseline_sum
    if sample_count < 2:
        return RatioSummary(point, None, None, "CI undefined for n < 2")

    baseline_variance = sum(float(np.var(b.samples, ddof=1)) / sample_count for b, _ in file_cells)
    candidate_variance = sum(float(np.var(c.samples, ddof=1)) / sample_count for _, c in file_cells)
    interval = fieller_interval(
        baseline_sum,
        candidate_sum,
        baseline_variance,
        candidate_variance,
        df=sample_count - 1,
    )
    if interval is None:
        return RatioSummary(point, None, None, "Fieller interval undefined")
    return RatioSummary(point, interval[0], interval[1], None)


def geometric_mean_ratio(file_cells: Sequence[tuple[CellSummary, CellSummary]]) -> RatioSummary:
    ratios: list[float] = []
    for baseline, candidate in file_cells:
        if not baseline.ok:
            return RatioSummary(None, None, None, baseline.issue or "baseline unavailable")
        if not candidate.ok:
            return RatioSummary(None, None, None, candidate.issue or "candidate unavailable")
        if baseline.mean is None or candidate.mean is None or baseline.mean <= 0:
            return RatioSummary(None, None, None, "mean unavailable")
        ratios.append(candidate.mean / baseline.mean)
    if not ratios:
        return RatioSummary(None, None, None, "no files")
    return RatioSummary(float(math.exp(sum(math.log(value) for value in ratios) / len(ratios))), None, None, None)


def target_cell_summaries(
    rows: DataFrame[ReportFrame],
    target: ResolvedTarget,
    spec: BenchmarkSpec,
    treatments: Sequence[Treatment] | None = None,
    *,
    validate: bool = True,
) -> CellMap:
    chosen_treatments = spec.treatments if treatments is None else treatments
    return {
        (file_spec.sha256, treatment): summarize_cell(
            selected_rows(
                rows,
                estimate_key_for(target, file_spec, treatment, spec.timeout_sec),
                spec.rounds,
                validate=validate,
            ),
            spec.rounds,
        )
        for file_spec in spec.files
        for treatment in chosen_treatments
    }


def target_rss_cell_summaries(
    rows: DataFrame[ReportFrame],
    target: ResolvedTarget,
    spec: BenchmarkSpec,
    treatments: Sequence[Treatment] | None = None,
    *,
    validate: bool = True,
) -> CellMap:
    chosen_treatments = spec.treatments if treatments is None else treatments
    return {
        (file_spec.sha256, treatment): summarize_rss_cell(
            selected_rows(
                rows,
                estimate_key_for(target, file_spec, treatment, spec.timeout_sec),
                spec.rounds,
                validate=validate,
            ),
            spec.rounds,
        )
        for file_spec in spec.files
        for treatment in chosen_treatments
    }


def target_suite_treatment_ratio(
    baseline_cells: CellMap,
    candidate_cells: CellMap,
    spec: BenchmarkSpec,
    treatment: Treatment,
) -> RatioSummary:
    return suite_ratio(
        [
            (
                baseline_cells[(file_spec.sha256, treatment)],
                candidate_cells[(file_spec.sha256, treatment)],
            )
            for file_spec in spec.files
        ]
    )


def treatment_file_cells(
    cell_map: CellMap,
    spec: BenchmarkSpec,
    baseline_treatment: Treatment,
    candidate_treatment: Treatment,
) -> list[tuple[FileSpec, CellSummary, CellSummary]]:
    return [
        (
            file_spec,
            cell_map[(file_spec.sha256, baseline_treatment)],
            cell_map[(file_spec.sha256, candidate_treatment)],
        )
        for file_spec in spec.files
    ]


def target_treatment_file_cells(
    baseline_cells: CellMap,
    candidate_cells: CellMap,
    spec: BenchmarkSpec,
    treatment: Treatment,
) -> list[tuple[FileSpec, CellSummary, CellSummary]]:
    return [
        (
            file_spec,
            baseline_cells[(file_spec.sha256, treatment)],
            candidate_cells[(file_spec.sha256, treatment)],
        )
        for file_spec in spec.files
    ]


def ratio_pairs(file_cells: Sequence[tuple[FileSpec, CellSummary, CellSummary]]) -> list[tuple[FileSpec, RatioSummary]]:
    return [(file_spec, ratio_summary(baseline, candidate)) for file_spec, baseline, candidate in file_cells]


def summary_pairs(
    file_cells: Sequence[tuple[FileSpec, CellSummary, CellSummary]],
) -> list[tuple[CellSummary, CellSummary]]:
    return [(baseline, candidate) for _, baseline, candidate in file_cells]


def worst_file_ratio(ratios: Sequence[tuple[FileSpec, RatioSummary]]) -> tuple[FileSpec | None, RatioSummary]:
    if not ratios:
        return (None, RatioSummary(None, None, None, "no files"))
    invalid = [(file_spec, ratio) for file_spec, ratio in ratios if ratio.point is None]
    if invalid:
        return invalid[0]
    valid = [(file_spec, ratio) for file_spec, ratio in ratios if ratio.point is not None]
    return max(valid, key=lambda item: item[1].point or 0.0)


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


def format_seconds_summary(summary: CellSummary) -> str:
    return format_estimate_or_interval(summary.mean, summary.ci_low, summary.ci_high, "s", 4)


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
    if unit == "B":
        return f"{int(amount)} B"
    return f"{amount:.1f} {unit}"


def format_bytes_summary(summary: CellSummary) -> str:
    if summary.mean is None:
        return "-"
    point_text = format_bytes(summary.mean)
    if summary.ci_low is None or summary.ci_high is None:
        return point_text
    return f"[{format_bytes(summary.ci_low)}, {format_bytes(summary.ci_high)}]"


def format_ratio_summary(summary: RatioSummary) -> str:
    return format_estimate_or_interval(summary.point, summary.ci_low, summary.ci_high, "x", 3)


def format_wall_time_change(summary: RatioSummary) -> str:
    return format_percent_change(summary)


def format_percent_change(summary: RatioSummary) -> str:
    point = None if summary.point is None else (summary.point - 1.0) * 100.0
    low = None if summary.ci_low is None else (summary.ci_low - 1.0) * 100.0
    high = None if summary.ci_high is None else (summary.ci_high - 1.0) * 100.0
    return format_estimate_or_interval(point, low, high, "%", 1)


def format_worst_file(file_spec: FileSpec | None) -> str:
    return "-" if file_spec is None else file_spec.display_path


def comparison_result(summary: RatioSummary) -> str:
    if summary.point is None:
        return "invalid"
    if summary.ci_low is None or summary.ci_high is None:
        return "point only"
    if summary.ci_high < 1:
        return "faster"
    if summary.ci_low > 1:
        return "slower"
    return "unclear"


def lower_is_better_result(summary: RatioSummary) -> str:
    if summary.point is None:
        return "invalid"
    if summary.ci_low is None or summary.ci_high is None:
        return "point only"
    if summary.ci_high < 1:
        return "less"
    if summary.ci_low > 1:
        return "more"
    return "unclear"


def proof_gate_result(summary: RatioSummary) -> tuple[str, str]:
    if summary.point is None:
        return ("invalid", f"invalid: {summary.issue or 'unavailable'}")
    if summary.ci_high is None:
        return ("point only", "point only")
    if summary.ci_high < 2:
        return ("established", "<2x established")
    return ("not established", "<2x not established")


def ratio_specs(treatments: Sequence[Treatment]) -> tuple[tuple[Treatment, Treatment, str], ...]:
    specs: list[tuple[Treatment, Treatment, str]] = []
    if "off" in treatments and "term" in treatments:
        specs.append(("off", "term", "term/off"))
    if "off" in treatments and "proofs" in treatments:
        specs.append(("off", "proofs", "proofs/off"))
    if "term" in treatments and "proofs" in treatments:
        specs.append(("term", "proofs", "proofs/term"))
    return tuple(specs)
