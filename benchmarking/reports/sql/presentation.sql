-- Stable renderer-facing relations over the singleton comparison scope.

CREATE TEMP VIEW presentation_endpoints AS
SELECT
    endpoint_order,
    endpoint_role,
    target_label,
    target_git_sha,
    target_is_dirty,
    binary_sha256,
    backend,
    treatment
FROM selected_endpoints;

CREATE TEMP VIEW presentation_summary AS
SELECT
    summary.summary_order,
    summary.metric,
    summary.summary_kind,
    summary.file_order,
    summary.point,
    summary.ci_low,
    summary.ci_high,
    summary.result_class,
    summary.issue
FROM comparison_summary AS summary;

CREATE TEMP VIEW presentation_files AS
SELECT
    comparisons.file_order,
    comparisons.metric_order,
    files.file_path,
    comparisons.metric,
    comparisons.baseline_mean,
    comparisons.baseline_ci_low,
    comparisons.baseline_ci_high,
    comparisons.candidate_mean,
    comparisons.candidate_ci_low,
    comparisons.candidate_ci_high,
    comparisons.point,
    comparisons.ci_low,
    comparisons.ci_high,
    comparisons.result_class,
    comparisons.issue
FROM file_metric_comparisons AS comparisons
JOIN selected_files AS files USING (file_order);

CREATE TEMP VIEW presentation_phases AS
SELECT
    comparisons.file_order,
    files.file_path,
    comparisons.phase_order,
    comparisons.phase,
    comparisons.baseline_ns,
    comparisons.candidate_ns,
    comparisons.delta_ns,
    comparisons.point
FROM phase_comparisons AS comparisons
JOIN selected_files AS files USING (file_order);

CREATE TEMP VIEW presentation_rulesets AS
SELECT
    comparisons.file_order,
    files.file_path,
    comparisons.ruleset_rank,
    comparisons.ruleset_count,
    comparisons.name,
    comparisons.baseline_total_ns,
    comparisons.candidate_total_ns,
    comparisons.delta_ns,
    comparisons.point
FROM ruleset_comparisons AS comparisons
JOIN selected_files AS files USING (file_order)
WHERE comparisons.ruleset_rank <= 10;
