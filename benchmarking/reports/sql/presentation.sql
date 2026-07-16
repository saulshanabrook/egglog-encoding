-- Presentation table macros keep stable output contracts for arbitrary typed
-- scopes. Analysis owns every statistical classification, ranking, and
-- derived timing value; these macros only project them and attach labels.
CREATE MACRO presentation_targets(requested_scope report_scope_t) AS TABLE
SELECT *
FROM scoped_target_metadata(requested_scope);

-- These two passthroughs deliberately keep all UI entry points under one
-- presentation_* namespace instead of making users mix scope_* and output
-- names when joining coordinates to labels.
CREATE MACRO presentation_files(requested_scope report_scope_t) AS TABLE
SELECT *
FROM scope_files(requested_scope);

CREATE MACRO presentation_cells(requested_scope report_scope_t) AS TABLE
SELECT *
FROM scope_cells(requested_scope);

CREATE MACRO presentation_cell_estimates(requested_scope report_scope_t) AS TABLE
SELECT
    summaries.metric_order,
    summaries.target_order,
    summaries.file_order,
    summaries.cell_order,
    summaries.metric,
    cells.backend,
    cells.treatment,
    summaries.sample_count,
    summaries.has_samples,
    summaries.mean,
    summaries.ci_low,
    summaries.ci_high,
    summaries.result_class,
    summaries.issue
FROM scoped_cell_summaries(requested_scope) AS summaries
JOIN scope_cells(requested_scope) AS cells USING (cell_order);

CREATE MACRO presentation_file_ratios(requested_scope report_scope_t) AS TABLE
SELECT
    comparison_order,
    metric_order,
    file_order,
    metric,
    baseline_target_order,
    baseline_cell_order,
    candidate_target_order,
    candidate_cell_order,
    baseline_sample_count,
    candidate_sample_count,
    has_samples,
    point,
    ci_low,
    ci_high,
    change_fraction,
    change_ci_low,
    change_ci_high,
    is_valid,
    ci_entirely_below_one,
    ci_entirely_above_one,
    result_class,
    issue
FROM scoped_file_ratios(requested_scope);

CREATE MACRO presentation_comparison_rollups(requested_scope report_scope_t) AS TABLE
SELECT
    comparison_order,
    metric_order,
    metric,
    baseline_target_order,
    baseline_cell_order,
    candidate_target_order,
    candidate_cell_order,
    baseline_total,
    candidate_total,
    has_samples,
    suite_point,
    suite_ci_low,
    suite_ci_high,
    suite_change_fraction,
    suite_change_ci_low,
    suite_change_ci_high,
    suite_ci_entirely_below_two,
    suite_result_class,
    suite_issue,
    geometric_mean_point,
    geometric_mean_change_fraction,
    geometric_mean_result_class,
    geometric_mean_issue,
    file_count,
    comparable_file_count,
    better_file_count,
    best_file_order,
    best_point,
    best_ci_low,
    best_ci_high,
    best_change_fraction,
    best_result_class,
    best_issue,
    worst_file_order,
    worst_point,
    worst_ci_low,
    worst_ci_high,
    worst_change_fraction,
    worst_result_class,
    worst_issue
FROM scoped_comparison_rollups(requested_scope);

CREATE MACRO presentation_compact_timings(requested_scope report_scope_t) AS TABLE
SELECT
    timings.target_order,
    timings.file_order,
    timings.cell_order,
    cells.backend,
    cells.treatment,
    timings.search_ns,
    timings.apply_ns,
    timings.search_and_apply_ns,
    timings.unattributed_ns,
    timings.pre_merge_ns,
    timings.merge_ns,
    timings.rebuild_ns,
    timings.ruleset_total_ns,
    timings.outside_rulesets_ns,
    timings.other_ns,
    timings.wall_ns,
    timings.has_samples,
    timings.result_class,
    timings.issue
FROM scoped_timing_summaries(requested_scope) AS timings
JOIN scope_cells(requested_scope) AS cells USING (cell_order);

CREATE MACRO presentation_ruleset_timings(requested_scope report_scope_t) AS TABLE
SELECT
    timings.file_order,
    timings.cell_order,
    timings.ruleset_order,
    timings.target_order,
    cells.backend,
    cells.treatment,
    timings.name,
    timings.search_ns,
    timings.apply_ns,
    timings.search_and_apply_ns,
    timings.unattributed_ns,
    timings.pre_merge_ns,
    timings.merge_ns,
    timings.rebuild_ns,
    timings.total_ns,
    timings.maximum_target_total,
    timings.result_ruleset_total_ns,
    timings.has_samples,
    timings.result_class,
    timings.ruleset_share
FROM scoped_ruleset_timings(requested_scope) AS timings
JOIN scope_cells(requested_scope) AS cells USING (cell_order);

-- The CLI and DuckDB UI use ordinary, discoverable views over the one current
-- scope. A caller can invoke the same-named macro with another report_scope_t
-- to recompute without mutating this state or using session variables.
CREATE VIEW presentation_targets AS
FROM presentation_targets(
    (SELECT scope FROM current_report_scope WHERE singleton)
);

CREATE VIEW presentation_files AS
FROM presentation_files(
    (SELECT scope FROM current_report_scope WHERE singleton)
);

CREATE VIEW presentation_cells AS
FROM presentation_cells(
    (SELECT scope FROM current_report_scope WHERE singleton)
);

CREATE VIEW presentation_cell_estimates AS
FROM presentation_cell_estimates(
    (SELECT scope FROM current_report_scope WHERE singleton)
);

CREATE VIEW presentation_file_ratios AS
FROM presentation_file_ratios(
    (SELECT scope FROM current_report_scope WHERE singleton)
);

CREATE VIEW presentation_comparison_rollups AS
FROM presentation_comparison_rollups(
    (SELECT scope FROM current_report_scope WHERE singleton)
);

CREATE VIEW presentation_compact_timings AS
FROM presentation_compact_timings(
    (SELECT scope FROM current_report_scope WHERE singleton)
);

CREATE VIEW presentation_ruleset_timings AS
FROM presentation_ruleset_timings(
    (SELECT scope FROM current_report_scope WHERE singleton)
);
