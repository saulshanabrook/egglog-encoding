-- Keep the supported metrics and their stable output order in one relation.
CREATE VIEW report_metrics AS
SELECT *
FROM (
    VALUES
        (0::UTINYINT, 'wall_sec'),
        (1::UTINYINT, 'max_rss_bytes')
) AS metrics(metric_order, metric);

-- Historical collection estimates need only one aggregate per exact cache key.
-- Fresh observations update these count/sum pairs in Python without retaining
-- every old sample in memory.
CREATE VIEW historical_process_estimates AS
SELECT
    binary_sha256,
    file_sha256,
    fact_directory_sha256,
    backend,
    treatment,
    timeout_sec,
    count(*)::UBIGINT AS sample_count,
    sum(wall_sec) AS total_wall_sec
FROM report_rows
WHERE status = 'success' AND wall_sec IS NOT NULL
GROUP BY ALL;

-- Stable target roles are report facts shared by Rich and Markdown renderers.
CREATE VIEW scoped_target_metadata AS
SELECT
    target_order,
    CASE
        WHEN count(*) OVER () = 1 THEN 'target'
        WHEN target_order = 0 THEN 'baseline'
        ELSE 'candidate'
    END AS target_role,
    target_label,
    target_source,
    target_path,
    target_git_ref,
    target_git_sha,
    target_is_dirty,
    binary_sha256
FROM scope_targets;

-- Select the latest requested observations per target occurrence and cell,
-- breaking equal timestamps by their append order in JSONL.
CREATE VIEW scoped_observations AS
WITH ranked AS (
    SELECT
        targets.target_order,
        files.file_order,
        cells.cell_order,
        reports.row_index,
        reports.started_at,
        reports.status,
        reports.wall_sec,
        reports.max_rss_bytes,
        reports.timing_summary,
        row_number() OVER (
            PARTITION BY targets.target_order, files.file_order, cells.cell_order
            ORDER BY reports.started_at::TIMESTAMPTZ DESC, reports.row_index DESC
        ) AS selection_rank
    FROM scope_targets AS targets
    CROSS JOIN scope_files AS files
    CROSS JOIN scope_cells AS cells
    CROSS JOIN scope_parameters AS parameters
    JOIN report_rows AS reports
        ON reports.binary_sha256 = targets.binary_sha256
        AND reports.file_sha256 = files.file_sha256
        AND reports.fact_directory_sha256 = files.fact_directory_sha256
        AND reports.backend = cells.backend
        AND reports.treatment = cells.treatment
        AND reports.timeout_sec = parameters.timeout_sec
)
SELECT * EXCLUDE (selection_rank)
FROM ranked
WHERE selection_rank <= (SELECT rounds FROM scope_parameters);

-- Missing/failure/timeout precedence belongs to one result-level relation so
-- ordinary metrics and phase timing cannot classify the same cell differently.
CREATE VIEW scoped_result_statuses AS
WITH requested AS (
    SELECT
        targets.target_order,
        files.file_order,
        cells.cell_order
    FROM scope_targets AS targets
    CROSS JOIN scope_files AS files
    CROSS JOIN scope_cells AS cells
),
aggregated AS (
    SELECT
        requested.*,
        count(observations.row_index)::UINTEGER AS row_count,
        count(observations.row_index) FILTER (
            WHERE observations.status = 'timed-out'
        )::UINTEGER AS timed_out_count,
        count(observations.row_index) FILTER (
            WHERE observations.status = 'failure'
        )::UINTEGER AS failure_count,
        parameters.rounds
    FROM requested
    CROSS JOIN scope_parameters AS parameters
    LEFT JOIN scoped_observations AS observations USING (target_order, file_order, cell_order)
    GROUP BY ALL
)
SELECT
    target_order,
    file_order,
    cell_order,
    row_count,
    CASE
        WHEN row_count < rounds THEN 'missing ' || (rounds - row_count)::VARCHAR || ' row(s)'
        WHEN failure_count > 0 THEN 'failure row selected'
        WHEN timed_out_count > 0 THEN 'timeout row selected'
        ELSE NULL
    END AS issue
FROM aggregated;

-- Calculate both ordinary metrics together so sample counts,
-- variance-of-the-mean, and Student-t intervals share one implementation.
CREATE VIEW scoped_cell_summaries AS
WITH requested AS (
    SELECT
        targets.target_order,
        files.file_order,
        cells.cell_order,
        metrics.metric_order,
        metrics.metric
    FROM scope_targets AS targets
    CROSS JOIN scope_files AS files
    CROSS JOIN scope_cells AS cells
    CROSS JOIN report_metrics AS metrics
),
observed_metrics AS (
    SELECT
        observations.target_order,
        observations.file_order,
        observations.cell_order,
        observations.row_index,
        metrics.metric_order,
        metrics.metric,
        CASE metrics.metric
            WHEN 'wall_sec' THEN observations.wall_sec
            WHEN 'max_rss_bytes' THEN observations.max_rss_bytes::DOUBLE
        END AS metric_value
    FROM scoped_observations AS observations
    CROSS JOIN report_metrics AS metrics
),
aggregated AS (
    SELECT
        requested.*,
        count(observed.metric_value)::UINTEGER AS sample_count,
        avg(observed.metric_value) AS raw_mean,
        var_samp(observed.metric_value) AS sample_variance,
        parameters.t_critical_95
    FROM requested
    CROSS JOIN scope_parameters AS parameters
    LEFT JOIN observed_metrics AS observed
        ON observed.target_order = requested.target_order
        AND observed.file_order = requested.file_order
        AND observed.cell_order = requested.cell_order
        AND observed.metric = requested.metric
    GROUP BY ALL
),
classified AS (
    SELECT
        aggregated.*,
        statuses.row_count,
        CASE
            WHEN statuses.issue IS NOT NULL THEN statuses.issue
            WHEN aggregated.sample_count != statuses.row_count THEN
                CASE aggregated.metric
                    WHEN 'wall_sec' THEN 'missing wall_sec'
                    WHEN 'max_rss_bytes' THEN 'missing max_rss_bytes'
                END
            ELSE NULL
        END AS issue
    FROM aggregated
    JOIN scoped_result_statuses AS statuses USING (target_order, file_order, cell_order)
),
estimated AS (
    SELECT
        *,
        CASE WHEN issue IS NULL THEN raw_mean END AS mean,
        CASE
            WHEN issue IS NULL AND sample_count >= 2 THEN sample_variance / sample_count
        END AS var_mean,
        CASE
            WHEN issue IS NULL AND sample_count >= 2 THEN
                raw_mean - t_critical_95 * sqrt(sample_variance / sample_count)
        END AS ci_low,
        CASE
            WHEN issue IS NULL AND sample_count >= 2 THEN
                raw_mean + t_critical_95 * sqrt(sample_variance / sample_count)
        END AS ci_high
    FROM classified
)
SELECT
    metric_order,
    target_order,
    file_order,
    cell_order,
    metric,
    sample_count,
    sample_count > 0 AS has_samples,
    mean,
    var_mean,
    ci_low,
    ci_high,
    CASE
        WHEN issue IS NOT NULL OR mean IS NULL THEN 'invalid'
        WHEN ci_low IS NULL OR ci_high IS NULL THEN 'point_only'
        ELSE 'interval'
    END AS result_class,
    issue
FROM estimated;

-- A general target/cell pair represents target, treatment, and backend
-- comparisons without embedding presentation-specific comparison categories.
CREATE VIEW scoped_comparison_cells AS
SELECT
    comparisons.comparison_order,
    comparisons.baseline_target_order,
    comparisons.baseline_cell_order,
    comparisons.candidate_target_order,
    comparisons.candidate_cell_order,
    files.file_order,
    metrics.metric_order,
    metrics.metric,
    baseline.sample_count AS baseline_sample_count,
    baseline.mean AS baseline_mean,
    baseline.var_mean AS baseline_var_mean,
    baseline.issue AS baseline_issue,
    candidate.sample_count AS candidate_sample_count,
    candidate.mean AS candidate_mean,
    candidate.var_mean AS candidate_var_mean,
    candidate.issue AS candidate_issue,
    parameters.t_critical_95
FROM scope_comparisons AS comparisons
CROSS JOIN scope_files AS files
CROSS JOIN report_metrics AS metrics
CROSS JOIN scope_parameters AS parameters
JOIN scoped_cell_summaries AS baseline
    ON baseline.target_order = comparisons.baseline_target_order
    AND baseline.file_order = files.file_order
    AND baseline.cell_order = comparisons.baseline_cell_order
    AND baseline.metric = metrics.metric
JOIN scoped_cell_summaries AS candidate
    ON candidate.target_order = comparisons.candidate_target_order
    AND candidate.file_order = files.file_order
    AND candidate.cell_order = comparisons.candidate_cell_order
    AND candidate.metric = metrics.metric;

CREATE VIEW scoped_file_ratios AS
WITH preliminary AS (
    SELECT
        *,
        CASE
            WHEN baseline_issue IS NOT NULL THEN baseline_issue
            WHEN candidate_issue IS NOT NULL THEN candidate_issue
            WHEN baseline_mean <= 0 THEN 'baseline mean is not positive'
            ELSE NULL
        END AS preliminary_issue
    FROM scoped_comparison_cells
),
fieller AS (
    SELECT
        *,
        baseline_mean * baseline_mean - t_critical_95 * t_critical_95 * baseline_var_mean AS fieller_a,
        candidate_mean * candidate_mean - t_critical_95 * t_critical_95 * candidate_var_mean AS fieller_d
    FROM preliminary
),
calculated AS (
    SELECT
        *,
        (baseline_mean * candidate_mean) * (baseline_mean * candidate_mean) - fieller_a * fieller_d
            AS fieller_radicand
    FROM fieller
),
estimated AS (
    SELECT
        *,
        CASE WHEN preliminary_issue IS NULL THEN candidate_mean / baseline_mean END AS point,
        CASE
            WHEN preliminary_issue IS NULL
                AND baseline_sample_count >= 2
                AND fieller_a > 0
                AND fieller_radicand >= 0 THEN
                baseline_mean * candidate_mean / fieller_a - sqrt(fieller_radicand) / fieller_a
        END AS ci_low,
        CASE
            WHEN preliminary_issue IS NULL
                AND baseline_sample_count >= 2
                AND fieller_a > 0
                AND fieller_radicand >= 0 THEN
                baseline_mean * candidate_mean / fieller_a + sqrt(fieller_radicand) / fieller_a
        END AS ci_high,
        CASE
            WHEN preliminary_issue IS NOT NULL THEN preliminary_issue
            WHEN baseline_sample_count < 2 THEN 'CI undefined for n < 2'
            WHEN fieller_a <= 0 OR fieller_radicand < 0 THEN 'Fieller interval undefined'
            ELSE NULL
        END AS issue
    FROM calculated
)
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
    baseline_sample_count > 0 OR candidate_sample_count > 0 AS has_samples,
    point,
    ci_low,
    ci_high,
    point - 1.0 AS change_fraction,
    ci_low - 1.0 AS change_ci_low,
    ci_high - 1.0 AS change_ci_high,
    point IS NOT NULL AS is_valid,
    ci_high IS NOT NULL AND ci_high < 1.0 AS ci_entirely_below_one,
    ci_low IS NOT NULL AND ci_low > 1.0 AS ci_entirely_above_one,
    CASE
        WHEN point IS NULL THEN 'invalid'
        WHEN ci_low IS NULL OR ci_high IS NULL THEN 'point_only'
        WHEN ci_high < 1.0 THEN 'lower'
        WHEN ci_low > 1.0 THEN 'higher'
        ELSE 'unclear'
    END AS result_class,
    issue
FROM estimated;

-- Suite ratios sum fixed-file means and their independent variances. Equal-file
-- geometric means remain a separate descriptive aggregate without an interval.
CREATE VIEW scoped_suite_ratios AS
WITH aggregated AS (
    SELECT
        comparison_order,
        first(metric_order) AS metric_order,
        metric,
        first(baseline_target_order) AS baseline_target_order,
        first(baseline_cell_order) AS baseline_cell_order,
        first(candidate_target_order) AS candidate_target_order,
        first(candidate_cell_order) AS candidate_cell_order,
        count(*)::UINTEGER AS file_count,
        first(
            CASE
                WHEN baseline_issue IS NOT NULL THEN baseline_issue
                WHEN candidate_issue IS NOT NULL THEN candidate_issue
            END
            ORDER BY file_order
        ) FILTER (WHERE baseline_issue IS NOT NULL OR candidate_issue IS NOT NULL) AS first_cell_issue,
        first(baseline_sample_count ORDER BY file_order)::UINTEGER AS sample_count,
        sum(baseline_mean) AS baseline_sum,
        sum(candidate_mean) AS candidate_sum,
        bool_or(baseline_issue IS NOT NULL OR baseline_mean IS NULL) AS baseline_total_unavailable,
        bool_or(candidate_issue IS NOT NULL OR candidate_mean IS NULL) AS candidate_total_unavailable,
        bool_or(baseline_sample_count > 0 OR candidate_sample_count > 0) AS has_samples,
        sum(baseline_var_mean) AS baseline_variance,
        sum(candidate_var_mean) AS candidate_variance,
        max(t_critical_95) AS t_critical_95,
        exp(
            avg(
                CASE
                    WHEN baseline_mean > 0 AND candidate_mean > 0 THEN ln(candidate_mean / baseline_mean)
                END
            )
        ) AS geometric_mean_point,
        bool_or(
            baseline_mean IS NULL
            OR candidate_mean IS NULL
            OR baseline_mean <= 0
            OR candidate_mean <= 0
        ) AS geometric_mean_unavailable
    FROM scoped_comparison_cells
    GROUP BY comparison_order, metric
),
preliminary AS (
    SELECT
        *,
        CASE
            WHEN first_cell_issue IS NOT NULL THEN first_cell_issue
            WHEN baseline_sum <= 0 THEN 'baseline mean is not positive'
            ELSE NULL
        END AS suite_preliminary_issue,
        CASE
            WHEN first_cell_issue IS NOT NULL THEN first_cell_issue
            WHEN geometric_mean_unavailable THEN 'mean unavailable'
            ELSE NULL
        END AS geometric_mean_issue
    FROM aggregated
),
fieller AS (
    SELECT
        *,
        baseline_sum * baseline_sum - t_critical_95 * t_critical_95 * baseline_variance AS fieller_a,
        candidate_sum * candidate_sum - t_critical_95 * t_critical_95 * candidate_variance AS fieller_d
    FROM preliminary
),
calculated AS (
    SELECT
        *,
        (baseline_sum * candidate_sum) * (baseline_sum * candidate_sum) - fieller_a * fieller_d
            AS fieller_radicand
    FROM fieller
),
estimated AS (
    SELECT
        *,
        CASE WHEN suite_preliminary_issue IS NULL THEN candidate_sum / baseline_sum END AS suite_point,
        CASE
            WHEN suite_preliminary_issue IS NULL
                AND sample_count >= 2
                AND fieller_a > 0
                AND fieller_radicand >= 0 THEN
                baseline_sum * candidate_sum / fieller_a - sqrt(fieller_radicand) / fieller_a
        END AS suite_ci_low,
        CASE
            WHEN suite_preliminary_issue IS NULL
                AND sample_count >= 2
                AND fieller_a > 0
                AND fieller_radicand >= 0 THEN
                baseline_sum * candidate_sum / fieller_a + sqrt(fieller_radicand) / fieller_a
        END AS suite_ci_high,
        CASE
            WHEN suite_preliminary_issue IS NOT NULL THEN suite_preliminary_issue
            WHEN sample_count < 2 THEN 'CI undefined for n < 2'
            WHEN fieller_a <= 0 OR fieller_radicand < 0 THEN 'Fieller interval undefined'
            ELSE NULL
        END AS suite_issue
    FROM calculated
)
SELECT
    comparison_order,
    metric_order,
    metric,
    baseline_target_order,
    baseline_cell_order,
    candidate_target_order,
    candidate_cell_order,
    CASE WHEN baseline_total_unavailable THEN NULL ELSE baseline_sum END AS baseline_total,
    CASE WHEN candidate_total_unavailable THEN NULL ELSE candidate_sum END AS candidate_total,
    has_samples,
    suite_point,
    suite_ci_low,
    suite_ci_high,
    suite_point - 1.0 AS suite_change_fraction,
    suite_ci_low - 1.0 AS suite_change_ci_low,
    suite_ci_high - 1.0 AS suite_change_ci_high,
    suite_ci_high IS NOT NULL AND suite_ci_high < 2.0 AS suite_ci_entirely_below_two,
    CASE
        WHEN suite_point IS NULL THEN 'invalid'
        WHEN suite_ci_low IS NULL OR suite_ci_high IS NULL THEN 'point_only'
        WHEN suite_ci_high < 1.0 THEN 'lower'
        WHEN suite_ci_low > 1.0 THEN 'higher'
        ELSE 'unclear'
    END AS suite_result_class,
    suite_issue,
    CASE WHEN geometric_mean_issue IS NULL THEN geometric_mean_point END AS geometric_mean_point,
    CASE WHEN geometric_mean_issue IS NULL THEN geometric_mean_point - 1.0 END AS geometric_mean_change_fraction,
    CASE WHEN geometric_mean_issue IS NULL THEN 'available' ELSE 'invalid' END AS geometric_mean_result_class,
    geometric_mean_issue,
    file_count
FROM estimated;

-- One decision-oriented row per comparison and metric. Best prefers the
-- smallest valid point estimate; worst reports the first invalid file when
-- one exists, otherwise the largest point estimate. Ties use file_order.
CREATE VIEW scoped_comparison_rollups AS
WITH ranked_files AS (
    SELECT
        ratios.*,
        row_number() OVER (
            PARTITION BY ratios.comparison_order, ratios.metric
            ORDER BY ratios.point IS NULL, ratios.point ASC NULLS LAST, ratios.file_order
        ) AS best_rank,
        row_number() OVER (
            PARTITION BY ratios.comparison_order, ratios.metric
            ORDER BY ratios.point IS NOT NULL, ratios.point DESC NULLS LAST, ratios.file_order
        ) AS worst_rank
    FROM scoped_file_ratios AS ratios
),
file_facts AS (
    SELECT
        comparison_order,
        metric,
        count(point)::UINTEGER AS comparable_file_count,
        count(*) FILTER (WHERE ci_high IS NOT NULL AND ci_high < 1.0)::UINTEGER AS better_file_count,
        max(file_order) FILTER (WHERE best_rank = 1)::UINTEGER AS best_file_order,
        max(point) FILTER (WHERE best_rank = 1) AS best_point,
        max(ci_low) FILTER (WHERE best_rank = 1) AS best_ci_low,
        max(ci_high) FILTER (WHERE best_rank = 1) AS best_ci_high,
        max(result_class) FILTER (WHERE best_rank = 1) AS best_result_class,
        max(issue) FILTER (WHERE best_rank = 1) AS best_issue,
        max(file_order) FILTER (WHERE worst_rank = 1)::UINTEGER AS worst_file_order,
        max(point) FILTER (WHERE worst_rank = 1) AS worst_point,
        max(ci_low) FILTER (WHERE worst_rank = 1) AS worst_ci_low,
        max(ci_high) FILTER (WHERE worst_rank = 1) AS worst_ci_high,
        max(result_class) FILTER (WHERE worst_rank = 1) AS worst_result_class,
        max(issue) FILTER (WHERE worst_rank = 1) AS worst_issue
    FROM ranked_files
    GROUP BY comparison_order, metric
)
SELECT
    suites.comparison_order,
    suites.metric_order,
    suites.metric,
    suites.baseline_target_order,
    suites.baseline_cell_order,
    suites.candidate_target_order,
    suites.candidate_cell_order,
    suites.baseline_total,
    suites.candidate_total,
    suites.has_samples,
    suites.suite_point,
    suites.suite_ci_low,
    suites.suite_ci_high,
    suites.suite_change_fraction,
    suites.suite_change_ci_low,
    suites.suite_change_ci_high,
    suites.suite_ci_entirely_below_two,
    suites.suite_result_class,
    suites.suite_issue,
    suites.geometric_mean_point,
    suites.geometric_mean_change_fraction,
    suites.geometric_mean_result_class,
    suites.geometric_mean_issue,
    suites.file_count,
    files.comparable_file_count,
    files.better_file_count,
    files.best_file_order,
    files.best_point,
    files.best_ci_low,
    files.best_ci_high,
    files.best_point - 1.0 AS best_change_fraction,
    files.best_result_class,
    files.best_issue,
    files.worst_file_order,
    files.worst_point,
    files.worst_ci_low,
    files.worst_ci_high,
    files.worst_point - 1.0 AS worst_change_fraction,
    files.worst_result_class,
    files.worst_issue
FROM scoped_suite_ratios AS suites
JOIN file_facts AS files USING (comparison_order, metric);

-- Compact components sum each observation's rulesets before averaging,
-- preserving the same arithmetic-mean population used for ordinary wall time.
-- ``other_ns`` deliberately folds the pre-merge residual into the compact
-- Other column; ``outside_rulesets_ns`` exposes only time beyond full ruleset
-- totals for deeper queries.
CREATE VIEW scoped_timing_summaries AS
WITH observation_phases AS (
    SELECT
        observations.target_order,
        observations.file_order,
        observations.cell_order,
        observations.row_index,
        observations.wall_sec,
        coalesce(list_sum(list_transform(
            observations.timing_summary.rulesets,
            item -> item.search_ns
        )), 0)::DOUBLE AS search_ns,
        coalesce(list_sum(list_transform(
            observations.timing_summary.rulesets,
            item -> item.apply_ns
        )), 0)::DOUBLE AS apply_ns,
        coalesce(list_sum(list_transform(
            observations.timing_summary.rulesets,
            item -> item.unattributed_ns
        )), 0)::DOUBLE AS unattributed_ns,
        coalesce(list_sum(list_transform(
            observations.timing_summary.rulesets,
            item -> item.merge_ns
        )), 0)::DOUBLE AS merge_ns,
        coalesce(list_sum(list_transform(
            observations.timing_summary.rulesets,
            item -> item.rebuild_ns
        )), 0)::DOUBLE AS rebuild_ns
    FROM scoped_observations AS observations
),
aggregated AS (
    SELECT
        statuses.target_order,
        statuses.file_order,
        statuses.cell_order,
        statuses.issue,
        avg(observed.wall_sec) * 1000000000.0 AS wall_ns,
        avg(observed.search_ns) AS search_ns,
        avg(observed.apply_ns) AS apply_ns,
        avg(observed.unattributed_ns) AS unattributed_ns,
        avg(observed.merge_ns) AS merge_ns,
        avg(observed.rebuild_ns) AS rebuild_ns
    FROM scoped_result_statuses AS statuses
    LEFT JOIN observation_phases AS observed USING (target_order, file_order, cell_order)
    GROUP BY ALL
),
derived AS (
    SELECT
        *,
        search_ns + apply_ns AS search_and_apply_ns,
        search_ns + apply_ns + unattributed_ns AS pre_merge_ns,
        search_ns + apply_ns + unattributed_ns + merge_ns + rebuild_ns AS ruleset_total_ns
    FROM aggregated
)
SELECT
    target_order,
    file_order,
    cell_order,
    CASE WHEN issue IS NULL THEN search_ns END AS search_ns,
    CASE WHEN issue IS NULL THEN apply_ns END AS apply_ns,
    CASE WHEN issue IS NULL THEN search_and_apply_ns END AS search_and_apply_ns,
    CASE WHEN issue IS NULL THEN unattributed_ns END AS unattributed_ns,
    CASE WHEN issue IS NULL THEN pre_merge_ns END AS pre_merge_ns,
    CASE WHEN issue IS NULL THEN merge_ns END AS merge_ns,
    CASE WHEN issue IS NULL THEN rebuild_ns END AS rebuild_ns,
    CASE WHEN issue IS NULL THEN ruleset_total_ns END AS ruleset_total_ns,
    CASE WHEN issue IS NULL THEN wall_ns - ruleset_total_ns END AS outside_rulesets_ns,
    CASE
        WHEN issue IS NULL
        THEN wall_ns - search_ns - apply_ns - merge_ns - rebuild_ns
    END AS other_ns,
    CASE WHEN issue IS NULL THEN wall_ns END AS wall_ns,
    issue IS NULL AND wall_ns IS NOT NULL AS has_samples,
    CASE WHEN issue IS NULL THEN 'available' ELSE 'invalid' END AS result_class,
    issue
FROM derived;

-- The ruleset union includes only fully valid selected results. A ruleset that
-- never appears for one target remains NULL in that target's aligned row. Once
-- it appears for a target, observations where it did not run contribute zero so
-- the mean still covers every selected observation rather than only active runs.
-- Totals, common ordering, and shares are semantic analysis rather than output
-- formatting, so the presentation view only adds backend/treatment labels.
CREATE VIEW scoped_ruleset_timings AS
WITH observation_rulesets AS (
    SELECT
        observations.target_order,
        observations.file_order,
        observations.cell_order,
        observations.row_index,
        ruleset.name,
        ruleset.search_ns::DOUBLE AS search_ns,
        ruleset.apply_ns::DOUBLE AS apply_ns,
        ruleset.unattributed_ns::DOUBLE AS unattributed_ns,
        ruleset.merge_ns::DOUBLE AS merge_ns,
        ruleset.rebuild_ns::DOUBLE AS rebuild_ns
    FROM scoped_observations AS observations
    JOIN scoped_timing_summaries AS valid_result
        ON valid_result.target_order = observations.target_order
        AND valid_result.file_order = observations.file_order
        AND valid_result.cell_order = observations.cell_order
        AND valid_result.issue IS NULL
    CROSS JOIN unnest(observations.timing_summary.rulesets) AS items(ruleset)
    WHERE observations.status = 'success'
),
ruleset_names AS (
    SELECT DISTINCT file_order, cell_order, name
    FROM observation_rulesets
),
target_means AS (
    SELECT
        targets.target_order,
        names.file_order,
        names.cell_order,
        names.name,
        count(values.row_index) > 0 AS has_samples,
        CASE
            WHEN count(values.row_index) > 0 THEN avg(coalesce(values.search_ns, 0))
        END AS search_ns,
        CASE
            WHEN count(values.row_index) > 0 THEN avg(coalesce(values.apply_ns, 0))
        END AS apply_ns,
        CASE
            WHEN count(values.row_index) > 0 THEN avg(coalesce(values.unattributed_ns, 0))
        END AS unattributed_ns,
        CASE
            WHEN count(values.row_index) > 0 THEN avg(coalesce(values.merge_ns, 0))
        END AS merge_ns,
        CASE
            WHEN count(values.row_index) > 0 THEN avg(coalesce(values.rebuild_ns, 0))
        END AS rebuild_ns
    FROM scope_targets AS targets
    JOIN ruleset_names AS names ON true
    JOIN scoped_timing_summaries AS valid_target
        ON valid_target.target_order = targets.target_order
        AND valid_target.file_order = names.file_order
        AND valid_target.cell_order = names.cell_order
        AND valid_target.issue IS NULL
    JOIN scoped_observations AS observations
        ON observations.target_order = targets.target_order
        AND observations.file_order = names.file_order
        AND observations.cell_order = names.cell_order
        AND observations.status = 'success'
    LEFT JOIN observation_rulesets AS values
        ON values.target_order = observations.target_order
        AND values.file_order = observations.file_order
        AND values.cell_order = observations.cell_order
        AND values.row_index = observations.row_index
        AND values.name = names.name
    GROUP BY targets.target_order, names.file_order, names.cell_order, names.name
),
phases AS (
    SELECT
        *,
        search_ns + apply_ns AS search_and_apply_ns,
        search_ns + apply_ns + unattributed_ns AS pre_merge_ns,
        search_ns + apply_ns + unattributed_ns + merge_ns + rebuild_ns AS total_ns
    FROM target_means
),
ordered AS (
    SELECT
        *,
        max(total_ns) OVER (PARTITION BY file_order, cell_order, name) AS maximum_target_total
    FROM phases
),
ranked AS (
    SELECT
        *,
        dense_rank() OVER (
            PARTITION BY file_order, cell_order
            ORDER BY maximum_target_total DESC, name
        ) - 1 AS ruleset_order
    FROM ordered
),
with_totals AS (
    SELECT
        *,
        sum(total_ns) OVER (
            PARTITION BY target_order, file_order, cell_order
        ) AS result_ruleset_total_ns
    FROM ranked
)
SELECT
    file_order,
    cell_order,
    ruleset_order::UINTEGER AS ruleset_order,
    target_order,
    name,
    search_ns,
    apply_ns,
    search_and_apply_ns,
    unattributed_ns,
    pre_merge_ns,
    merge_ns,
    rebuild_ns,
    total_ns,
    maximum_target_total,
    result_ruleset_total_ns,
    has_samples,
    'available' AS result_class,
    CASE
        WHEN result_ruleset_total_ns = 0 THEN NULL
        ELSE total_ns / result_ruleset_total_ns
    END AS ruleset_share
FROM with_totals;
