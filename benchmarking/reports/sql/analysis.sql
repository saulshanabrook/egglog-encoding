-- Statistical analysis for the one immutable baseline/candidate scope.

CREATE VIEW report_metrics AS
SELECT *
FROM (
    VALUES
        (0::UTINYINT, 'wall_sec'),
        (1::UTINYINT, 'max_rss_bytes')
) AS metrics(metric_order, metric);

CREATE VIEW report_phases AS
SELECT *
FROM (
    VALUES
        (0::UTINYINT, 'search'),
        (1::UTINYINT, 'apply'),
        (2::UTINYINT, 'merge'),
        (3::UTINYINT, 'rebuild'),
        (4::UTINYINT, 'other')
) AS phases(phase_order, phase);

-- Collection ETA data covers the complete cache rather than the installed
-- report scope.
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

CREATE VIEW selected_endpoints AS
WITH endpoints AS (
    SELECT
        0::UTINYINT AS endpoint_order,
        'baseline' AS endpoint_role,
        scope.baseline AS endpoint
    FROM current_report_scope
    WHERE singleton
    UNION ALL
    SELECT
        1::UTINYINT AS endpoint_order,
        'candidate' AS endpoint_role,
        scope.candidate AS endpoint
    FROM current_report_scope
    WHERE singleton
)
SELECT
    endpoint_order,
    endpoint_role,
    endpoint.binary_sha256,
    endpoint.target_label,
    endpoint.target_source,
    endpoint.target_path,
    endpoint.target_git_ref,
    endpoint.target_git_sha,
    endpoint.target_is_dirty,
    endpoint.backend,
    endpoint.treatment
FROM endpoints;

CREATE VIEW selected_files AS
SELECT
    (ordinality - 1)::UINTEGER AS file_order,
    file.file_sha256,
    file.fact_directory_sha256,
    file.file_path,
    file.absolute_file_path,
    file.fact_directory_path
FROM current_report_scope,
    unnest(scope.files) WITH ORDINALITY AS rows(file, ordinality)
WHERE singleton;

CREATE VIEW selected_parameters AS
SELECT
    scope.rounds AS rounds,
    scope.timeout_sec AS timeout_sec,
    scope.t_critical_95 AS t_critical_95
FROM current_report_scope
WHERE singleton;

-- Select the latest requested observations for each endpoint/file. Equal
-- timestamps are broken by physical JSONL order.
CREATE VIEW selected_observations AS
WITH ranked AS (
    SELECT
        endpoints.endpoint_order,
        files.file_order,
        reports.row_index,
        reports.started_at,
        reports.status,
        reports.wall_sec,
        reports.max_rss_bytes,
        reports.timing_summary,
        row_number() OVER (
            PARTITION BY endpoints.endpoint_order, files.file_order
            ORDER BY reports.started_at::TIMESTAMPTZ DESC, reports.row_index DESC
        ) AS selection_rank
    FROM selected_endpoints AS endpoints
    CROSS JOIN selected_files AS files
    CROSS JOIN selected_parameters AS parameters
    JOIN report_rows AS reports
        ON reports.binary_sha256 = endpoints.binary_sha256
        AND reports.file_sha256 = files.file_sha256
        AND reports.fact_directory_sha256 = files.fact_directory_sha256
        AND reports.backend = endpoints.backend
        AND reports.treatment = endpoints.treatment
        AND reports.timeout_sec = parameters.timeout_sec
)
SELECT * EXCLUDE (selection_rank)
FROM ranked
WHERE selection_rank <= (SELECT rounds FROM selected_parameters);

CREATE VIEW selected_result_statuses AS
WITH requested AS (
    SELECT endpoints.endpoint_order, files.file_order
    FROM selected_endpoints AS endpoints
    CROSS JOIN selected_files AS files
),
aggregated AS (
    SELECT
        requested.endpoint_order,
        requested.file_order,
        count(observations.row_index)::UINTEGER AS row_count,
        count(observations.row_index) FILTER (
            WHERE observations.status = 'timed-out'
        )::UINTEGER AS timed_out_count,
        count(observations.row_index) FILTER (
            WHERE observations.status = 'failure'
        )::UINTEGER AS failure_count,
        parameters.rounds
    FROM requested
    CROSS JOIN selected_parameters AS parameters
    LEFT JOIN selected_observations AS observations USING (endpoint_order, file_order)
    GROUP BY ALL
)
SELECT
    endpoint_order,
    file_order,
    row_count,
    CASE
        WHEN row_count < rounds THEN 'missing ' || (rounds - row_count)::VARCHAR || ' row(s)'
        WHEN failure_count > 0 THEN 'failure row selected'
        WHEN timed_out_count > 0 THEN 'timeout row selected'
        ELSE NULL
    END AS issue
FROM aggregated;

-- Absolute wall/RSS estimates share one implementation so their samples and
-- Student-t intervals cannot drift apart.
CREATE VIEW endpoint_metric_estimates AS
WITH requested AS (
    SELECT
        metrics.metric_order,
        endpoints.endpoint_order,
        files.file_order,
        metrics.metric
    FROM selected_endpoints AS endpoints
    CROSS JOIN selected_files AS files
    CROSS JOIN report_metrics AS metrics
),
observed AS (
    SELECT
        observations.endpoint_order,
        observations.file_order,
        observations.row_index,
        metrics.metric_order,
        metrics.metric,
        CASE metrics.metric
            WHEN 'wall_sec' THEN observations.wall_sec
            WHEN 'max_rss_bytes' THEN observations.max_rss_bytes::DOUBLE
        END AS metric_value
    FROM selected_observations AS observations
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
    CROSS JOIN selected_parameters AS parameters
    LEFT JOIN observed
        ON observed.endpoint_order = requested.endpoint_order
        AND observed.file_order = requested.file_order
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
                    WHEN 'wall_sec' THEN 'wall time unavailable'
                    WHEN 'max_rss_bytes' THEN 'peak RSS unavailable'
                END
            ELSE NULL
        END AS issue
    FROM aggregated
    JOIN selected_result_statuses AS statuses USING (endpoint_order, file_order)
)
SELECT
    metric_order,
    endpoint_order,
    file_order,
    metric,
    sample_count,
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
    END AS ci_high,
    issue
FROM classified;

CREATE VIEW file_metric_comparisons AS
WITH paired AS (
    SELECT
        baseline.metric_order,
        baseline.file_order,
        baseline.metric,
        baseline.sample_count AS baseline_sample_count,
        baseline.mean AS baseline_mean,
        baseline.var_mean AS baseline_var_mean,
        baseline.ci_low AS baseline_ci_low,
        baseline.ci_high AS baseline_ci_high,
        baseline.issue AS baseline_issue,
        candidate.sample_count AS candidate_sample_count,
        candidate.mean AS candidate_mean,
        candidate.var_mean AS candidate_var_mean,
        candidate.ci_low AS candidate_ci_low,
        candidate.ci_high AS candidate_ci_high,
        candidate.issue AS candidate_issue,
        parameters.t_critical_95,
        CASE
            WHEN baseline.issue IS NOT NULL THEN baseline.issue
            WHEN candidate.issue IS NOT NULL THEN candidate.issue
            WHEN baseline.mean <= 0 THEN 'baseline mean is not positive'
            ELSE NULL
        END AS preliminary_issue
    FROM endpoint_metric_estimates AS baseline
    JOIN endpoint_metric_estimates AS candidate
        ON candidate.file_order = baseline.file_order
        AND candidate.metric = baseline.metric
        AND candidate.endpoint_order = 1
    CROSS JOIN selected_parameters AS parameters
    WHERE baseline.endpoint_order = 0
),
fieller AS (
    SELECT
        *,
        baseline_mean * baseline_mean
            - t_critical_95 * t_critical_95 * baseline_var_mean AS fieller_a,
        candidate_mean * candidate_mean
            - t_critical_95 * t_critical_95 * candidate_var_mean AS fieller_d
    FROM paired
),
calculated AS (
    SELECT
        *,
        (baseline_mean * candidate_mean) * (baseline_mean * candidate_mean)
            - fieller_a * fieller_d AS fieller_radicand
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
    metric_order,
    file_order,
    metric,
    baseline_mean,
    baseline_ci_low,
    baseline_ci_high,
    candidate_mean,
    candidate_ci_low,
    candidate_ci_high,
    point,
    ci_low,
    ci_high,
    CASE
        WHEN point IS NULL THEN 'invalid'
        WHEN ci_low IS NULL OR ci_high IS NULL THEN 'point_only'
        WHEN ci_high < 1.0 THEN 'lower'
        WHEN ci_low > 1.0 THEN 'higher'
        ELSE 'unclear'
    END AS result_class,
    issue
FROM estimated;

-- The fixed-suite result applies only to wall time. Lowest/highest summaries
-- remain available from valid comparable files even when another file makes
-- the suite incomplete.
CREATE VIEW comparison_summary AS
WITH suite_aggregated AS (
    SELECT
        first(
            CASE
                WHEN baseline.issue IS NOT NULL THEN baseline.issue
                WHEN candidate.issue IS NOT NULL THEN candidate.issue
            END
            ORDER BY baseline.file_order
        ) FILTER (WHERE baseline.issue IS NOT NULL OR candidate.issue IS NOT NULL) AS first_issue,
        min(baseline.sample_count)::UINTEGER AS sample_count,
        sum(baseline.mean) AS baseline_total,
        sum(candidate.mean) AS candidate_total,
        sum(baseline.var_mean) AS baseline_variance,
        sum(candidate.var_mean) AS candidate_variance,
        max(parameters.t_critical_95) AS t_critical_95
    FROM endpoint_metric_estimates AS baseline
    JOIN endpoint_metric_estimates AS candidate
        ON candidate.file_order = baseline.file_order
        AND candidate.metric = baseline.metric
        AND candidate.endpoint_order = 1
    CROSS JOIN selected_parameters AS parameters
    WHERE baseline.endpoint_order = 0 AND baseline.metric = 'wall_sec'
),
suite_preliminary AS (
    SELECT
        *,
        CASE
            WHEN first_issue IS NOT NULL THEN first_issue
            WHEN baseline_total <= 0 THEN 'baseline mean is not positive'
            ELSE NULL
        END AS preliminary_issue,
        baseline_total * baseline_total
            - t_critical_95 * t_critical_95 * baseline_variance AS fieller_a,
        candidate_total * candidate_total
            - t_critical_95 * t_critical_95 * candidate_variance AS fieller_d
    FROM suite_aggregated
),
suite_calculated AS (
    SELECT
        *,
        (baseline_total * candidate_total) * (baseline_total * candidate_total)
            - fieller_a * fieller_d AS fieller_radicand
    FROM suite_preliminary
),
suite AS (
    SELECT
        CASE WHEN preliminary_issue IS NULL THEN candidate_total / baseline_total END AS point,
        CASE
            WHEN preliminary_issue IS NULL
                AND sample_count >= 2
                AND fieller_a > 0
                AND fieller_radicand >= 0 THEN
                baseline_total * candidate_total / fieller_a - sqrt(fieller_radicand) / fieller_a
        END AS ci_low,
        CASE
            WHEN preliminary_issue IS NULL
                AND sample_count >= 2
                AND fieller_a > 0
                AND fieller_radicand >= 0 THEN
                baseline_total * candidate_total / fieller_a + sqrt(fieller_radicand) / fieller_a
        END AS ci_high,
        CASE
            WHEN preliminary_issue IS NOT NULL THEN preliminary_issue
            WHEN sample_count < 2 THEN 'CI undefined for n < 2'
            WHEN fieller_a <= 0 OR fieller_radicand < 0 THEN 'Fieller interval undefined'
            ELSE NULL
        END AS issue
    FROM suite_calculated
),
ranked_files AS (
    SELECT
        comparisons.*,
        row_number() OVER (
            PARTITION BY metric
            ORDER BY point ASC, file_order ASC
        ) AS lowest_rank,
        row_number() OVER (
            PARTITION BY metric
            ORDER BY point DESC, file_order DESC
        ) AS highest_rank
    FROM file_metric_comparisons AS comparisons
    WHERE point IS NOT NULL
),
metric_issues AS (
    SELECT
        metric,
        first(issue ORDER BY file_order) FILTER (WHERE point IS NULL) AS first_issue
    FROM file_metric_comparisons
    GROUP BY metric
),
tail_specs AS (
    SELECT *
    FROM (
        VALUES
            (1::UTINYINT, 0::UTINYINT, 'wall_sec', 'lowest_file', 'lowest'),
            (2::UTINYINT, 0::UTINYINT, 'wall_sec', 'highest_file', 'highest'),
            (3::UTINYINT, 1::UTINYINT, 'max_rss_bytes', 'lowest_file', 'lowest'),
            (4::UTINYINT, 1::UTINYINT, 'max_rss_bytes', 'highest_file', 'highest')
    ) AS specs(summary_order, metric_order, metric, summary_kind, rank_kind)
),
tails AS (
    SELECT
        specs.summary_order,
        specs.metric_order,
        specs.metric,
        specs.summary_kind,
        selected.file_order,
        selected.point,
        selected.ci_low,
        selected.ci_high,
        coalesce(selected.result_class, 'invalid') AS result_class,
        CASE
            WHEN selected.file_order IS NOT NULL THEN selected.issue
            ELSE coalesce(issues.first_issue, 'no comparable files')
        END AS issue
    FROM tail_specs AS specs
    LEFT JOIN ranked_files AS selected
        ON selected.metric = specs.metric
        AND (
            (specs.rank_kind = 'lowest' AND selected.lowest_rank = 1)
            OR (specs.rank_kind = 'highest' AND selected.highest_rank = 1)
        )
    LEFT JOIN metric_issues AS issues ON issues.metric = specs.metric
)
SELECT
    0::UTINYINT AS summary_order,
    0::UTINYINT AS metric_order,
    'wall_sec' AS metric,
    'suite' AS summary_kind,
    NULL::UINTEGER AS file_order,
    suite.point,
    suite.ci_low,
    suite.ci_high,
    CASE
        WHEN suite.point IS NULL THEN 'invalid'
        WHEN suite.ci_low IS NULL OR suite.ci_high IS NULL THEN 'point_only'
        WHEN suite.ci_high < 1.0 THEN 'lower'
        WHEN suite.ci_low > 1.0 THEN 'higher'
        ELSE 'unclear'
    END AS result_class,
    suite.issue
FROM suite
UNION ALL
SELECT * FROM tails;

-- Aggregate the five recorded components for each observation. Other is the
-- residual requested by the UI and deliberately includes unattributed
-- pre-merge time as well as time outside recorded rulesets.
CREATE VIEW observation_phase_totals AS
SELECT
    observations.endpoint_order,
    observations.file_order,
    observations.row_index,
    observations.wall_sec * 1000000000.0 AS wall_ns,
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
        item -> item.merge_ns
    )), 0)::DOUBLE AS merge_ns,
    coalesce(list_sum(list_transform(
        observations.timing_summary.rulesets,
        item -> item.rebuild_ns
    )), 0)::DOUBLE AS rebuild_ns
FROM selected_observations AS observations
WHERE observations.status = 'success';

CREATE VIEW endpoint_phase_estimates AS
WITH requested AS (
    SELECT
        endpoints.endpoint_order,
        files.file_order,
        phases.phase_order,
        phases.phase
    FROM selected_endpoints AS endpoints
    CROSS JOIN selected_files AS files
    CROSS JOIN report_phases AS phases
),
observed AS (
    SELECT
        totals.endpoint_order,
        totals.file_order,
        totals.row_index,
        phases.phase_order,
        phases.phase,
        CASE phases.phase
            WHEN 'search' THEN totals.search_ns
            WHEN 'apply' THEN totals.apply_ns
            WHEN 'merge' THEN totals.merge_ns
            WHEN 'rebuild' THEN totals.rebuild_ns
            WHEN 'other' THEN
                totals.wall_ns - totals.search_ns - totals.apply_ns - totals.merge_ns - totals.rebuild_ns
        END AS phase_ns
    FROM observation_phase_totals AS totals
    CROSS JOIN report_phases AS phases
),
aggregated AS (
    SELECT
        requested.*,
        avg(observed.phase_ns) AS raw_mean_ns,
        statuses.issue
    FROM requested
    JOIN selected_result_statuses AS statuses USING (endpoint_order, file_order)
    LEFT JOIN observed
        ON observed.endpoint_order = requested.endpoint_order
        AND observed.file_order = requested.file_order
        AND observed.phase = requested.phase
    GROUP BY ALL
)
SELECT
    endpoint_order,
    file_order,
    phase_order,
    phase,
    CASE WHEN issue IS NULL THEN raw_mean_ns END AS mean_ns,
    issue
FROM aggregated;

CREATE VIEW phase_comparisons AS
WITH paired AS (
    SELECT
        baseline.file_order,
        baseline.phase_order,
        baseline.phase,
        baseline.mean_ns AS baseline_ns,
        candidate.mean_ns AS candidate_ns,
        CASE
            WHEN baseline.issue IS NOT NULL THEN baseline.issue
            WHEN candidate.issue IS NOT NULL THEN candidate.issue
            WHEN baseline.mean_ns <= 0 THEN 'baseline phase mean is not positive'
            WHEN candidate.mean_ns < 0 THEN 'candidate phase mean is negative'
            ELSE NULL
        END AS issue
    FROM endpoint_phase_estimates AS baseline
    JOIN endpoint_phase_estimates AS candidate
        ON candidate.file_order = baseline.file_order
        AND candidate.phase = baseline.phase
        AND candidate.endpoint_order = 1
    WHERE baseline.endpoint_order = 0
)
SELECT
    file_order,
    phase_order,
    phase,
    baseline_ns,
    candidate_ns,
    candidate_ns - baseline_ns AS delta_ns,
    CASE WHEN issue IS NULL THEN candidate_ns / baseline_ns END AS point
FROM paired;

CREATE VIEW observation_rulesets AS
SELECT
    observations.endpoint_order,
    observations.file_order,
    observations.row_index,
    ruleset.name,
    (
        ruleset.search_ns
        + ruleset.apply_ns
        + ruleset.unattributed_ns
        + ruleset.merge_ns
        + ruleset.rebuild_ns
    )::DOUBLE AS total_ns
FROM selected_observations AS observations
JOIN selected_result_statuses AS statuses USING (endpoint_order, file_order)
CROSS JOIN unnest(observations.timing_summary.rulesets) AS items(ruleset)
WHERE observations.status = 'success' AND statuses.issue IS NULL;

CREATE VIEW valid_ruleset_files AS
SELECT file_order
FROM selected_result_statuses
GROUP BY file_order
HAVING count(*) = 2 AND count(*) FILTER (WHERE issue IS NULL) = 2;

CREATE VIEW ruleset_names AS
SELECT DISTINCT rulesets.file_order, rulesets.name
FROM observation_rulesets AS rulesets
JOIN valid_ruleset_files USING (file_order);

CREATE VIEW ruleset_endpoint_estimates AS
SELECT
    endpoints.endpoint_order,
    names.file_order,
    names.name,
    count(values.row_index) > 0 AS is_present,
    CASE
        WHEN count(values.row_index) > 0 THEN avg(coalesce(values.total_ns, 0))
    END AS mean_total_ns
FROM selected_endpoints AS endpoints
JOIN ruleset_names AS names ON true
JOIN selected_observations AS observations
    ON observations.endpoint_order = endpoints.endpoint_order
    AND observations.file_order = names.file_order
    AND observations.status = 'success'
LEFT JOIN observation_rulesets AS values
    ON values.endpoint_order = observations.endpoint_order
    AND values.file_order = observations.file_order
    AND values.row_index = observations.row_index
    AND values.name = names.name
GROUP BY endpoints.endpoint_order, names.file_order, names.name;

CREATE VIEW ruleset_comparisons AS
WITH paired AS (
    SELECT
        baseline.file_order,
        baseline.name,
        baseline.is_present AS baseline_present,
        candidate.is_present AS candidate_present,
        baseline.mean_total_ns AS baseline_total_ns,
        candidate.mean_total_ns AS candidate_total_ns,
        coalesce(candidate.mean_total_ns, 0) - coalesce(baseline.mean_total_ns, 0) AS delta_ns
    FROM ruleset_endpoint_estimates AS baseline
    JOIN ruleset_endpoint_estimates AS candidate
        ON candidate.file_order = baseline.file_order
        AND candidate.name = baseline.name
        AND candidate.endpoint_order = 1
    WHERE baseline.endpoint_order = 0
),
ranked AS (
    SELECT
        *,
        CASE
            WHEN baseline_present AND candidate_present AND baseline_total_ns > 0 THEN
                candidate_total_ns / baseline_total_ns
        END AS point,
        row_number() OVER (
            PARTITION BY file_order
            ORDER BY abs(delta_ns) DESC, name
        )::UINTEGER AS ruleset_rank,
        count(*) OVER (PARTITION BY file_order)::UINTEGER AS ruleset_count
    FROM paired
)
SELECT
    file_order,
    ruleset_rank,
    ruleset_count,
    name,
    baseline_total_ns,
    candidate_total_ns,
    delta_ns,
    point
FROM ranked;
