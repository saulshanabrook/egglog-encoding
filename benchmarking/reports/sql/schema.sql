-- JSONL is a trusted, disposable cache written by this benchmark runner. These
-- named types mirror the Python TypedDicts in benchmarking.reports.records;
-- the strict STRUCT cast below rejects old rows with missing or extra keys.
CREATE TYPE report_status_t AS ENUM ('success', 'timed-out', 'failure');
CREATE TYPE report_treatment_t AS ENUM ('off', 'term', 'proofs');

-- Python mirror: RulesetTimingRecord.
CREATE TYPE ruleset_timing_record_t AS STRUCT(
    name VARCHAR,
    search_ns UBIGINT,
    apply_ns UBIGINT,
    unattributed_ns UBIGINT,
    merge_ns UBIGINT,
    rebuild_ns UBIGINT
);

-- Python mirror: TimingSummaryRecord.
CREATE TYPE timing_summary_record_t AS STRUCT(
    schema_version UINTEGER,
    rulesets ruleset_timing_record_t[]
);

-- One cache lookup binds a list of these values directly; unlike the report
-- scope below, selection keys do not need to remain visible to later views.
CREATE TYPE selection_key_t AS STRUCT(
    request_order UINTEGER,
    binary_sha256 VARCHAR,
    file_sha256 VARCHAR,
    fact_directory_sha256 VARCHAR,
    backend VARCHAR,
    treatment report_treatment_t,
    timeout_sec UINTEGER
);

-- Python mirror: ReportRecord.
CREATE TYPE report_record_t AS STRUCT(
    started_at VARCHAR,
    status report_status_t,
    target_label VARCHAR,
    target_source VARCHAR,
    target_path VARCHAR,
    target_git_ref VARCHAR,
    target_git_sha VARCHAR,
    target_is_dirty BOOLEAN,
    binary_sha256 VARCHAR,
    file_path VARCHAR,
    file_sha256 VARCHAR,
    fact_directory_path VARCHAR,
    fact_directory_sha256 VARCHAR,
    backend VARCHAR,
    treatment report_treatment_t,
    timeout_sec UINTEGER,
    wall_sec DOUBLE,
    max_rss_bytes UBIGINT,
    error_exit_code INTEGER,
    error_signal INTEGER,
    error_message VARCHAR,
    timing_summary timing_summary_record_t
);

-- Keep row identity as the zero-based physical JSONL position. DuckDB's direct
-- JSON-to-STRUCT cast intentionally owns parsing and convenient coercions.
CREATE VIEW report_rows AS
WITH parsed AS (
    SELECT
        ordinality - 1 AS row_index,
        json::report_record_t AS record
    FROM read_json_objects(
        report_path(),
        format = 'newline_delimited'
    ) WITH ORDINALITY
)
SELECT row_index, unnest(record)
FROM parsed;

-- A report scope compares exactly two endpoint tuples over one ordered file
-- list. Endpoint roles are fields rather than list data so an installed scope
-- cannot represent zero, one, or more than two systems.
CREATE TYPE report_scope_endpoint_t AS STRUCT(
    binary_sha256 VARCHAR,
    target_label VARCHAR,
    target_source VARCHAR,
    target_path VARCHAR,
    target_git_ref VARCHAR,
    target_git_sha VARCHAR,
    target_is_dirty BOOLEAN,
    backend VARCHAR,
    treatment report_treatment_t
);

CREATE TYPE report_scope_file_t AS STRUCT(
    file_sha256 VARCHAR,
    fact_directory_sha256 VARCHAR,
    file_path VARCHAR,
    absolute_file_path VARCHAR,
    fact_directory_path VARCHAR
);

CREATE TYPE report_scope_t AS STRUCT(
    baseline report_scope_endpoint_t,
    candidate report_scope_endpoint_t,
    files report_scope_file_t[],
    rounds UINTEGER,
    timeout_sec UINTEGER,
    t_critical_95 DOUBLE
);

-- Each transient catalog installs this immutable singleton once. Live report
-- retargeting opens a fresh catalog instead of updating or deleting this row.
CREATE TABLE current_report_scope (
    singleton BOOLEAN PRIMARY KEY CHECK (singleton),
    scope report_scope_t NOT NULL
);
