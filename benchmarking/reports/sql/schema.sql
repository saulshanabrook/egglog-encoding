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
    merge_ns UBIGINT,
    rebuild_ns UBIGINT
);

-- Python mirror: TimingSummaryRecord.
CREATE TYPE timing_summary_record_t AS STRUCT(
    schema_version UINTEGER,
    rulesets ruleset_timing_record_t[]
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

-- Ordered request relations let analysis scan the external file for the whole
-- selected matrix instead of issuing one JSON scan per displayed cell.  These
-- are ordinary objects in the private in-memory catalog (rather than TEMP
-- objects) so another connection from the optional DuckDB UI can inspect them.
CREATE TABLE scope_targets (
    target_order UINTEGER PRIMARY KEY,
    binary_sha256 VARCHAR NOT NULL,
    target_label VARCHAR NOT NULL,
    target_source VARCHAR NOT NULL,
    target_path VARCHAR NOT NULL,
    target_git_ref VARCHAR NOT NULL,
    target_git_sha VARCHAR NOT NULL,
    target_is_dirty BOOLEAN NOT NULL
);

CREATE TABLE scope_files (
    file_order UINTEGER PRIMARY KEY,
    file_sha256 VARCHAR NOT NULL,
    fact_directory_sha256 VARCHAR NOT NULL,
    file_path VARCHAR NOT NULL,
    absolute_file_path VARCHAR NOT NULL,
    fact_directory_path VARCHAR
);

CREATE TABLE scope_cells (
    cell_order UINTEGER PRIMARY KEY,
    backend VARCHAR NOT NULL,
    treatment report_treatment_t NOT NULL
);

CREATE TABLE scope_parameters (
    rounds UINTEGER NOT NULL,
    timeout_sec UINTEGER NOT NULL,
    t_critical_95 DOUBLE
);

CREATE TABLE scope_comparisons (
    comparison_order UINTEGER PRIMARY KEY,
    baseline_target_order UINTEGER NOT NULL,
    baseline_cell_order UINTEGER NOT NULL,
    candidate_target_order UINTEGER NOT NULL,
    candidate_cell_order UINTEGER NOT NULL
);

CREATE TABLE selection_keys (
    request_order UINTEGER PRIMARY KEY,
    binary_sha256 VARCHAR NOT NULL,
    file_sha256 VARCHAR NOT NULL,
    fact_directory_sha256 VARCHAR NOT NULL,
    backend VARCHAR NOT NULL,
    treatment report_treatment_t NOT NULL,
    timeout_sec UINTEGER NOT NULL
);
