-- Persistent types mirror benchmarking.reports.records; report_rows derives
-- its columns from report_record_t so the storage schema is declared once.
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

-- The singleton value is inserted by Python so the expected cache version has
-- one owner. Incompatible caches are disposable and intentionally have no
-- migration path.
CREATE TABLE report_cache_metadata (
    schema_version UINTEGER NOT NULL
);

-- Preserve append order as the final tie-breaker when timestamps are equal.
CREATE SEQUENCE report_row_sequence START 0 MINVALUE 0;

-- CTAS does not evaluate nextval because LIMIT 0 emits no rows. Each append
-- explicitly supplies the next row index alongside one typed writer record.
CREATE TABLE report_rows AS
SELECT
    nextval('report_row_sequence') AS row_index,
    unnest(NULL::report_record_t)
LIMIT 0;
