-- Session-only parameter types and state do not affect the cache schema version.

-- One cache lookup binds a list of these values directly.
CREATE TEMP TYPE selection_key_t AS STRUCT(
    request_order UINTEGER,
    binary_sha256 VARCHAR,
    file_sha256 VARCHAR,
    fact_directory_sha256 VARCHAR,
    backend VARCHAR,
    treatment report_treatment_t,
    timeout_sec UINTEGER
);

-- Endpoint roles are fields so an installed scope always compares exactly two
-- endpoints over one ordered file list.
CREATE TEMP TYPE report_scope_endpoint_t AS STRUCT(
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

CREATE TEMP TYPE report_scope_file_t AS STRUCT(
    file_sha256 VARCHAR,
    fact_directory_sha256 VARCHAR,
    file_path VARCHAR,
    absolute_file_path VARCHAR,
    fact_directory_path VARCHAR
);

CREATE TEMP TYPE report_scope_t AS STRUCT(
    baseline report_scope_endpoint_t,
    candidate report_scope_endpoint_t,
    files report_scope_file_t[],
    rounds UINTEGER,
    timeout_sec UINTEGER,
    t_critical_95 DOUBLE
);

-- Live retargeting uses a fresh connection rather than mutating this singleton.

CREATE TEMP TABLE current_report_scope (
    singleton BOOLEAN PRIMARY KEY CHECK (singleton),
    scope report_scope_t NOT NULL
);
