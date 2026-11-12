"""Import source-bound proof replay evidence without creating timing observations."""

from __future__ import annotations

import json
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any, cast

from .engines import PROOF_ORACLES, TREATMENT_SPECS
from .models import BenchmarkEndpoint, FileSpec

VALIDATION_UNAVAILABLE_STATUSES = frozenset(
    ("timed-out", "memory-limited", "resource-limited", "stack-overflow", "infrastructure-unavailable")
)


def is_semantic_proof_failure(evidence: Mapping[str, Any] | None) -> bool:
    """Keep checker rejection distinct from a replay that could not finish or launch."""
    return (
        evidence is not None
        and evidence["status"] == "failed"
        and (evidence.get("observation") or {}).get("status") not in VALIDATION_UNAVAILABLE_STATUSES
    )


def read_proof_source_bindings(path: Path | None) -> dict[str, str]:
    """Bind immutable production executable hashes to their compiled Rust source receipt."""
    if path is None or not path.is_file():
        return {}
    receipt = json.loads(path.read_bytes())
    if "binary_sources" in receipt:
        return cast(dict[str, str], receipt["binary_sources"])
    return {receipt["binary_sha256"]: receipt["compiled_source_sha"]}


def read_proof_validation(path: Path) -> tuple[dict[str, Any], ...]:
    """Read the trusted replay log and reject a timing cache at this boundary."""
    if not path.is_file():
        return ()
    rows = []
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        if row.get("validation_schema_version") != 1 or row.get("kind") != "proof-validation-replay":
            raise ValueError("unsupported proof-validation replay schema")
        if {"wall_sec", "max_rss_bytes", "timing_summary"} & row.keys():
            raise ValueError("proof-validation replay evidence must not contain performance measurements")
        rows.append(row)
    return tuple(rows)


def qualify_proof_validation(row: Mapping[str, Any] | None) -> dict[str, Any]:
    """Require an executed successful replay that verified every materialized certificate."""
    summary = row["proof_summary"] if row else None
    if row is None:
        status, issue = "pending", "separate proof validation pending"
    elif row["status"] != "success" or (summary is not None and not summary["success"]):
        status, issue = "failed", row["error_message"] or "proof validation failed"
    elif summary is None:
        status, issue = "unknown", "validator did not emit executed proof counters"
    elif summary["produced_certificates"] < 1:
        status, issue = "unknown", "validator produced no certificate"
    elif summary["verified_certificates"] != summary["produced_certificates"]:
        status, issue = "failed", "not every produced certificate was validated"
    else:
        status, issue = "passed", None
    return {"status": status, "issue": issue, "summary": summary, "observation": dict(row) if row else None}


def select_remote_proof_validation(
    rows: Sequence[dict[str, Any]],
    production: BenchmarkEndpoint,
    file: FileSpec,
    *,
    source_bindings: Mapping[str, str] | None = None,
) -> dict[str, Any] | None:
    """Bind a replay to the measured profile while retaining its distinct host and binary."""
    oracle = PROOF_ORACLES[production.treatment]
    physical = file.for_binary(TREATMENT_SPECS[oracle].binary_name)
    matching = [
        row
        for row in rows
        if row["production_binary_sha256"] == production.binary_sha256
        and row["file_sha256"] == physical.sha256
        and row["production_treatment"] == production.treatment
        and row["checked_treatment"] == oracle
        and row["threads"] == production.threads
        and row["requested_threads"] == production.requested_threads
    ]
    if not matching:
        return None
    row = max(enumerate(matching), key=lambda item: (item[1]["started_at"], item[0]))[1]
    result = qualify_proof_validation(row)
    validator = row["validator"]
    compiled_source = (source_bindings or {}).get(production.binary_sha256, production.target.git_sha)
    if (
        row["source_git_sha"] != compiled_source
        or validator["source_git_sha"] != row["source_git_sha"]
        or not validator["host"]
        or not validator["binary_sha256"]
    ):
        result.update(
            status="unknown", summary=None, issue="remote proof replay source or executable provenance does not match"
        )
    return {
        **result,
        "kind": "remote-validation-replay",
        "scope": "strict replay of the frozen source and input; not an exported local certificate",
        "validator": validator,
        "production_source_git_sha": compiled_source,
    }
