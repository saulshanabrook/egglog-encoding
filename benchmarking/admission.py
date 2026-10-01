"""Own immutable pilot policy, evidence identities, and admission record lookup."""

from __future__ import annotations

import json
from collections.abc import Mapping, Sequence
from dataclasses import asdict, dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Literal

from .memory_guard import GROUP_LIMIT_BYTES, pilot_safety_deferral
from .models import FileSpec
from .reports.store import ReportRecord
from .targets import sha256_file

PILOT_RELATIVE_PATH = Path("benchmarks/local/pilot.jsonl")
type ProofTreatment = Literal["proofs", "proof-extraction"]
PROOF_TREATMENTS: tuple[ProofTreatment, ...] = ("proofs", "proof-extraction")


@dataclass(frozen=True)
class PilotPolicy:
    timeout_sec: float = 120
    memory_limit_bytes: int = GROUP_LIMIT_BYTES
    version: int = 1


def pilot_identity(
    file: FileSpec,
    family: str,
    binary_hashes: Mapping[str, str],
    policy: PilotPolicy,
    root: Path,
) -> dict[str, Any]:
    """Bind admission to executable/input contents and the complete gate policy."""

    engines = ("egglog", "egg") if family == "math-growth" else ("egglog",)
    identity: dict[str, Any] = {
        "file_sha256": file.sha256,
        "fact_directory_sha256": file.fact_directory_sha256,
        "binary_hashes": {engine: binary_hashes.get(engine) for engine in engines},
        "policy": asdict(policy),
        "proof_validation": "proof-testing",
    }
    if family == "math-growth":
        validator = root / "benchmarking/math_workloads.py"
        identity["math_validator_sha256"] = sha256_file(validator) if validator.is_file() else None
    return identity


def load_pilot_records(path: Path) -> list[dict[str, Any]]:
    """Load separate admission evidence without creating or touching a cache."""

    if not path.exists():
        return []
    try:
        return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    except ValueError as error:
        raise ValueError(f"invalid pilot evidence {path}; remove it and rerun the pilot") from error


def find_pilot_record(
    records: Sequence[dict[str, Any]],
    file: FileSpec,
    family: str,
    binary_hashes: Mapping[str, str],
    policy: PilotPolicy,
    root: Path,
    *,
    treatment: ProofTreatment | None = None,
) -> dict[str, Any] | None:
    """Find exact evidence, sharing strict gates but not another timed mode's failure."""

    identity = pilot_identity(file, family, binary_hashes, policy, root)
    other = "proof-extraction" if treatment == "proofs" else "proofs"
    return next(
        (
            record
            for record in reversed(records)
            if record["identity"] == identity
            and not (treatment is not None and str(record.get("reason") or "").startswith(f"{other}:"))
        ),
        None,
    )


def preparation_outcome(
    file: FileSpec,
    family: str,
    binary_hashes: Mapping[str, str],
    root: Path,
    pilots: Sequence[dict[str, Any]],
    measurements: Sequence[ReportRecord],
    timeout_sec: int = 120,
    rounds: int = 10,
    *,
    treatment: ProofTreatment = "proof-extraction",
    require_validation: bool = False,
) -> tuple[str, str | None]:
    """Classify measurements and known failures without requiring correctness tests.

    Only measured collector rows contribute performance observations. Older
    pilot checks may establish a terminal outcome, but their timings never
    become benchmark observations. Only the explicit pilot workflow requires
    current strict-proof evidence; successful timing is not proof validation.
    """

    evidence = find_pilot_record(
        pilots, file, family, binary_hashes, PilotPolicy(timeout_sec=timeout_sec), root, treatment=treatment
    )
    selected: dict[str, list[ReportRecord]] = {}
    for endpoint_treatment in ("off", treatment):
        matching = [
            (index, row)
            for index, row in enumerate(measurements)
            if row["binary_sha256"] == binary_hashes.get("egglog")
            and row["file_sha256"] == file.sha256
            and row["fact_directory_sha256"] == file.fact_directory_sha256
            and row["timeout_sec"] == timeout_sec
            and row["treatment"] == endpoint_treatment
        ]
        matching.sort(key=lambda item: (datetime.fromisoformat(item[1]["started_at"]), item[0]))
        selected[endpoint_treatment] = [row for _, row in matching[-max(30, rounds) :]]
    for endpoint_treatment, rows in selected.items():
        for row in reversed(rows):
            if row["status"] == "success":
                continue
            if endpoint_treatment != "off" and not selected["off"]:
                return "pending", "normal-mode screening is missing from the benchmark cache"
            reason = f"{endpoint_treatment}: {row['error_message'] or row['status']}"
            if "resource guard" in reason and "process-group RSS" not in reason:
                return "resource-limited", reason
            if row["status"] == "timed-out" or "process-group RSS" in reason:
                return "resource-limited", reason
            return ("normal-mode-blocked" if endpoint_treatment == "off" else "proof-error"), reason
    if evidence is not None and evidence["status"] != "admitted":
        reason = str(evidence.get("reason") or evidence["status"])
        if evidence["status"] == "blocked":
            return "pending", reason
        if evidence.get("operational_stop") and "process-group RSS" not in reason:
            return "resource-limited", reason
        if evidence["status"] in ("timed-out", "memory-limit") or "process-group RSS" in reason:
            return "resource-limited", reason
        return ("normal-mode-blocked" if reason.startswith("off:") else "proof-error"), reason
    deferral = pilot_safety_deferral(evidence, earlier=pilots, file=file)
    if deferral is not None:
        return "safety-deferred", deferral
    if require_validation and evidence is None:
        return "pending", "without a current pilot; run preparation for the selected binaries and timeout"
    if not all(selected.values()):
        return "pending", f"initial off/{treatment} observations are missing from the benchmark cache"
    return "ready", None
