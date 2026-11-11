"""Immutable acquisition attempts, separate from the performance cache."""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Callable, Mapping
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from benchmarking.targets import sha256_file
from scripts.reproduction_process import exclusive_job


def run_stage(
    storage: Path,
    case: str,
    stage: str,
    identity: Mapping[str, Any],
    execute: Callable[[Path], dict[str, Any]],
    *,
    retry: bool = False,
) -> dict[str, Any]:
    """Reuse only matching attempts whose recorded output bytes remain intact.

    The caller owns source/configuration/dependency identity and the substantive
    completion checks. This layer serializes execution and binds their outcome
    to retained files. A failed attempt is evidence, not an invitation to retry.
    """
    if not all(re.fullmatch(r"[A-Za-z0-9_.-]+", value) and value not in (".", "..") for value in (case, stage)):
        raise ValueError("case and stage must be safe path components")
    digest = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
    directory = storage / case / stage / digest
    with exclusive_job(storage / ".heavy-job.lock"):
        directory.mkdir(parents=True, exist_ok=True)
        previous = sorted(directory.glob("attempt-*/stage.json"))
        if previous and not retry:
            record: dict[str, Any] = json.loads(previous[-1].read_text())
            artifacts = record["artifacts"]
            intact = all(Path(path).is_file() and sha256_file(Path(path)) == sha for path, sha in artifacts.items())
            if intact:
                return record
        # Count directories, including an abruptly terminated attempt with no
        # final receipt. Never write over its partial logs or generated inputs.
        attempt = directory / f"attempt-{len(list(directory.glob('attempt-*'))) + 1:04}"
        attempt.mkdir()
        record = {
            "case": case,
            "stage": stage,
            "identity": dict(identity),
            "identity_sha256": digest,
            "attempt": str(attempt.resolve()),
            "started_at": datetime.now(UTC).isoformat(),
            "status": "interrupted",
            "artifacts": {},
        }
        receipt = attempt / "stage.json"
        receipt.write_text(json.dumps(record, indent=2) + "\n")
        try:
            outcome = execute(attempt)
            outputs = [Path(path).resolve() for path in outcome.pop("artifacts", [])]
            if outcome["status"] == "success" and not outputs:
                raise ValueError("successful acquisition stage must retain actual outputs")
            if any(not path.is_file() for path in outputs):
                raise ValueError("stage reported missing output artifacts")
            record.update(outcome, artifacts={str(path): sha256_file(path) for path in outputs})
        except (OSError, ValueError) as error:
            record.update(status="resource-stopped" if "guard refused" in str(error) else "blocked", reason=str(error))
        finally:
            record["finished_at"] = datetime.now(UTC).isoformat()
            temporary = attempt / "stage.json.tmp"
            temporary.write_text(json.dumps(record, indent=2) + "\n")
            temporary.replace(receipt)
        return record
