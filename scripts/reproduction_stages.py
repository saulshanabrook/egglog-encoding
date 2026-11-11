"""Immutable acquisition attempts, separate from the performance cache."""

from __future__ import annotations

import hashlib
import json
import os
import re
from collections.abc import Callable, Mapping
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from benchmarking.targets import sha256_file
from scripts.reproduction_process import exclusive_job


def directory_identity(directory: Path) -> str:
    """Bind runtime tree membership and bytes, including external symlink targets."""
    if not directory.is_dir():
        raise ValueError(f"retained artifact directory is missing: {directory}")
    digest = hashlib.sha256()
    ancestors: set[Path] = set()

    def visit(path: Path) -> None:
        relative = path.relative_to(directory).as_posix()
        link = os.readlink(path) if path.is_symlink() else None
        if path.is_dir():
            resolved = path.resolve()
            if resolved in ancestors:
                raise ValueError(f"cycle in retained artifact directory: {path}")
            digest.update(json.dumps([relative, "directory", link]).encode() + b"\n")
            ancestors.add(resolved)
            for child in sorted(path.iterdir()):
                if child.name not in {".git", "__pycache__"}:
                    visit(child)
            ancestors.remove(resolved)
        elif path.is_file():
            digest.update(json.dumps([relative, "file", link, sha256_file(path)]).encode() + b"\n")
        else:
            raise ValueError(f"retained artifact is missing or not a regular file/directory: {path}")

    visit(directory)
    return digest.hexdigest()


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
    to retained files and declared directory trees. A failed attempt is evidence,
    not an invitation to retry. Old receipts without directory identities retain
    their original file-only reuse contract.
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
            try:
                intact = all(
                    Path(path).is_file() and sha256_file(Path(path)) == sha for path, sha in artifacts.items()
                ) and all(
                    directory_identity(Path(path)) == sha
                    for path, sha in record.get("artifact_directories", {}).items()
                )
            except (OSError, ValueError):
                intact = False
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
            "artifact_directories": {},
        }
        receipt = attempt / "stage.json"
        receipt.write_text(json.dumps(record, indent=2) + "\n")
        try:
            outcome = execute(attempt)
            outputs = [Path(path).absolute() for path in outcome.pop("artifacts", [])]
            directories = [Path(path).absolute() for path in outcome.pop("artifact_directories", [])]
            if outcome["status"] == "success" and not outputs:
                raise ValueError("successful acquisition stage must retain actual outputs")
            if any(not path.is_file() for path in outputs):
                raise ValueError("stage reported missing output artifacts")
            record.update(
                outcome,
                artifacts={str(path): sha256_file(path) for path in outputs},
                artifact_directories={str(path): directory_identity(path) for path in directories},
            )
        except (OSError, ValueError) as error:
            record.update(status="resource-stopped" if "guard refused" in str(error) else "blocked", reason=str(error))
        finally:
            record["finished_at"] = datetime.now(UTC).isoformat()
            temporary = attempt / "stage.json.tmp"
            temporary.write_text(json.dumps(record, indent=2) + "\n")
            temporary.replace(receipt)
        return record
