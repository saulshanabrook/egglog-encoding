"""Publish one copy of each validated standalone replay, retaining source aliases."""

from __future__ import annotations

import json
from collections.abc import Sequence
from pathlib import Path
from typing import Any

from benchmarking.targets import sha256_file


def write_corpus(rows: Sequence[dict[str, Any]], directory: Path) -> dict[str, Any]:
    """Project verified validation records into a portable corpus.

    The caller verifies either current identities or retained immutable receipts
    and their artifact hashes. Only ordinary validation successes contribute
    files. Complete independent MISAAL invocations may contribute despite a failed
    enclosing compiler; incomplete calls and capture-only records remain in the
    manifest without contributing files. Original acquisition evidence stays in
    its immutable stage directory, and parent completion is never inferred.
    """
    directory.mkdir(parents=True, exist_ok=True)
    cases = []
    workloads: dict[str, dict[str, Any]] = {}
    for row in rows:
        outcome = row["outcome"]
        case = {
            key: row[key]
            for key in (
                "id",
                "catalog_id",
                "family",
                "source",
                "configuration",
                "scope",
                "paper_aliases",
                "completion_scope",
                "parent_outcome",
                "evidence",
            )
            if key in row
        }
        case.update(status=outcome["status"], reason=outcome.get("reason"), workloads=[])
        if outcome.get("receipt") or outcome.get("attempt"):
            receipt = Path(outcome["receipt"]) if outcome.get("receipt") else Path(outcome["attempt"]) / "stage.json"
            case["receipt"] = str(receipt)
            case["receipt_sha256"] = sha256_file(receipt) if receipt.is_file() else None
            if outcome.get("receipt_sha256") and case["receipt_sha256"] != outcome["receipt_sha256"]:
                raise ValueError(f"{row['id']}: validation receipt changed")
        cases.append(case)
        if outcome["status"] != "success":
            continue
        if outcome.get("stage") != "validate":
            case.update(status="pending", reason="capture completed; standalone validation stage is still required")
            continue
        if not outcome.get("workloads"):
            raise ValueError(f"{row['id']}: ordinary validation is required before corpus publication")
        capture = outcome.get("capture_stage", {})
        if row.get("completion_scope") == "independent-misaal-invocation":
            if row["family"] != "misaal" or capture.get("invocation_complete") is not True:
                raise ValueError(f"{row['id']}: independent MISAAL invocation completion is required")
        elif capture.get("status") not in {"success", "ordinary-validation-pending", "ordinary-validation-failed"}:
            raise ValueError(f"{row['id']}: incomplete source capture cannot contribute a replay")
        if not case.get("receipt_sha256"):
            raise ValueError(f"{row['id']}: validation receipt is unavailable")
        validations = {item["replay"]: item for item in outcome["validations"]}
        for order, source in enumerate(outcome["workloads"]):
            validation = validations.get(source)
            if (
                validation is None
                or validation.get("status") != "success"
                or not validation.get("output_contract_passed")
            ):
                raise ValueError(f"{row['id']}: replay lacks a successful native-output validation: {source}")
            path = Path(source)
            digest = sha256_file(path)
            if digest != validation["replay_sha256"]:
                raise ValueError(f"{row['id']}: validated replay changed: {source}")
            # Current validation accepts self-contained replays only. A future
            # input-data extension must include facts in both validation and key.
            if validation.get("facts_sha256") or validation.get("fact_directory"):
                raise ValueError("bundled fact data is not yet supported by corpus publication")
            name = digest.removeprefix("sha256:") + ".egg"
            target = directory / name
            if target.exists():
                if sha256_file(target) != digest:
                    raise ValueError(f"stored corpus bytes changed: {target}")
            else:
                temporary = target.with_suffix(".tmp")
                temporary.write_bytes(path.read_bytes())
                if sha256_file(temporary) != digest:
                    temporary.unlink()
                    raise ValueError(f"replay changed while copying: {source}")
                temporary.replace(target)
            case["workloads"].append(name)
            entry = workloads.setdefault(name, {"file": name, "sha256": digest, "facts_sha256": "", "aliases": []})
            entry["aliases"].append(
                {"case": row["id"], "order": order, "captured_replay": source, "validation": case["receipt"]}
            )
    manifest = {"cases": cases, "workloads": list(workloads.values())}
    content = json.dumps(manifest, indent=2) + "\n"
    destination = directory / "manifest.json"
    if not destination.is_file() or destination.read_text() != content:
        temporary = destination.with_suffix(".tmp")
        temporary.write_text(content)
        temporary.replace(destination)
    return manifest
