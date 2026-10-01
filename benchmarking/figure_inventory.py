"""Export catalog identities and coverage, without reading benchmark observations."""

from __future__ import annotations

import argparse
import json
import os
import tempfile
from pathlib import Path
from typing import TypedDict

from .admission import PILOT_RELATIVE_PATH, PilotPolicy, load_pilot_records, pilot_identity
from .suites import resolve_suite


class WorkloadAlias(TypedDict):
    case: str
    family: str
    path: str


class FigureWorkload(TypedDict):
    id: str
    label: str
    family: str
    iteration: int | None
    file_sha256: str
    fact_directory_sha256: str
    aliases: list[WorkloadAlias]
    unavailable_reason: str
    validation_failures: dict[str, str]


class SourceExclusion(TypedDict):
    case: str
    family: str
    paths: list[str]
    reason: str


class FigureInventory(TypedDict):
    id: int
    timeout_sec: int
    workloads: list[FigureWorkload]
    exclusions: list[SourceExclusion]


def figure_inventory(root: Path, timeout_sec: int = 300) -> FigureInventory:
    """Reuse suite resolution, deduplicate replays, and retain unavailable source calls.

    Failed strict checks are metadata, bound to the tested executable/input/timeout.
    Their timings never enter this index. Absent validation does not block plotting.
    """

    if timeout_sec <= 0:
        raise ValueError("timeout must be positive")
    selection = resolve_suite("expanded", root, include_normal_only=True)
    workloads: dict[str, FigureWorkload] = {}
    exclusions: list[SourceExclusion] = []
    for case in selection.cases:
        omitted = selection.source_exclusions.get(case.id, ())
        chosen = case.provenance.get("benchmark_selection")
        if case.status == "deferred" or omitted or (chosen and not chosen["workloads"]):
            exclusions.append(
                {
                    "case": case.id,
                    "family": case.family,
                    "paths": list(omitted or case.workloads),
                    "reason": chosen["reason"] if chosen else case.reason or "Deferred",
                }
            )
        if case.status == "deferred" or (chosen and not chosen["workloads"]):
            continue
        iteration = int(case.id.rsplit("-", 1)[1]) if case.family == "math-growth" else None
        files = selection.case_files[case.id]
        normal_paths = {item["invocation"]: item["path"] for item in case.provenance.get("normal_workloads", [])}
        calls = case.provenance.get("invocations", [])
        expected = list(dict.fromkeys((*case.workloads, *normal_paths.values())))
        if chosen is not None:
            expected = chosen["workloads"]
        labels = {
            path: case.id + (f" / call {index + 1}" if len(expected) > 1 else "") for index, path in enumerate(expected)
        }
        for call in calls:
            path = call.get("workload") or normal_paths.get(call["index"])
            if path:
                labels[path] = case.id + (f" / call {call['index'] + 1}" if len(calls) > 1 else "")
        for file in files:
            identity = f"{file.sha256}/{file.fact_directory_sha256}"
            workload = workloads.setdefault(
                identity,
                {
                    "id": identity,
                    "label": labels[file.display_path],
                    "family": case.family,
                    "iteration": iteration,
                    "file_sha256": file.sha256,
                    "fact_directory_sha256": file.fact_directory_sha256,
                    "aliases": [],
                    "unavailable_reason": selection.proof_blockers.get((file.sha256, file.fact_directory_sha256), ""),
                    "validation_failures": {},
                },
            )
            workload["aliases"].append({"case": case.id, "family": case.family, "path": file.display_path})

        available = {file.display_path for file in files}
        missing = [(labels[path], case.reason) for path in expected if path not in available]
        missing.extend(
            (f"{case.id} / call {call['index'] + 1}", call.get("reason") or case.reason)
            for call in calls
            if not call.get("workload") and call["index"] not in normal_paths
        )
        if not calls and not expected and not omitted:
            missing = [(case.id, case.reason)]
        for label, reason in missing:
            workloads[label] = {
                "id": label,
                "label": label,
                "family": case.family,
                "iteration": iteration,
                "file_sha256": "",
                "fact_directory_sha256": "",
                "aliases": [],
                "unavailable_reason": selection.capture_errors.get(case.id) or reason or "Replay unavailable",
                "validation_failures": {},
            }

    files_by_identity = {f"{file.sha256}/{file.fact_directory_sha256}": file for file in selection.files}
    for evidence in load_pilot_records(root / PILOT_RELATIVE_PATH):
        identity = evidence["identity"]
        key = f"{identity['file_sha256']}/{identity['fact_directory_sha256']}"
        checked_file = files_by_identity.get(key)
        if checked_file is None or identity != pilot_identity(
            checked_file,
            selection.validation_families[(checked_file.sha256, checked_file.fact_directory_sha256)],
            identity["binary_hashes"],
            PilotPolicy(timeout_sec=timeout_sec),
            root,
        ):
            continue
        reason = str(evidence.get("reason") or "")
        # proof-testing is Egglog's strict mode, not native Egg's verifier.
        if reason.startswith("proof-testing:") or evidence["status"] == "admitted":
            binary = identity["binary_hashes"]["egglog"]
            failure_key = f"{binary}/{timeout_sec}"
            if evidence["status"] == "admitted":
                workloads[key]["validation_failures"].pop(failure_key, None)
            else:
                workloads[key]["validation_failures"][failure_key] = "Strict proof validation failed"
    return {"id": 1, "timeout_sec": timeout_sec, "workloads": list(workloads.values()), "exclusions": exclusions}


def write_inventory(root: Path, destination: Path, timeout_sec: int = 300) -> None:
    """Atomically update changed metadata while preserving unchanged image dependencies."""

    encoded = (
        json.dumps(figure_inventory(root, timeout_sec), ensure_ascii=False, separators=(",", ":")).encode() + b"\n"
    )
    if destination.is_file() and destination.read_bytes() == encoded:
        return
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(dir=destination.parent, prefix=".inventory-", delete=False) as handle:
            temporary = Path(handle.name)
            handle.write(encoded)
        os.replace(temporary, destination)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--output", type=Path, default=Path("benchmarks/local/figure-inventory.json"))
    parser.add_argument("--timeout-sec", type=int, default=300)
    args = parser.parse_args()
    write_inventory(args.root.resolve(), args.output, args.timeout_sec)
