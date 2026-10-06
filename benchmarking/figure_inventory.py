"""Project prepared corpus metadata for figures without reading timing observations."""

from __future__ import annotations

import argparse
import json
import os
import tempfile
from pathlib import Path
from typing import TypedDict

from .suites import SAFETY_POLICY, VALIDATION_POLICY, load_manifest


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
    expected_cases: int
    workloads: list[FigureWorkload]
    exclusions: list[SourceExclusion]


def figure_inventory(root: Path, timeout_sec: int = 300) -> FigureInventory:
    """Preserve manifest identities, call order, aliases, blockers, and exact strict failures."""

    if timeout_sec <= 0:
        raise ValueError("timeout must be positive")
    manifest = load_manifest(root)
    cases = {case.id: case for case in manifest.cases}
    workloads: dict[str, FigureWorkload] = {}
    exclusions: list[SourceExclusion] = []
    for source in manifest.workloads:
        aliases = [alias for alias in source.aliases if cases[alias.case].status != "excluded"]
        if not aliases:
            continue
        case = cases[aliases[0].case]
        identity = f"{source.sha256}/{source.facts_sha256}"
        workload = workloads.setdefault(
            identity,
            {
                "id": identity,
                "label": case.id + (f" / call {aliases[0].order + 1}" if len(case.workloads) > 1 else ""),
                "family": case.family,
                "iteration": 11 if case.family == "math-growth" else None,
                "file_sha256": source.sha256,
                "fact_directory_sha256": source.facts_sha256,
                "aliases": [],
                "unavailable_reason": "",
                "validation_failures": {},
            },
        )
        workload["aliases"].extend(
            {"case": alias.case, "family": cases[alias.case].family, "path": source.file} for alias in aliases
        )
    for case in manifest.cases:
        if case.status == "excluded":
            exclusions.append(
                {
                    "case": case.id,
                    "family": case.family,
                    "paths": list(case.workloads),
                    "reason": case.reason or "Excluded source",
                }
            )
        elif case.status in ("blocked", "pending") or not case.workloads:
            workloads[case.id] = {
                "id": case.id,
                "label": case.id,
                "family": case.family,
                "iteration": 11 if case.family == "math-growth" else None,
                "file_sha256": "",
                "fact_directory_sha256": "",
                "aliases": [],
                "unavailable_reason": case.reason or "Replay unavailable",
                "validation_failures": {},
            }
    for family, recipe in manifest.sources.items():
        if recipe.get("excluded") and not any(row["family"] == family for row in exclusions):
            exclusions.append({"case": family, "family": family, "paths": [], "reason": recipe["excluded"]})
    for outcome in manifest.outcomes:
        identity = f"{outcome['file_sha256']}/{outcome['fact_directory_sha256']}"
        if identity in workloads and outcome["kind"] == "safety" and outcome["policy"] == SAFETY_POLICY:
            workloads[identity]["unavailable_reason"] = (
                "" if outcome["status"] == "success" else (outcome["reason"] or "Safety deferred")
            )
        if (
            identity not in workloads
            or outcome["kind"] != "validation"
            or outcome["policy"] != VALIDATION_POLICY
            or outcome["timeout_sec"] != timeout_sec
        ):
            continue
        key = f"{outcome['binary_sha256']}/{timeout_sec}/{outcome['disequality_encoding']}"
        if outcome["status"] == "success":
            workloads[identity]["validation_failures"].pop(key, None)
        else:
            workloads[identity]["validation_failures"][key] = outcome["reason"] or "Strict proof validation failed"
    return {
        "id": 1,
        "timeout_sec": timeout_sec,
        "expected_cases": len(cases),
        "workloads": list(workloads.values()),
        "exclusions": exclusions,
    }


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
