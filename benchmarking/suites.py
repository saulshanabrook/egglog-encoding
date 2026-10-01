"""Resolve the source catalog without losing blocked cases or capture aliases."""

from __future__ import annotations

import json
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Literal, cast

from .admission import (
    PROOF_TREATMENTS,
    PilotPolicy,
    find_pilot_record,
    load_pilot_records,
    pilot_identity,
    preparation_outcome,
)
from .engines import TREATMENT_SPECS
from .memory_guard import pilot_safety_deferral
from .models import FileSpec
from .reports.store import ReportRecord
from .targets import sha256_file
from .workloads import resolve_files

EXPANDED_FAMILIES = ("math-growth", "eggcc", "luminal", "hardboiled", "misaal", "churchroad", "dialegg", "speq")
SUITE_NAMES = ("expanded", "math-11", *EXPANDED_FAMILIES)


@dataclass(frozen=True)
class CatalogCase:
    id: str
    family: str
    source: str
    status: Literal["captured", "blocked", "deferred"]
    reason: str | None
    workloads: tuple[str, ...]
    provenance: dict[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class SuiteCatalog:
    families: dict[str, dict[str, Any]]
    cases: tuple[CatalogCase, ...]


@dataclass(frozen=True)
class SuiteSelection:
    name: str
    root: Path
    catalog: SuiteCatalog
    cases: tuple[CatalogCase, ...]
    files: tuple[FileSpec, ...]
    case_files: dict[str, tuple[FileSpec, ...]]
    capture_errors: dict[str, str]
    validation_families: dict[tuple[str, str], str]
    proof_blockers: dict[tuple[str, str], str] = field(default_factory=dict)
    source_exclusions: dict[str, tuple[str, ...]] = field(default_factory=dict)


def load_catalog(root: Path) -> SuiteCatalog:
    """Read the checked-in source inventory, including cases without captures."""

    path = root / "benchmarks/catalog.json"
    try:
        raw = json.loads(path.read_text())
        cases = tuple(
            CatalogCase(
                id=case["id"],
                family=case["family"],
                source=case["source"],
                status=case["status"],
                reason=case.get("reason"),
                workloads=tuple(case["workloads"]),
                provenance={
                    k: v
                    for k, v in case.items()
                    if k not in {"id", "family", "source", "status", "reason", "workloads"}
                },
            )
            for case in raw["cases"]
        )
        if len({case.id for case in cases}) != len(cases):
            raise ValueError("source case IDs must be unique")
        if any(case.status not in ("captured", "blocked", "deferred") for case in cases):
            raise ValueError("unsupported capture status")
        for case in cases:
            selection = case.provenance.get("benchmark_selection")
            if selection is None:
                continue
            paths = selection["workloads"]
            if (
                not isinstance(paths, list)
                or any(not isinstance(path, str) for path in paths)
                or len(paths) != len(set(paths))
                or not isinstance(selection["reason"], str)
                or not selection["reason"].strip()
            ):
                raise ValueError(f"{case.id}: benchmark_selection requires unique workload paths and a reason")
            recorded = {*case.workloads, *(row["path"] for row in case.provenance.get("normal_workloads", []))}
            if unmatched := set(paths) - recorded:
                raise ValueError(
                    f"{case.id}: benchmark_selection paths are not captured: {', '.join(sorted(unmatched))}"
                )
        return SuiteCatalog(raw["families"], cases)
    except (KeyError, TypeError, ValueError) as error:
        raise ValueError(f"invalid benchmark catalog {path}: {error}") from error


def resolve_suite(name: str | Sequence[str], root: Path, *, include_normal_only: bool = False) -> SuiteSelection:
    """Resolve a catalog-ordered union and deduplicate capture identities."""

    names = (name,) if isinstance(name, str) else tuple(dict.fromkeys(name))
    if not names or any(value not in SUITE_NAMES for value in names):
        raise ValueError(f"unknown benchmark suite {name!r}; choose from {', '.join(SUITE_NAMES)}")
    catalog = load_catalog(root)
    families = EXPANDED_FAMILIES if "expanded" in names else names
    cases = tuple(
        case
        for case in catalog.cases
        if case.family in families
        or ("math-11" in names and case.family == "math-growth" and case.id == "math-growth-011")
    )
    unique: dict[tuple[str, str], FileSpec] = {}
    case_files: dict[str, tuple[FileSpec, ...]] = {}
    errors: dict[str, str] = {}
    validation_families: dict[tuple[str, str], str] = {}
    proof_blockers: dict[tuple[str, str], str] = {}
    paired_identities: set[tuple[str, str]] = set()
    source_exclusions: dict[str, tuple[str, ...]] = {}
    for case in cases:
        captured: list[FileSpec] = []
        paths: list[tuple[str, str | None]] = []
        reproduction = case.provenance.get("complete_reproduction")
        if reproduction is not None:
            reason = reproduction.get("reason")
            if reproduction["status"] != "complete":
                errors[case.id] = reason or "complete source reproduction is required before suite admission"
                case_files[case.id] = ()
                continue
            receipt = root / reproduction["receipt"]
            if not receipt.is_file() or sha256_file(receipt) != reproduction["receipt_sha256"]:
                errors[case.id] = "complete reproduction receipt changed or is unavailable"
                case_files[case.id] = ()
                continue
        if case.status == "captured":
            if (
                not case.workloads
                and not case.provenance.get("normal_workloads")
                and (case.provenance.get("benchmark_selection") or {}).get("workloads") != []
            ):
                errors[case.id] = "catalog marks this case captured but lists no workload files"
            paths.extend((path, None) for path in case.workloads)
        if include_normal_only:
            paths.extend((row["path"], row["proof_blocker"]) for row in case.provenance.get("normal_workloads", []))
        if selection := case.provenance.get("benchmark_selection"):
            allowed = set(selection["workloads"])
            source_exclusions[case.id] = tuple(
                path
                for path in dict.fromkeys(
                    (*case.workloads, *(row["path"] for row in case.provenance.get("normal_workloads", [])))
                )
                if path not in allowed
            )
            paths = [(path, blocker) for path, blocker in paths if path in allowed]
        for path, proof_blocker in paths:
            try:
                relative = Path(path)
                if relative.is_absolute() or not (root / relative).resolve().is_relative_to(root.resolve()):
                    raise ValueError(f"catalog workload must stay within the repository: {path}")
                file = resolve_files((path,), root)[0]
                if reproduction is not None and reproduction["workloads"].get(path) != {
                    "file_sha256": file.sha256,
                    "facts_sha256": file.fact_directory_sha256,
                }:
                    raise ValueError("complete reproduction replay identity changed; validate the new input first")
                identity = (file.sha256, file.fact_directory_sha256)
                unique.setdefault(identity, file)
                if proof_blocker is None:
                    paired_identities.add(identity)
                else:
                    proof_blockers.setdefault(identity, proof_blocker)
                # An alias cannot weaken a Math capture's boundary/parity
                # gates just because another family lists the same bytes.
                if validation_families.get(identity) != "math-growth":
                    validation_families[identity] = case.family
                captured.append(file)
            except (OSError, ValueError) as error:
                errors[case.id] = str(error)
        case_files[case.id] = tuple(captured)
    return SuiteSelection(
        ", ".join(names),
        root,
        catalog,
        cases,
        tuple(unique.values()),
        case_files,
        errors,
        validation_families,
        {identity: reason for identity, reason in proof_blockers.items() if identity not in paired_identities},
        source_exclusions,
    )


def build_coverage(
    selection: SuiteSelection,
    pilot_path: Path,
    binary_hashes: Mapping[str, str] | None = None,
    report_records: Sequence[ReportRecord] = (),
    *,
    timeout_sec: int = 120,
) -> dict[str, Any]:
    """Project every expected case, current pilot evidence, and measured row counts."""

    records = load_pilot_records(pilot_path)
    rows: list[dict[str, Any]] = []
    for case in selection.cases:
        workloads: list[dict[str, Any]] = []
        for file in selection.case_files[case.id]:
            family = selection.validation_families[(file.sha256, file.fact_directory_sha256)]
            proof_blocker = selection.proof_blockers.get((file.sha256, file.fact_directory_sha256))
            evidence = (
                find_pilot_record(
                    records,
                    file,
                    family,
                    binary_hashes,
                    PilotPolicy(timeout_sec=timeout_sec),
                    selection.root,
                    treatment="proof-extraction",
                )
                if binary_hashes is not None
                else None
            )
            safety_stop = None
            if evidence is None and binary_hashes is not None:
                identity = pilot_identity(
                    file, family, binary_hashes, PilotPolicy(timeout_sec=timeout_sec), selection.root
                )
                safety_stop = next(
                    (
                        record
                        for record in reversed(records)
                        if record["identity"] == identity and record.get("operational_stop")
                    ),
                    None,
                )
            measurements = Counter(
                (row["treatment"], row["status"], row["timeout_sec"])
                for row in report_records
                if row["file_sha256"] == file.sha256
                and row["fact_directory_sha256"] == file.fact_directory_sha256
                and binary_hashes is not None
                and row["binary_sha256"] == binary_hashes.get(TREATMENT_SPECS[row["treatment"]].engine)
            )
            collection_reason = (
                pilot_safety_deferral(evidence, earlier=records, file=file)
                if evidence is None or evidence["status"] == "admitted"
                else None
            )
            pilot_reason = None
            if evidence is not None:
                pilot_reason = evidence["reason"]
            elif safety_stop is not None:
                collection_reason = "Safety stop; pilot incomplete"
                pilot_reason = safety_stop["reason"]
            preparation_by_treatment = {}
            for treatment in PROOF_TREATMENTS:
                reason: str | None
                if proof_blocker:
                    status, reason = "proof-query-blocked", proof_blocker
                elif binary_hashes is None:
                    status, reason = "pending", "current executable identities are unavailable"
                else:
                    status, reason = preparation_outcome(
                        file,
                        family,
                        binary_hashes,
                        selection.root,
                        records,
                        report_records,
                        timeout_sec,
                        treatment=treatment,
                    )
                preparation_by_treatment[treatment] = {"status": status, "reason": reason}
            if proof_blocker:
                pilot_reason = proof_blocker
                collection_reason = None
            workloads.append(
                {
                    "path": file.display_path,
                    "file_sha256": file.sha256,
                    "fact_directory_sha256": file.fact_directory_sha256,
                    "pilot_status": (
                        "proof-query-blocked" if proof_blocker else evidence["status"] if evidence else "not-validated"
                    ),
                    "pilot_reason": pilot_reason,
                    "admitted": not proof_blocker and evidence is not None and evidence["status"] == "admitted",
                    "collection_reason": collection_reason,
                    "preparation_status": preparation_by_treatment["proof-extraction"]["status"],
                    "preparation_reason": preparation_by_treatment["proof-extraction"]["reason"],
                    "preparation_by_treatment": preparation_by_treatment,
                    "measurements": [
                        {"treatment": key[0], "status": key[1], "timeout_sec": key[2], "rows": count}
                        for key, count in sorted(measurements.items())
                    ],
                }
            )
        rows.append(
            {
                "id": case.id,
                "family": case.family,
                "source": case.source,
                "capture_status": "missing" if case.id in selection.capture_errors else case.status,
                "reason": selection.capture_errors.get(case.id, case.reason),
                "workloads": workloads,
                "excluded_workloads": selection.source_exclusions.get(case.id, ()),
                **case.provenance,
            }
        )
    return {
        "suite": selection.name,
        "families": {
            name: selection.catalog.families.get(name, {}) for name in dict.fromkeys(c.family for c in selection.cases)
        },
        "expected_cases": len(rows),
        "unique_captured_workloads": len(selection.files),
        "binary_hashes": dict(binary_hashes) if binary_hashes is not None else None,
        "timeout_sec": timeout_sec,
        "cases": rows,
    }


def render_coverage_markdown(coverage: Mapping[str, Any]) -> str:
    """Keep failed, blocked, and unvalidated cases visible alongside admissions."""

    lines = [
        f"# {coverage['suite']} benchmark coverage",
        "",
        f"Expected cases: {coverage['expected_cases']}. "
        f"Unique captured workloads: {coverage['unique_captured_workloads']}.",
        "Off, recording, and extraction observations use the shared benchmark cache. "
        "Collection does not run screening or strict-proof checks.",
        "Inventoried, obtainable, blocked inputs, and deferred count source cases; "
        "raw calls count recorded engine calls, "
        "including fragments in a persistent session. Replays, ready, and measured count distinct replay workloads.",
        "Churchroad's five ordered fragments per circuit share one engine session; "
        "raw calls are not independent workloads.",
        "Explicit source-role omissions are listed separately below; they are not proof failures.",
        f"Measured requires 10 successful observations for that mode and off at {coverage['timeout_sec']} seconds, "
        "without a known proof-validation failure. "
        "Terminal errors and resource limits remain classified outcomes without repeated attempts.",
        "",
        "| Family | Inventoried | Obtainable | Raw calls | Replays | Ready record / extract | "
        "Measured record | Measured record + extract | Blocked inputs | Deferred |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for family in coverage["families"]:
        cases = [case for case in coverage["cases"] if case["family"] == family]
        replays = {(w["file_sha256"], w["fact_directory_sha256"]): w for c in cases for w in c["workloads"]}
        ready: Counter[str] = Counter()
        measured_counts: Counter[str] = Counter()
        for replay in replays.values():
            counts: Counter[str] = Counter()
            for row in replay["measurements"]:
                if row["timeout_sec"] == coverage["timeout_sec"] and row["status"] == "success":
                    counts[row["treatment"]] += row["rows"]
            for treatment in PROOF_TREATMENTS:
                is_ready = replay["preparation_by_treatment"][treatment]["status"] == "ready"
                ready[treatment] += is_ready
                measured_counts[treatment] += is_ready and counts["off"] >= 10 and counts[treatment] >= 10
        values = (
            family,
            len(cases),
            sum(c.get("obtainable", False) for c in cases),
            sum(len(c.get("invocations", [])) + len(c.get("ordered_calls", [])) for c in cases),
            len(replays),
            f"{ready['proofs']} / {ready['proof-extraction']}",
            measured_counts["proofs"],
            measured_counts["proof-extraction"],
            sum(
                c["capture_status"] in ("blocked", "missing")
                and (c.get("benchmark_selection") or {}).get("workloads") != []
                for c in cases
            ),
            sum(c["capture_status"] == "deferred" for c in cases),
        )
        lines.append("| " + " | ".join(map(str, values)) + " |")
    lines.extend(
        [
            "",
            "Partial source captures and pilot rejections remain in the case table below.",
            "",
            "| Family | Case | Replay preparation | Outcome | Measured rows | Reason |",
            "| --- | --- | --- | --- | --- | --- |",
        ]
    )
    for case in coverage["cases"]:
        workloads = cast(list[dict[str, Any]], case["workloads"])
        statuses = ", ".join(
            dict.fromkeys(
                f"{treatment}: {outcome['status']}"
                for workload in workloads
                for treatment, outcome in workload["preparation_by_treatment"].items()
            )
        ) or (
            "excluded from benchmarks"
            if (case.get("benchmark_selection") or {}).get("workloads") == []
            else "unavailable"
        )
        reasons = (
            [
                ("Source capture, including omitted calls: " if case.get("excluded_workloads") else "")
                + str(case["reason"])
            ]
            if case["reason"]
            else []
        )
        reasons.extend(str(w["pilot_reason"]) for w in workloads if w["pilot_reason"])
        reasons.extend(str(w["collection_reason"]) for w in workloads if w.get("collection_reason"))
        reasons.extend(
            str(outcome["reason"])
            for workload in workloads
            for outcome in workload["preparation_by_treatment"].values()
            if outcome["reason"]
        )
        measurements = Counter(
            f"{row['treatment']} {row['status']} ({row['timeout_sec']}s)"
            for workload in workloads
            for row in workload["measurements"]
            for _ in range(row["rows"])
        )
        measured = "; ".join(f"{label}: {count}" for label, count in measurements.items()) or "0"
        cells = (
            case["family"],
            case["id"],
            case["capture_status"],
            statuses,
            measured,
            "; ".join(dict.fromkeys(reasons)),
        )
        lines.append("| " + " | ".join(str(cell).replace("|", "\\|").replace("\n", " ") for cell in cells) + " |")
    if any(case.get("excluded_workloads") for case in coverage["cases"]):
        lines.extend(["", "## Source-role omissions", "", "| Case | Replay | Reason |", "| --- | --- | --- |"])
        for case in coverage["cases"]:
            for path in case.get("excluded_workloads", []):
                omitted_cells = (case["id"], path, case["benchmark_selection"]["reason"])
                lines.append(
                    "| " + " | ".join(str(cell).replace("|", "\\|").replace("\n", " ") for cell in omitted_cells) + " |"
                )
    return "\n".join(lines) + "\n"
