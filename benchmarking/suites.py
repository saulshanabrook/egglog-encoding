"""Resolve a prepared source manifest without losing aliases or unavailable cases."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Literal, NotRequired, TypedDict

from .models import BenchmarkEndpoint, DisequalityEncoding, FileSpec
from .reports.store import CacheKey, ReportRecord, ReportStore
from .workloads import resolve_files

MANIFEST_RELATIVE_PATH = Path("benchmarks/local/corpus/manifest.json")
EXPANDED_FAMILIES = ("math-growth", "eggcc", "luminal", "hardboiled", "misaal", "churchroad", "dialegg", "speq")
SUITE_NAMES = ("expanded", "math-11", *EXPANDED_FAMILIES)
VALIDATION_POLICY = "proof-testing-v1"
SAFETY_POLICY = "memory-guard-v1"
type ProofTreatment = Literal["proofs", "proof-extraction"]
PROOF_TREATMENTS: tuple[ProofTreatment, ...] = ("proofs", "proof-extraction")


class CorpusOutcome(TypedDict):
    file_sha256: str
    fact_directory_sha256: str
    binary_sha256: str
    timeout_sec: int
    disequality_encoding: DisequalityEncoding
    kind: Literal["validation", "safety"]
    policy: str
    status: Literal["success", "failure", "deferred"]
    reason: str | None
    evidence: NotRequired[str]


@dataclass(frozen=True)
class WorkloadAlias:
    case: str
    order: int


@dataclass(frozen=True)
class ManifestWorkload:
    file: str
    sha256: str
    facts_sha256: str
    aliases: tuple[WorkloadAlias, ...]
    adaptations: tuple[str, ...]
    facts: str | None = None


@dataclass(frozen=True)
class CorpusCase:
    id: str
    family: str
    source: str
    status: Literal["ready", "blocked", "excluded", "pending"]
    workloads: tuple[str, ...]
    reason: str | None = None
    configuration: Any = None
    evidence: str | None = None


@dataclass(frozen=True)
class CorpusManifest:
    path: Path
    sources: dict[str, dict[str, Any]]
    cases: tuple[CorpusCase, ...]
    workloads: tuple[ManifestWorkload, ...]
    outcomes: tuple[CorpusOutcome, ...]
    preparation: dict[str, Any] = field(default_factory=dict)


def load_manifest(root: Path) -> CorpusManifest:
    """Read prepared identities and source outcomes, without opening workload files."""

    path = root / MANIFEST_RELATIVE_PATH
    if not path.is_file():
        raise ValueError(f"prepared corpus manifest is missing: {path}; run make reproduce-benchmarks")
    try:
        raw = json.loads(path.read_text())
        cases = tuple(
            CorpusCase(
                case["id"],
                case["family"],
                case["source"],
                case["status"],
                tuple(case["workloads"]),
                case.get("reason"),
                case.get("configuration"),
                case.get("evidence"),
            )
            for case in raw["cases"]
        )
        workloads = tuple(
            ManifestWorkload(
                workload["file"],
                workload["sha256"],
                workload.get("facts_sha256", ""),
                tuple(WorkloadAlias(alias["case"], alias["order"]) for alias in workload["aliases"]),
                tuple(workload.get("adaptations", ())),
                workload.get("facts"),
            )
            for workload in raw["workloads"]
        )
        if len({case.id for case in cases}) != len(cases):
            raise ValueError("source case IDs must be unique")
        if any(case.status not in ("ready", "blocked", "excluded", "pending") for case in cases):
            raise ValueError("unsupported source status")
        files = {workload.file for workload in workloads}
        if len(files) != len(workloads):
            raise ValueError("manifest workload paths must be unique")
        if any(set(case.workloads) - files for case in cases):
            raise ValueError("source case references an unknown workload")
        case_ids = {case.id for case in cases}
        if any(alias.case not in case_ids for workload in workloads for alias in workload.aliases):
            raise ValueError("workload alias references an unknown case")
        return CorpusManifest(
            path, raw["sources"], cases, workloads, tuple(raw.get("outcomes", ())), raw.get("preparation", {})
        )
    except (KeyError, TypeError, ValueError) as error:
        raise ValueError(f"invalid corpus manifest {path}: {error}") from error


@dataclass(frozen=True)
class SuiteSelection:
    name: str
    root: Path
    manifest: CorpusManifest
    cases: tuple[CorpusCase, ...]
    files: tuple[FileSpec, ...]
    case_files: dict[str, tuple[FileSpec, ...]]
    capture_errors: dict[str, str] = field(default_factory=dict)


def resolve_suite(name: str | Sequence[str], root: Path) -> SuiteSelection:
    """Resolve manifest order, verify prepared inputs, and deduplicate exact identities."""

    names = (name,) if isinstance(name, str) else tuple(dict.fromkeys(name))
    if not names or any(value not in SUITE_NAMES for value in names):
        raise ValueError(f"unknown benchmark suite {name!r}; choose from {', '.join(SUITE_NAMES)}")
    manifest = load_manifest(root)
    families = EXPANDED_FAMILIES if "expanded" in names else names
    cases = tuple(
        case
        for case in manifest.cases
        if case.family in families or ("math-11" in names and case.family == "math-growth")
    )
    by_path = {workload.file: workload for workload in manifest.workloads}
    unique: dict[tuple[str, str], FileSpec] = {}
    case_files: dict[str, tuple[FileSpec, ...]] = {}
    errors: dict[str, str] = {}
    for case in cases:
        captured: list[FileSpec] = []
        for path in case.workloads if case.status != "excluded" else ():
            workload = by_path[path]
            try:
                absolute = manifest.path.parent / path
                if Path(path).is_absolute() or not absolute.resolve().is_relative_to(root.resolve()):
                    raise ValueError(f"manifest workload must stay within the checkout: {path}")
                file = resolve_files((path,), manifest.path.parent, workload.facts)[0]
                if (file.sha256, file.fact_directory_sha256) != (workload.sha256, workload.facts_sha256):
                    raise ValueError(f"prepared workload identity changed: {path}; regenerate the corpus")
                unique.setdefault((file.sha256, file.fact_directory_sha256), file)
                captured.append(file)
            except (OSError, ValueError) as error:
                errors[case.id] = str(error)
        case_files[case.id] = tuple(captured)
    return SuiteSelection(", ".join(names), root, manifest, cases, tuple(unique.values()), case_files, errors)


def suite_outcomes(
    selection: SuiteSelection,
    endpoints: Sequence[BenchmarkEndpoint],
    timeout_sec: int,
) -> tuple[tuple[tuple[FileSpec, str], ...], tuple[tuple[FileSpec, str], ...]]:
    """Separate exact strict failures from historical operational safety deferrals."""

    validation: list[tuple[FileSpec, str]] = []
    deferred: list[tuple[FileSpec, str]] = []
    for file in selection.files:
        matching = [
            record
            for record in selection.manifest.outcomes
            if (record["file_sha256"], record["fact_directory_sha256"]) == (file.sha256, file.fact_directory_sha256)
        ]
        for endpoint in endpoints:
            key = CacheKey.for_endpoint(endpoint, file, timeout_sec)
            exact = next(
                (
                    record
                    for record in reversed(matching)
                    if record["kind"] == "validation"
                    and record["policy"] == VALIDATION_POLICY
                    and record["binary_sha256"] == key.binary_sha256
                    and record["timeout_sec"] == key.timeout_sec
                    and record["disequality_encoding"] == key.disequality_encoding
                ),
                None,
            )
            if exact is not None and exact["status"] != "success":
                validation.append((file, exact["reason"] or "strict proof validation failed"))
                break
        safety = next(
            (
                record
                for record in reversed(matching)
                if record["kind"] == "safety" and record["policy"] == SAFETY_POLICY
            ),
            None,
        )
        if safety is not None and safety["status"] != "success":
            deferred.append((file, safety["reason"] or "historically unsafe workload deferred"))
    return tuple(validation), tuple(deferred)


def build_coverage(
    selection: SuiteSelection,
    binary_hashes: Mapping[str, str] | None = None,
    report_records: Sequence[ReportRecord] = (),
    *,
    timeout_sec: int = 300,
) -> dict[str, Any]:
    """Show every expected source case, alias, outcome, and matching measured row."""

    cases = []
    for case in selection.cases:
        workloads = []
        for file in selection.case_files[case.id]:
            measurements = Counter(
                (row["binary_sha256"], row["treatment"], row["disequality_encoding"], row["status"])
                for row in report_records
                if (row["file_sha256"], row["fact_directory_sha256"], row["timeout_sec"])
                == (file.sha256, file.fact_directory_sha256, timeout_sec)
                and (binary_hashes is None or row["binary_sha256"] in binary_hashes.values())
            )
            workloads.append(
                {
                    "path": file.display_path,
                    "file_sha256": file.sha256,
                    "fact_directory_sha256": file.fact_directory_sha256,
                    "measurements": [
                        dict(zip(("binary", "treatment", "disequality", "status", "rows"), (*key, n), strict=True))
                        for key, n in sorted(measurements.items())
                    ],
                    "outcomes": [
                        record
                        for record in selection.manifest.outcomes
                        if (record["file_sha256"], record["fact_directory_sha256"])
                        == (file.sha256, file.fact_directory_sha256)
                    ],
                }
            )
        cases.append(
            {
                "id": case.id,
                "family": case.family,
                "source": case.source,
                "status": "missing" if case.id in selection.capture_errors else case.status,
                "reason": selection.capture_errors.get(case.id, case.reason),
                "workloads": workloads,
            }
        )
    return {
        "suite": selection.name,
        "expected_cases": len(cases),
        "unique_workloads": len(selection.files),
        "timeout_sec": timeout_sec,
        "cases": cases,
        "exclusions": [
            {"family": family, "reason": source["excluded"]}
            for family, source in selection.manifest.sources.items()
            if source.get("excluded")
            and ("expanded" in selection.name.split(", ") or family in selection.name.split(", "))
        ],
    }


def render_coverage_markdown(coverage: Mapping[str, Any]) -> str:
    lines = [
        f"# {coverage['suite']} benchmark coverage",
        "",
        f"Expected source cases: {coverage['expected_cases']}. Unique workloads: {coverage['unique_workloads']}.",
        "Aliases remain separate source cases. All exact-identity observations contribute to suite analysis.",
        "Strict validation is separate from timing collection.",
        "",
        "| Family | Case | Status | Workloads | Observations | Reason |",
        "| --- | --- | --- | ---: | --- | --- |",
    ]
    for case in coverage["cases"]:
        observations = [
            f"{row['treatment']}/{row['disequality']}: {row['rows']} {row['status']}"
            for workload in case["workloads"]
            for row in workload["measurements"]
        ]
        reasons = [case["reason"]] if case["reason"] else []
        reasons.extend(
            outcome["reason"] or outcome["status"]
            for workload in case["workloads"]
            for outcome in workload["outcomes"]
            if outcome["status"] != "success"
        )
        values = (
            case["family"],
            case["id"],
            case["status"],
            len(case["workloads"]),
            "; ".join(observations) or "none",
            "; ".join(dict.fromkeys(reasons)),
        )
        lines.append("| " + " | ".join(str(value).replace("|", "\\|").replace("\n", " ") for value in values) + " |")
    for exclusion in coverage["exclusions"]:
        lines.extend(("", f"Excluded {exclusion['family']}: {exclusion['reason']}"))
    return "\n".join(lines) + "\n"


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", choices=SUITE_NAMES, default="expanded")
    parser.add_argument("--report", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--timeout-sec", type=int, default=300)
    args = parser.parse_args(argv)
    selection = resolve_suite(args.suite, Path(__file__).resolve().parents[1])
    rows = ReportStore(args.report).records if args.report else ()
    rendered = render_coverage_markdown(build_coverage(selection, report_records=rows, timeout_sec=args.timeout_sec))
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    else:
        print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
