"""Resume complete source reproductions without reading the performance cache."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
from collections import Counter
from collections.abc import Sequence
from pathlib import Path
from typing import Any

from benchmarking.targets import sha256_file
from scripts.reproduction_corpus import write_corpus
from scripts.reproduction_dispatch import STOP_STATUSES, capture_case, capture_outcome, misaal_request
from scripts.reproduction_inventory import FAMILIES, expected_cases, select_cases
from scripts.reproduction_preparation import RECIPES, prepare_family
from scripts.reproduction_published import INPUT_KIND, published_entries, verify_input
from scripts.reproduction_stages import run_stage
from scripts.reproduction_validation import validate_capture

ROOT = Path(__file__).resolve().parents[1]
STORAGE = ROOT / "benchmarks/local/reproduction"
VALIDATABLE_STATUSES = {"reproduced", "ordinary-validation-pending", "ordinary-validation-failed"}
VALIDATION_SOURCES = (
    "scripts/reproduction_validation.py",
    "scripts/dialegg_speq_complete.py",
    "scripts/hardboiled_replay.py",
    "scripts/suite_capture_dialegg_speq.py",
    "scripts/paper_benchmarks/materialize.py",
    "scripts/paper_benchmarks/record_speq.py",
    "benchmarking/pilot.py",
    "benchmarking/memory_guard.py",
    "benchmarking/targets.py",
)


def compact_outcome(outcome: dict[str, Any], *, receipts: dict[Path, str | None] | None = None) -> dict[str, Any]:
    """Keep shared preparation/history as shallow links to immutable stage receipts.

    Current capture and validation records retain their existing verification
    contract. Preparation can describe an entire family, so embedding it in
    every case would multiply its potentially large artifact inventory.
    """
    if receipts is None:
        receipts = {}
    result = dict(outcome)
    targets = [key for key in ("preparation", "historical_outcome", "prior_outcome") if key in result]
    if outcome.get("preparation_stage"):
        targets.append("")
    for key in targets:
        record = outcome[key] if key else outcome
        summary = {
            name: record[name]
            for name in (
                "case",
                "stage",
                "status",
                "reason",
                "attempt",
                "identity_sha256",
                "started_at",
                "finished_at",
                "historical_status",
            )
            if name in record
        }
        if record.get("attempt"):
            receipt = Path(record["attempt"]) / "stage.json"
            summary["receipt"] = str(receipt)
            if record.get("receipt") == str(receipt) and "receipt_sha256" in record:
                # Retain the original identity, including missing evidence; a
                # changed file must not silently become the historical receipt.
                summary["receipt_sha256"] = record["receipt_sha256"]
            else:
                if receipt not in receipts:
                    receipts[receipt] = sha256_file(receipt) if receipt.is_file() else None
                summary["receipt_sha256"] = receipts[receipt]
        if key:
            result[key] = summary
        else:
            result = {**summary, "preparation_stage": True}
    return result


def write_index(path: Path, index: dict[str, Any]) -> None:
    """Project before persistence and atomically replace the current index."""
    receipts: dict[Path, str | None] = {}
    for case, outcome in index.items():
        index[case] = compact_outcome(outcome, receipts=receipts)
    temporary = path.with_suffix(".tmp")
    with temporary.open("w") as stream:
        json.dump(index, stream, indent=2)
        stream.write("\n")
    temporary.replace(path)


def resolve_case_settings(cases: list[dict[str, Any]], settings: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """Resolve exact-case budgets before identity, execution, and report checks.

    The override map is coordinator metadata. Only the selected numeric timeout
    enters each existing configuration; unrelated identities remain unchanged.
    """
    families = {case["id"]: case["family"] for case in cases}
    for family, config in settings.items():
        policy = config.get("raytrace_materialization_policy")
        if "materialization_policy" in config:
            raise ValueError("materialization_policy is a resolved case field, not a family setting")
        if policy is not None and (family != "eggcc" or policy != "raytrace-384mib-v1"):
            raise ValueError("unknown or non-Eggcc raytrace materialization policy")
        overrides = config.get("case_timeout_sec", {})
        if not isinstance(overrides, dict):
            raise ValueError(f"{family}.case_timeout_sec must map exact case IDs to positive finite seconds")
        if overrides and family != "eggcc":
            raise ValueError("case_timeout_sec overrides are supported only for Eggcc")
        for case_id, timeout in overrides.items():
            if families.get(case_id) != family:
                raise ValueError(f"unknown {family} case timeout ID: {case_id!r}")
            try:
                valid = type(timeout) in (int, float) and timeout > 0 and math.isfinite(timeout)
            except OverflowError:
                valid = False
            if not valid:
                raise ValueError(f"{case_id}: case timeout must be a positive finite number of seconds")
    resolved = {}
    for case in cases:
        if case["family"] not in settings:
            continue
        family_config = settings[case["family"]]
        if case.get("input_kind") != family_config.get("input_kind"):
            continue
        config = {
            key: value
            for key, value in family_config.items()
            if key not in {"case_timeout_sec", "raytrace_materialization_policy"}
        }
        if (
            case["family"] == "churchroad"
            and "source_root" in config.get("paths", {})
            and not (
                case["id"].startswith("churchroad-later-")
                and case.get("repository") == "https://github.com/gussmith23/churchroad-evaluation"
            )
        ):
            # Acquiring the later inputs must not change the original canary settings.
            config["paths"] = {key: value for key, value in config["paths"].items() if key != "source_root"}
        if case["id"] == "eggcc-raytrace--statewalk" and family_config.get("raytrace_materialization_policy"):
            config["materialization_policy"] = family_config["raytrace_materialization_policy"]
        if case["id"] in family_config.get("case_timeout_sec", {}):
            config["timeout_sec"] = family_config["case_timeout_sec"][case["id"]]
        resolved[case["id"]] = config
    return resolved


def preparation_blocker(case: dict[str, Any], settings: dict[str, Any]) -> dict[str, Any] | None:
    """Apply explicit dependency blockers only to their exact configuration fields."""
    for blocker in settings.get("configuration_blockers", []):
        if blocker.get("case_ids") is not None and case["id"] not in blocker["case_ids"]:
            continue
        constraint = blocker["configuration"]
        if not constraint:
            raise ValueError("a configuration blocker must identify the affected configuration")
        if all(case["configuration"].get(key) == value for key, value in constraint.items()):
            return {
                "status": "preparation-blocked",
                "reason": blocker["reason"],
                "evidence": blocker.get("evidence", []),
                "configuration": constraint,
            }
    return None


def case_identity(
    case: dict[str, Any], settings: dict[str, Any], *, hashes: dict[Path, str | None] | None = None
) -> dict[str, Any]:
    """Bind source/configuration, adapters, prepared tools, and declared dependencies."""
    paths = [
        ROOT / value for key, value in settings.get("paths", {}).items() if value is not None and key != "requests"
    ]
    runtime_trees: set[Path] = set()
    paths.extend(ROOT / value for value in settings.get("identity_paths", []))
    if case.get("input_kind") == INPUT_KIND:
        entry = published_entries()[case["id"]]
        verify_input(entry, (ROOT / settings["paths"]["inputs"] / entry["file"]).read_bytes())
    if case["family"] == "misaal":
        request = misaal_request(case, settings, ROOT)
        paths.append(ROOT / settings["paths"]["requests"] / f"{case['id']}.json")
        paths.extend(Path(request[key]) for key in ("backend", "python", "generator"))
        if request.get("egglog_export") != "egglog-only-v1":
            paths.append(Path(request["llvm_as"]))
        if "racket" in request:
            paths.append(Path(request["racket"]))
        if runtime := request.get("racket_runtime"):
            seal_path = Path(runtime["path"])
            paths.append(seal_path)
            seal = json.loads(seal_path.read_text())
            runtime_trees.update(Path(row["path"]) for row in seal["code_trees"].values())
            paths.extend(sorted(runtime_trees))
            paths.extend(Path(name) for name in seal["artifacts"])
        paths.extend(Path(request["checkout"]) / relative for relative in request["source_hashes"])
        paths.extend(Path(path) for path in request.get("identity_paths", []))
    # These are acquisition/adaptation implementations only. Hashes do not
    # migrate or partition the existing performance observation cache.
    scripts = [
        "scripts/reproduction_dispatch.py",
        "scripts/reproduction_inventory.py",
        "scripts/reproduction_stages.py",
        "scripts/reproduction_process.py",
        "scripts/reproduction_validation.py",
        "benchmarking/pilot.py",
        "benchmarking/memory_guard.py",
        "scripts/paper_benchmarks/materialize.py",
        "benchmarks/reproduction/population.json",
    ]
    family_scripts = {
        "speq": ["scripts/dialegg_speq_complete.py", "scripts/paper_benchmarks/record_speq.py"],
        "dialegg": ["scripts/dialegg_speq_complete.py", "scripts/suite_capture_dialegg_speq.py"],
        "eggcc": ["scripts/suite_capture_eggcc_churchroad.py", "scripts/eggcc_churchroad_complete.py"],
        "churchroad": ["scripts/suite_capture_eggcc_churchroad.py", "scripts/eggcc_churchroad_complete.py"],
        "misaal": [
            "scripts/misaal_reproduction.py",
            "scripts/suite_capture_hardboiled_misaal.py",
            "scripts/reproduction_misaal_export.py",
            "scripts/reproduction_misaal_patterns.py",
            "scripts/reproduction_misaal_groups.py",
            "scripts/reproduction_misaal_runtime.py",
        ],
        "hardboiled": (
            ["scripts/reproduction_published.py"]
            if case.get("input_kind") == INPUT_KIND
            else ["scripts/hardboiled_replay.py", "scripts/suite_capture_hardboiled_misaal.py"]
        ),
    }
    paths.extend(ROOT / name for name in (*scripts, *family_scripts[case["family"]], *VALIDATION_SOURCES))
    if case["family"] == "speq" and settings.get("phi_polarity_repair"):
        paths.extend(
            ROOT / name
            for name in (
                "scripts/speq_phi_diagnostic.py",
                "scripts/paper_benchmarks/speq_phi_harness.cpp",
                "scripts/paper_benchmarks/speq_phi_fixtures.ll",
            )
        )
    if case["family"] == "speq" and settings.get("c99_frontend_repair"):
        paths.extend(
            ROOT / name
            for name in (
                "scripts/speq_c99_diagnostic.py",
                "scripts/speq_c99_gates.py",
                "scripts/paper_benchmarks/speq_c99_fir.inc",
                "scripts/paper_benchmarks/speq_c99_harness.cpp",
                "scripts/paper_benchmarks/speq_c99_fixture.ll",
                "scripts/paper_benchmarks/speq_rev_plugin.cpp",
            )
        )
    if hashes is None:
        hashes = {}
    identities: dict[str, str | None] = {}
    for path in dict.fromkeys(paths):
        if path in hashes:
            identities[str(path.absolute())] = hashes[path]
            continue
        if path in runtime_trees:
            from scripts.reproduction_stages import directory_identity

            identities[str(path.absolute())] = "sha256:" + directory_identity(path)
        elif path.is_dir():
            digest = hashlib.sha256()
            for file in sorted(path.rglob("*")):
                relative = file.relative_to(path)
                if not file.is_file() or {".git", "__pycache__"}.intersection(relative.parts):
                    continue
                digest.update(relative.as_posix().encode() + b"\0" + sha256_file(file).encode() + b"\0")
            identities[str(path.absolute())] = "sha256:" + digest.hexdigest()
        else:
            identities[str(path.absolute())] = sha256_file(path) if path.is_file() else None
        hashes[path] = identities[str(path.absolute())]
    return {"case": case, "settings": settings, "inputs": identities}


def write_report(
    cases: list[dict[str, Any]], index: dict[str, Any], population: dict[str, Any], settings: dict[str, Any]
) -> None:
    """Keep every expected parent visible, with corpus results separate from paper cells."""
    resolved = resolve_case_settings(cases, settings)
    rows = []
    hashes: dict[Path, str | None] = {}
    receipts: dict[Path, str | None] = {}
    for case in cases:
        outcome = compact_outcome(
            index.get(case["id"], {"status": "pending", "reason": "not attempted"}), receipts=receipts
        )
        if case["id"] in index:
            index[case["id"]] = outcome
        config = resolved.get(case["id"])
        blocker = preparation_blocker(case, config if config is not None else {})
        if blocker and outcome["status"] != "success":
            prior = outcome.get("prior_outcome", outcome)
            outcome = compact_outcome(
                {**blocker, "prior_outcome": prior} if prior.get("attempt") else blocker, receipts=receipts
            )
            index[case["id"]] = outcome
        if outcome.get("identity_sha256") and not outcome.get("preparation_stage") and outcome["status"] != "pending":
            try:
                identity = case_identity(case, resolved[case["id"]], hashes=hashes)
                captured = outcome.get("capture_stage", outcome)
                digest = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
                if digest != captured.get("identity_sha256"):
                    raise ValueError("source, configuration, or tool identity changed")
                for record in (captured, outcome):
                    if (record["status"] == "success" and not record.get("artifacts")) or any(
                        not Path(path).is_file() or sha256_file(Path(path)) != expected
                        for path, expected in record.get("artifacts", {}).items()
                    ):
                        raise ValueError("retained evidence is missing or changed")
            except (OSError, KeyError, ValueError) as error:
                outcome = {
                    **outcome,
                    "status": "pending",
                    "historical_status": outcome["status"],
                    "reason": f"Stale evidence: {error}",
                }
                index[case["id"]] = outcome
        if outcome["status"] == "success" and outcome.get("stage") != "validate":
            outcome = {
                **outcome,
                "status": "pending",
                "reason": "capture completed; standalone validation stage is still required",
            }
        rows.append(
            {**case, "timeout_sec": config.get("timeout_sec", 300) if config is not None else None, "outcome": outcome}
        )
    hardboiled = population.get("hardboiled", {})
    published_hardboiled = hardboiled.get("input_kind") == INPUT_KIND
    native_history = hardboiled.get("native_history", hardboiled)
    paper_cells = [
        {**cell, "status": "mapping-unresolved" if cell["supported"] else "paper-unsupported"}
        for cell in native_history.get("amx_cells", [])
    ]
    report = {"cases": rows, "population": population, "hardboiled_amx_paper_cells": paper_cells}
    (STORAGE / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    lines = [
        "# Source inputs and ordinary replay",
        "",
        "These are source acquisition and standalone replay outcomes, not performance measurements.",
        *(
            ["HardBoiled uses the author's 42 published inputs; its native compiler history is separate."]
            if published_hardboiled
            else []
        ),
        "Timeouts apply separately to each ordinary replay; Eggcc source parents use the same budget. "
        "MISAAL source budgets remain in its requests; resource guards are unchanged.",
        "",
        "| Family | Required inputs | Reproduced | Pending | Other outcomes |",
        "|---|---:|---:|---:|---:|",
    ]
    for family in FAMILIES:
        scoped = [row for row in rows if row["family"] == family and row["scope"] == "required"]
        counts = Counter(row["outcome"]["status"] for row in scoped)
        lines.append(
            f"| {family} | {len(scoped)} | {counts['success']} | {counts['pending']} | "
            f"{len(scoped) - counts['success'] - counts['pending']} |"
        )
    if paper_cells:
        lines.extend(
            [
                "",
                (
                    "Historical HardBoiled AMX paper cells do not gate the author-published input suite. "
                    if published_hardboiled
                    else "HardBoiled AMX paper cells are separate from the five artifact programs. "
                )
                + "A successful native program does not establish its paper-cell mapping.",
                "",
                "| AMX schedule | Layout | Paper-cell outcome |",
                "|---|---|---|",
                *[f"| {cell['schedule']} | {cell['layout']} | {cell['status']} |" for cell in paper_cells],
                "",
                "Mapping evidence: [HardBoiled AMX audit](../../reproduction/hardboiled-amx-mapping.md).",
            ]
        )
    lines.extend(
        [
            "",
            (
                "The historical native HardBoiled inventory and AMX mapping gaps remain in population.json. "
                "They are not missing inputs in the selected author-published suite."
                if published_hardboiled
                else "HardBoiled's seven supported AMX paper cells still require an exact mapping "
                "to source configurations. "
                "The five published executables do not establish that mapping."
            ),
            "",
            "| Case | Scope | Ordinary replay timeout (seconds) | Outcome | Evidence or remaining requirement |",
            "|---|---|---:|---|---|",
        ]
    )
    for row in rows:
        result = row["outcome"]
        note = str(result.get("reason") or result.get("attempt") or "").replace("|", "\\|").replace("\n", " ")
        timeout = row["timeout_sec"] if row["timeout_sec"] is not None else "unconfigured"
        lines.append(f"| {row['id']} | {row['scope']} | {timeout} | {result['status']} | {note} |")
    (STORAGE / "REPORT.md").write_text("\n".join(lines) + "\n")
    write_corpus(rows, STORAGE / "corpus")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", action="append", choices=FAMILIES)
    parser.add_argument("--case", action="append", default=[])
    parser.add_argument(
        "--stage", choices=("inventory", "prepare", "capture", "validate", "report", "all"), default="all"
    )
    parser.add_argument("--settings", type=Path, default=STORAGE / "settings.json")
    parser.add_argument(
        "--resume-eggcc-capture",
        type=Path,
        help="verified complete native raytrace stage to materialize without rerunning",
    )
    parser.add_argument("--engine", type=Path, default=ROOT / "target/release/egglog-experimental")
    parser.add_argument(
        "--retry", action="store_true", help="Deliberately retry matching failed or successful attempts"
    )
    args = parser.parse_args(argv)
    population = json.loads((ROOT / "benchmarks/reproduction/population.json").read_text())
    catalog = json.loads((ROOT / "benchmarks/catalog.json").read_text())
    cases = expected_cases(catalog, population)
    selected = select_cases(cases, args.family or FAMILIES, args.case)
    settings = json.loads(args.settings.read_text()) if args.settings.is_file() else {}
    resolved = resolve_case_settings(cases, settings)
    if args.resume_eggcc_capture is not None and (
        args.stage not in {"capture", "all"}
        or [case["id"] for case in selected] != ["eggcc-raytrace--statewalk"]
        or resolved.get("eggcc-raytrace--statewalk", {}).get("materialization_policy") != "raytrace-384mib-v1"
    ):
        raise ValueError(
            "complete recovery requires one selected raytrace case and its explicit materialization policy"
        )
    STORAGE.mkdir(parents=True, exist_ok=True)
    (STORAGE / "inventory.json").write_text(json.dumps(cases, indent=2) + "\n")
    index_path = STORAGE / "index.json"
    index = json.loads(index_path.read_text()) if index_path.exists() else {}
    receipts: dict[Path, str | None] = {}
    index = {case: compact_outcome(outcome, receipts=receipts) for case, outcome in index.items()}
    if args.stage in ("inventory", "report"):
        write_report(cases, index, population, settings)
        write_index(index_path, index)
        print(f"{len(selected)} selected source/configuration requests; report: {STORAGE / 'REPORT.md'}")
        return 0
    safety_stop = False
    preparation_failures: set[str] = set()
    try:
        if args.stage in ("prepare", "all"):
            for family in dict.fromkeys(case["family"] for case in selected):
                input_kind = population.get(family, {}).get("input_kind")
                if (
                    args.stage == "all"
                    and family in settings
                    and settings[family].get("input_kind") == input_kind
                    and (family != "misaal" or settings[family].get("egglog_export") == "egglog-only-v1")
                ):
                    continue
                if family not in RECIPES:
                    preparation_failures.add(family)
                    print(f"{family} preparation: pending — pinned recipe is not integrated", flush=True)
                    for case in selected:
                        if case["family"] == family and family not in settings:
                            index[case["id"]] = {
                                "status": "pending",
                                "reason": f"pinned {family} preparation recipe is not integrated",
                            }
                    continue
                sources = [
                    "scripts/reproduction_preparation.py",
                    "scripts/reproduction_inventory.py",
                    "scripts/misaal_reproduction.py",
                    f"scripts/reproduction_prepare_{family}.py",
                    "scripts/reproduction_prepare_misaal.py",
                    "scripts/reproduction_prepare_misaal_cases.py",
                    "scripts/reproduction_prepare_misaal_arm.py",
                    "scripts/reproduction_prepare_misaal_hvx.py",
                    "scripts/reproduction_misaal_hvx_lowering.py",
                    "scripts/reproduction_misaal_legalizer.py",
                    "scripts/reproduction_prepare_hardboiled.py",
                    "scripts/eggcc_churchroad_complete.py",
                    "scripts/paper_benchmarks/record_speq.py",
                    "scripts/paper_benchmarks/materialize.py",
                    "scripts/reproduction_process.py",
                    "benchmarking/pilot.py",
                    "benchmarking/memory_guard.py",
                ]
                if family == "misaal":
                    sources = [
                        "scripts/reproduction_preparation.py",
                        "scripts/reproduction_inventory.py",
                        "scripts/misaal_reproduction.py",
                        "scripts/reproduction_misaal_export.py",
                        "scripts/reproduction_prepare_misaal.py",
                        "scripts/reproduction_prepare_misaal_cases.py",
                        "scripts/reproduction_misaal_patterns.py",
                        "scripts/reproduction_misaal_runtime.py",
                        "scripts/reproduction_process.py",
                        "benchmarking/pilot.py",
                        "benchmarking/memory_guard.py",
                    ]
                if family == "speq":
                    sources.extend(
                        [
                            "scripts/speq_phi_diagnostic.py",
                            "scripts/speq_c99_diagnostic.py",
                            "scripts/speq_c99_gates.py",
                            "scripts/paper_benchmarks/speq_phi_harness.cpp",
                            "scripts/paper_benchmarks/speq_phi_fixtures.ll",
                            "scripts/paper_benchmarks/speq_c99_fir.inc",
                            "scripts/paper_benchmarks/speq_c99_harness.cpp",
                            "scripts/paper_benchmarks/speq_c99_fixture.ll",
                            "scripts/paper_benchmarks/speq_rev_plugin.cpp",
                        ]
                    )
                if family == "eggcc":
                    sources.append("benchmarks/reproduction/fixtures/eggcc-core-row-order.patch")
                if input_kind == INPUT_KIND:
                    sources.extend(
                        ["scripts/reproduction_published.py", "scripts/reproduction_prepare_misaal_racket.py"]
                    )
                preparation_identity = {
                    "family": family,
                    "engine": str(args.engine.resolve()),
                    "engine_sha256": sha256_file(args.engine) if args.engine.is_file() else None,
                    "host": {"system": platform.system(), "machine": platform.machine(), "release": platform.release()},
                    "sources": {name: sha256_file(ROOT / name) for name in sources},
                    "inventory": {
                        name: sha256_file(ROOT / name)
                        for name in ("benchmarks/catalog.json", "benchmarks/reproduction/population.json")
                    },
                }

                if family == "misaal":
                    prior = settings.get(family, {})
                    templates = prior.get("export_templates", prior.get("paths", {}).get("requests"))
                    preparation_identity["export_templates"] = {
                        "path": templates,
                        "requests": {path.name: sha256_file(path) for path in sorted((ROOT / templates).glob("*.json"))}
                        if templates
                        else {},
                        "configuration_blockers": prior.get("configuration_blockers", []),
                    }
                    if prior.get("export_frontend"):
                        receipt = ROOT / prior["export_frontend"]
                        preparation_identity["export_frontend"] = {"path": str(receipt), "sha256": sha256_file(receipt)}

                prepared_now = False

                def prepare(attempt: Path, family: str = family, input_kind: str | None = input_kind) -> dict[str, Any]:
                    nonlocal prepared_now
                    prepared_now = True
                    if family == "misaal":
                        return prepare_family(family, attempt, args.engine, settings=settings.get(family, {}))
                    if input_kind is not None:
                        return prepare_family(family, attempt, args.engine, input_kind=input_kind)
                    return prepare_family(family, attempt, args.engine)

                prepared = run_stage(
                    STORAGE / "stages",
                    family + "-prerequisites",
                    "prepare",
                    preparation_identity,
                    prepare,
                    retry=args.retry,
                )
                print(f"{family} preparation: {prepared['status']}", flush=True)
                if prepared["status"] == "success":
                    config = json.loads(Path(prepared["settings"]).read_text())[family]
                    for field in ("case_timeout_sec", "raytrace_materialization_policy"):
                        if field in settings.get(family, {}):
                            config[field] = settings[family][field]
                    settings[family] = config
                    resolved = resolve_case_settings(cases, settings)
                    args.settings.parent.mkdir(parents=True, exist_ok=True)
                    temporary = args.settings.with_suffix(".tmp")
                    temporary.write_text(json.dumps(settings, indent=2) + "\n")
                    temporary.replace(args.settings)
                    for case in selected:
                        previous = index.get(case["id"], {})
                        if case["family"] == family and previous.get("preparation_stage"):
                            index[case["id"]] = compact_outcome(
                                {
                                    "status": "pending",
                                    "reason": "prerequisites prepared; complete source capture is required",
                                    "preparation": prepared,
                                    "historical_outcome": previous,
                                },
                                receipts=receipts,
                            )
                else:
                    preparation_failures.add(family)
                    for case in selected:
                        if case["family"] == family:
                            index[case["id"]] = compact_outcome(
                                {**prepared, "preparation_stage": True}, receipts=receipts
                            )
                if prepared_now and prepared["status"] in STOP_STATUSES:
                    safety_stop = True
                    break
        if args.stage == "prepare" or safety_stop:
            return 2 if safety_stop else 1 if preparation_failures else 0
        for case in selected:
            if case["family"] in preparation_failures:
                continue
            config = resolved.get(case["id"])
            if config is None:
                index[case["id"]] = {"status": "pending", "reason": "source/tool preparation is not configured"}
                continue
            if blocker := preparation_blocker(case, config):
                prior = index.get(case["id"], {})
                prior = prior.get("prior_outcome", prior)
                index[case["id"]] = compact_outcome(
                    {**blocker, "prior_outcome": prior} if prior.get("attempt") else blocker, receipts=receipts
                )
                print(f"{case['id']}: {blocker['status']} — {blocker['reason']}", flush=True)
                continue
            try:
                identity = case_identity(case, config)
            except (OSError, KeyError, ValueError) as error:
                index[case["id"]] = {"status": "pending", "reason": f"source identity is not verified: {error}"}
                continue

            executed_now = False

            def execute(
                attempt: Path,
                case: dict[str, Any] = case,
                config: dict[str, Any] = config,
                identity: dict[str, Any] = identity,
            ) -> dict[str, Any]:
                nonlocal executed_now
                executed_now = True
                output = attempt / "capture"
                if config.get("materialization_policy"):
                    from scripts.suite_capture_eggcc_churchroad import RAYTRACE_EVIDENCE_BYTES, capture_complete

                    paths = {key: ROOT / value for key, value in config["paths"].items() if value is not None}
                    result = capture_complete(
                        "eggcc",
                        [{**case, "native_options": case["configuration"].get("native_options", [])}],
                        output,
                        paths["checkout"],
                        paths["binary"],
                        paths["egglog"],
                        timeout_sec=config.get("timeout_sec", 300),
                        max_evidence_bytes=RAYTRACE_EVIDENCE_BYTES,
                        validate_ordinary=False,
                        resume_stage=args.resume_eggcc_capture,
                        resume_identity=identity,
                    )[0]
                else:
                    result = capture_case(case, config, output)
                receipt = attempt / "capture-result.json"
                receipt.write_text(json.dumps(result, indent=2, default=str) + "\n")
                return {
                    "status": capture_outcome(result),
                    "reason": result.get("reason"),
                    "capture": str(receipt),
                    "artifacts": [
                        str(path) for path in attempt.rglob("*") if path.is_file() and path.name != "stage.json"
                    ],
                }

            if args.stage == "validate":
                result = index.get(case["id"], {})
                result = result.get("capture_stage", result)
                if not result.get("capture"):
                    index[case["id"]] = {"status": "pending", "reason": "complete source capture is required first"}
                    continue
                expected = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
                if result.get("identity_sha256") != expected or any(
                    not Path(path).is_file() or sha256_file(Path(path)) != digest
                    for path, digest in result["artifacts"].items()
                ):
                    index[case["id"]] = {
                        **result,
                        "status": "pending",
                        "reason": "capture identity or evidence changed; run capture first",
                    }
                    continue
            else:
                result = run_stage(STORAGE / "stages", case["id"], "complete", identity, execute, retry=args.retry)
            index[case["id"]] = result
            write_index(index_path, index)
            if args.stage in {"all", "validate"} and result.get("capture") and result["status"] not in STOP_STATUSES:
                captured = json.loads(Path(result["capture"]).read_text())
                if captured.get("status") in VALIDATABLE_STATUSES and (
                    captured.get("input_kind") == INPUT_KIND
                    or captured.get("source_completion", {}).get("status") in {"success", "complete"}
                ):
                    engine = ROOT / config["paths"]["egglog"]
                    validation_identity = {
                        "capture_sha256": sha256_file(Path(result["capture"])),
                        "artifacts": result["artifacts"],
                        "engine_sha256": sha256_file(engine),
                        "validation_sources": {name: sha256_file(ROOT / name) for name in VALIDATION_SOURCES},
                        "timeout_sec": config.get("timeout_sec", 300),
                    }

                    def validate(
                        attempt: Path,
                        captured: dict[str, Any] = captured,
                        engine: Path = engine,
                        config: dict[str, Any] = config,
                    ) -> dict[str, Any]:
                        nonlocal executed_now
                        executed_now = True
                        checked = validate_capture(
                            captured, engine, attempt / "replay", timeout_sec=config.get("timeout_sec", 300)
                        )
                        return {
                            **checked,
                            "artifacts": [
                                str(path) for path in attempt.rglob("*") if path.is_file() and path.name != "stage.json"
                            ],
                        }

                    validation = run_stage(
                        STORAGE / "stages", case["id"], "validate", validation_identity, validate, retry=args.retry
                    )
                    result = {**validation, "capture_stage": result}
            index[case["id"]] = result
            write_index(index_path, index)
            print(
                f"{case['id']}: {result['status']}" + (f" — {result['reason']}" if result.get("reason") else ""),
                flush=True,
            )
            # A fresh stop halts this invocation. On resume, an intact cached
            # failure launches nothing and must not block unrelated cases.
            if executed_now and result["status"] in STOP_STATUSES:
                safety_stop = True
                break
    finally:
        write_report(cases, index, population, settings)
        write_index(index_path, index)
    unresolved_paper_cells = (
        args.stage == "all"
        and not args.case
        and any(case["family"] == "hardboiled" for case in selected)
        and any(
            cell["supported"] and cell["source_mapping"] == "unresolved"
            for cell in population.get("hardboiled", {}).get("amx_cells", [])
        )
    )
    if safety_stop:
        return 2
    return (
        0
        if not unresolved_paper_cells and all(index.get(case["id"], {}).get("status") == "success" for case in selected)
        else 1
    )


if __name__ == "__main__":
    raise SystemExit(main())
