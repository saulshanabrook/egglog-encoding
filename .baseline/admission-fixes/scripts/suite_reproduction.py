"""Resume complete source reproductions without reading the performance cache."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from collections.abc import Sequence
from pathlib import Path
from typing import Any

from benchmarking.targets import sha256_file
from scripts.reproduction_inventory import FAMILIES, expected_cases, select_cases
from scripts.reproduction_stages import run_stage
from scripts.reproduction_validation import validate_capture

ROOT = Path(__file__).resolve().parents[1]
STORAGE = ROOT / "benchmarks/local/reproduction"
STOP_STATUSES = {"resource-stopped", "memory-limit", "timed-out", "cancelled", "interrupted"}


def capture_case(case: dict[str, Any], settings: dict[str, Any], output: Path) -> dict[str, Any]:
    """Delegate in-process so each adapter owns its monitored native process group."""
    family = case["family"]
    paths = {key: (ROOT / value).absolute() for key, value in settings["paths"].items() if value is not None}
    timeout = float(settings.get("timeout_sec", 300))
    if family in ("dialegg", "speq"):
        from scripts.dialegg_speq_complete import complete_capture

        args = argparse.Namespace(
            **{"speq_rev_plugin": None, **paths},
            family=family,
            case=[case["id"]],
            output=output,
            timeout_sec=timeout,
            speq_frontend_flag=settings.get("frontend_flags", []),
        )
        code = complete_capture(args)
        manifest = json.loads((output / "manifest.json").read_text())
        capture = manifest["families"][family]
        row = capture["cases"].get(case["id"], {"status": "pending", "reason": "stopped before this case"})
        if code == 2:
            stop = capture["operational_stop"]
            row = {**row, "status": stop["status"], "reason": stop.get("message") or row.get("reason")}
        return dict(row)
    if family in ("eggcc", "churchroad"):
        from scripts.suite_capture_eggcc_churchroad import capture_complete

        source_case = {**case, "native_options": case["configuration"].get("native_options", [])}
        records = capture_complete(
            family,
            [source_case],
            output,
            paths["checkout"],
            paths["binary"],
            paths["egglog"],
            timeout_sec=timeout,
        )
        return dict(records[0])
    if family == "misaal":
        from scripts.misaal_reproduction import capture_misaal

        request = paths["requests"] / f"{case['id']}.json"
        if not request.is_file():
            return {"status": "pending", "reason": f"complete native request not prepared: {request}"}
        return dict(capture_misaal(request, output))
    if family == "hardboiled":
        from scripts.suite_capture_hardboiled_misaal import capture_hardboiled, prepare_hardboiled_capture

        output.mkdir(parents=True)
        capture_hardboiled(
            paths["checkout"],
            paths["build"],
            output / "native",
            paths["sidecar"],
            {case["id"]},
            optimization_only=True,
            library=paths["library"],
            compiler=str(paths["compiler"]),
            case_records=[case],
            revision=settings["revision"],
        )
        return dict(prepare_hardboiled_capture(output / "native/cases.json", output / "replays")[0])
    raise ValueError(f"unknown reproduction family {family}")


def capture_outcome(capture: dict[str, Any]) -> str:
    """Propagate nested adapter safety stops before considering completion."""
    stack: list[Any] = [capture]
    while stack:
        value = stack.pop()
        if isinstance(value, dict):
            if value.get("status") in STOP_STATUSES:
                return str(value["status"])
            stack.extend(value.values())
        elif isinstance(value, list):
            stack.extend(value)
    if capture.get("resource_stop"):
        return "resource-stopped"
    if capture["status"] == "reproduced":
        if not capture.get("workloads") or capture.get("source_completion", {}).get("status") not in {
            "success",
            "complete",
        }:
            raise ValueError("adapter reported reproduction without successful source completion and replay outputs")
        return "success"
    return str(capture["status"])


def case_identity(case: dict[str, Any], settings: dict[str, Any]) -> dict[str, Any]:
    """Bind source/configuration, adapters, prepared tools, and declared dependencies."""
    paths = [ROOT / value for value in settings.get("paths", {}).values() if value is not None]
    paths.extend(ROOT / value for value in settings.get("identity_paths", []))
    # These are acquisition/adaptation implementations only. Hashes do not
    # migrate or partition the existing performance observation cache.
    scripts = [
        "scripts/suite_reproduction.py",
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
        "misaal": ["scripts/misaal_reproduction.py", "scripts/suite_capture_hardboiled_misaal.py"],
        "hardboiled": ["scripts/hardboiled_replay.py", "scripts/suite_capture_hardboiled_misaal.py"],
    }
    paths.extend(ROOT / name for name in (*scripts, *family_scripts[case["family"]]))
    identities: dict[str, str | None] = {}
    for path in dict.fromkeys(paths):
        if path.is_dir():
            digest = hashlib.sha256()
            for file in sorted(path.rglob("*")):
                relative = file.relative_to(path)
                if not file.is_file() or {".git", "__pycache__"}.intersection(relative.parts):
                    continue
                digest.update(relative.as_posix().encode() + b"\0" + sha256_file(file).encode() + b"\0")
            identities[str(path.absolute())] = "sha256:" + digest.hexdigest()
        else:
            identities[str(path.absolute())] = sha256_file(path) if path.is_file() else None
    return {"case": case, "settings": settings, "inputs": identities}


def write_report(cases: list[dict[str, Any]], index: dict[str, Any], population: dict[str, Any]) -> None:
    """Keep every expected parent visible, with corpus results separate from paper cells."""
    rows = [
        {**case, "outcome": index.get(case["id"], {"status": "pending", "reason": "not attempted"})} for case in cases
    ]
    report = {"cases": rows, "population": population}
    (STORAGE / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    lines = [
        "# Complete source reproduction",
        "",
        "These are source-optimization and standalone replay outcomes, not performance measurements.",
        "",
        "| Family | Required parents | Reproduced | Pending | Other outcomes |",
        "|---|---:|---:|---:|---:|",
    ]
    for family in FAMILIES:
        scoped = [row for row in rows if row["family"] == family and row["scope"] == "required"]
        counts = Counter(row["outcome"]["status"] for row in scoped)
        lines.append(
            f"| {family} | {len(scoped)} | {counts['success']} | {counts['pending']} | "
            f"{len(scoped) - counts['success'] - counts['pending']} |"
        )
    lines.extend(
        [
            "",
            "HardBoiled's seven supported AMX paper cells still require an exact mapping to source configurations. "
            "The five published executables do not establish that mapping.",
            "",
            "| Case | Scope | Outcome | Evidence or remaining requirement |",
            "|---|---|---|---|",
        ]
    )
    for row in rows:
        result = row["outcome"]
        note = str(result.get("reason") or result.get("attempt") or "").replace("|", "\\|").replace("\n", " ")
        lines.append(f"| {row['id']} | {row['scope']} | {result['status']} | {note} |")
    (STORAGE / "REPORT.md").write_text("\n".join(lines) + "\n")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", action="append", choices=FAMILIES)
    parser.add_argument("--case", action="append", default=[])
    parser.add_argument("--stage", choices=("inventory", "capture", "validate", "report", "all"), default="all")
    parser.add_argument("--settings", type=Path, default=STORAGE / "settings.json")
    parser.add_argument(
        "--retry", action="store_true", help="Deliberately retry matching failed or successful attempts"
    )
    args = parser.parse_args(argv)
    population = json.loads((ROOT / "benchmarks/reproduction/population.json").read_text())
    catalog = json.loads((ROOT / "benchmarks/catalog.json").read_text())
    cases = expected_cases(catalog, population)
    selected = select_cases(cases, args.family or FAMILIES, args.case)
    STORAGE.mkdir(parents=True, exist_ok=True)
    (STORAGE / "inventory.json").write_text(json.dumps(cases, indent=2) + "\n")
    index_path = STORAGE / "index.json"
    index = json.loads(index_path.read_text()) if index_path.exists() else {}
    if args.stage in ("inventory", "report"):
        write_report(cases, index, population)
        print(f"{len(selected)} selected source/configuration requests; report: {STORAGE / 'REPORT.md'}")
        return 0
    settings = json.loads(args.settings.read_text()) if args.settings.is_file() else {}
    safety_stop = False
    try:
        for case in selected:
            config = settings.get(case["family"])
            if config is None:
                index[case["id"]] = {"status": "pending", "reason": "source/tool preparation is not configured"}
                continue
            identity = case_identity(case, config)

            def execute(attempt: Path, case: dict[str, Any] = case, config: dict[str, Any] = config) -> dict[str, Any]:
                output = attempt / "capture"
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
            index_path.write_text(json.dumps(index, indent=2) + "\n")
            if args.stage in {"all", "validate"} and result.get("capture") and result["status"] not in STOP_STATUSES:
                captured = json.loads(Path(result["capture"]).read_text())
                if captured.get("source_completion", {}).get("status") in {"success", "complete"}:
                    engine = ROOT / config["paths"]["egglog"]
                    validation_identity = {
                        "capture_sha256": sha256_file(Path(result["capture"])),
                        "artifacts": result["artifacts"],
                        "engine_sha256": sha256_file(engine),
                        "validator_sha256": sha256_file(ROOT / "scripts/reproduction_validation.py"),
                        "timeout_sec": config.get("timeout_sec", 300),
                    }

                    def validate(
                        attempt: Path,
                        captured: dict[str, Any] = captured,
                        engine: Path = engine,
                        config: dict[str, Any] = config,
                    ) -> dict[str, Any]:
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
            index_path.write_text(json.dumps(index, indent=2) + "\n")
            print(
                f"{case['id']}: {result['status']}" + (f" — {result['reason']}" if result.get("reason") else ""),
                flush=True,
            )
            if result["status"] in STOP_STATUSES:
                safety_stop = True
                break
    finally:
        index_path.write_text(json.dumps(index, indent=2) + "\n")
        write_report(cases, index, population)
    return (
        2 if safety_stop else 0 if all(index.get(case["id"], {}).get("status") == "success" for case in selected) else 1
    )


if __name__ == "__main__":
    raise SystemExit(main())
