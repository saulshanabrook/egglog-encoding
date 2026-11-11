"""Publish retained complete Egglog workloads without rerunning their source compilers."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from collections import Counter
from dataclasses import asdict
from pathlib import Path
from typing import Any

from benchmarking.pilot import PilotProcessResult, run_bounded_command
from benchmarking.targets import sha256_file
from scripts.dialegg_speq_complete import validate_extract_output
from scripts.hardboiled_replay import egglog_forms, native_check_contract
from scripts.reproduction_corpus import write_corpus
from scripts.reproduction_inventory import FAMILIES, expected_cases
from scripts.reproduction_stages import directory_identity


def verify_files(artifacts: dict[str, str], hashes: dict[Path, str], root: Path) -> None:
    """Verify retained bytes once per inspection, without hashing live source trees."""
    for name, expected in artifacts.items():
        path = (root / name).resolve()
        if path not in hashes:
            hashes[path] = sha256_file(path)
        if hashes[path].removeprefix("sha256:") != expected.removeprefix("sha256:"):
            raise ValueError(f"retained evidence changed: {path}")


def read_stage(reference: dict[str, Any], root: Path, hashes: dict[Path, str]) -> dict[str, Any]:
    """Resolve the original receipt and verify its identity and declared outputs."""
    path = (root / reference["attempt"] / "stage.json").resolve()
    record: dict[str, Any] = json.loads(path.read_text())
    digest = hashlib.sha256(json.dumps(record["identity"], sort_keys=True).encode()).hexdigest()
    if (
        digest != record["identity_sha256"]
        or digest != reference["identity_sha256"]
        or Path(record["attempt"]).resolve() != path.parent
        or record["case"] != reference["case"]
        or record["stage"] != reference["stage"]
    ):
        raise ValueError(f"retained receipt identity changed: {path}")
    if reference.get("receipt_sha256"):
        verify_files({str(path): reference["receipt_sha256"]}, hashes, root)
    if any(
        reference[key] != record.get(key)
        for key in ("artifacts", "artifact_directories", "workloads", "validations", "capture")
        if key in reference
    ):
        raise ValueError(f"retained receipt outputs changed: {path}")
    if record["status"] == "success" and not record["artifacts"]:
        raise ValueError(f"successful receipt has no artifacts: {path}")
    verify_files(record["artifacts"], hashes, root)
    for name, expected in record.get("artifact_directories", {}).items():
        if directory_identity(root / name) != expected:
            raise ValueError(f"retained evidence directory changed: {name}")
    return record


def retained_rows(root: Path) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Recover original validations and enumerate unvalidated independent MISAAL calls.

    Current index status is only discovery metadata. Success must come from its
    original receipt, bound to the capture receipt and the exact replay bytes.
    Missing or changed evidence remains an explicit blocked row.
    """
    catalog = json.loads((root / "benchmarks/catalog.json").read_text())
    population = json.loads((root / "benchmarks/reproduction/population.json").read_text())
    index = json.loads((root / "benchmarks/local/reproduction/index.json").read_text())
    rows: list[dict[str, Any]] = []
    jobs: dict[str, dict[str, Any]] = {}
    hashes: dict[Path, str] = {}
    native_captures: dict[Path, dict[str, Any]] = {}
    for case in expected_cases(catalog, population):
        reference = index.get(case["id"], {})
        if case["family"] == "misaal" and reference.get("stage") != "validate":
            continue
        row = {**case, "outcome": {"status": "blocked", "reason": reference.get("reason", "no retained validation")}}
        rows.append(row)
        if not reference.get("attempt") or reference.get("preparation_stage"):
            continue
        try:
            validation = read_stage(reference, root, hashes)
            if validation["stage"] != "validate" or validation["status"] != "success":
                row["outcome"] = {"status": validation["status"], "reason": validation.get("reason")}
                continue
            capture = read_stage(reference["capture_stage"], root, hashes)
            capture["receipt_sha256"] = sha256_file(Path(capture["attempt"]) / "stage.json")
            capture_path = root / capture["capture"]
            if (
                validation["identity"]["capture_sha256"] != sha256_file(capture_path)
                or validation["identity"]["artifacts"] != capture["artifacts"]
                or capture["identity"]["case"]["id"] != case["id"]
            ):
                raise ValueError("validation does not bind this retained source capture")
            # Retain the captured configuration, rather than relabeling old bytes
            # with the current acquisition recipe.
            row.update(capture["identity"]["case"])
            row["completion_scope"] = "standalone-workload"
            if case["family"] == "churchroad" and case["id"].startswith("churchroad-later-"):
                row["evidence"] = {
                    "capture_stage": {
                        key: capture[key] for key in ("attempt", "case", "stage", "identity_sha256", "receipt_sha256")
                    }
                }
            row["outcome"] = {
                **validation,
                "capture_stage": capture,
                "receipt_sha256": sha256_file(Path(validation["attempt"]) / "stage.json"),
            }
        except (OSError, KeyError, ValueError) as error:
            row["outcome"] = {"status": "blocked", "reason": str(error)}

    for case in catalog["cases"]:
        if case["family"] != "misaal":
            continue
        invocations = case.get("invocations", [])
        if not invocations and not any(row["id"] == case["id"] for row in rows):
            rows.append(
                {**case, "catalog_id": case["id"], "outcome": {"status": "blocked", "reason": case.get("reason")}}
            )
        for invocation in invocations:
            if case["id"] == "misaal-x86-add" and "backend_status" not in invocation:
                # This one retained legacy call links through its recovery case
                # receipt, rather than the newer per-call catalog fields.
                try:
                    promoted = next(
                        item for item in json.loads((root / case["evidence"]).read_text()) if item["id"] == case["id"]
                    )
                    recovered = next(
                        item
                        for item in json.loads((root / promoted["evidence"]).read_text())
                        if item["id"] == case["id"]
                    )
                    verify_files(
                        {
                            recovered["source_capture_evidence"]: recovered["source_capture_sha256"],
                            recovered["continuation_evidence"]: recovered["continuation_sha256"],
                        },
                        hashes,
                        root,
                    )
                    capture = json.loads((root / recovered["source_capture_evidence"]).read_text())
                    continuation = json.loads((root / recovered["continuation_evidence"]).read_text())
                    raw = Path(capture["raw_invocations"][0])
                    call = json.loads(raw.with_suffix(".json").read_text())
                    backend_path = raw.parent / (Path(call["original_filename"]).stem + ".backend.json")
                    backend = json.loads(backend_path.read_text())
                    if (
                        len(capture["raw_invocations"]) != 1
                        or call["caller"] != "apply_rewrite"
                        or call["sha256"] != invocation["sha256"]
                        or backend["input_sha256"] != invocation["sha256"]
                        or backend["returncode"] != 0
                        or continuation["status"] != "success"
                        or not continuation["phase"]["boundary_reached"]
                    ):
                        raise ValueError("legacy MISAAL call completion is unverified")
                    verify_files({str(raw): invocation["sha256"]}, hashes, root)
                    invocation = {
                        **invocation,
                        "caller": call["caller"],
                        "backend_status": "success",
                        "backend_returncode": 0,
                        "stdout": backend["output"],
                        "stdout_sha256": backend["output_sha256"],
                        "legacy_backend": backend,
                        "legacy_evidence": str(backend_path),
                        "completion_receipts": {
                            str(path): sha256_file(path)
                            for path in (
                                root / case["evidence"],
                                root / promoted["evidence"],
                                root / recovered["source_capture_evidence"],
                                root / recovered["continuation_evidence"],
                                raw.with_suffix(".json"),
                                backend_path,
                            )
                        },
                    }
                except (OSError, KeyError, ValueError, StopIteration) as error:
                    invocation = {**invocation, "recovery_error": str(error)}
            row = {
                "id": f"{case['id']}--invocation-{invocation['index']:04}",
                "catalog_id": case["id"],
                "family": "misaal",
                "source": case["source"],
                "configuration": case.get("configuration", {}),
                "completion_scope": "independent-misaal-invocation",
                "parent_outcome": {"capture_complete": case.get("capture_complete"), "reason": case.get("reason")},
                "evidence": invocation,
                "outcome": {"status": "blocked", "reason": "call is incomplete or is not an independent optimization"},
            }
            rows.append(row)
            if not (
                invocation.get("caller") == "apply_rewrite"
                and invocation.get("status", "success") == invocation.get("backend_status") == "success"
                and invocation.get("returncode", 0) == invocation.get("backend_returncode") == 0
            ):
                continue
            try:
                if "legacy_backend" not in invocation:
                    capture_path = root / case["backend_capture_evidence"]
                    if capture_path not in native_captures:
                        native_captures[capture_path] = json.loads(capture_path.read_text())
                    original_capture = native_captures[capture_path]
                    original = next(
                        item for item in original_capture["invocations"] if item["index"] == invocation["index"]
                    )
                    call_path = (root / invocation["raw"]).with_suffix(".json")
                    call = json.loads(call_path.read_text())
                    if (
                        original_capture["case_id"] != case["id"]
                        or original_capture["source_sha256"] != case["source_sha256"]
                        or original_capture["program_sha256"] != case["generated_program_sha256"]
                        or call != original
                        or call["caller"] != "apply_rewrite"
                        or call["status"] != "success"
                        or call["returncode"] != 0
                        or call["sha256"] != invocation["sha256"]
                        or Path(call["raw"]).resolve() != (root / invocation["raw"]).resolve()
                        or (root / invocation["stdout"]).resolve() != call_path.with_suffix(".stdout.log").resolve()
                    ):
                        raise ValueError("catalog call is not bound to its successful native invocation receipt")
                    invocation["completion_receipts"] = {
                        str(path): sha256_file(path) for path in (capture_path, call_path)
                    }
                artifacts = {
                    invocation["raw"]: invocation["sha256"],
                    invocation["stdout"]: invocation["stdout_sha256"],
                    invocation["workload"]: invocation["replay_sha256"],
                }
                verify_files(artifacts, hashes, root)
                replay = (root / invocation["workload"]).resolve()
                source = replay.read_text()
                forms = [tokens for _, _, tokens in egglog_forms(source)]
                if (
                    invocation.get("query_kind") != "source-extraction"
                    or not invocation.get("extract_count")
                    or not any(tokens[1] == "run" or tokens[1] == "run-schedule" for tokens in forms)
                    or any(tokens[1] in {"include", "input", "prove", "prove-extract"} for tokens in forms)
                ):
                    raise ValueError("call lacks a complete standalone optimization and source extraction")
                expected = validate_extract_output(source, (root / invocation["stdout"]).read_text())
                identity = {"replay_sha256": sha256_file(replay)}
                key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
                job = jobs.setdefault(
                    key,
                    {
                        "key": key,
                        "replay": str(replay),
                        **identity,
                        "native_output_count": len(expected),
                        "aliases": [],
                    },
                )
                job["aliases"].append(row["id"])
                row["validation_key"] = key
                row["outcome"] = {
                    "status": "pending",
                    "reason": "retained complete call needs ordinary replay validation",
                }
            except (OSError, KeyError, ValueError, StopIteration) as error:
                row["outcome"] = {"status": "blocked", "reason": str(error)}
    return rows, list(jobs.values())


def validate_job(job: dict[str, Any], engine: Path, directory: Path, *, timeout_sec: float = 300) -> dict[str, Any]:
    """Run one retained complete call unchanged; the caller sequences safety stops.

    The source invocation and its actual output have already been verified.
    Ordinary replay must finish and return every original extraction root. It
    need not choose the historical engine's identical minimum-cost expression.
    """
    replay = Path(job["replay"])
    verify_files({str(replay): job["replay_sha256"]}, {}, Path.cwd())
    output = directory.resolve() / job["key"]
    receipt = output / "validation.json"
    if receipt.exists():
        record: dict[str, Any] = json.loads(receipt.read_text())
        if (
            any(record["job"][key] != job[key] for key in ("key", "replay_sha256", "native_output_count"))
            or record["engine_sha256"] != sha256_file(engine)
            or record["timeout_sec"] != timeout_sec
            or record["output_contract"] != "complete-source-extractions"
        ):
            raise ValueError("retained validation identity changed; use a fresh validation directory")
        verify_files(record["artifacts"], {}, Path.cwd())
        return record
    output.mkdir(parents=True, exist_ok=False)
    engine_sha256 = sha256_file(engine)
    try:
        process = run_bounded_command(
            [str(engine.resolve()), "-j", "1", str(replay)],
            output,
            output / "replay",
            timeout_sec=timeout_sec,
            require_guard=True,
            allow_warning_pressure=False,
            disk_reserve_bytes=10 * 1024**3,
        )
    except ValueError as error:
        if "guard refused" not in str(error):
            raise
        stdout, stderr = output / "replay.stdout.log", output / "replay.stderr.log"
        stdout.write_text("")
        stderr.write_text(str(error) + "\n")
        process = PilotProcessResult("resource-stopped", None, 0, 0, stdout, stderr, str(error))
    validation = {"replay": str(replay), "replay_sha256": job["replay_sha256"], **asdict(process)}
    validation.update(stdout_path=str(process.stdout_path), stderr_path=str(process.stderr_path))
    record = {
        "job": job,
        "stage": "validate",
        "status": process.status,
        "reason": process.message,
        "engine_sha256": engine_sha256,
        "timeout_sec": timeout_sec,
        "receipt": str(receipt),
        "workloads": [],
        "validations": [validation],
        "capture_stage": {"invocation_complete": True},
        "output_contract": "complete-source-extractions",
    }
    if process.status == "success":
        try:
            verify_files({str(replay): job["replay_sha256"], str(engine.resolve()): engine_sha256}, {}, Path.cwd())
            outputs = validate_extract_output(replay.read_text(), process.stdout_path.read_text())
            if len(outputs) != job["native_output_count"]:
                raise ValueError("ordinary replay lost an original extraction root")
            validation["output_contract_passed"] = True
            record["workloads"] = [str(replay)]
        except ValueError as error:
            record.update(status="blocked", reason=str(error))
    record["artifacts"] = {str(path): sha256_file(path) for path in (replay, process.stdout_path, process.stderr_path)}
    receipt.write_text(json.dumps(record, indent=2, default=str) + "\n")
    return record


def add_packaged_misaal(rows: list[dict[str, Any]], jobs: list[dict[str, Any]], package: Path, root: Path) -> None:
    """Account for the explicitly retained incomplete parents' complete calls.

    Packaging uses the existing materializer outside this module. Its selected
    representatives are only a replay lookup; aliases come from the original
    child receipts, including calls whose bytes already have full-parent replay
    validation. No child or acquisition directories are searched.
    """
    manifest = json.loads(package.read_text())
    package_sha256 = sha256_file(package)
    hashes: dict[Path, str] = {}
    contracts: dict[tuple[str, str], int] = {}
    verify_files({str(package.parent / "selected-calls.json"): manifest["selected_calls_sha256"]}, hashes, root)
    available: dict[str, tuple[dict[str, Any], dict[str, Any] | None]] = {}
    for row in rows:
        outcome = row["outcome"]
        if row["family"] != "misaal" or outcome["status"] != "success" or "attempt" not in outcome:
            continue
        captured = json.loads(Path(outcome["capture_stage"]["capture"]).read_text())
        for invocation in captured["invocations"]:
            validation = next(item for item in outcome["validations"] if item["replay"] == invocation["replay"])
            available[invocation["sha256"]] = (
                invocation,
                {
                    "status": "success",
                    "stage": "validate",
                    "receipt": str(Path(outcome["attempt"]) / "stage.json"),
                    "receipt_sha256": outcome["receipt_sha256"],
                    "workloads": [invocation["replay"]],
                    "validations": [validation],
                    "capture_stage": {"invocation_complete": True},
                },
            )
    for invocation in manifest["invocations"]:
        available[invocation["sha256"]] = (invocation, None)
    by_key = {job["key"]: job for job in jobs}
    catalog = {case["id"]: case for case in json.loads((root / "benchmarks/catalog.json").read_text())["cases"]}
    for source in manifest["source_receipts"]:
        child_path = Path(source["receipt"])
        verify_files({str(child_path): source["sha256"]}, hashes, root)
        child = json.loads(child_path.read_text())
        case = catalog[source["case"]]
        for call in child["invocations"]:
            row = {
                "id": f"{case['id']}--retained-{call['index']:04}",
                "catalog_id": case["id"],
                "family": "misaal",
                "source": case["source"],
                "configuration": case.get("configuration", {}),
                "completion_scope": "independent-misaal-invocation",
                "parent_outcome": {
                    "status": child["status"],
                    "source_capture_complete": child.get("source_capture_complete"),
                    "receipt": str(child_path),
                    "receipt_sha256": source["sha256"],
                },
                "evidence": {"receipt": str(child_path), "receipt_sha256": source["sha256"], "index": call["index"]},
                "outcome": {"status": "blocked", "reason": "retained invocation did not complete"},
            }
            rows.append(row)
            if call["status"] != "success" or call["returncode"] != 0 or call["caller"] != "apply_rewrite":
                continue
            try:
                raw = Path(call["raw"])
                result_path = raw.with_suffix(".result.json")
                if json.loads(result_path.read_text()) != call:
                    raise ValueError("retained child call differs from its native result receipt")
                replay_entry, validated = available[call["sha256"]]
                replay = Path(replay_entry["replay"])
                stdout = raw.with_suffix(".stdout.log")
                evidence = {
                    str(raw): call["sha256"],
                    str(stdout): call["stdout_sha256"],
                    str(replay): replay_entry["replay_sha256"],
                    str(result_path): sha256_file(result_path),
                    str(child_path): source["sha256"],
                    str(package): package_sha256,
                }
                verify_files(evidence, hashes, root)
                contract_key = (replay_entry["replay_sha256"], call["stdout_sha256"])
                if contract_key not in contracts:
                    text = replay.read_text()
                    native_outputs = validate_extract_output(text, stdout.read_text())
                    forms = [tokens for _, _, tokens in egglog_forms(text)]
                    selections = replay_entry["selections"]
                    extracts = [index for index, tokens in enumerate(forms) if tokens[1] == "extract"]
                    contract = native_check_contract(
                        text,
                        [(index + 1, selected["check"]) for index, selected in zip(extracts, selections, strict=True)],
                        selections,
                    )
                    if contract != replay_entry["output_contract"] or native_outputs != validate_extract_output(
                        text, call["selected"]
                    ):
                        raise ValueError("retained output contract differs from the original returned expression")
                    contracts[contract_key] = len(native_outputs)
                if call["selected"] != replay_entry["selected"]:
                    raise ValueError("retained call is not bound to this replay's native output queries")
                row["evidence"]["artifacts"] = evidence
                if validated is not None:
                    row["outcome"] = validated
                    continue
                identity = {"replay_sha256": sha256_file(replay)}
                key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
                if key not in by_key:
                    job = {
                        "key": key,
                        "replay": str(replay),
                        **identity,
                        "native_output_count": contracts[contract_key],
                        "aliases": [],
                    }
                    by_key[key] = job
                    jobs.append(job)
                by_key[key]["aliases"].append(row["id"])
                row["validation_key"] = key
                row["outcome"] = {
                    "status": "pending",
                    "reason": "complete retained call needs ordinary replay validation",
                }
            except (OSError, KeyError, ValueError) as error:
                row["outcome"] = {"status": "blocked", "reason": str(error)}


def apply_validations(rows: list[dict[str, Any]], jobs: list[dict[str, Any]], directory: Path, root: Path) -> None:
    """Attach immutable ordinary replay results to their original call aliases."""
    hashes: dict[Path, str] = {}
    outcomes = {}
    for job in jobs:
        receipt = directory.resolve() / job["key"] / "validation.json"
        if not receipt.is_file():
            continue
        record = json.loads(receipt.read_text())
        if (
            any(record["job"][key] != job[key] for key in ("key", "replay_sha256", "native_output_count"))
            or record["receipt"] != str(receipt)
            or record["stage"] != "validate"
            or record["timeout_sec"] != 300
            or record["output_contract"] != "complete-source-extractions"
        ):
            raise ValueError(f"retained validation job changed: {receipt}")
        verify_files(record["artifacts"], hashes, root)
        record["receipt_sha256"] = sha256_file(receipt)
        outcomes[job["key"]] = record
    for row in rows:
        if row.get("validation_key") in outcomes:
            row["outcome"] = outcomes[row["validation_key"]]


def project_catalog(catalog: dict[str, Any], manifest: dict[str, Any], receipt: Path, root: Path) -> dict[str, Any]:
    """Project selected aliases onto source IDs without changing acquisition populations."""
    result = copy.deepcopy(catalog)
    receipt_sha256 = sha256_file(receipt)
    cases = {case["id"]: case for case in result["cases"]}
    groups: dict[str, list[dict[str, Any]]] = {}
    workloads = {row["file"]: row for row in manifest["workloads"]}
    later: dict[str, Any] = {}
    for row in manifest["cases"]:
        case_id = row.get("catalog_id", row["id"])
        groups.setdefault(case_id, []).append(row)
        if row["family"] == "churchroad" and row["id"].startswith("churchroad-later-") and row["workloads"]:
            if not later:
                population = json.loads((root / "benchmarks/reproduction/population.json").read_text())
                later = population["churchroad"]["later_evaluation"]
            if (
                case_id != row["id"]
                or row["id"] != f"churchroad-later-{Path(row['source']).stem}"
                or row["source"] not in later["sources"]
                or row.get("scope") != "artifact-extra"
                or row.get("configuration", {}).get("repository") != later["repository"]
                or row.get("configuration", {}).get("revision") != later["revision"]
                or row.get("configuration", {}).get("top_module_name") != Path(row["source"]).stem
                or row.get("configuration", {}).get("architecture") != "xilinx-ultrascale-plus"
                or row.get("status") != "success"
                or not row.get("receipt_sha256")
            ):
                raise ValueError(f"later Churchroad case does not match verified inventory: {row['id']}")
            hashes: dict[Path, str] = {}
            verify_files({row["receipt"]: row["receipt_sha256"]}, hashes, root)
            validation = read_stage(
                {**json.loads((root / row["receipt"]).read_text()), "receipt_sha256": row["receipt_sha256"]},
                root,
                hashes,
            )
            capture_reference = row.get("evidence", {}).get("capture_stage", {})
            if not capture_reference.get("receipt_sha256"):
                raise ValueError(f"later Churchroad case lacks its captured identity: {row['id']}")
            capture = read_stage(capture_reference, root, hashes)
            captured_case = capture["identity"]["case"]
            if (
                validation["stage"] != "validate"
                or validation["status"] != "success"
                or validation["case"] != row["id"]
                or capture["case"] != row["id"]
                or capture["stage"] != "complete"
                or capture["status"] not in {"success", "ordinary-validation-pending", "ordinary-validation-failed"}
                or any(
                    captured_case.get(key) != row[key] for key in ("id", "family", "source", "configuration", "scope")
                )
                or captured_case.get("repository") != later["repository"]
                or captured_case.get("revision") != later["revision"]
                or validation["identity"]["capture_sha256"] != sha256_file(root / capture["capture"])
                or validation["identity"]["artifacts"] != capture["artifacts"]
            ):
                raise ValueError(f"later Churchroad validation does not bind its captured identity: {row['id']}")
            validations = {item["replay"]: item for item in validation["validations"]}
            replay_hashes = []
            for replay in validation["workloads"]:
                item = validations.get(replay, {})
                if (
                    item.get("status") != "success"
                    or not item.get("output_contract_passed")
                    or capture["artifacts"].get(replay) != item.get("replay_sha256")
                ):
                    raise ValueError(f"later Churchroad replay lacks bound ordinary validation: {replay}")
                verify_files({replay: item["replay_sha256"]}, hashes, root)
                replay_hashes.append(item["replay_sha256"].removeprefix("sha256:"))
            if replay_hashes != [workloads[name]["sha256"].removeprefix("sha256:") for name in row["workloads"]]:
                raise ValueError(f"later Churchroad manifest replays differ from validation: {row['id']}")
            verify_files(
                {str(receipt.parent / name): workloads[name]["sha256"] for name in row["workloads"]}, hashes, root
            )
            if case_id not in cases:
                case = {key: row[key] for key in ("id", "family", "source", "configuration", "scope")}
                case.update(repository=later["repository"], revision=later["revision"], status="captured", workloads=[])
                result["cases"].append(case)
                cases[case_id] = case
        elif case_id not in cases and row["id"].startswith("hardboiled-published-"):
            case = {key: row[key] for key in ("id", "family", "source", "configuration")}
            case.update(status="captured", workloads=[])
            result["cases"].append(case)
            cases[case_id] = case
        elif case_id not in cases and row["workloads"]:
            raise ValueError(f"retained alias has no catalog source: {case_id}")
    for case in result["cases"]:
        if case["family"] not in FAMILIES:
            continue
        if case["family"] == "hardboiled" and not case["id"].startswith("hardboiled-published-"):
            case["benchmark_selection"] = {
                "workloads": [],
                "reason": "Superseded by the 42 selected author-published inputs.",
            }
            continue
        members = groups.get(case["id"], [])
        selected = list(dict.fromkeys(name for row in members for name in row["workloads"]))
        paths = [str((receipt.parent / name).relative_to(root)) for name in selected]
        case["complete_reproduction"] = {
            "status": "complete" if paths else "blocked",
            "scope": "standalone-workload",
            "reason": "Selected complete Egglog workloads; enclosing compiler completion is not claimed."
            if paths
            else "; ".join(dict.fromkeys(row.get("reason") or row["status"] for row in members))
            or "No recoverable workload.",
            "receipt": str(receipt.relative_to(root)),
            "receipt_sha256": receipt_sha256,
            "workloads": {
                path: {"file_sha256": workloads[name]["sha256"], "facts_sha256": workloads[name]["facts_sha256"]}
                for path, name in zip(paths, selected, strict=True)
            },
        }
        if paths:
            case["status"] = "captured"
            normal = {
                sha256_file(root / item["path"]): item
                for item in case.get("normal_workloads", [])
                if (root / item["path"]).is_file()
            }
            paired = []
            for path, name in zip(paths, selected, strict=True):
                if blocker := normal.get(workloads[name]["sha256"]):
                    alias = {**blocker, "path": path}
                    if alias not in case["normal_workloads"]:
                        case["normal_workloads"].append(alias)
                else:
                    paired.append(path)
            case["workloads"] = list(dict.fromkeys([*case["workloads"], *paired]))
            case["benchmark_selection"] = {
                "workloads": paths,
                "reason": "Retained complete Egglog workloads, including saved configurations and aliases.",
            }
    return result


def read_candidates(path: Path, root: Path) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Reverify a frozen population without rediscovering or adding candidates."""
    snapshot = json.loads(path.read_text())
    rows, jobs = snapshot["rows"], snapshot["jobs"]
    hashes: dict[Path, str] = {}
    for row in rows:
        outcome = row["outcome"]
        if outcome.get("attempt"):
            original = read_stage(outcome, root, hashes)
            if original["status"] != outcome["status"] or original["validations"] != outcome["validations"]:
                raise ValueError(f"frozen validation changed: {row['id']}")
            if not outcome["capture_stage"].get("receipt_sha256"):
                raise ValueError(f"frozen capture receipt hash is required: {row['id']}")
            read_stage(outcome["capture_stage"], root, hashes)
        if outcome.get("receipt_sha256"):
            receipt = outcome.get("receipt") or str(Path(outcome["attempt"]) / "stage.json")
            verify_files({receipt: outcome["receipt_sha256"]}, hashes, root)
        evidence = row.get("evidence", {})
        if not isinstance(evidence, dict):
            continue
        verify_files(evidence.get("artifacts", {}), hashes, root)
        verify_files(evidence.get("completion_receipts", {}), hashes, root)
        if row.get("validation_key") and "raw" in evidence:
            verify_files(
                {
                    evidence["raw"]: evidence["sha256"],
                    evidence["stdout"]: evidence["stdout_sha256"],
                    evidence["workload"]: evidence["replay_sha256"],
                },
                hashes,
                root,
            )
    for job in jobs:
        verify_files({job["replay"]: job["replay_sha256"]}, hashes, root)
    return rows, jobs


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--candidates", type=Path, help="reverify this frozen rows/jobs snapshot without rediscovery")
    parser.add_argument(
        "--misaal-package", type=Path, help="include explicitly packaged complete calls during discovery"
    )
    parser.add_argument(
        "--output", type=Path, help="publish verified successes and an immutable manifest snapshot here"
    )
    parser.add_argument("--catalog-output", type=Path, help="write the projected catalog here for review")
    parser.add_argument(
        "--validation-directory", type=Path, help="attach previously completed independent-call validations"
    )
    args = parser.parse_args(argv)
    root = args.root.resolve()
    if args.candidates and args.misaal_package:
        parser.error("a frozen candidate snapshot cannot be extended during publication")
    rows, jobs = read_candidates(args.candidates, root) if args.candidates else retained_rows(root)
    if args.misaal_package:
        add_packaged_misaal(rows, jobs, args.misaal_package.resolve(), root)
    if args.validation_directory:
        apply_validations(rows, jobs, args.validation_directory, root)
    if args.catalog_output and not args.output:
        parser.error("--catalog-output requires --output")
    if args.output:
        directory = args.output.resolve()
        manifest = write_corpus(rows, directory)
        content = (directory / "manifest.json").read_bytes()
        receipt = directory / (hashlib.sha256(content).hexdigest() + ".json")
        if receipt.exists() and receipt.read_bytes() != content:
            raise ValueError("immutable corpus manifest changed")
        if not receipt.exists():
            receipt.write_bytes(content)
        if args.catalog_output:
            catalog = json.loads((root / "benchmarks/catalog.json").read_text())
            projected = project_catalog(catalog, manifest, receipt, root)
            args.catalog_output.write_text(json.dumps(projected, indent=2) + "\n")
    print(
        json.dumps(
            {"cases": dict(Counter(row["outcome"]["status"] for row in rows)), "validation_jobs": jobs}, indent=2
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
