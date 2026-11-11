"""Dispatch pinned source/tool preparation, leaving native optimization separate."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from scripts.reproduction_dispatch import STOP_STATUSES
from scripts.reproduction_inventory import expected_cases

ROOT = Path(__file__).resolve().parents[1]

RECIPES = ("eggcc", "hardboiled", "misaal", "churchroad", "dialegg", "speq")


def preparation_stop(record: dict[str, Any], directory: Path) -> str | None:
    """Propagate nested or wrapped safety failures before another target starts."""
    pending: list[Any] = [record]
    for steps in (directory / "steps", directory / "generators/steps"):
        pending.extend(json.loads(path.read_text()) for path in sorted(steps.glob("*.result.json")))
    while pending:
        value = pending.pop()
        if isinstance(value, dict):
            status = value.get("status")
            if status in STOP_STATUSES:
                return str(status)
            if status == "launch-refused" or "guard refused" in str(value.get("reason", "")):
                return "resource-stopped"
            pending.extend(value.values())
        elif isinstance(value, list):
            pending.extend(value)
    return None


def prepare_misaal_family(attempt: Path, engine: Path) -> dict[str, Any]:
    """Prepare each original ISA serially, then merge only verified ready requests.

    The caller owns the single heavy-job lock. Target failures retain every
    inventory row; a safety stop prevents subsequent targets and publication.
    """
    from scripts.misaal_reproduction import verified_request
    from scripts.reproduction_misaal_patterns import CONTRACT as PATTERN_DEDUPLICATION
    from scripts.reproduction_prepare_misaal import LLVM12, prepare, sha256_file, write_json
    from scripts.reproduction_prepare_misaal_arm import prepare_misaal_arm
    from scripts.reproduction_prepare_misaal_cases import prepare_misaal_cases
    from scripts.reproduction_prepare_misaal_hvx import prepare_misaal_hvx

    inventory = expected_cases(
        json.loads((ROOT / "benchmarks/catalog.json").read_text()),
        json.loads((ROOT / "benchmarks/reproduction/population.json").read_text()),
    )
    cases = {case["id"]: case for case in inventory if case["family"] == "misaal"}
    if not cases or any(
        case["configuration"] not in ({"target": "x86"}, {"target": "arm"}, {"target": "hexagon"})
        for case in cases.values()
    ):
        raise ValueError("MISAAL preparation requires inventoried x86, ARM or Hexagon configurations")
    record: dict[str, Any] = {
        "status": "blocked",
        "reason": None,
        "request_policy": {"pattern_deduplication": PATTERN_DEDUPLICATION},
        "target_preparations": {},
        "cases": {
            case_id: {
                **case,
                "status": "not-reached",
                "reason": "shared native preparation not completed",
                "request": None,
            }
            for case_id, case in cases.items()
        },
    }
    output = attempt / "environment"
    output.mkdir()
    try:
        request = prepare(output)
        seed = json.loads(request.read_text())
    except (OSError, ValueError, RuntimeError) as error:
        record.update(reason=str(error))
        record["status"] = preparation_stop(record, output) or "blocked"
        for row in record["cases"].values():
            row["reason"] = f"shared native preparation failed: {error}"
        return record
    stop = preparation_stop({}, output)
    if stop:
        record.update(status=stop, reason="shared native preparation recorded a safety stop")
        return record
    identities = [seed[key] for key in ("library", "legalizer", "backend", "python", "llvm_as")]
    identities.extend([str(output / "python/lib"), str(LLVM12 / "lib/libLLVM.dylib")])
    for target, relative in (("x86", "generators"), ("arm", "arm"), ("hexagon", "hvx")):
        selected = {case_id: case for case_id, case in cases.items() if case["configuration"] == {"target": target}}
        if not selected:
            continue
        directory = attempt / relative
        try:
            if target == "x86":
                outcome = prepare_misaal_cases(directory, request, case_ids=list(selected))
            else:
                # Fresh native preparation already resolved its pinned CMake.
                # Reuse that actual executable even when it is absent from PATH.
                cache = Path(seed["preparation"]) / "halide-build/CMakeCache.txt"
                commands = [
                    line.partition("=")[2]
                    for line in cache.read_text().splitlines()
                    if line.startswith("CMAKE_COMMAND:INTERNAL=")
                ]
                if len(commands) != 1 or not commands[0]:
                    raise ValueError("native preparation did not record exactly one CMake executable")
                recipe = prepare_misaal_arm if target == "arm" else prepare_misaal_hvx
                outcome = recipe(
                    directory,
                    request,
                    case_ids=list(selected),
                    cmake=Path(commands[0]),
                    boost_include=Path(seed["preparation"]) / "boost_1_81_0",
                )
            if set(outcome["cases"]) != set(selected):
                raise ValueError(f"{target} preparation did not account for every selected inventory case")
            for case_id, row in outcome["cases"].items():
                if any(row.get(key) != selected[case_id][key] for key in ("source", "configuration")):
                    raise ValueError(f"{target} preparation changed an original source/configuration identity")
            record["cases"].update(outcome["cases"])
        except (OSError, ValueError, RuntimeError) as error:
            outcome = {"status": "blocked", "reason": str(error), "cases": {}}
            for case_id, case in selected.items():
                record["cases"][case_id] = {**case, "status": "blocked", "reason": str(error), "request": None}
        target_receipt = attempt / f"preparation-{target}.json"
        write_json(target_receipt, outcome)
        record["target_preparations"][target] = {"status": outcome["status"], "evidence": str(target_receipt)}
        for case_id in selected:
            record["cases"][case_id]["preparation_evidence"] = str(target_receipt)
        stop = preparation_stop(outcome, directory)
        if stop:
            record.update(status=stop, reason=f"{target} preparation stopped; no later target was launched")
            for row in record["cases"].values():
                if row["status"] == "not-reached":
                    row["reason"] = record["reason"]
            return record
        if outcome.get("settings"):
            settings = json.loads(Path(outcome["settings"]).read_text())["misaal"]
            identities.extend(settings.get("identity_paths", []))
    requests = attempt / "requests"
    requests.mkdir()
    for case_id, row in record["cases"].items():
        if row["status"] != "prepared":
            continue
        source = Path(row["request"])
        try:
            payload = source.read_bytes()
            request_data = json.loads(payload)
            if (
                any(request_data.get(key) != cases[case_id][key] for key in ("source", "configuration"))
                or request_data.get("case_id") != case_id
            ):
                raise ValueError("prepared request changed its inventory identity before merging")
            if row["request_sha256"] != sha256_file(source):
                raise ValueError("prepared request bytes changed before merging")
            verified_request(source)
            if (
                "pattern_deduplication" in request_data
                and request_data["pattern_deduplication"] != PATTERN_DEDUPLICATION
            ):
                raise ValueError("prepared request conflicts with the family pattern-deduplication policy")
        except (OSError, ValueError) as error:
            row.update(status="blocked", reason=str(error), rejected_request=str(source), request=None)
            continue
        published = requests / f"{case_id}.json"
        write_json(published, {**request_data, "pattern_deduplication": PATTERN_DEDUPLICATION})
        row["published_request"] = str(published)
        identities.extend(request_data.get("identity_paths", []))
        identities.append(request_data["legalizer"])
    if not any(row["status"] == "prepared" for row in record["cases"].values()):
        record["reason"] = "no original MISAAL generator requests could be prepared; inspect target and case evidence"
        return record
    from scripts.reproduction_prepare_misaal_racket import prepare_source_runtime

    runtime_directory = attempt / "racket"
    runtime = prepare_source_runtime(
        runtime_directory,
        [Path(row["published_request"]) for row in record["cases"].values() if row["status"] == "prepared"],
        lock_owned=True,
    )
    record["racket_preparation"] = {"status": runtime["status"], "evidence": str(runtime_directory / "result.json")}
    if runtime["status"] != "success":
        record.update(status=runtime["status"], reason=runtime.get("reason") or "Racket prerequisites did not pass")
        for row in record["cases"].values():
            if row["status"] == "prepared":
                row.update(status="blocked", reason=record["reason"], native_request=row["published_request"])
        return record
    for case_id, row in record["cases"].items():
        if row["status"] != "prepared":
            continue
        published = Path(runtime["requests"][case_id])
        ready = verified_request(published)
        if ready.get("pattern_deduplication") != PATTERN_DEDUPLICATION:
            raise ValueError("runtime publication lost the family pattern-deduplication policy")
        row.update(published_request=str(published), published_request_sha256=sha256_file(published))
        identities.extend(ready["identity_paths"])
    requests = runtime_directory / "requests"
    blockers = [
        {
            "case_ids": [case_id],
            "configuration": row["configuration"],
            "reason": row.get("reason") or "original generator preparation did not complete",
            "evidence": [row["preparation_evidence"]],
        }
        for case_id, row in record["cases"].items()
        if row["status"] != "prepared"
    ]
    settings_path = attempt / "settings.json"
    write_json(
        settings_path,
        {
            "misaal": {
                "paths": {"requests": str(requests), "checkout": seed["checkout"], "egglog": str(engine.resolve())},
                "revision": seed["revision"],
                "identity_paths": list(dict.fromkeys(identities)),
                "configuration_blockers": blockers,
                "timeout_sec": 300,
            }
        },
    )
    record.update(
        status="success",
        settings=str(settings_path),
        settings_sha256=sha256_file(settings_path),
        reason="prepared original requests available; complete source optimization remains unexecuted",
        generator_preparation_status="blocked" if blockers else "success",
    )
    return record


def prepare_family(family: str, attempt: Path, engine: Path) -> dict[str, Any]:
    """Run under the coordinator's lock; publish settings only after actual builds."""
    output = attempt / "environment"
    try:
        if not engine.is_file():
            raise ValueError(f"ordinary replay engine is missing: {engine}")
        if family == "eggcc":
            from scripts.reproduction_prepare_eggcc import prepare_eggcc

            record = prepare_eggcc(output, engine)
        elif family == "churchroad":
            from scripts.reproduction_prepare_churchroad import prepare_churchroad

            record = prepare_churchroad(output, engine)
        elif family == "dialegg":
            from scripts.reproduction_prepare_dialegg import prepare_dialegg

            record = prepare_dialegg(output, engine)
        elif family == "speq":
            from scripts.reproduction_prepare_speq import prepare_speq

            record = prepare_speq(
                output,
                engine,
                llvm_config=Path("/opt/homebrew/opt/llvm@17/bin/llvm-config"),
                acquire_archive=True,
                c99_frontend_repair="polybench-gemm-address-v1",
            )
        elif family == "hardboiled":
            from scripts.reproduction_prepare_hardboiled import LLVM, prepare

            output.mkdir()
            path = prepare(output, LLVM.resolve())
            settings = json.loads(path.read_text())
            settings[family]["paths"]["egglog"] = str(engine.resolve())
            # The selected ordinary engine is part of this coordinator request.
            path.write_text(json.dumps(settings, indent=2) + "\n")
            record = {"status": "success", "settings": str(path)}
        elif family == "misaal":
            record = prepare_misaal_family(attempt, engine)
        else:
            return {"status": "pending", "reason": f"pinned {family} preparation recipe is not integrated"}
    except (OSError, ValueError, RuntimeError) as error:
        record = {
            "status": "resource-stopped" if "guard refused" in str(error) else "preparation-blocked",
            "reason": str(error),
        }
    # A failed dependency is not a completed preparation. Propagate a saved
    # guard stop even when the family preparer wrapped it as a build failure.
    results = sorted(output.glob("steps/*.result.json"))
    if results:
        last = json.loads(results[-1].read_text())
        if last.get("status") in STOP_STATUSES:
            record["status"] = last["status"]
    if record["status"] != "success":
        if record["status"] not in STOP_STATUSES:
            record["status"] = "preparation-blocked"
    elif not Path(record["settings"]).is_file():
        raise ValueError("preparer reported success without native-tool settings")
    receipt = attempt / "preparation-result.json"
    receipt.write_text(json.dumps(record, indent=2, default=str) + "\n")
    # Include the prepared source and runtime, not disposable object/cache trees.
    # Explicit built products in family receipts are retained as well.
    ignored = {".git", "__pycache__", "build", "target", "halide-build", "sidecar-target", "cargo-home", "rustup-home"}
    artifacts = {
        str(path.resolve())
        for path in attempt.rglob("*")
        if path.is_file()
        and path != attempt / "stage.json"
        and not ignored.intersection(path.relative_to(attempt).parts)
    }
    artifacts.update(record.get("artifacts", {}))
    directories = set(record.get("artifact_directories", []))
    if record["status"] == "success":
        settings = json.loads(Path(record["settings"]).read_text())[family]
        for value in settings["paths"].values():
            if value is not None and Path(value).is_file():
                artifacts.add(str(Path(value).absolute()))
        # Principal binaries are explicit files above; build/cache directories
        # remain disposable. Source and declared runtime trees also bind new or
        # removed members, which a fixed list of existing files cannot detect.
        dependencies = [*settings.get("identity_paths", []), settings["paths"].get("checkout")]
        for value in dependencies:
            if value is None:
                continue
            path = Path(value).absolute()
            if path.is_dir():
                directories.add(str(path))
            elif path.is_file():
                artifacts.add(str(path))
            else:
                raise ValueError(f"prepared runtime dependency is missing: {path}")
    return {**record, "artifacts": sorted(artifacts), "artifact_directories": sorted(directories)}
