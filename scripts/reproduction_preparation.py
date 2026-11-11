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


def prepare_misaal_family(attempt: Path, engine: Path, settings: dict[str, Any]) -> dict[str, Any]:
    """Prepare export generators from explicit retained templates, without LLVM lowering."""
    from scripts.misaal_reproduction import EGGLOG_EXPORT, verified_request
    from scripts.reproduction_misaal_export import (
        prepare_export_frontend,
        prepare_export_generator,
        verified_export_template,
        verified_frontend,
    )
    from scripts.reproduction_prepare_misaal import MISAAL_REVISION, sha256_file, write_json

    template_directory = settings.get("export_templates", settings.get("paths", {}).get("requests"))
    if not template_directory:
        raise ValueError(
            "MISAAL export preparation needs explicit retained request templates; native preparation is disabled"
        )
    templates = (ROOT / template_directory).resolve()
    if not templates.is_dir():
        raise ValueError(f"MISAAL export request templates are missing: {templates}")
    inventory = expected_cases(
        json.loads((ROOT / "benchmarks/catalog.json").read_text()),
        json.loads((ROOT / "benchmarks/reproduction/population.json").read_text()),
    )
    cases = [case for case in inventory if case["family"] == "misaal"]
    blockers = list(settings.get("configuration_blockers", []))
    record: dict[str, Any] = {"status": "blocked", "egglog_export": EGGLOG_EXPORT, "cases": {}}
    ready = []
    for case in cases:
        row = {**case, "status": "blocked", "request": None}
        record["cases"][case["id"]] = row
        blocked = next(
            (
                blocker
                for blocker in blockers
                if (blocker.get("case_ids") is None or case["id"] in blocker["case_ids"])
                and blocker["configuration"]
                and all(case["configuration"].get(key) == value for key, value in blocker["configuration"].items())
            ),
            None,
        )
        if blocked:
            row.update(reason=blocked["reason"], preparation_evidence=blocked.get("evidence", []))
            continue
        template = templates / f"{case['id']}.json"
        try:
            request = verified_export_template(template)
            if (
                request.get("egglog_export") is not None
                or request.get("case_id") != case["id"]
                or any(request.get(key) != case[key] for key in ("source", "configuration"))
            ):
                raise ValueError("export template differs from the original inventory request")
            row.update(template=str(template), template_sha256=sha256_file(template), checkout=request["checkout"])
            ready.append(case)
        except (OSError, ValueError, KeyError) as error:
            row.update(reason=str(error), preparation_evidence=[str(template)])
            blockers.append(
                {
                    "case_ids": [case["id"]],
                    "configuration": case["configuration"],
                    "reason": row["reason"],
                    "evidence": row["preparation_evidence"],
                }
            )
    if not ready:
        return {
            **record,
            "reason": "no unblocked original request templates verified; no frontend or generator was built",
        }
    frontend_directory = attempt / "environment"
    if settings.get("export_frontend"):
        frontend_receipt = (ROOT / settings["export_frontend"]).resolve()
        frontend = verified_frontend(frontend_receipt)
    else:
        frontend = prepare_export_frontend(frontend_directory, templates / f"{ready[0]['id']}.json")
        frontend_receipt = frontend_directory / "frontend.json"
    record["frontend"] = {"status": frontend["status"], "evidence": str(frontend_receipt)}
    stop = preparation_stop(frontend, frontend_directory)
    if frontend["status"] != "success" or stop:
        return {
            **record,
            "status": stop or "blocked",
            "reason": frontend.get("reason") or "export frontend preparation failed",
        }
    requests = attempt / "requests"
    requests.mkdir()
    identities = [str(frontend_receipt)]
    for case in ready:
        case_id = case["id"]
        row = record["cases"][case_id]
        directory = attempt / "generators" / case_id
        row["preparation_evidence"] = [str(directory / "generator.json")]
        try:
            result = prepare_export_generator(directory, templates / f"{case_id}.json", frontend_receipt)
            stop = preparation_stop(result, directory)
            if stop:
                return {
                    **record,
                    "status": stop,
                    "reason": f"{case_id} export preparation stopped; no later generator launched",
                }
            if result["status"] != "success":
                raise ValueError(result.get("reason") or "export generator preparation failed")
            if sha256_file(templates / f"{case_id}.json") != row["template_sha256"]:
                raise ValueError("retained template changed during export preparation")
            source = directory / "capture-request.json"
            request = verified_request(source)
            if (
                request.get("egglog_export") != EGGLOG_EXPORT
                or any(request.get(key) != case[key] for key in ("source", "configuration"))
                or request.get("case_id") != case_id
            ):
                raise ValueError("prepared export request changed its inventory or export policy")
            published = requests / f"{case_id}.json"
            published.write_bytes(source.read_bytes())
            row.update(status="prepared", request=str(published), request_sha256=sha256_file(published))
            identities.extend(request.get("identity_paths", []))
            identities.extend(request[key] for key in ("backend", "python", "generator", "library"))
        except (OSError, ValueError, RuntimeError) as error:
            stop = preparation_stop({}, directory)
            if stop:
                return {
                    **record,
                    "status": stop,
                    "reason": f"{case_id} export preparation stopped; no later generator launched",
                }
            row.update(reason=str(error))
            blockers.append(
                {
                    "case_ids": [case_id],
                    "configuration": case["configuration"],
                    "reason": row["reason"],
                    "evidence": row["preparation_evidence"],
                }
            )
    if not any(row["status"] == "prepared" for row in record["cases"].values()):
        return {**record, "reason": "no export generator prepared; inspect retained per-case evidence"}
    config = {
        "egglog_export": EGGLOG_EXPORT,
        "export_templates": str(templates),
        "paths": {
            "requests": str(requests),
            "checkout": next(row["checkout"] for row in record["cases"].values() if row["status"] == "prepared"),
            "egglog": str(engine.resolve()),
        },
        "revision": MISAAL_REVISION,
        "identity_paths": list(dict.fromkeys(identities)),
        "configuration_blockers": blockers,
        "timeout_sec": settings.get("timeout_sec", 300),
    }
    if settings.get("export_frontend"):
        config["export_frontend"] = settings["export_frontend"]
    settings_path = attempt / "settings.json"
    write_json(settings_path, {"misaal": config})
    return {
        **record,
        "status": "success",
        "settings": str(settings_path),
        "settings_sha256": sha256_file(settings_path),
        "reason": "export generators prepared; complete Egglog source traversal remains unexecuted",
    }


def prepare_family(
    family: str, attempt: Path, engine: Path, *, input_kind: str | None = None, settings: dict[str, Any] | None = None
) -> dict[str, Any]:
    """Run under the coordinator's lock; publish verified acquisition or build settings."""
    output = attempt / "environment"
    try:
        if not engine.is_file():
            raise ValueError(f"ordinary replay engine is missing: {engine}")
        if input_kind is not None:
            from scripts.reproduction_published import INPUT_KIND, prepare_published

            if family != "hardboiled" or input_kind != INPUT_KIND:
                raise ValueError("unsupported published input preparation")
            record = prepare_published(output, engine)
        elif family == "eggcc":
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
            record = prepare_misaal_family(attempt, engine, settings or {})
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
        raise ValueError("preparer reported success without prepared settings")
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
