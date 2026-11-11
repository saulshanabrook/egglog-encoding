"""Dispatch pinned source/tool preparation, leaving native optimization separate."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from scripts.reproduction_dispatch import STOP_STATUSES

RECIPES = ("eggcc", "hardboiled", "churchroad", "dialegg")


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
        elif family == "hardboiled":
            from scripts.reproduction_prepare_hardboiled import LLVM, prepare

            output.mkdir()
            path = prepare(output, LLVM.resolve())
            settings = json.loads(path.read_text())
            settings[family]["paths"]["egglog"] = str(engine.resolve())
            # The selected ordinary engine is part of this coordinator request.
            path.write_text(json.dumps(settings, indent=2) + "\n")
            record = {"status": "success", "settings": str(path)}
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
    ignored = {".git", "__pycache__", "build", "halide-build", "sidecar-target", "cargo-home", "rustup-home"}
    artifacts = {
        str(path.resolve())
        for path in attempt.rglob("*")
        if path.is_file() and not ignored.intersection(path.relative_to(attempt).parts)
    }
    artifacts.update(record.get("artifacts", {}))
    if record["status"] == "success":
        settings = json.loads(Path(record["settings"]).read_text())[family]
        for value in settings["paths"].values():
            if value is not None and Path(value).is_file():
                artifacts.add(str(Path(value).resolve()))
    return {**record, "artifacts": sorted(artifacts)}
