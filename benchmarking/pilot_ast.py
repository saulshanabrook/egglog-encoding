"""Bind restricted Slotted compile-only sizes to portable pilot snapshots."""

from __future__ import annotations

import json
import os
import tempfile
from pathlib import Path
from typing import Any

from .models import FileSpec
from .slotted_ast import COLUMNS, PIPELINE, export_slotted_ast, slotted_ast_records


def program_size_snapshot(files: tuple[FileSpec, ...], cache: Path, *, collect: bool) -> dict[str, Any]:
    """Resolve the current compiler when collecting; preserve missing cached coverage otherwise."""
    planned = [{"file": file.display_path, "file_sha256": file.sha256} for file in files]
    try:
        records = slotted_ast_records(files, cache, collect=collect)
    except ValueError as error:
        if collect:
            raise
        return {"status": "pending", "pipeline": PIPELINE, "inputs": planned, "records": [], "issue": str(error)}
    return {"status": "complete", "pipeline": PIPELINE, "inputs": planned, "records": list(records), "issue": None}


def export_program_size(snapshot: dict[str, Any], destination: Path) -> tuple[Path, ...]:
    """Reuse the AST renderer under new names without inspecting inputs or a compiler."""
    destination.mkdir(parents=True, exist_ok=True)
    names = {
        "ast.tex": "table.tex",
        "ast.json": "results.json",
        "ast.csv": "csv",
        "ast.md": "md",
        "files.txt": "files.txt",
    }
    records = snapshot["records"]
    if records:
        with tempfile.TemporaryDirectory(dir=destination) as scratch:
            folder = Path(scratch)
            for path in export_slotted_ast(records, folder):
                suffix = path.name.removeprefix("slotted-runtime.")
                if suffix == "ast.json":
                    report = json.loads(path.read_bytes())
                    report.update(
                        figure="slotted-program-size",
                        timing_identity="Compile-only compiler/input identities are independent of timing endpoints",
                        program_size_snapshot=snapshot,
                    )
                    path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
                os.replace(path, destination / f"slotted-program-size.{names[suffix]}")
    else:
        contents = {
            "table.tex": r"\fbox{\parbox{0.9\linewidth}{\centering Program-size compilation results pending.}}" + "\n",
            "results.json": json.dumps({"figure": "slotted-program-size", **snapshot}, ensure_ascii=False) + "\n",
            "csv": ",".join(COLUMNS) + "\n",
            "md": "Program-size compilation results pending.\n\n" + (snapshot.get("issue") or "") + "\n",
            "files.txt": "".join(f"{file['file']}\n" for file in snapshot["inputs"]),
        }
        for suffix, content in contents.items():
            (destination / f"slotted-program-size.{suffix}").write_text(content)
    return tuple(destination / f"slotted-program-size.{suffix}" for suffix in names.values())
