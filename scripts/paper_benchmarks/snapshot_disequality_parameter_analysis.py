#!/usr/bin/env python3
"""Snapshot all disequality encodings after experimental Egglog desugaring."""

from __future__ import annotations

import argparse
import json
import subprocess
from collections.abc import Sequence
from pathlib import Path

from scripts.paper_benchmarks.prepare_parameter_analysis import compare_files, sha256_bytes, write_files

ENCODINGS = ("ee", "oee", "nee", "de")
SCHEMA_VERSION = 1


def command_output(command: Sequence[str]) -> str:
    """Run one deterministic metadata command."""

    return subprocess.run(command, check=True, capture_output=True, text=True).stdout.strip()


def snapshots(binary: Path, program: Path, compiler_revision: str) -> dict[str, bytes]:
    """Resolve the same source program under each encoding and return snapshot files."""

    files: dict[str, bytes] = {}
    for encoding in ENCODINGS:
        completed = subprocess.run(
            (
                str(binary),
                "--disequality-encoding",
                encoding,
                "--mode",
                "desugar",
                str(program),
            ),
            check=True,
            capture_output=True,
            text=True,
        )
        files[f"{encoding}.egg"] = completed.stdout.encode()
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "compiler_revision": compiler_revision,
        "binary_version": command_output((str(binary), "--version")),
        "source": {
            "name": program.name,
            "sha256": sha256_bytes(program.read_bytes()),
        },
        "snapshots": {
            encoding: {
                "file": f"{encoding}.egg",
                "sha256": sha256_bytes(files[f"{encoding}.egg"]),
                "bytes": len(files[f"{encoding}.egg"]),
            }
            for encoding in ENCODINGS
        },
        "command": "egglog-experimental --disequality-encoding ENCODING --mode desugar parameter-analysis.egg",
    }
    files["manifest.json"] = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()
    return files


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True, help="Built egglog-experimental binary")
    parser.add_argument("--program", type=Path, required=True, help="Parameter-analysis Egglog source")
    parser.add_argument("--output", type=Path, required=True, help="Snapshot directory")
    parser.add_argument("--compiler-revision", help="Git revision of the compiler sources")
    parser.add_argument("--force", action="store_true", help="Replace an existing snapshot directory")
    parser.add_argument("--check", action="store_true", help="Compare fresh snapshots with committed bytes")
    args = parser.parse_args(argv)
    if not args.check and args.compiler_revision is None:
        parser.error("--compiler-revision is required when generating snapshots")
    return args


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if args.check and args.force:
        raise ValueError("--check and --force cannot be combined")
    compiler_revision = args.compiler_revision
    if args.check and compiler_revision is None:
        manifest = json.loads((args.output / "manifest.json").read_text(encoding="utf-8"))
        compiler_revision = str(manifest["compiler_revision"])
    assert compiler_revision is not None
    files = snapshots(args.binary, args.program, compiler_revision)
    if args.check:
        compare_files(args.output, files)
    else:
        write_files(args.output, files, args.force)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
