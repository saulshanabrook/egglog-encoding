#!/usr/bin/env python3
"""Verify the dedicated Dis/Equality Graphs artifact import commit."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from collections import defaultdict
from pathlib import Path
from zipfile import ZipFile

IMPORT_COMMIT = "c52112f751c6e3a05205f275a85a5e0e7829e192"
ARCHIVE_SHA256 = "3e9080ca461457af0a10cfc433a5150952f82f752b4c316df1e03236d93599c4"
ARCHIVE_URL = "https://zenodo.org/records/13938878/files/die-graph.zip?download=1"
REPOSITORY_PREFIX = "benchmarks/disequality/"


def exclusion_category(path: str) -> str | None:
    if path == "die-graph.tar.xz":
        return "prebuilt_container_image"
    if path.startswith("euf-solver/benchmarks/"):
        return "large_euf_benchmark_corpus"
    if path.startswith("parameter-analysis/"):
        return "parameter_analysis_managed_by_existing_pipeline"
    if path.endswith("/precomputed-results.csv"):
        return "precomputed_results"
    if path in {"Dockerfile", "setup-container"}:
        return "artifact_container_wrapper"
    if path in {
        "inductive-prover/propel/.git",
        "inductive-prover/propel/.gitignore",
    }:
        return "nested_repository_metadata"
    return None


def build_manifest(archive: Path, repository: Path) -> dict[str, object]:
    digest = hashlib.sha256()
    with archive.open("rb") as archive_file:
        while chunk := archive_file.read(1024 * 1024):
            digest.update(chunk)
    if digest.hexdigest() != ARCHIVE_SHA256:
        raise RuntimeError(f"archive SHA-256 is {digest.hexdigest()}, expected {ARCHIVE_SHA256}")

    imported_paths = subprocess.check_output(
        [
            "git",
            "diff-tree",
            "--root",
            "--no-commit-id",
            "--name-only",
            "-r",
            IMPORT_COMMIT,
            "--",
            REPOSITORY_PREFIX,
        ],
        cwd=repository,
        text=True,
    ).splitlines()
    imported_paths = sorted(path for path in imported_paths if path)

    included = []
    exclusion_counts: dict[str, int] = defaultdict(int)
    exclusion_bytes: dict[str, int] = defaultdict(int)
    with ZipFile(archive) as artifact:
        members = {info.filename: info for info in artifact.infolist() if not info.is_dir()}
        imported_members = {path.removeprefix(REPOSITORY_PREFIX) for path in imported_paths}
        missing = sorted(imported_members - members.keys())
        if missing:
            raise RuntimeError(f"imported paths absent from archive: {missing}")

        for repository_path in imported_paths:
            archive_path = repository_path.removeprefix(REPOSITORY_PREFIX)
            contents = artifact.read(archive_path)
            committed = subprocess.check_output(["git", "show", f"{IMPORT_COMMIT}:{repository_path}"], cwd=repository)
            if contents != committed:
                raise RuntimeError(f"{repository_path} differs between the archive and import commit")
            included.append(
                {
                    "archive_path": archive_path,
                    "repository_path": repository_path,
                    "size_bytes": len(contents),
                    "sha256": hashlib.sha256(contents).hexdigest(),
                }
            )

        for path in sorted(members.keys() - imported_members):
            category = exclusion_category(path)
            if category is None:
                raise RuntimeError(f"archive member has no import disposition: {path}")
            exclusion_counts[category] += 1
            exclusion_bytes[category] += members[path].file_size

    imported_at = subprocess.check_output(
        ["git", "show", "-s", "--format=%aI", IMPORT_COMMIT],
        cwd=repository,
        text=True,
    ).strip()
    return {
        "schema_version": 1,
        "source": {
            "doi": "10.5281/zenodo.13938878",
            "archive_url": ARCHIVE_URL,
            "archive_name": archive.name,
            "archive_size_bytes": archive.stat().st_size,
            "archive_sha256": ARCHIVE_SHA256,
        },
        "import": {
            "commit": IMPORT_COMMIT,
            "imported_at": imported_at,
            "included_file_count": len(included),
            "excluded_file_count": sum(exclusion_counts.values()),
            "excluded_categories": {
                category: {
                    "file_count": exclusion_counts[category],
                    "uncompressed_size_bytes": exclusion_bytes[category],
                }
                for category in sorted(exclusion_counts)
            },
        },
        "included_files": included,
    }


def main() -> int:
    repository = Path(__file__).resolve().parents[3]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=repository / "benchmarks" / "disequality" / "IMPORT_MANIFEST.json",
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()

    manifest = build_manifest(args.archive.resolve(), repository)
    rendered = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.manifest.is_file() or args.manifest.read_text() != rendered:
            raise SystemExit(f"import manifest does not match {args.archive}")
        import_summary = manifest["import"]
        assert isinstance(import_summary, dict)
        print(
            f"verified {import_summary['included_file_count']} imported and "
            f"{import_summary['excluded_file_count']} excluded files"
        )
        return 0

    args.manifest.write_text(rendered)
    print(f"wrote {args.manifest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
