"""Gather a portable figure snapshot without collecting or transforming observations."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
import zipfile
from pathlib import Path
from typing import TypedDict

from .reports.store import parse_grouped_report
from .suites import resolve_suite

FIGURES = ("math-cutoff-11", "proof-overhead-cdf")


class ArchiveProvenance(TypedDict):
    repository_commit: str
    repository_dirty: bool
    binary_sha256: list[str]
    render_packages: list[str]
    files: dict[str, str]


def archive_figures(root: Path, destination: Path) -> Path:
    """Freeze metadata, verify inputs, and preserve the specs' relative URLs."""

    root, destination = root.resolve(), destination.resolve()
    selection = resolve_suite("expanded", root)
    if selection.capture_errors:
        raise ValueError("cannot archive changed or missing inputs: " + "; ".join(selection.capture_errors.values()))
    manifest = selection.manifest
    paths = {
        Path("Makefile"),
        Path("Cargo.lock"),
        Path("benchmarks/sources.json"),
        manifest.path.relative_to(root),
        Path("benchmarks/local/figure-inventory.json"),
        Path(".reports-grouped.json"),
    }
    paths.update(Path(f"figures/expanded/{name}.{suffix}") for name in FIGURES for suffix in ("vl.json", "svg", "png"))
    outcomes_path = manifest.path.parent / ".local/outcomes.json"
    if outcomes_path.is_file():
        paths.add(outcomes_path.relative_to(root))
    for outcome in manifest.outcomes:
        if evidence := outcome.get("evidence"):
            directory = (manifest.path.parent / evidence).resolve()
            if not directory.is_relative_to((manifest.path.parent / ".local/validation").resolve()):
                raise ValueError(f"validation evidence escapes the local validation directory: {evidence}")
            paths.update(path.relative_to(root) for path in directory.rglob("*") if path.is_file())
    for workload in manifest.workloads:
        paths.add((manifest.path.parent / workload.file).resolve().relative_to(root))
        if workload.facts:
            facts = (manifest.path.parent / workload.facts).resolve()
            paths.update(path.resolve().relative_to(root) for path in facts.rglob("*") if path.is_file())
    if any((root / path).resolve() == destination for path in paths):
        raise ValueError("archive destination would replace an input")
    # Freeze the small metadata and the grouped snapshot together. Workload files
    # are content-addressed and checked again while copying into the archive.
    snapshots = {
        path: (root / path).read_bytes()
        for path in paths
        if path.suffix == ".json" or path.name in ("Makefile", "Cargo.lock")
    }
    grouped = parse_grouped_report(snapshots[Path(".reports-grouped.json")], ".reports-grouped.json")
    inventory = json.loads(snapshots[Path("benchmarks/local/figure-inventory.json")])
    inputs = {(workload.sha256, workload.facts_sha256) for workload in manifest.workloads}
    labels = {
        parameter["value"]
        for name in FIGURES
        for parameter in json.loads(snapshots[Path(f"figures/expanded/{name}.vl.json")])["params"]
        if parameter["name"] == "target_label"
    }
    engines = sorted(
        {
            group["key"]["binary_sha256"]
            for group in grouped.data["groups"]
            if labels.intersection(group["labels"])
            and (group["key"]["file_sha256"], group["key"]["fact_directory_sha256"]) in inputs
            and group["key"]["timeout_sec"] == inventory["timeout_sec"]
            and group["key"]["treatment"] in ("off", "proofs", "proof-extraction", "egg", "egg-proof-extraction")
        }
    )
    stamp: ArchiveProvenance = {
        "repository_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
        "repository_dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=root)),
        "binary_sha256": engines,
        "render_packages": re.findall(r"--package=([^\s]+)", snapshots[Path("Makefile")].decode()),
        "files": {},
    }
    expected = {
        (manifest.path.parent / workload.file).resolve().relative_to(root): workload.sha256
        for workload in manifest.workloads
    }
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=destination.parent, suffix=".zip", delete=False) as temporary:
        temporary_path = Path(temporary.name)
    try:
        with zipfile.ZipFile(temporary_path, "w", compression=zipfile.ZIP_DEFLATED) as archive:
            for path in sorted(paths):
                source = root / path
                if not source.resolve().is_relative_to(root):
                    raise ValueError(f"archive input escapes the checkout: {path}")
                content = snapshots.get(path)
                if content is None:
                    content = source.read_bytes()
                digest = "sha256:" + hashlib.sha256(content).hexdigest()
                if path in expected and digest != expected[path]:
                    raise ValueError(f"workload changed during archiving: {path}")
                stamp["files"][path.as_posix()] = digest
                archive.writestr(path.as_posix(), content)
            archive.writestr("provenance.json", json.dumps(stamp, indent=2) + "\n")
            images = " \\\n  ".join(
                f"figures/expanded/{name}.{suffix}" for name in FIGURES for suffix in ("svg", "png")
            )
            archive.writestr(
                "README.md",
                "# Paper figure evidence\n\n"
                "This snapshot contains measured observations, the complete prepared input manifest, "
                "workloads, source recipes, local validation outcomes and referenced logs, and the exact "
                "figure specifications. Missing or failed "
                "results are retained. Source and executable identities are recorded in the manifests "
                "and grouped observations; file hashes are in `provenance.json`.\n\n"
                "With Node.js, npm, and Make installed, rerender using the pinned renderer packages:\n\n"
                f"```sh\nmake -B {images}\n```\n\n"
                "This command does not build an engine or collect measurements. "
                "Do not use the collection targets from the included Makefile in this evidence archive.\n",
            )
        os.replace(temporary_path, destination)
    finally:
        temporary_path.unlink(missing_ok=True)
    return destination


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(archive_figures(Path.cwd(), args.output))
