#!/usr/bin/env python3
"""Run only the authorized public CLI collection and cache-only delta reports."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("stack_figures", HERE / "stack-figures.py")
figures = importlib.util.module_from_spec(spec)
spec.loader.exec_module(figures)


def verify_source(stage):
    source = Path(stage["source"])
    if figures.git(source, "rev-parse", "HEAD") != stage["git_sha"]:
        raise ValueError(f"Unexpected source commit: {source}")
    if figures.git(source, "status", "--porcelain"):
        raise ValueError(f"Dirty benchmark source: {source}")


def wait_for_build(stage, builds):
    marker = builds / f"{stage['label']}.ready.json"
    announced = False
    while not marker.is_file():
        if not announced:
            print(f"Waiting for prepared build: {marker}", flush=True)
            announced = True
        time.sleep(5)
    ready = json.loads(marker.read_text())
    if ready["git_sha"] != stage["git_sha"] or ready["path"] != stage["source"]:
        raise ValueError(f"Build marker does not match the selected source: {marker}")
    for name, expected in ready["binaries"].items():
        actual = figures.digest(Path(stage["source"]) / "target/release" / name)
        if actual != "sha256:" + expected:
            raise ValueError(f"Prepared binary changed after build: {stage['label']} / {name}")
    return ready


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=HERE / "manifest.json")
    parser.add_argument("--only", action="append", help="Collect a selected stage; earlier native coverage must exist")
    parser.add_argument("--run", action="store_true", help="Actually run builds/benchmarks; otherwise only print the plan")
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    figures.validate_manifest(manifest, require_bound=args.run)
    sys.path.insert(0, manifest["renderer_root"])
    _, resolved = figures.config_and_figures(manifest)
    plan = [command for command in figures.commands(manifest, resolved)
            if not args.only or command["stage"] in args.only]
    if not args.run:
        print(json.dumps(plan, indent=2))
        return
    from benchmarking.reports.store import parse_grouped_report

    stages = {stage["label"]: stage for stage in manifest["stages"]}
    verify_source(manifest["native"])
    for stage in stages.values():
        if not args.only or stage["label"] in args.only:
            verify_source(stage)
    logs = args.manifest.parent / "logs"
    logs.mkdir(exist_ok=True)
    builds = args.manifest.parent / "builds"
    metadata = {"started_at": datetime.now(timezone.utc).isoformat(), "manifest": manifest,
                "commands": plan, "hostname": platform.node(), "platform": platform.platform(),
                "lscpu": json.loads(subprocess.check_output(["lscpu", "--json"], text=True)),
                "environment": {name: os.environ.get(name) for name in
                                ("CARGO_TARGET_DIR", "CARGO_BUILD_JOBS", "RUSTFLAGS", "RUST_TEST_THREADS")}}
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    figures.write_json(logs / f"collection-{stamp}.json", metadata)
    # This collection window begins only after every stage is built and tested.
    # Verify all build markers before the first timed launch, including when a
    # selected-stage resume reuses earlier endpoint observations.
    prepared = {source["label"]: wait_for_build(source, builds)
                for source in (manifest["native"], *manifest["stages"])}
    native_build = prepared[manifest["native"]["label"]]
    environment = dict(os.environ, CARGO_BUILD_JOBS="2", CARGO_INCREMENTAL="0", OPENBLAS_NUM_THREADS="1")
    environment.pop("CARGO_TARGET_DIR", None)
    for command in plan:
        stage = stages[command["stage"]]
        wait_for_build(stage, builds)
        verify_source(stage)
        verify_source(manifest["native"])
        prefix = logs / f"{command['stage']}-{command['figure']}"
        print(f"Collecting {command['stage']} / {command['figure']}; logs {prefix}", flush=True)
        with prefix.with_suffix(".md").open("w") as out, prefix.with_suffix(".log").open("w") as err:
            subprocess.run(command["argv"], cwd=command["cwd"], env=environment, stdout=out, stderr=err, check=True)
        grouped_path = Path(manifest["grouped_path"])
        grouped = parse_grouped_report(grouped_path.read_bytes(), str(grouped_path))
        figure = next(item for item in resolved if item.figure.name == command["figure"])
        index = manifest["stages"].index(stage)
        baseline, reference, candidate = figures.comparison_sources(manifest, index, figure)
        for source, treatment in ((baseline, reference), (stage, candidate)):
            endpoint = figures.endpoint(grouped, source, treatment, manifest["protocol"])
            marker = native_build if source is manifest["native"] else wait_for_build(source, builds)
            binary = "slotted-reference" if source is manifest["native"] else "egglog-experimental"
            if endpoint.binary_sha256 != "sha256:" + marker["binaries"][binary]:
                raise ValueError(f"CLI measured an unexpected executable: {source['label']} / {binary}")
            for file in figure.files:
                figures.selected_condition(grouped, endpoint, file, manifest)
        # Both endpoints were just checked for complete samples. Cache-only target
        # selectors reuse them and never request a new build or measurement.
        if index and figure.figure.name == "slotted-runtime":
            parent = manifest["stages"][index - 1]
            parent_endpoint = figures.endpoint(grouped, parent, candidate, manifest["protocol"])
            for file in figure.files:
                figures.selected_condition(grouped, parent_endpoint, file, manifest)
            delta = command["argv"].copy()
            delta[delta.index("--target") + 1] = stage["label"] + "="
            delta[delta.index("--compare-target") + 1] = parent["label"] + "="
            delta[delta.index("--compare-treatment") + 1] = candidate
            with (logs / f"{stage['label']}-{figure.figure.name}-delta.md").open("w") as out:
                with (logs / f"{stage['label']}-{figure.figure.name}-delta.log").open("w") as err:
                    subprocess.run(delta, cwd=command["cwd"], env=environment, stdout=out, stderr=err, check=True)
        elif index:
            shutil.copyfile(prefix.with_suffix(".md"), logs / f"{stage['label']}-{figure.figure.name}-delta.md")
        print(f"Verified {command['stage']} / {command['figure']}: {len(figure.files)} workloads", flush=True)


if __name__ == "__main__":
    main()
