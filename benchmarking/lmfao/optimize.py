"""Subprocess entrypoint called by LMFAO's logical-optimizer hook."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

from benchmarking.native_memory import native_memory_command
from benchmarking.targets import sha256_file
from benchmarking.workloads import resolve_files
from benchmarks.reproduction.slotted.lmfao import frozen, ordinary

from . import model
from .optimizer import ROOT, export_graph, write_json


def run(config: dict[str, Any], source: Path, destination: Path) -> None:
    out = destination.parent
    phases = {}
    start = time.perf_counter()
    definition = model.Workload.read(source)
    if definition.document != model.WORKLOAD.document:
        raise ValueError("LMFAO frontend differs from the frozen benchmark workload; regenerate explicitly")
    files = frozen(modes=(config["variant"],), definition=definition)
    for name, contents in files.items():
        (out / name).write_text(contents)
    manifest = json.loads(files["manifest.json"])
    file = resolve_files([str(out / manifest["variants"][0]["file"])], ROOT)[0]
    mode, input_path = "slotted", file.absolute_path
    if config["treatment"] == "off":
        mode, input_path = "off", out / "ordinary.egg"
        input_path.write_text(
            ordinary(file.absolute_path.read_text(), canonical=config["binding_control"] == "canonical")
        )
    phases["translation"] = time.perf_counter() - start
    start = time.perf_counter()
    if config["treatment"] == "slotted-ref-multi":
        mode, input_path = "graph", out / "graph.json"
        export_graph(
            Path(config["binary"]),
            file,
            config["treatment"],
            input_path,
            manifest["export_names"],
            config["timeout"],
            config["memory_limit_bytes"],
        )
        phases["native_rewriting_and_export"] = time.perf_counter() - start
    command, env = native_memory_command(
        [config["extractor"], mode, str(input_path), str(destination), str(config["dag_timeout"])],
        os.environ,
        config["memory_limit_bytes"],
    )
    # Inherit the LMFAO process group so its outer timeout also stops extraction.
    # The Rust executable creates threads only; run() handles its own timeout.
    with (out / "extract.log").open("wb") as log:
        subprocess.run(
            command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=config["timeout"]
        )
    info = json.loads((out / "extraction.json").read_text())
    phases.update(info["phases_seconds"])
    if mode == "graph":
        phases.pop("rewriting")
    info.update(
        phases_seconds=phases,
        source_workload_sha256=sha256_file(source),
        source_input_sha256=sha256_file(input_path),
        extractor_sha256=sha256_file(Path(config["extractor"])),
    )
    write_json(out / "extraction.json", info)


if __name__ == "__main__":
    settings, source, destination = map(Path, sys.argv[1:])
    run(json.loads(settings.read_text()), source, destination)
