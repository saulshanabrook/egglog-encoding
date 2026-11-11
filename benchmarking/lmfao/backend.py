"""Compile selected views with the pinned LMFAO backend and check all outputs."""

from __future__ import annotations

import json
import math
import os
import re
import subprocess
import time
from pathlib import Path
from typing import Any

from benchmarking.native_memory import native_memory_command
from benchmarking.processes import terminate_process_group, wait4_process
from benchmarking.targets import sha256_file

from . import model
from .data import Results

FLAGS = "-std=c++11 -O3 -pthread -mtune=native -ftree-vectorize -fopenmp"


def command(
    args: list[str], directory: Path, log: str, *, env: dict[str, str] | None = None, timeout: int = 300
) -> float:
    start = time.perf_counter()
    with (directory / log).open("wb") as output:
        process = subprocess.Popen(
            args,
            cwd=directory,
            env=env,
            stdout=output,
            stderr=subprocess.STDOUT,
            text=True,
            start_new_session=True,
        )
        try:
            returncode, _ = wait4_process(process, timeout)
            elapsed = time.perf_counter() - start
            if returncode:
                raise subprocess.CalledProcessError(returncode, args)
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
            raise RuntimeError(f"{args[0]} failed; see {directory / log}") from error
        finally:
            terminate_process_group(process)
    return elapsed


def generate(
    compiler: Path,
    data: Path,
    directory: Path,
    optimizer: dict[str, Any] | None = None,
    *,
    timeout: int = 300,
    root_policy: str | None = None,
) -> dict[str, Any]:
    directory.mkdir(parents=True, exist_ok=True)
    for name in ("workload.json", "plan.json", "extraction.json", "proof.egg"):
        (directory / name).unlink(missing_ok=True)
    env = {k: v for k, v in os.environ.items() if not k.startswith("LMFAO_")}
    env["LMFAO_WORKLOAD_FILE"] = str(directory / "workload.json")
    env["LMFAO_PLAN_FILE"] = str(directory / "plan.json")
    args = [
        str(compiler),
        "--path",
        str(data),
        "--model",
        "covar",
        "--parallel",
        "none",
        "--mo",
        "1",
        "--compress",
        "1",
        "--out",
        str(directory),
    ]
    start = time.perf_counter()
    if root_policy is not None:
        if root_policy != "paper" or optimizer is not None:
            raise ValueError("paper roots require the original LMFAO compiler")
        env["LMFAO_ROOT_POLICY"] = root_policy
    if optimizer is not None:
        command(args, directory, "export.log", env={**env, "LMFAO_EXPORT_ONLY": "1"}, timeout=timeout)
        if not (directory / "workload.json").exists():
            raise ValueError("backend did not export its workload; prepare the pinned adapter")
        optimize(optimizer, directory / "workload.json", directory / "plan.json")
        env["LMFAO_IMPORT_PLAN"] = str(directory / "plan.json")
    command(args, directory, "generate.log", env=env, timeout=timeout)
    generated = time.perf_counter() - start
    if optimizer is not None and "LMFAO imported selected DAG:" not in (directory / "generate.log").read_text():
        raise ValueError("backend did not acknowledge plan import; install the pinned optimizer bridge")
    if root_policy == "paper" and "LMFAO paper coverage roots:" not in (directory / "generate.log").read_text():
        raise ValueError("backend did not acknowledge paper root selection; prepare the current bridge")
    if not (directory / "workload.json").exists() or not (directory / "plan.json").exists():
        raise ValueError("backend did not export its workload and plan; install the pinned optimizer bridge")
    if model.Workload.read(directory / "workload.json").document != model.WORKLOAD.document:
        raise ValueError("LMFAO frontend differs from the frozen benchmark workload")
    return {
        "generation_seconds": generated,
        "compiler_counts": (directory / "compiler-data.out").read_text(),
        "logical_optimizer": f"LMFAO {root_policy or 'configured'} roots" if optimizer is None else "egraph subprocess",
    }


def optimize(config: dict[str, Any], source: Path, destination: Path) -> None:
    out = destination.parent
    phases = {}
    start = time.perf_counter()
    definition = model.Workload.read(source)
    if definition.document != model.WORKLOAD.document:
        raise ValueError("LMFAO frontend differs from the frozen benchmark workload; regenerate explicitly")
    from .program import benchmark_input

    mode = config["treatment"]
    input_path = benchmark_input("slotted" if mode == "slotted" else "debruijn", out, config["rewrite_rounds"])
    phases["input_preparation"] = time.perf_counter() - start
    args, env = native_memory_command(
        [config["extractor"], mode, str(input_path), str(destination), str(config["dag_timeout"])],
        os.environ,
        config["memory_limit_bytes"],
    )
    command(args, out, "extract.log", env=env, timeout=config["timeout"])
    info = json.loads((out / "extraction.json").read_text())
    phases.update(info["phases_seconds"])
    info.update(
        phases_seconds=phases,
        source_workload_sha256=sha256_file(source),
        source_input_sha256=sha256_file(input_path),
        extractor_sha256=sha256_file(Path(config["extractor"])),
    )
    (out / "extraction.json").write_text(json.dumps(info, indent=2) + "\n")


def compile(directory: Path, *, flags: str = FLAGS, jobs: int = 4, timeout: int = 300) -> dict[str, Any]:
    elapsed = command(["make", f"-j{jobs}", "CXX=g++", "CXXFLAG=" + flags], directory, "build.log", timeout=timeout)
    return {"compilation_seconds": elapsed, "flags": flags}


def validate(directory: Path, expected: Results, *, flags: str = FLAGS, timeout: int = 300) -> dict[str, Any]:
    """Use a separate diagnostic executable; preserve the timed objects/binary."""
    source = (directory / "main.cpp").read_text()
    needle = "void dumpOutputViews()\n   {\n      std::ofstream ofs;"
    if source.count(needle) != 1:
        raise ValueError("pinned backend dump function changed")
    (directory / "main-dump.cpp").write_text(source.replace(needle, needle + "\n      ofs << std::setprecision(17);"))
    import shlex

    options = shlex.split(flags)
    command(
        ["g++", *options, "-DDUMP_OUTPUT", "-include", "iomanip", "-c", "main-dump.cpp", "-o", "main-dump.o"],
        directory,
        "build-dump-main.log",
        timeout=timeout,
    )
    command(
        ["g++", *options, "-DDUMP_OUTPUT", "-c", "ApplicationHandler.cpp", "-o", "application-dump.o"],
        directory,
        "build-dump-application.log",
        timeout=timeout,
    )
    target = next(line for line in (directory / "Makefile").read_text().splitlines() if line.startswith("lmfao :"))
    objects = [
        {"main.o": "main-dump.o", "application.o": "application-dump.o"}.get(name, name)
        for name in target.split(":", 1)[1].split()
    ]
    command(["g++", *options, *objects, "-o", "lmfao-dump"], directory, "link-dump.log", timeout=timeout)
    (directory / "output").mkdir(exist_ok=True)
    command(
        [str(directory / "lmfao-dump")],
        directory,
        "validate.log",
        env={**os.environ, "OMP_NUM_THREADS": "1"},
        timeout=timeout,
    )
    mapping = [
        tuple(map(int, line.split(",")))
        for line in (directory / "output/covarianceMatrix.out").read_text().splitlines()
    ]
    if len(mapping) != len(expected):
        raise AssertionError("missing query outputs")
    worst = 0.0
    for i, (view, aggregate) in enumerate(mapping):
        lines = (directory / f"output/V{view}.tbl").read_text().splitlines()
        keys, columns = map(int, lines[0].split())
        if keys != len(model.WORKLOAD.queries[i].groups) or aggregate >= columns:
            raise AssertionError("query output shape differs")
        got = {}
        for line in lines[1:]:
            values = line.split("|")
            key = tuple(map(int, values[:keys]))
            if len(values) != keys + columns or key in got:
                raise AssertionError("malformed or duplicate output row")
            got[key] = float(values[keys + aggregate])
        want = {tuple(r[:-1]): float(r[-1]) for r in expected[i]}
        if got.keys() != want.keys():
            raise AssertionError((i, "group keys differ"))
        for key, value in want.items():
            equal = (
                math.isclose(got[key], value, rel_tol=1e-9, abs_tol=1e-7)
                if model.WORKLOAD.queries[i].factors
                else got[key] == value
            )
            if not equal:
                raise AssertionError((i, key, got[key], value))
            worst = max(worst, abs(got[key] - value) / max(1, abs(value)))
    return {
        "queries_checked": len(expected),
        "counts_and_keys": "exact",
        "max_scaled_error": worst,
        "relative_tolerance": 1e-9,
        "absolute_tolerance": 1e-7,
    }


def execute(directory: Path, repeat: int, timeout: int) -> dict[str, float]:
    elapsed = command(
        [str(directory / "lmfao")],
        directory,
        f"run-{repeat}.log",
        env={**os.environ, "OMP_NUM_THREADS": "1"},
        timeout=timeout,
    )
    log = (directory / f"run-{repeat}.log").read_text()
    matches = re.findall(r"^Data process: ([0-9]+)ms\.$", log, re.MULTILINE)
    if len(matches) != 1:
        raise ValueError("missing upstream computation-time report")
    return {"process_seconds": elapsed, "computation_seconds": int(matches[0]) / 1000}
