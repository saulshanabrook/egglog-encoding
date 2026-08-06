"""Declare the fixed paper Math, pointer, and bounded Herbie benchmark lanes."""

from __future__ import annotations

import sys
from dataclasses import replace
from pathlib import Path

from scripts.generate_math_checkpoints import CHECKPOINTS, EXPECTED_TABLE_SIZES, EXPECTED_TABLE_TOTALS, TABLES

from .herbie import herbie_lanes
from .lanes import LaneRegistry
from .models import CommandSpec, Preset, ProcessLane
from .rust_artifact import RUST_ARTIFACT_COMPATIBILITY, RUST_ARTIFACT_TOOLCHAIN

_CURRENT_MODES = (
    ("current-off", ()),
    ("current-term", ("--term-encoding",)),
    ("current-proofs", ("--proofs",)),
)

_ARTIFACT_EGG_SIZES = {
    0: 35,
    10: 13_106,
    20: 24_329,
    30: 47_434,
    40: 92_137,
    50: 183_270,
    60: 320_438,
    70: 442_458,
    80: 709_503,
    90: 1_244_385,
    100: 1_861_957,
}


def production_registry(repo_root: Path) -> LaneRegistry:
    """Return the repository's concrete paper evaluation adapters."""

    root = repo_root.resolve(strict=True)
    return LaneRegistry(
        {
            "math": lambda preset, artifact: math_lanes(root, artifact, preset),
            "pointer": lambda preset, artifact: pointer_lanes(root, artifact, preset),
            "herbie": lambda preset, artifact: herbie_lanes(root, artifact, preset),
        }
    )


def math_lanes(repo_root: Path, artifact_root: Path, preset: Preset) -> tuple[ProcessLane, ...]:
    """Compare paper Egg/Eqlog with current off, term, and proof modes."""

    checkpoints, rounds = _math_selection(preset)
    artifact_input_source = artifact_root / "micro-benchmarks"
    artifact_work = repo_root / ".paper-build" / "artifact-math-work"
    artifact_source = artifact_work / "micro-benchmarks"
    artifact_target = repo_root / ".paper-build" / "artifact-math-target"
    artifact_binary = artifact_target / "release" / "eqlog-benchmark"
    current_target = repo_root / ".paper-build" / "current-target"
    current_binary = current_target / "release" / "egglog-experimental"

    artifact_build = _artifact_cargo_build(
        repo_root,
        artifact_root,
        artifact_work,
        artifact_source,
        artifact_target,
        "paper-math",
        "math",
    )
    current_build = _current_build(repo_root, current_target)
    lanes: list[ProcessLane] = []
    for iterations in checkpoints:
        expected_total = EXPECTED_TABLE_TOTALS[iterations]
        artifact_inputs = (
            artifact_input_source / "Cargo.toml",
            artifact_input_source / "Cargo.lock",
            artifact_input_source / "src",
            artifact_root / "eqlog" / "Cargo.toml",
            artifact_root / "eqlog" / "Cargo.lock",
            artifact_root / "eqlog" / "src",
            artifact_input_source / "benchmarks.csv",
            Path(__file__).resolve().parent / "rust_artifact.py",
        )
        lanes.append(
            ProcessLane(
                evaluation="math",
                name=f"artifact-egg-n{iterations:03d}",
                build=artifact_build,
                observations=_rounds(
                    CommandSpec(
                        label="run",
                        argv=(
                            str(artifact_binary),
                            "--repeat",
                            "1",
                            "--iter-size",
                            str(iterations),
                            "--only-iter",
                            str(iterations),
                            "--csvfile",
                            "/dev/stdout",
                            "--disable-eqlog",
                        ),
                        cwd=artifact_source,
                        timeout_sec=_math_timeout(iterations),
                        env={"RUST_LOG": "error"},
                        expected_stdout_csv_record=(
                            f"math-run-{iterations}",
                            "Egg",
                            _ARTIFACT_EGG_SIZES[iterations],
                        ),
                        expected_stdout_lines=(),
                    ),
                    rounds,
                ),
                input_paths=artifact_inputs,
                versions={
                    "compatibility": RUST_ARTIFACT_COMPATIBILITY,
                    "engine": "paper-egg",
                    "iterations": str(iterations),
                    "rust-toolchain": RUST_ARTIFACT_TOOLCHAIN,
                },
            )
        )
        lanes.append(
            ProcessLane(
                evaluation="math",
                name=f"artifact-eqlog-n{iterations:03d}",
                build=artifact_build,
                observations=_rounds(
                    CommandSpec(
                        label="run",
                        argv=(
                            str(artifact_binary),
                            "--repeat",
                            "1",
                            "--iter-size",
                            str(iterations),
                            "--only-iter",
                            str(iterations),
                            "--csvfile",
                            "/dev/stdout",
                            "--disable-egg",
                            "--disable-eqlog-naive",
                        ),
                        cwd=artifact_source,
                        timeout_sec=_math_timeout(iterations),
                        env={"RUST_LOG": "error"},
                        expected_stdout_csv_record=(f"math-run-{iterations}", "Eqlog", expected_total),
                        expected_stdout_lines=tuple(
                            f"Function {table} has size {size}"
                            for table, size in zip(TABLES, EXPECTED_TABLE_SIZES[iterations], strict=True)
                        ),
                    ),
                    rounds,
                ),
                input_paths=artifact_inputs,
                versions={
                    "engine": "paper-eqlog",
                    "iterations": str(iterations),
                    "compatibility": RUST_ARTIFACT_COMPATIBILITY,
                    "rust-toolchain": RUST_ARTIFACT_TOOLCHAIN,
                },
            )
        )

        fixture = repo_root / "benchmarks" / "math-microbenchmark" / f"math-run-{iterations:03d}.egg"
        current_inputs = (
            fixture,
            repo_root / "benchmarks" / "math-microbenchmark" / "base.egg",
        )
        for lane_name, flags in _CURRENT_MODES:
            command = _current_command(
                current_binary,
                repo_root,
                fixture,
                flags,
                timeout_sec=_math_timeout(iterations),
                expected_stdout_lines=tuple(str(size) for size in EXPECTED_TABLE_SIZES[iterations]),
            )
            validate: tuple[CommandSpec, ...] = ()
            if lane_name == "current-proofs":
                validate = (
                    _current_command(
                        current_binary,
                        repo_root,
                        fixture,
                        ("--proof-testing",),
                        timeout_sec=_math_timeout(iterations),
                        label="proof-check",
                    ),
                )
            lanes.append(
                ProcessLane(
                    evaluation="math",
                    name=f"{lane_name}-n{iterations:03d}",
                    build=(current_build,),
                    validate=validate,
                    observations=_rounds(command, rounds),
                    input_paths=current_inputs,
                    versions={"engine": lane_name, "iterations": str(iterations)},
                )
            )
    return tuple(lanes)


def pointer_lanes(repo_root: Path, artifact_root: Path, preset: Preset) -> tuple[ProcessLane, ...]:
    """Run the paper initdb pointer workload and its current adaptation."""

    rounds = {"quick": 1, "representative": 3, "artifact-full": 5}[preset]
    artifact_input_source = artifact_root / "eqlog"
    artifact_work = repo_root / ".paper-build" / "artifact-eqlog-work"
    artifact_source = artifact_work / "eqlog"
    pointer_source = artifact_root / "pointer-analysis-benchmark"
    artifact_target = repo_root / ".paper-build" / "artifact-eqlog-target"
    artifact_binary = artifact_target / "release" / "eqlog"
    artifact_build = _artifact_cargo_build(
        repo_root,
        artifact_root,
        artifact_work,
        artifact_source,
        artifact_target,
        "paper-eqlog",
        "eqlog",
    )
    artifact_facts = pointer_source / "benchmark-input" / "postgresql-9.5.2" / "initdb.bc"
    paper_command = CommandSpec(
        label="run",
        argv=(str(artifact_binary), "-F", str(artifact_facts), str(pointer_source / "main.egg")),
        cwd=pointer_source,
        timeout_sec=600,
        env={"RUST_LOG": "info"},
        expected_stdout_lines=(
            "Function expr_points_to has size 5832",
            "Function ptr_points_to has size 342",
        ),
    )
    lanes: list[ProcessLane] = [
        ProcessLane(
            evaluation="pointer",
            name="artifact-eqlog-initdb",
            build=artifact_build,
            observations=_rounds(paper_command, rounds),
            input_paths=(
                artifact_input_source / "Cargo.toml",
                artifact_input_source / "Cargo.lock",
                artifact_input_source / "src",
                pointer_source / "main.egg",
                artifact_facts,
                Path(__file__).resolve().parent / "rust_artifact.py",
            ),
            versions={
                "compatibility": RUST_ARTIFACT_COMPATIBILITY,
                "engine": "paper-eqlog",
                "rust-toolchain": RUST_ARTIFACT_TOOLCHAIN,
                "workload": "postgresql-initdb",
            },
        )
    ]

    current_target = repo_root / ".paper-build" / "current-target"
    current_binary = current_target / "release" / "egglog-experimental"
    current_build = _current_build(repo_root, current_target)
    fixture = repo_root / "benchmarks" / "pointer-analysis-initdb.egg"
    facts = repo_root / "benchmarks" / "data" / "pointer-analysis-initdb"
    for lane_name, flags in _CURRENT_MODES:
        command = _current_command(
            current_binary,
            repo_root,
            fixture,
            flags,
            timeout_sec=600,
            fact_directory=facts,
            expected_stdout_lines=("5832", "342"),
        )
        validate: tuple[CommandSpec, ...] = ()
        if lane_name == "current-proofs":
            validate = (
                _current_command(
                    current_binary,
                    repo_root,
                    fixture,
                    ("--proof-testing",),
                    timeout_sec=600,
                    fact_directory=facts,
                    label="proof-check",
                ),
            )
        lanes.append(
            ProcessLane(
                evaluation="pointer",
                name=f"{lane_name}-initdb",
                build=(current_build,),
                validate=validate,
                observations=_rounds(command, rounds),
                input_paths=(fixture, facts),
                versions={"engine": lane_name, "workload": "postgresql-initdb"},
            )
        )
    return tuple(lanes)


def _math_selection(preset: Preset) -> tuple[tuple[int, ...], int]:
    if preset == "quick":
        return (10,), 1
    if preset == "representative":
        return (10,), 5
    return CHECKPOINTS, 1


def _math_timeout(iterations: int) -> float:
    return 120 if iterations <= 20 else 900


def _artifact_cargo_build(
    repo_root: Path,
    artifact_root: Path,
    work_root: Path,
    source: Path,
    target: Path,
    label: str,
    kind: str,
) -> tuple[CommandSpec, ...]:
    return (
        CommandSpec(
            label=f"{label}-stage",
            argv=(
                str(Path(sys.executable).resolve()),
                "-m",
                "paper_benchmarking.rust_artifact",
                "--artifact-root",
                str(artifact_root),
                "--destination",
                str(work_root),
                "--kind",
                kind,
            ),
            cwd=repo_root,
            timeout_sec=60,
            env={"PYTHONPATH": str(repo_root)},
        ),
        CommandSpec(
            label=label,
            argv=("cargo", "build", "--release", "--locked"),
            cwd=source,
            timeout_sec=1_800,
            env={
                "CARGO_INCREMENTAL": "0",
                "CARGO_TARGET_DIR": str(target),
                "RUSTC_WRAPPER": "",
                "RUSTUP_TOOLCHAIN": RUST_ARTIFACT_TOOLCHAIN,
            },
        ),
    )


def _current_build(repo_root: Path, target: Path) -> CommandSpec:
    return CommandSpec(
        label="current-egglog",
        argv=("cargo", "build", "--release", "--locked", "-p", "egglog-experimental"),
        cwd=repo_root,
        timeout_sec=1_800,
        env={"CARGO_INCREMENTAL": "0", "CARGO_TARGET_DIR": str(target), "RUSTC_WRAPPER": ""},
    )


def _current_command(
    binary: Path,
    repo_root: Path,
    fixture: Path,
    flags: tuple[str, ...],
    *,
    timeout_sec: float,
    fact_directory: Path | None = None,
    expected_stdout_lines: tuple[str, ...] | None = None,
    label: str = "run",
) -> CommandSpec:
    fact_args = ("-F", str(fact_directory)) if fact_directory is not None else ()
    return CommandSpec(
        label=label,
        argv=(str(binary), "-j", "1", *flags, *fact_args, str(fixture)),
        cwd=repo_root,
        timeout_sec=timeout_sec,
        env={"RAYON_NUM_THREADS": "1", "RUST_LOG": "error"},
        expected_stdout_lines=expected_stdout_lines,
    )


def _rounds(command: CommandSpec, rounds: int) -> tuple[CommandSpec, ...]:
    return tuple(replace(command, label=f"{command.label}-{round_number}") for round_number in range(1, rounds + 1))
