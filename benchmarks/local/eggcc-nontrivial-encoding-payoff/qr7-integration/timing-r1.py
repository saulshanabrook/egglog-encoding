#!/usr/bin/env python3
"""Collect one frozen QR7 generated-runtime session."""

from __future__ import annotations

import sys
from pathlib import Path

# This directory contains inspect.py, which would shadow the standard library
# when argparse imports inspect.
_IMPORT_ROOT = Path(__file__).resolve().parent
sys.path = [entry for entry in sys.path if Path(entry or Path.cwd()).resolve() != _IMPORT_ROOT]

import argparse
import fcntl
import hashlib
import json
import os
import platform
import signal
import statistics
import subprocess
import time
from typing import Any, BinaryIO, TextIO


ROOT = _IMPORT_ROOT
DESIGN = ROOT / "prospective-timing-design-r1.json"
PREFLIGHT = ROOT / "timing-preflight-r1.json"
PREPARER = ROOT / "prepare-timing-r1.py"
VERIFIER = ROOT / "verify-timing-r1.py"
FREEZER = ROOT / "freeze-timing-r1.py"
LOCK = ROOT / "timing-r1.lock"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json_line(stream: TextIO, value: dict[str, Any]) -> None:
    stream.write(json.dumps(value, sort_keys=True) + "\n")
    stream.flush()
    os.fsync(stream.fileno())


def machine_state() -> dict[str, Any]:
    try:
        load_average = list(os.getloadavg())
    except OSError:
        load_average = None
    vm = subprocess.run(
        ["/usr/bin/vm_stat"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30, check=False
    )
    return {
        "monotonic_ns": time.monotonic_ns(),
        "wall_time_ns": time.time_ns(),
        "load_average": load_average,
        "platform": platform.platform(),
        "machine": platform.machine(),
        "python": platform.python_version(),
        "cpu_count": os.cpu_count(),
        "pid": os.getpid(),
        "vm_stat_exit_code": vm.returncode,
        "vm_stat_stdout_sha256": hashlib.sha256(vm.stdout).hexdigest(),
        "vm_stat_stderr": vm.stderr.decode(errors="replace"),
        "memory_pressure_is_advisory_only": True,
    }


def process_snapshot() -> dict[str, Any]:
    command = ["/bin/ps", "-axo", "pid=,ppid=,%cpu=,%mem=,comm="]
    completed = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30, check=False)
    rows = []
    if completed.returncode == 0:
        for line in completed.stdout.decode(errors="replace").splitlines():
            fields = line.strip().split(maxsplit=4)
            if len(fields) == 5:
                pid, ppid, cpu, memory, command_name = fields
                rows.append(
                    {
                        "pid": int(pid),
                        "ppid": int(ppid),
                        "cpu_percent": float(cpu),
                        "memory_percent": float(memory),
                        "command": command_name,
                    }
                )
    return {
        "wall_time_ns": time.time_ns(),
        "monotonic_ns": time.monotonic_ns(),
        "command": command,
        "exit_code": completed.returncode,
        "stderr": completed.stderr.decode(errors="replace"),
        "processes": rows,
        "admission_gate": False,
        "memory_or_process_pressure_never_discards_samples": True,
    }


def run_process(binary: Path, args: list[int], expected: bytes, timeout_s: int, child_env: dict[str, str]) -> bytes:
    process = subprocess.Popen(
        [str(binary), *map(str, args)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=child_env,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout_s)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.communicate()
        raise
    if process.returncode != 0:
        raise RuntimeError(f"native process exited {process.returncode}")
    if stderr:
        raise RuntimeError(f"native process wrote stderr: {stderr.decode(errors='replace')}")
    if stdout != expected:
        raise RuntimeError(f"wrong stdout: {stdout!r} != {expected!r}")
    return stdout


def measured_batch(
    binary: Path,
    args: list[int],
    expected: bytes,
    timeout_s: int,
    invocations: int,
    child_env: dict[str, str],
) -> tuple[int, str]:
    completed: list[tuple[int, bytes, bytes]] = []
    start = time.perf_counter_ns()
    for _ in range(invocations):
        process = subprocess.Popen(
            [str(binary), *map(str, args)],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=child_env,
            start_new_session=True,
        )
        try:
            stdout, stderr = process.communicate(timeout=timeout_s)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.communicate()
            raise
        completed.append((process.returncode, stdout, stderr))
    duration_ns = time.perf_counter_ns() - start
    output_hash = hashlib.sha256()
    for returncode, stdout, stderr in completed:
        if returncode != 0:
            raise RuntimeError(f"native process exited {returncode}")
        if stderr:
            raise RuntimeError(f"native process wrote stderr: {stderr.decode(errors='replace')}")
        if stdout != expected:
            raise RuntimeError(f"wrong stdout: {stdout!r} != {expected!r}")
        output_hash.update(stdout)
    return duration_ns, output_hash.hexdigest()


def validate_preflight(design: dict[str, Any]) -> dict[str, Any]:
    preflight = json.loads(PREFLIGHT.read_text())
    expected = {
        "design_sha256": sha256(DESIGN),
        "collector_sha256": sha256(Path(__file__)),
        "preparer_sha256": sha256(PREPARER),
        "verifier_sha256": sha256(VERIFIER),
        "freezer_sha256": sha256(FREEZER),
    }
    for key, value in expected.items():
        if preflight.get(key) != value:
            raise RuntimeError(f"preflight drift for {key}")
    if not preflight.get("all_identity_and_order_checks_passed"):
        raise RuntimeError("timing preflight did not pass")
    for arm, identity in design["arms"].items():
        if sha256(Path(identity["binary"])) != identity["binary_sha256"]:
            raise RuntimeError(f"binary drift for {arm}")
    return preflight


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("session", choices=("screen", "confirmation"))
    args = parser.parse_args()
    if os.environ.get("EGGLOG_BENCH_MEMORY_GUARD") is not None:
        raise RuntimeError("EGGLOG_BENCH_MEMORY_GUARD must be absent, not empty")

    design = json.loads(DESIGN.read_text())
    if design["timed_samples_taken"]:
        raise RuntimeError("prospective design unexpectedly claims prior samples")
    preflight = validate_preflight(design)
    declared = next(item for item in design["sessions"] if item["name"] == args.session)
    output_dir = ROOT / "timing-r1" / args.session
    if output_dir.exists():
        raise RuntimeError(f"refusing to overwrite {output_dir}")

    lock_stream = LOCK.open("a+")
    try:
        fcntl.flock(lock_stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as error:
        raise RuntimeError("another QR7 timing session holds the lock") from error
    output_dir.mkdir(parents=True)
    lock_stream.seek(0)
    lock_stream.truncate()
    lock_stream.write(json.dumps({"pid": os.getpid(), "session": args.session, "wall_time_ns": time.time_ns()}) + "\n")
    lock_stream.flush()
    os.fsync(lock_stream.fileno())

    events_path = output_dir / "events.jsonl"
    warmups_path = output_dir / "warmups.jsonl"
    samples_path = output_dir / "samples.jsonl"
    snapshots_path = output_dir / "process-snapshots.jsonl"
    binaries = {arm: Path(identity["binary"]) for arm, identity in design["arms"].items()}
    workloads = {item["name"]: item for item in design["workloads"]}
    child_env = dict(design["child_environment"])
    timeout_s = design["timeout_s_per_process"]
    rows: list[dict[str, Any]] = []
    completed_invocations = 0
    start_state = machine_state()

    with (
        events_path.open("x") as events,
        warmups_path.open("x") as warmups,
        samples_path.open("x") as samples,
        snapshots_path.open("x") as snapshots,
    ):
        write_json_line(
            events,
            {
                "event": "session_started",
                "session": args.session,
                "design_sha256": sha256(DESIGN),
                "preflight_sha256": sha256(PREFLIGHT),
                "preflight_identity_checks_passed": preflight["all_identity_and_order_checks_passed"],
                "machine_state": start_state,
            },
        )
        write_json_line(snapshots, {"phase": "session_start", "completed_cycles": 0, "snapshot": process_snapshot()})
        try:
            for workload in design["workloads"]:
                expected = workload["expected_stdout"].encode()
                for arm in design["arms"]:
                    for warmup in range(design["warmups_per_arm_per_workload_per_session"]):
                        stdout = run_process(binaries[arm], workload["args"], expected, timeout_s, child_env)
                        completed_invocations += 1
                        write_json_line(
                            warmups,
                            {
                                "session": args.session,
                                "workload": workload["name"],
                                "arm": arm,
                                "warmup": warmup,
                                "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
                            },
                        )

            for cycle_spec in declared["cycle_order"]:
                for workload_position, workload_name in enumerate(cycle_spec["workload_order"]):
                    workload = workloads[workload_name]
                    expected = workload["expected_stdout"].encode()
                    for arm_position, arm in enumerate(cycle_spec["arm_order"]):
                        context = {
                            "session": args.session,
                            "cycle": cycle_spec["cycle"],
                            "complete_block": cycle_spec["complete_block"],
                            "williams_row": cycle_spec["williams_row"],
                            "workload": workload_name,
                            "workload_position": workload_position,
                            "arm": arm,
                            "arm_position": arm_position,
                        }
                        duration_ns, output_sha256 = measured_batch(
                            binaries[arm],
                            workload["args"],
                            expected,
                            timeout_s,
                            design["invocations_per_observation"],
                            child_env,
                        )
                        completed_invocations += design["invocations_per_observation"]
                        row = {
                            **context,
                            "args": workload["args"],
                            "expected_stdout": workload["expected_stdout"],
                            "invocations": design["invocations_per_observation"],
                            "duration_ns": duration_ns,
                            "mean_process_ns": duration_ns / design["invocations_per_observation"],
                            "output_sha256": output_sha256,
                        }
                        rows.append(row)
                        write_json_line(samples, row)
                if (cycle_spec["cycle"] + 1) % len(design["arms"]) == 0:
                    write_json_line(
                        snapshots,
                        {
                            "phase": "complete_block_boundary",
                            "completed_cycles": cycle_spec["cycle"] + 1,
                            "snapshot": process_snapshot(),
                        },
                    )

            write_json_line(
                snapshots,
                {"phase": "session_end", "completed_cycles": declared["cycles"], "snapshot": process_snapshot()},
            )
            end_state = machine_state()
            arm_medians = {
                workload["name"]: {
                    arm: statistics.median(
                        row["duration_ns"]
                        for row in rows
                        if row["workload"] == workload["name"] and row["arm"] == arm
                    )
                    for arm in design["arms"]
                }
                for workload in design["workloads"]
            }
            summary = {
                "schema_version": 1,
                "session": args.session,
                "design_sha256": sha256(DESIGN),
                "preflight_sha256": sha256(PREFLIGHT),
                "start_state": start_state,
                "end_state": end_state,
                "raw_row_count": len(rows),
                "samples_sha256": sha256(samples_path),
                "warmups_sha256": sha256(warmups_path),
                "events_sha256_before_completion": sha256(events_path),
                "process_snapshots_sha256": sha256(snapshots_path),
                "completed_invocations": completed_invocations,
                "all_outputs_exact": True,
                "all_outliers_retained": True,
                "memory_pressure_was_not_an_admission_gate": True,
                "arm_median_batch_ns": arm_medians,
            }
            summary_path = output_dir / "summary.json"
            summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
            write_json_line(
                events,
                {
                    "event": "session_completed",
                    "session": args.session,
                    "raw_rows": len(rows),
                    "completed_invocations": completed_invocations,
                    "summary_sha256": sha256(summary_path),
                    "machine_state": end_state,
                },
            )
            print(json.dumps(summary, indent=2, sort_keys=True))
        except BaseException as error:
            write_json_line(
                events,
                {
                    "event": "session_failed",
                    "session": args.session,
                    "error_type": type(error).__name__,
                    "error": str(error),
                    "completed_invocations": completed_invocations,
                    "persisted_rows": len(rows),
                    "machine_state": machine_state(),
                },
            )
            raise
        finally:
            fcntl.flock(lock_stream, fcntl.LOCK_UN)
            lock_stream.close()


if __name__ == "__main__":
    main()
