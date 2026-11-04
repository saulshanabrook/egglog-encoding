#!/usr/bin/env python3
"""Run one frozen Parts32 generated-runtime confirmation session."""

from __future__ import annotations

import sys
from pathlib import Path

# This evidence directory contains inspect.py. Remove it from module search
# before argparse can import the standard-library inspect module.
_IMPORT_ROOT = Path(__file__).resolve().parent
sys.path = [entry for entry in sys.path if Path(entry or Path.cwd()).resolve() != _IMPORT_ROOT]

import argparse
import fcntl
import hashlib
import json
import math
import os
import platform
import random
import statistics
import subprocess
import time
from typing import Any, TextIO

ROOT = _IMPORT_ROOT
DESIGN = ROOT / "prospective-timing-design-frozen.json"
PREFLIGHT = ROOT / "timing-preflight.json"
VERIFIER = ROOT / "verify-timing.py"
LOCK = ROOT / "timing-measurement.lock"
PREPARER = ROOT / "prepare-timing.py"
SOURCE_IDENTITIES = ROOT / "final-source-identities.json"
PROCESS_COMMAND = ["ps", "-axo", "pid=,ppid=,%cpu=,%mem=,comm="]
# Admission checks run outside measured batches. Known build/benchmark jobs are
# rejected even when momentarily idle. The fixed >=75% per-process CPU cutoff
# also rejects unknown near-full-core jobs without classifying ordinary GUI
# activity as a benchmark job. It is not an aggregate host-idle guarantee.
# Only this Python process and its inventory subprocess are exempt.
PROCESS_POLICY = {
    "version": 2,
    "material_cpu_percent": 75.0,
    "known_job_names": [
        "as",
        "c++",
        "cargo",
        "cc",
        "cc1",
        "cc1plus",
        "clang",
        "clang++",
        "cmake",
        "egg-math-benchmark",
        "eggcc",
        "egglog",
        "egglog-experimental",
        "g++",
        "gcc",
        "ld",
        "ld64",
        "lld",
        "lld-link",
        "make",
        "ninja",
        "program",
        "rustc",
        "rustdoc",
        "tiger",
    ],
    "known_job_prefixes": ["clang-", "clang++-", "gcc-", "g++-", "llvm-"],
    "exemptions": ["self_pid", "inventory_pid"],
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def json_sha256(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def capture_process_snapshot() -> dict[str, Any]:
    """Inventory all processes without reading unrelated argv or environments."""
    snapshot: dict[str, Any] = {
        "schema_version": 1,
        "command": PROCESS_COMMAND,
        "policy": PROCESS_POLICY,
        "self": {
            "pid": os.getpid(),
            "ppid": os.getppid(),
            "cwd": str(Path.cwd()),
            "argv": list(sys.argv),
            "executable": sys.executable,
        },
        "inventory_pid": None,
        "exit_code": None,
        "inventory_error": None,
        "processes": [],
        "competitors": [],
        "passed": False,
    }
    try:
        with subprocess.Popen(PROCESS_COMMAND, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) as process:
            snapshot["inventory_pid"] = process.pid
            try:
                stdout, stderr = process.communicate(timeout=30)
            except subprocess.TimeoutExpired:
                process.kill()
                process.communicate()
                raise RuntimeError("process inventory timed out") from None
            snapshot["exit_code"] = process.returncode
        if process.returncode != 0 or stderr:
            raise RuntimeError("process inventory returned an error")
        for line in stdout.splitlines():
            if not line.strip():
                continue
            pid, ppid, cpu, memory, comm = line.strip().split(maxsplit=4)
            item = {
                "pid": int(pid),
                "ppid": int(ppid),
                "cpu_percent": float(cpu),
                "memory_percent": float(memory),
                # Escape controls in executable names; comm contains no argv.
                "comm": "".join(char if char.isprintable() else f"\\u{ord(char):04x}" for char in comm),
            }
            if not all(math.isfinite(item[field]) and item[field] >= 0 for field in ("cpu_percent", "memory_percent")):
                raise ValueError("invalid process utilization")
            snapshot["processes"].append(item)
            if item["pid"] in (snapshot["self"]["pid"], snapshot["inventory_pid"]):
                continue
            name = Path(item["comm"]).name
            reasons = []
            if name in PROCESS_POLICY["known_job_names"] or any(
                name.startswith(prefix) for prefix in PROCESS_POLICY["known_job_prefixes"]
            ):
                reasons.append("known_compiler_or_benchmark")
            if item["cpu_percent"] >= PROCESS_POLICY["material_cpu_percent"]:
                reasons.append("material_cpu")
            if reasons:
                snapshot["competitors"].append({**item, "reasons": reasons})
        pids = [item["pid"] for item in snapshot["processes"]]
        if len(pids) != len(set(pids)) or snapshot["self"]["pid"] not in pids or snapshot["inventory_pid"] not in pids:
            raise ValueError("incomplete or duplicate process inventory")
        own_process = next(item for item in snapshot["processes"] if item["pid"] == snapshot["self"]["pid"])
        if own_process["ppid"] != snapshot["self"]["ppid"]:
            raise ValueError("process parent identity mismatch")
        snapshot["passed"] = not snapshot["competitors"]
    except (OSError, RuntimeError, ValueError) as error:
        snapshot["inventory_error"] = f"{type(error).__name__}: {error}"
    snapshot["monotonic_ns"] = time.monotonic_ns()
    snapshot["wall_time_ns"] = time.time_ns()
    return snapshot


def checked_process_snapshot(stream: TextIO, events: TextIO, checks: list[dict[str, Any]], **context: Any) -> None:
    snapshot = capture_process_snapshot()
    check = {
        **context,
        "checkpoint_index": len(checks),
        "snapshot": snapshot,
        "snapshot_sha256": json_sha256(snapshot),
    }
    write_json_line(stream, check)
    checks.append(check)
    write_json_line(
        events,
        {
            "event": "process_snapshot_checked" if snapshot["passed"] else "process_snapshot_failed",
            **context,
            "checkpoint_index": check["checkpoint_index"],
            "snapshot_sha256": check["snapshot_sha256"],
            "process_check_sha256": json_sha256(check),
        },
    )
    if not snapshot["passed"]:
        raise RuntimeError("process admission failed; retained inventory and competitors in process-checks.jsonl")


def machine_state() -> dict[str, Any]:
    try:
        load_average = list(os.getloadavg())
    except OSError:
        load_average = None
    return {
        "monotonic_ns": time.monotonic_ns(),
        "wall_time_ns": time.time_ns(),
        "load_average": load_average,
        "platform": platform.platform(),
        "machine": platform.machine(),
        "python": platform.python_version(),
        "pid": os.getpid(),
    }


def write_json_line(stream: TextIO, value: dict[str, Any]) -> None:
    stream.write(json.dumps(value, sort_keys=True) + "\n")
    stream.flush()
    os.fsync(stream.fileno())


def percentile(values: list[float], probability: float) -> float:
    ordered = sorted(values)
    position = probability * (len(ordered) - 1)
    lower = int(position)
    upper = min(lower + 1, len(ordered) - 1)
    weight = position - lower
    return ordered[lower] * (1.0 - weight) + ordered[upper] * weight


def clustered_interval(logs_by_block: list[list[float]], *, seed: int, draws: int = 10_000) -> list[float]:
    rng = random.Random(seed)
    estimates = []
    for _ in range(draws):
        sampled_logs = [value for _ in logs_by_block for value in logs_by_block[rng.randrange(len(logs_by_block))]]
        estimates.append(math.exp(statistics.median(sampled_logs)))
    return [percentile(estimates, 0.025), percentile(estimates, 0.975)]


def validate_preflight(design: dict[str, Any]) -> dict[str, Any]:
    preflight = json.loads(PREFLIGHT.read_text())
    expected = {
        "design_sha256": sha256(DESIGN),
        "timing_sha256": sha256(Path(__file__)),
        "verifier_sha256": sha256(VERIFIER),
        "preparer_sha256": sha256(PREPARER),
        "source_identities_sha256": sha256(SOURCE_IDENTITIES),
    }
    for field in ("source", "compiler_binary", "compiler_source_snapshot"):
        actual = sha256(Path(design[field]))
        if actual != design[f"{field}_sha256"]:
            raise RuntimeError(f"{field} hash drift")
        expected[f"{field}_sha256"] = actual
    for key, value in expected.items():
        if preflight.get(key) != value:
            raise RuntimeError(f"preflight {key} drift: {preflight.get(key)!r} != {value!r}")
    if not preflight.get("memory_guard_unset"):
        raise RuntimeError("preflight did not establish an unset memory guard")
    snapshot = preflight["process_snapshot"]
    if (
        not snapshot["passed"]
        or snapshot["competitors"]
        or snapshot["policy"] != PROCESS_POLICY
        or preflight["process_snapshot_sha256"] != json_sha256(snapshot)
    ):
        raise RuntimeError("preflight did not establish a checked process inventory")
    for arm, identity in design["arms"].items():
        for field in ("binary", "emitted", "main_assembly", "bril_main_assembly"):
            path = Path(identity[field])
            expected_hash = identity[f"{field}_sha256"]
            if sha256(path) != expected_hash:
                raise RuntimeError(f"{arm} {field} hash drift")
            if preflight["arms"][arm][f"{field}_sha256"] != expected_hash:
                raise RuntimeError(f"{arm} {field} preflight drift")
    return preflight


def checked_invocation(
    binary: Path,
    args: list[int],
    expected: bytes,
    timeout_s: int,
    events: TextIO,
    context: dict[str, Any],
) -> bytes:
    try:
        completed = subprocess.run(
            [str(binary), *map(str, args)],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_s,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        write_json_line(
            events,
            {
                "event": "invocation_failed",
                "failure": "timeout",
                **context,
                "stdout": (error.stdout or b"").decode(errors="replace"),
                "stderr": (error.stderr or b"").decode(errors="replace"),
                "machine_state": machine_state(),
            },
        )
        raise
    if completed.returncode != 0 or completed.stderr or completed.stdout != expected:
        write_json_line(
            events,
            {
                "event": "invocation_failed",
                "failure": (
                    "nonzero_exit" if completed.returncode != 0 else "stderr" if completed.stderr else "wrong_stdout"
                ),
                **context,
                "exit_code": completed.returncode,
                "stdout": completed.stdout.decode(errors="replace"),
                "stderr": completed.stderr.decode(errors="replace"),
                "machine_state": machine_state(),
            },
        )
        raise RuntimeError(f"failed invocation: {context}")
    return completed.stdout


def measured_batch(
    binary: Path,
    args: list[int],
    expected: bytes,
    timeout_s: int,
    invocation_count: int,
    events: TextIO,
    context: dict[str, Any],
) -> tuple[int, str]:
    command = [str(binary), *map(str, args)]
    completed_processes = []
    start_ns = time.perf_counter_ns()
    try:
        for _ in range(invocation_count):
            completed_processes.append(
                subprocess.run(
                    command,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=timeout_s,
                    check=False,
                )
            )
    except subprocess.TimeoutExpired as error:
        duration_ns = time.perf_counter_ns() - start_ns
        write_json_line(
            events,
            {
                "event": "invocation_failed",
                "failure": "timeout",
                **context,
                "invocation": len(completed_processes),
                "completed_processes_in_batch": len(completed_processes),
                "partial_batch_duration_ns": duration_ns,
                "stdout": (error.stdout or b"").decode(errors="replace"),
                "stderr": (error.stderr or b"").decode(errors="replace"),
                "machine_state": machine_state(),
            },
        )
        raise
    duration_ns = time.perf_counter_ns() - start_ns

    output_hash = hashlib.sha256()
    for invocation, completed in enumerate(completed_processes):
        if completed.returncode != 0 or completed.stderr or completed.stdout != expected:
            write_json_line(
                events,
                {
                    "event": "invocation_failed",
                    "failure": (
                        "nonzero_exit"
                        if completed.returncode != 0
                        else "stderr"
                        if completed.stderr
                        else "wrong_stdout"
                    ),
                    **context,
                    "invocation": invocation,
                    "completed_processes_in_batch": len(completed_processes),
                    "batch_duration_ns": duration_ns,
                    "exit_code": completed.returncode,
                    "stdout": completed.stdout.decode(errors="replace"),
                    "stderr": completed.stderr.decode(errors="replace"),
                    "machine_state": machine_state(),
                },
            )
            raise RuntimeError(f"failed measured invocation: {context}, {invocation}")
        output_hash.update(completed.stdout)
    return duration_ns, output_hash.hexdigest()


def summarize(rows: list[dict[str, Any]], design: dict[str, Any], session: int) -> dict[str, Any]:
    cycle_count = design["cycles"]
    block_cycles = design["joint_block_cycles"]
    block_count = design["joint_blocks_per_session"]
    workloads: dict[str, Any] = {}
    by_key: dict[tuple[str, int], dict[str, dict[str, Any]]] = {}
    for row in rows:
        by_key.setdefault((row["workload"], row["cycle"]), {})[row["arm"]] = row

    for workload in design["workloads"]:
        name = workload["name"]
        result: dict[str, Any] = {"arm_durations": {}}
        for arm in design["arms"]:
            durations = [by_key[(name, cycle)][arm]["duration_ns"] for cycle in range(cycle_count)]
            result["arm_durations"][arm] = {
                "median_ns": statistics.median(durations),
                "min_ns": min(durations),
                "max_ns": max(durations),
                "sample_sd_ns": statistics.stdev(durations),
            }

        for numerator, denominator in design["comparisons"]:
            label = f"{numerator}/{denominator}"
            details = []
            logs_by_block = [[] for _ in range(block_count)]
            for cycle in range(cycle_count):
                numerator_row = by_key[(name, cycle)][numerator]
                denominator_row = by_key[(name, cycle)][denominator]
                ratio = numerator_row["duration_ns"] / denominator_row["duration_ns"]
                log_ratio = math.log(ratio)
                block = cycle // block_cycles
                logs_by_block[block].append(log_ratio)
                details.append(
                    {
                        "cycle": cycle,
                        "joint_block": block,
                        "ratio": ratio,
                        "log_ratio": log_ratio,
                        "workload_position": numerator_row["workload_position"],
                        "numerator_position": numerator_row["arm_position"],
                        "denominator_position": denominator_row["arm_position"],
                    }
                )
            logs = [detail["log_ratio"] for detail in details]
            ratios = [detail["ratio"] for detail in details]
            strata: dict[str, list[float]] = {}
            for detail in details:
                key = (
                    f"w{detail['workload_position']}:n{detail['numerator_position']}:d{detail['denominator_position']}"
                )
                strata.setdefault(key, []).append(detail["log_ratio"])
            result[label] = {
                "point_estimate": math.exp(statistics.median(logs)),
                "bootstrap95": clustered_interval(logs_by_block, seed=20261019),
                "min_ratio": min(ratios),
                "max_ratio": max(ratios),
                "sample_sd_ratio": statistics.stdev(ratios),
                "sample_sd_log_ratio": statistics.stdev(logs),
                "all_below_one": all(ratio < 1.0 for ratio in ratios),
                "joint_block_estimates": [math.exp(statistics.median(block)) for block in logs_by_block],
                "first_half_estimate": math.exp(statistics.median(logs[: len(logs) // 2])),
                "second_half_estimate": math.exp(statistics.median(logs[len(logs) // 2 :])),
                "order_stratum_estimates": {
                    key: math.exp(statistics.median(values)) for key, values in sorted(strata.items())
                },
                "cycle_details": details,
            }
        result["speedup_gate_passed"] = all(
            result[label]["bootstrap95"][1] < 0.99 for label in design["per_session_speedup_comparisons"]
        )
        workloads[name] = result

    return {
        "session": session,
        "design_sha256": sha256(DESIGN),
        "preflight_sha256": sha256(PREFLIGHT),
        "raw_row_count": len(rows),
        "workloads": workloads,
        "all_workload_speedup_gates_passed": all(result["speedup_gate_passed"] for result in workloads.values()),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("session", type=int, choices=(1, 2))
    args = parser.parse_args()

    design = json.loads(DESIGN.read_text())
    if design["timed_samples_taken"]:
        raise RuntimeError("the prospective design unexpectedly reports samples")
    if os.environ.get("EGGLOG_BENCH_MEMORY_GUARD") is not None:
        raise RuntimeError("EGGLOG_BENCH_MEMORY_GUARD must be unset")
    preflight = validate_preflight(design)
    session_order = next(item for item in design["session_orders"] if item["session"] == args.session)
    if len(session_order["cycle_order"]) != design["cycles"]:
        raise RuntimeError("incomplete declared cycle order")

    output_dir = ROOT / "timing" / f"session-{args.session:02d}"
    lock_stream = LOCK.open("a+")
    try:
        fcntl.flock(lock_stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as error:
        raise RuntimeError("another Parts32 measurement session holds the lock") from error
    if output_dir.exists():
        raise RuntimeError(f"refusing to overwrite {output_dir}")
    output_dir.mkdir(parents=True)
    lock_stream.seek(0)
    lock_stream.truncate()
    lock_stream.write(
        json.dumps(
            {"pid": os.getpid(), "session": args.session, "wall_time_ns": time.time_ns()},
            sort_keys=True,
        )
        + "\n"
    )
    lock_stream.flush()
    os.fsync(lock_stream.fileno())

    binaries = {arm: Path(identity["binary"]) for arm, identity in design["arms"].items()}
    events_path = output_dir / "events.jsonl"
    warmups_path = output_dir / "warmups.jsonl"
    samples_path = output_dir / "samples.jsonl"
    process_checks_path = output_dir / "process-checks.jsonl"
    process_checks: list[dict[str, Any]] = []
    rows: list[dict[str, Any]] = []
    completed_invocations = 0
    with (
        events_path.open("a") as events,
        warmups_path.open("a") as warmups,
        samples_path.open("a") as samples,
        process_checks_path.open("a") as processes,
    ):
        start_state = machine_state()
        write_json_line(
            events,
            {
                "event": "session_started",
                "session": args.session,
                "design_sha256": sha256(DESIGN),
                "preflight_sha256": sha256(PREFLIGHT),
                "preflight": preflight,
                "machine_state": start_state,
            },
        )
        try:
            checked_process_snapshot(
                processes,
                events,
                process_checks,
                session=args.session,
                phase="session_start",
                completed_cycles=0,
                completed_invocations=0,
                persisted_raw_rows=0,
            )
            timeout_s = design["timeout_s_per_process"]
            for workload in design["workloads"]:
                expected = workload["expected_stdout"].encode()
                for arm in design["arms"]:
                    for warmup in range(design["warmups_per_arm_per_workload"]):
                        context = {
                            "session": args.session,
                            "phase": "warmup",
                            "workload": workload["name"],
                            "arm": arm,
                            "warmup": warmup,
                        }
                        stdout = checked_invocation(
                            binaries[arm], workload["args"], expected, timeout_s, events, context
                        )
                        completed_invocations += 1
                        write_json_line(
                            warmups,
                            {**context, "stdout_sha256": hashlib.sha256(stdout).hexdigest()},
                        )

            invocation_count = design["invocations_per_observation"]
            workloads = {item["name"]: item for item in design["workloads"]}
            for declared in session_order["cycle_order"]:
                cycle = declared["cycle"]
                for workload_position, workload_name in enumerate(declared["workload_order"]):
                    workload = workloads[workload_name]
                    expected = workload["expected_stdout"].encode()
                    for arm_position, arm in enumerate(declared["arm_order"]):
                        context = {
                            "session": args.session,
                            "phase": "measurement",
                            "cycle": cycle,
                            "joint_block": declared["joint_block"],
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
                            invocation_count,
                            events,
                            context,
                        )
                        completed_invocations += invocation_count
                        row = {
                            "session": args.session,
                            "cycle": cycle,
                            "joint_block": declared["joint_block"],
                            "workload": workload_name,
                            "workload_position": workload_position,
                            "arm": arm,
                            "arm_position": arm_position,
                            "args": workload["args"],
                            "expected_stdout": workload["expected_stdout"],
                            "invocations": invocation_count,
                            "duration_ns": duration_ns,
                            "mean_process_ns": duration_ns / invocation_count,
                            "output_sha256": output_sha256,
                        }
                        rows.append(row)
                        write_json_line(samples, row)
                if (cycle + 1) % design["joint_block_cycles"] == 0:
                    checked_process_snapshot(
                        processes,
                        events,
                        process_checks,
                        session=args.session,
                        phase="joint_block_boundary",
                        completed_cycles=cycle + 1,
                        completed_invocations=completed_invocations,
                        persisted_raw_rows=len(rows),
                    )

            summary = summarize(rows, design, args.session)
            checked_process_snapshot(
                processes,
                events,
                process_checks,
                session=args.session,
                phase="session_end",
                completed_cycles=design["cycles"],
                completed_invocations=completed_invocations,
                persisted_raw_rows=len(rows),
            )
            end_state = machine_state()
            summary.update(
                {
                    "start_state": start_state,
                    "end_state": end_state,
                    "raw_sha256": sha256(samples_path),
                    "events_sha256_before_completion": sha256(events_path),
                    "process_checks_sha256": sha256(process_checks_path),
                    "process_snapshot_sha256": [check["snapshot_sha256"] for check in process_checks],
                    "global_identity_sha256": {
                        key: preflight[key]
                        for key in (
                            "source_sha256",
                            "compiler_binary_sha256",
                            "compiler_source_snapshot_sha256",
                            "source_identities_sha256",
                        )
                    },
                    "warmups_sha256": sha256(warmups_path),
                    "warmup_count": sum(1 for _ in warmups_path.open()),
                    "completed_invocations": completed_invocations,
                    "all_outputs_exact": True,
                    "binary_sha256": {arm: identity["binary_sha256"] for arm, identity in design["arms"].items()},
                }
            )
            summary_path = output_dir / "summary.json"
            with summary_path.open("x") as summary_stream:
                summary_stream.write(json.dumps(summary, indent=2, sort_keys=True) + "\n")
                summary_stream.flush()
                os.fsync(summary_stream.fileno())
            write_json_line(
                events,
                {
                    "event": "session_completed",
                    "session": args.session,
                    "completed_invocations": completed_invocations,
                    "raw_rows": len(rows),
                    "summary_sha256": sha256(summary_path),
                    "process_checks_sha256": sha256(process_checks_path),
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
                    "persisted_raw_rows": len(rows),
                    "machine_state": machine_state(),
                },
            )
            raise
    fcntl.flock(lock_stream, fcntl.LOCK_UN)
    lock_stream.close()


if __name__ == "__main__":
    main()
