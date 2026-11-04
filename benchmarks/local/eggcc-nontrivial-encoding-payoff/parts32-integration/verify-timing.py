#!/usr/bin/env python3
"""Independently recompute the frozen Parts32 timing result."""

from __future__ import annotations

import hashlib
import json
import math
import os
import random
import statistics
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
DESIGN = ROOT / "prospective-timing-design-frozen.json"
PREFLIGHT = ROOT / "timing-preflight.json"
PRODUCER = ROOT / "timing.py"
PREPARER = ROOT / "prepare-timing.py"
SOURCE_IDENTITIES = ROOT / "final-source-identities.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_process_snapshot(snapshot: dict[str, Any], expected_script: Path, session: int | None = None) -> str:
    """Recheck admission independently, without importing producer code."""
    assert set(snapshot) == {
        "schema_version",
        "command",
        "policy",
        "self",
        "inventory_pid",
        "exit_code",
        "inventory_error",
        "processes",
        "competitors",
        "passed",
        "monotonic_ns",
        "wall_time_ns",
    }
    assert snapshot["schema_version"] == 1
    assert snapshot["command"] == ["ps", "-axo", "pid=,ppid=,%cpu=,%mem=,comm="]
    # Reconstruct prospective policy v2 independently: known jobs always block;
    # >=75% per process catches unknown near-full-core jobs, not aggregate load.
    policy = {
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
    assert snapshot["policy"] == policy
    assert snapshot["exit_code"] == 0
    assert snapshot["inventory_error"] is None
    assert snapshot["passed"] is True
    owner = snapshot["self"]
    assert set(owner) == {"pid", "ppid", "cwd", "argv", "executable"}
    assert Path(owner["cwd"]).is_absolute()
    assert Path(owner["executable"]).is_absolute()
    assert len(owner["argv"]) == (1 if session is None else 2)
    assert (Path(owner["cwd"]) / owner["argv"][0]).resolve() == expected_script.resolve()
    if session is not None:
        assert owner["argv"][1] == str(session)
    assert snapshot["inventory_pid"] > 0
    assert snapshot["inventory_pid"] != owner["pid"]
    pids = []
    competitors = []
    for process in snapshot["processes"]:
        assert set(process) == {"pid", "ppid", "cpu_percent", "memory_percent", "comm"}
        assert isinstance(process["pid"], int) and process["pid"] >= 0
        assert isinstance(process["ppid"], int) and process["ppid"] >= 0
        assert process["comm"] and all(char.isprintable() for char in process["comm"])
        for field in ("cpu_percent", "memory_percent"):
            assert math.isfinite(process[field]) and process[field] >= 0
        pids.append(process["pid"])
        if process["pid"] in (owner["pid"], snapshot["inventory_pid"]):
            continue
        name = Path(process["comm"]).name
        reasons = []
        if name in policy["known_job_names"] or name.startswith(tuple(policy["known_job_prefixes"])):
            reasons.append("known_compiler_or_benchmark")
        if process["cpu_percent"] >= policy["material_cpu_percent"]:
            reasons.append("material_cpu")
        if reasons:
            competitors.append({**process, "reasons": reasons})
    assert len(pids) == len(set(pids))
    assert owner["pid"] in pids and snapshot["inventory_pid"] in pids
    own_process = next(item for item in snapshot["processes"] if item["pid"] == owner["pid"])
    assert own_process["ppid"] == owner["ppid"]
    assert snapshot["competitors"] == competitors == []
    return hashlib.sha256(json.dumps(snapshot, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def verify_global_identities(design: dict[str, Any], preflight: dict[str, Any]) -> dict[str, str]:
    identities = {"source_identities_sha256": sha256(SOURCE_IDENTITIES)}
    assert preflight["source_identities"] == str(SOURCE_IDENTITIES)
    assert preflight["preparer"] == str(PREPARER)
    assert preflight["preparer_sha256"] == sha256(PREPARER)
    for field in ("source", "compiler_binary", "compiler_source_snapshot"):
        actual = sha256(Path(design[field]))
        assert actual == design[f"{field}_sha256"]
        identities[f"{field}_sha256"] = actual
    for key, value in identities.items():
        assert preflight[key] == value
    source_identities = json.loads(SOURCE_IDENTITIES.read_text())
    assert source_identities["source_frozen"] is True
    assert source_identities["source_archive"] == design["compiler_source_snapshot"]
    assert source_identities["source_archive_sha256"] == identities["compiler_source_snapshot_sha256"]
    compiler_identity = next(item for item in source_identities["files"] if item["path"] == design["compiler_binary"])
    assert compiler_identity["sha256"] == identities["compiler_binary_sha256"]
    assert preflight["process_snapshot_sha256"] == verify_process_snapshot(preflight["process_snapshot"], PREPARER)
    for arm, identity in design["arms"].items():
        for field in ("binary", "emitted", "main_assembly", "bril_main_assembly"):
            assert preflight["arms"][arm][field] == identity[field]
            assert preflight["arms"][arm][f"{field}_sha256"] == identity[f"{field}_sha256"]
    return identities


def quantile(values: list[float], probability: float) -> float:
    ordered = sorted(values)
    position = probability * (len(ordered) - 1)
    before = int(position)
    after = min(before + 1, len(ordered) - 1)
    fraction = position - before
    return ordered[before] + fraction * (ordered[after] - ordered[before])


def resample_blocks(log_blocks: list[list[float]], seed: int) -> list[float]:
    rng = random.Random(seed)
    estimates = []
    for _ in range(10_000):
        selected = [log_blocks[rng.randrange(len(log_blocks))] for _ in log_blocks]
        estimates.append(math.exp(statistics.median([value for block in selected for value in block])))
    return [quantile(estimates, 0.025), quantile(estimates, 0.975)]


def assert_same(actual: Any, expected: Any) -> None:
    if isinstance(actual, float) or isinstance(expected, float):
        assert math.isclose(float(actual), float(expected), rel_tol=1e-15, abs_tol=1e-15)
    elif isinstance(actual, dict):
        assert set(actual).issubset(expected)
        for key, value in actual.items():
            assert_same(value, expected[key])
    elif isinstance(actual, list):
        assert len(actual) == len(expected)
        for left, right in zip(actual, expected, strict=True):
            assert_same(left, right)
    else:
        assert actual == expected


def verify_session(design: dict[str, Any], session: int) -> dict[str, Any]:
    directory = ROOT / "timing" / f"session-{session:02d}"
    sample_path = directory / "samples.jsonl"
    warmups_path = directory / "warmups.jsonl"
    events_path = directory / "events.jsonl"
    summary_path = directory / "summary.json"
    process_checks_path = directory / "process-checks.jsonl"
    rows = [json.loads(line) for line in sample_path.read_text().splitlines()]
    warmups = [json.loads(line) for line in warmups_path.read_text().splitlines()]
    event_lines = events_path.read_text().splitlines(keepends=True)
    events = [json.loads(line) for line in event_lines]
    process_checks = [json.loads(line) for line in process_checks_path.read_text().splitlines()]
    recorded = json.loads(summary_path.read_text())
    declared = next(item for item in design["session_orders"] if item["session"] == session)

    arms = list(design["arms"])
    workloads = {item["name"]: item for item in design["workloads"]}
    cycles = design["cycles"]
    expected_rows = len(arms) * len(workloads) * cycles
    assert len(rows) == expected_rows
    assert recorded["raw_row_count"] == expected_rows
    assert recorded["raw_sha256"] == sha256(sample_path)
    assert recorded["design_sha256"] == sha256(DESIGN)
    assert recorded["preflight_sha256"] == sha256(PREFLIGHT)
    assert recorded["session"] == session
    assert recorded["all_outputs_exact"] is True
    assert recorded["global_identity_sha256"] == verify_global_identities(design, json.loads(PREFLIGHT.read_text()))
    assert len(warmups) == (len(arms) * len(workloads) * design["warmups_per_arm_per_workload"])
    assert [event["event"] for event in events] == [
        "session_started",
        *["process_snapshot_checked"] * (design["joint_blocks_per_session"] + 2),
        "session_completed",
    ]
    assert events[0]["session"] == session
    assert events[0]["design_sha256"] == sha256(DESIGN)
    assert events[0]["preflight_sha256"] == sha256(PREFLIGHT)
    assert events[0]["preflight"] == json.loads(PREFLIGHT.read_text())
    assert events[0]["machine_state"] == recorded["start_state"]
    completion = events[-1]
    assert completion["session"] == session
    assert completion["raw_rows"] == expected_rows
    assert completion["summary_sha256"] == sha256(summary_path)
    assert completion["machine_state"] == recorded["end_state"]
    expected_completed_invocations = len(warmups) + expected_rows * design["invocations_per_observation"]
    assert completion["completed_invocations"] == expected_completed_invocations
    assert recorded["completed_invocations"] == expected_completed_invocations
    assert recorded["events_sha256_before_completion"] == hashlib.sha256("".join(event_lines[:-1]).encode()).hexdigest()
    assert recorded["warmups_sha256"] == sha256(warmups_path)
    assert recorded["warmup_count"] == len(warmups)
    assert set(recorded["end_state"]) == set(recorded["start_state"])
    assert recorded["process_checks_sha256"] == sha256(process_checks_path)
    assert completion["process_checks_sha256"] == sha256(process_checks_path)
    checkpoints = [
        ("session_start", 0),
        *[
            ("joint_block_boundary", cycle)
            for cycle in range(design["joint_block_cycles"], cycles + 1, design["joint_block_cycles"])
        ],
        ("session_end", cycles),
    ]
    assert len(process_checks) == len(checkpoints)
    snapshot_hashes = []
    previous_monotonic = recorded["start_state"]["monotonic_ns"]
    for index, (check, checkpoint) in enumerate(zip(process_checks, checkpoints, strict=True)):
        phase, completed_cycles = checkpoint
        completed_rows = completed_cycles * len(arms) * len(workloads)
        expected_context = {
            "checkpoint_index": index,
            "session": session,
            "phase": phase,
            "completed_cycles": completed_cycles,
            "completed_invocations": (
                0 if phase == "session_start" else len(warmups) + completed_rows * design["invocations_per_observation"]
            ),
            "persisted_raw_rows": completed_rows,
        }
        assert all(check[key] == value for key, value in expected_context.items())
        snapshot = check["snapshot"]
        digest = verify_process_snapshot(snapshot, PRODUCER, session)
        assert check["snapshot_sha256"] == digest
        snapshot_hashes.append(digest)
        assert snapshot["self"]["pid"] == recorded["start_state"]["pid"]
        assert snapshot["self"] == process_checks[0]["snapshot"]["self"]
        assert previous_monotonic <= snapshot["monotonic_ns"] <= recorded["end_state"]["monotonic_ns"]
        previous_monotonic = snapshot["monotonic_ns"]
        assert events[index + 1] == {
            "event": "process_snapshot_checked",
            **expected_context,
            "snapshot_sha256": digest,
            "process_check_sha256": hashlib.sha256(
                json.dumps(check, sort_keys=True, separators=(",", ":")).encode()
            ).hexdigest(),
        }
    assert recorded["process_snapshot_sha256"] == snapshot_hashes

    expected_warmups = []
    for workload in design["workloads"]:
        expected_output_hash = hashlib.sha256(workload["expected_stdout"].encode()).hexdigest()
        for arm in arms:
            for warmup in range(design["warmups_per_arm_per_workload"]):
                expected_warmups.append(
                    {
                        "session": session,
                        "phase": "warmup",
                        "workload": workload["name"],
                        "arm": arm,
                        "warmup": warmup,
                        "stdout_sha256": expected_output_hash,
                    }
                )
    assert warmups == expected_warmups

    expected_sequence = []
    for cycle in declared["cycle_order"]:
        assert cycle["joint_block"] == cycle["cycle"] // design["joint_block_cycles"]
        for workload_position, workload in enumerate(cycle["workload_order"]):
            for arm_position, arm in enumerate(cycle["arm_order"]):
                expected_sequence.append(
                    (
                        cycle["cycle"],
                        cycle["joint_block"],
                        workload,
                        workload_position,
                        arm,
                        arm_position,
                    )
                )
    observed_sequence = [
        (
            row["cycle"],
            row["joint_block"],
            row["workload"],
            row["workload_position"],
            row["arm"],
            row["arm_position"],
        )
        for row in rows
    ]
    assert observed_sequence == expected_sequence

    by_key: dict[tuple[str, int], dict[str, dict[str, Any]]] = {}
    for row in rows:
        assert row["session"] == session
        workload = workloads[row["workload"]]
        assert row["args"] == workload["args"]
        assert row["expected_stdout"] == workload["expected_stdout"]
        assert row["invocations"] == design["invocations_per_observation"]
        assert row["duration_ns"] > 0
        assert row["mean_process_ns"] == row["duration_ns"] / row["invocations"]
        expected_bytes = workload["expected_stdout"].encode() * row["invocations"]
        assert row["output_sha256"] == hashlib.sha256(expected_bytes).hexdigest()
        key = (row["workload"], row["cycle"])
        assert row["arm"] not in by_key.setdefault(key, {})
        by_key[key][row["arm"]] = row

    results: dict[str, Any] = {}
    for name in workloads:
        results[name] = {"arm_durations": {}}
        for arm in arms:
            durations = [by_key[(name, cycle)][arm]["duration_ns"] for cycle in range(cycles)]
            computed_arm = {
                "median_ns": statistics.median(durations),
                "min_ns": min(durations),
                "max_ns": max(durations),
                "sample_sd_ns": statistics.stdev(durations),
            }
            assert_same(computed_arm, recorded["workloads"][name]["arm_durations"][arm])
            results[name]["arm_durations"][arm] = computed_arm
        for numerator, denominator in design["comparisons"]:
            label = f"{numerator}/{denominator}"
            logs = []
            ratios = []
            blocks = [[] for _ in range(design["joint_blocks_per_session"])]
            details = []
            strata: dict[str, list[float]] = {}
            for cycle in range(cycles):
                numerator_row = by_key[(name, cycle)][numerator]
                denominator_row = by_key[(name, cycle)][denominator]
                ratio = numerator_row["duration_ns"] / denominator_row["duration_ns"]
                log_ratio = math.log(ratio)
                ratios.append(ratio)
                logs.append(log_ratio)
                joint_block = cycle // design["joint_block_cycles"]
                blocks[joint_block].append(log_ratio)
                detail = {
                    "cycle": cycle,
                    "joint_block": joint_block,
                    "ratio": ratio,
                    "log_ratio": log_ratio,
                    "workload_position": numerator_row["workload_position"],
                    "numerator_position": numerator_row["arm_position"],
                    "denominator_position": denominator_row["arm_position"],
                }
                details.append(detail)
                stratum = (
                    f"w{detail['workload_position']}:n{detail['numerator_position']}:d{detail['denominator_position']}"
                )
                strata.setdefault(stratum, []).append(log_ratio)
            computed = {
                "point_estimate": math.exp(statistics.median(logs)),
                "bootstrap95": resample_blocks(blocks, 20261019),
                "min_ratio": min(ratios),
                "max_ratio": max(ratios),
                "sample_sd_ratio": statistics.stdev(ratios),
                "sample_sd_log_ratio": statistics.stdev(logs),
                "all_below_one": all(ratio < 1.0 for ratio in ratios),
                "joint_block_estimates": [math.exp(statistics.median(block)) for block in blocks],
                "first_half_estimate": math.exp(statistics.median(logs[: len(logs) // 2])),
                "second_half_estimate": math.exp(statistics.median(logs[len(logs) // 2 :])),
                "order_stratum_estimates": {
                    key: math.exp(statistics.median(values)) for key, values in sorted(strata.items())
                },
                "cycle_details": details,
            }
            retained = recorded["workloads"][name][label]
            assert_same(computed, retained)
            results[name][label] = computed
        gate = all(results[name][label]["bootstrap95"][1] < 0.99 for label in design["per_session_speedup_comparisons"])
        assert gate == recorded["workloads"][name]["speedup_gate_passed"]
        results[name]["speedup_gate_passed"] = gate

    for arm, identity in design["arms"].items():
        for field in ("binary", "emitted", "main_assembly", "bril_main_assembly"):
            assert sha256(Path(identity[field])) == identity[f"{field}_sha256"]
        assert recorded["binary_sha256"][arm] == identity["binary_sha256"]
    assert recorded["all_workload_speedup_gates_passed"] == all(
        result["speedup_gate_passed"] for result in results.values()
    )
    return {
        "session": session,
        "samples_sha256": sha256(sample_path),
        "summary_sha256": sha256(summary_path),
        "events_sha256": sha256(events_path),
        "process_checks_sha256": sha256(process_checks_path),
        "process_snapshot_sha256": snapshot_hashes,
        "results": results,
        "all_workload_speedup_gates_passed": recorded["all_workload_speedup_gates_passed"],
    }


def main() -> None:
    if not __debug__:
        raise RuntimeError("optimized Python disables required verifier assertions")
    design = json.loads(DESIGN.read_text())
    preflight = json.loads(PREFLIGHT.read_text())
    assert preflight["design_sha256"] == sha256(DESIGN)
    assert preflight["timing_sha256"] == sha256(PRODUCER)
    assert preflight["verifier_sha256"] == sha256(Path(__file__))
    global_identities = verify_global_identities(design, preflight)
    assert set(design["arms"]) == {"U0", "B1", "SeedOnly", "Manual", "Encoding"}
    assert design["independent_sessions"] == 2
    assert design["timed_samples_taken"] is False
    baseline_hashes = {
        tuple(design["arms"][arm][field + "_sha256"] for field in ("emitted", "main_assembly", "bril_main_assembly"))
        for arm in ("U0", "B1", "SeedOnly")
    }
    winning_hashes = {
        tuple(design["arms"][arm][field + "_sha256"] for field in ("emitted", "main_assembly", "bril_main_assembly"))
        for arm in ("Manual", "Encoding")
    }
    assert len(baseline_hashes) == 1
    assert len(winning_hashes) == 1
    verified = [verify_session(design, session) for session in (1, 2)]
    consistent_placebo_shifts = []
    threshold = design["consistent_placebo_shift_threshold"]
    for workload in (item["name"] for item in design["workloads"]):
        for label in design["placebo_validity_comparisons"]:
            estimates = [session["results"][workload][label]["point_estimate"] for session in verified]
            if all(value < 1.0 - threshold for value in estimates) or all(
                value > 1.0 + threshold for value in estimates
            ):
                consistent_placebo_shifts.append({"workload": workload, "comparison": label, "estimates": estimates})
    speedup_gates_passed = all(session["all_workload_speedup_gates_passed"] for session in verified)
    result = {
        "verifier_sha256": sha256(Path(__file__)),
        "producer_sha256": sha256(PRODUCER),
        "design_sha256": sha256(DESIGN),
        "preflight_sha256": sha256(PREFLIGHT),
        "global_identity_sha256": global_identities,
        "preflight_process_snapshot_sha256": preflight["process_snapshot_sha256"],
        "sessions": verified,
        "all_session_speedup_gates_passed": speedup_gates_passed,
        "consistent_placebo_shifts": consistent_placebo_shifts,
        "placebo_validity_passed": not consistent_placebo_shifts,
        "all_sessions_passed": speedup_gates_passed and not consistent_placebo_shifts,
        "code_identity_groups_verified": True,
        "no_failed_or_partial_session": True,
    }
    destination = ROOT / "timing" / "independent-verification.json"
    with destination.open("x") as stream:
        stream.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        stream.flush()
        os.fsync(stream.fileno())
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
