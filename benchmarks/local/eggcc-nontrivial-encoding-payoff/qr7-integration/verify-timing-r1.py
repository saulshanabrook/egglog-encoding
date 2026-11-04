#!/usr/bin/env python3
"""Independently verify frozen QR7 runtime sessions and acceptance gates."""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import random
import statistics
from typing import Any


ROOT = Path(__file__).resolve().parent
DESIGN = ROOT / "prospective-timing-design-r1.json"
PREFLIGHT = ROOT / "timing-preflight-r1.json"
COLLECTOR = ROOT / "timing-r1.py"
PREPARER = ROOT / "prepare-timing-r1.py"
FREEZER = ROOT / "freeze-timing-r1.py"
OUTPUT = ROOT / "timing-r1/independent-verification.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def percentile(values: list[float], probability: float) -> float:
    ordered = sorted(values)
    position = probability * (len(ordered) - 1)
    lower = int(position)
    upper = min(lower + 1, len(ordered) - 1)
    weight = position - lower
    return ordered[lower] * (1.0 - weight) + ordered[upper] * weight


def paired_result(
    by_cycle: dict[int, dict[str, dict[str, Any]]],
    numerator: str,
    denominator: str,
    block_cycles: int,
    draws: int,
    seed: int,
) -> dict[str, Any]:
    details = []
    logs_by_block: dict[int, list[float]] = {}
    for cycle in sorted(by_cycle):
        numerator_row = by_cycle[cycle][numerator]
        denominator_row = by_cycle[cycle][denominator]
        ratio = numerator_row["duration_ns"] / denominator_row["duration_ns"]
        log_ratio = math.log(ratio)
        block = cycle // block_cycles
        logs_by_block.setdefault(block, []).append(log_ratio)
        details.append((cycle, block, ratio, log_ratio))
    blocks = [logs_by_block[index] for index in sorted(logs_by_block)]
    label_seed = int.from_bytes(hashlib.sha256(f"{numerator}/{denominator}".encode()).digest()[:8], "big")
    rng = random.Random(seed ^ label_seed)
    estimates = []
    for _ in range(draws):
        sampled = [value for _ in blocks for value in blocks[rng.randrange(len(blocks))]]
        estimates.append(math.exp(statistics.median(sampled)))
    ratios = [item[2] for item in details]
    logs = [item[3] for item in details]
    return {
        "numerator": numerator,
        "denominator": denominator,
        "paired_cycle_count": len(details),
        "point_estimate": math.exp(statistics.median(logs)),
        "bootstrap95": [percentile(estimates, 0.025), percentile(estimates, 0.975)],
        "min_ratio": min(ratios),
        "max_ratio": max(ratios),
        "sample_sd_ratio": statistics.stdev(ratios) if len(ratios) > 1 else 0.0,
        "complete_block_estimates": [math.exp(statistics.median(block)) for block in blocks],
        "estimated_time_reduction_percent": 100.0 * (1.0 - math.exp(statistics.median(logs))),
    }


def verify_session(design: dict[str, Any], session_spec: dict[str, Any]) -> dict[str, Any]:
    name = session_spec["name"]
    folder = ROOT / "timing-r1" / name
    samples_path = folder / "samples.jsonl"
    warmups_path = folder / "warmups.jsonl"
    events_path = folder / "events.jsonl"
    snapshots_path = folder / "process-snapshots.jsonl"
    summary_path = folder / "summary.json"
    rows = [json.loads(line) for line in samples_path.read_text().splitlines()]
    warmups = [json.loads(line) for line in warmups_path.read_text().splitlines()]
    event_lines = events_path.read_text().splitlines(keepends=True)
    events = [json.loads(line) for line in event_lines]
    snapshots = [json.loads(line) for line in snapshots_path.read_text().splitlines()]
    summary = json.loads(summary_path.read_text())
    arms = list(design["arms"])
    workloads = {item["name"]: item for item in design["workloads"]}
    expected_rows = session_spec["cycles"] * len(arms) * len(workloads)
    assert len(rows) == expected_rows
    assert summary["raw_row_count"] == expected_rows
    assert summary["samples_sha256"] == sha256(samples_path)
    assert summary["warmups_sha256"] == sha256(warmups_path)
    assert summary["process_snapshots_sha256"] == sha256(snapshots_path)
    assert summary["design_sha256"] == sha256(DESIGN)
    assert summary["preflight_sha256"] == sha256(PREFLIGHT)
    assert summary["session"] == name
    assert summary["all_outputs_exact"] is True
    assert summary["all_outliers_retained"] is True
    assert summary["memory_pressure_was_not_an_admission_gate"] is True
    assert [event["event"] for event in events] == ["session_started", "session_completed"]
    assert summary["events_sha256_before_completion"] == hashlib.sha256("".join(event_lines[:-1]).encode()).hexdigest()
    assert events[-1]["summary_sha256"] == sha256(summary_path)

    expected_warmups = []
    for workload in design["workloads"]:
        expected_hash = hashlib.sha256(workload["expected_stdout"].encode()).hexdigest()
        for arm in arms:
            for warmup in range(design["warmups_per_arm_per_workload_per_session"]):
                expected_warmups.append(
                    {
                        "session": name,
                        "workload": workload["name"],
                        "arm": arm,
                        "warmup": warmup,
                        "stdout_sha256": expected_hash,
                    }
                )
    assert warmups == expected_warmups

    expected_sequence = []
    for cycle_spec in session_spec["cycle_order"]:
        for workload_position, workload in enumerate(cycle_spec["workload_order"]):
            for arm_position, arm in enumerate(cycle_spec["arm_order"]):
                expected_sequence.append(
                    (
                        cycle_spec["cycle"],
                        cycle_spec["complete_block"],
                        cycle_spec["williams_row"],
                        workload,
                        workload_position,
                        arm,
                        arm_position,
                    )
                )
    observed_sequence = [
        (
            row["cycle"],
            row["complete_block"],
            row["williams_row"],
            row["workload"],
            row["workload_position"],
            row["arm"],
            row["arm_position"],
        )
        for row in rows
    ]
    assert observed_sequence == expected_sequence

    by_workload: dict[str, dict[int, dict[str, dict[str, Any]]]] = {
        workload: {} for workload in workloads
    }
    for row in rows:
        workload = workloads[row["workload"]]
        assert row["session"] == name
        assert row["args"] == workload["args"]
        assert row["expected_stdout"] == workload["expected_stdout"]
        assert row["invocations"] == design["invocations_per_observation"]
        assert row["duration_ns"] > 0
        assert row["mean_process_ns"] == row["duration_ns"] / row["invocations"]
        expected_bytes = workload["expected_stdout"].encode() * row["invocations"]
        assert row["output_sha256"] == hashlib.sha256(expected_bytes).hexdigest()
        cycle = by_workload[row["workload"]].setdefault(row["cycle"], {})
        assert row["arm"] not in cycle
        cycle[row["arm"]] = row
    assert all(len(cycles) == session_spec["cycles"] for cycles in by_workload.values())
    assert all(set(arms_by_cycle) == set(arms) for cycles in by_workload.values() for arms_by_cycle in cycles.values())

    expected_snapshot_phases = ["session_start"] + ["complete_block_boundary"] * session_spec["complete_blocks"] + ["session_end"]
    assert [item["phase"] for item in snapshots] == expected_snapshot_phases
    assert all(item["snapshot"]["admission_gate"] is False for item in snapshots)
    assert all(item["snapshot"]["memory_or_process_pressure_never_discards_samples"] is True for item in snapshots)
    expected_invocations = len(warmups) + len(rows) * design["invocations_per_observation"]
    assert summary["completed_invocations"] == expected_invocations
    assert events[-1]["completed_invocations"] == expected_invocations

    comparisons = {(arm, "u0") for arm in arms}
    comparisons.update(tuple(pair) for pair in design["primary_hot_comparisons"])
    comparisons.add(("encoding", "manual"))
    for group in design["same_code_groups"].values():
        comparisons.update((arm, group["reference"]) for arm in group["arms"] if arm != group["reference"])
    workload_results = {}
    for workload_name, cycles in by_workload.items():
        arm_durations = {
            arm: [cycles[cycle][arm]["duration_ns"] for cycle in sorted(cycles)] for arm in arms
        }
        workload_results[workload_name] = {
            "arm_batch_ns": {
                arm: {
                    "median": statistics.median(values),
                    "min": min(values),
                    "max": max(values),
                    "sample_sd": statistics.stdev(values) if len(values) > 1 else 0.0,
                    "median_mean_process_ns": statistics.median(values) / design["invocations_per_observation"],
                }
                for arm, values in arm_durations.items()
            },
            "comparisons": {
                f"{numerator}/{denominator}": paired_result(
                    cycles,
                    numerator,
                    denominator,
                    len(arms),
                    design["bootstrap_draws"],
                    design["bootstrap_seed"],
                )
                for numerator, denominator in sorted(comparisons)
            },
        }
    return {
        "session": name,
        "cycles": session_spec["cycles"],
        "complete_blocks": session_spec["complete_blocks"],
        "raw_row_count": len(rows),
        "completed_invocations": expected_invocations,
        "samples_sha256": sha256(samples_path),
        "summary_sha256": sha256(summary_path),
        "start_wall_time_ns": summary["start_state"]["wall_time_ns"],
        "end_wall_time_ns": summary["end_state"]["wall_time_ns"],
        "workloads": workload_results,
    }


def main() -> None:
    if OUTPUT.exists():
        raise RuntimeError(f"refusing to overwrite {OUTPUT}")
    design = json.loads(DESIGN.read_text())
    preflight = json.loads(PREFLIGHT.read_text())
    assert preflight["design_sha256"] == sha256(DESIGN)
    assert preflight["collector_sha256"] == sha256(COLLECTOR)
    assert preflight["preparer_sha256"] == sha256(PREPARER)
    assert preflight["verifier_sha256"] == sha256(Path(__file__))
    assert preflight["freezer_sha256"] == sha256(FREEZER)
    assert preflight["all_identity_and_order_checks_passed"] is True
    assert preflight["memory_guard_unset"] is True
    assert preflight["memory_pressure_is_not_an_admission_gate"] is True
    sessions = {
        spec["name"]: verify_session(design, spec) for spec in design["sessions"]
    }
    assert sessions["screen"]["end_wall_time_ns"] < sessions["confirmation"]["start_wall_time_ns"]

    screen_hot = sessions["screen"]["workloads"]["hot-equal-key"]["comparisons"]
    confirmation_hot = sessions["confirmation"]["workloads"]["hot-equal-key"]["comparisons"]
    primary_labels = [f"{numerator}/{denominator}" for numerator, denominator in design["primary_hot_comparisons"]]
    screen_gate = all(screen_hot[label]["point_estimate"] < 0.99 for label in primary_labels)
    confirmation_gate = all(confirmation_hot[label]["bootstrap95"][1] < 0.99 for label in primary_labels)

    same_code = {}
    for group_name, group in design["same_code_groups"].items():
        reference = group["reference"]
        rows = {}
        for arm in group["arms"]:
            if arm == reference:
                ratio = 1.0
            else:
                ratio = confirmation_hot[f"{arm}/{reference}"]["point_estimate"]
            rows[arm] = ratio
        same_code[group_name] = {
            "reference": reference,
            "paired_point_ratio_to_reference": rows,
            "all_within_two_percent": all(0.98 <= ratio <= 1.02 for ratio in rows.values()),
        }
    same_code_gate = all(group["all_within_two_percent"] for group in same_code.values())

    result = {
        "schema_version": 1,
        "status": "passed" if screen_gate and confirmation_gate and same_code_gate else "failed",
        "design": str(DESIGN),
        "design_sha256": sha256(DESIGN),
        "preflight": str(PREFLIGHT),
        "preflight_sha256": sha256(PREFLIGHT),
        "collector_sha256": sha256(COLLECTOR),
        "verifier_sha256": sha256(Path(__file__)),
        "sessions": sessions,
        "primary_hot_comparisons": primary_labels,
        "gates": {
            "all_outputs_exact_and_all_rows_retained": True,
            "screen_primary_point_estimates_below_0_99": screen_gate,
            "independent_confirmation_primary_bootstrap95_upper_below_0_99": confirmation_gate,
            "confirmation_same_code_groups_within_two_percent": same_code_gate,
            "memory_pressure_never_blocked_or_discarded_samples": True,
            "neutral_workload_reported_without_speedup_requirement": True,
            "overall_speedup_acceptance": screen_gate and confirmation_gate and same_code_gate,
        },
        "same_code_checks": same_code,
        "claim_boundary": {
            "supported": "generated-program fresh-process runtime for the fixed QR7 workload",
            "excluded": ["compiler time", "proof support", "disequality contribution", "raytracing"],
            "transport_off": design["transport_off_interpretation"],
        },
    }
    OUTPUT.parent.mkdir(exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": result["status"], "gates": result["gates"], "primary_confirmation": {label: confirmation_hot[label] for label in primary_labels}}, indent=2, sort_keys=True))
    if result["status"] != "passed":
        raise RuntimeError("QR7 timing acceptance failed; evidence retained")


if __name__ == "__main__":
    main()
