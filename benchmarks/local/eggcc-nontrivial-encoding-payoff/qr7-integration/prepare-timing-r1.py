#!/usr/bin/env python3
"""Verify and bind the prospective QR7 timing cohort before sampling."""

from __future__ import annotations

from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import time
from typing import Any


ROOT = Path(__file__).resolve().parent
DESIGN = ROOT / "prospective-timing-design-r1.json"
PREFLIGHT = ROOT / "timing-preflight-r1.json"
COLLECTOR = ROOT / "timing-r1.py"
VERIFIER = ROOT / "verify-timing-r1.py"
FREEZER = ROOT / "freeze-timing-r1.py"
SOURCE_FREEZER = ROOT / "freeze-source-r1.py"
BINARY_INSPECTOR = ROOT / "inspect-binaries.py"
SOURCE_IDENTITIES = ROOT / "source-identities-r1.json"
BINARY_INSPECTION = ROOT / "actual-binary-inspection-r1.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_orders(design: dict[str, Any]) -> dict[str, Any]:
    arms = list(design["arms"])
    expected_pairs = {(left, right) for left in arms for right in arms if left != right}
    workloads = {item["name"] for item in design["workloads"]}
    result = {}
    for session in design["sessions"]:
        assert len(session["cycle_order"]) == session["cycles"]
        assert session["cycles"] == session["complete_blocks"] * len(arms)
        blocks = []
        for block in range(session["complete_blocks"]):
            rows = [item for item in session["cycle_order"] if item["complete_block"] == block]
            assert len(rows) == len(arms)
            assert {item["williams_row"] for item in rows} == set(range(len(arms)))
            positions = Counter()
            predecessors = Counter()
            workload_positions = Counter()
            for item in rows:
                assert set(item["arm_order"]) == set(arms)
                assert set(item["workload_order"]) == workloads
                for position, arm in enumerate(item["arm_order"]):
                    positions[(arm, position)] += 1
                predecessors.update(zip(item["arm_order"], item["arm_order"][1:]))
                for position, workload in enumerate(item["workload_order"]):
                    workload_positions[(workload, position)] += 1
            assert set(positions.values()) == {1}
            assert set(predecessors) == expected_pairs
            assert set(predecessors.values()) == {1}
            assert set(workload_positions.values()) == {len(arms) // len(workloads)}
            blocks.append(
                {
                    "block": block,
                    "arm_position_count": 1,
                    "directed_predecessor_pair_count": 1,
                    "workload_position_count": len(arms) // len(workloads),
                }
            )
        result[session["name"]] = blocks
    return result


def main() -> None:
    if PREFLIGHT.exists():
        raise RuntimeError(f"refusing to overwrite {PREFLIGHT}")
    timing_root = ROOT / "timing-r1"
    if timing_root.exists() and any(timing_root.iterdir()):
        raise RuntimeError("QR7 timing artifacts already exist")
    if os.environ.get("EGGLOG_BENCH_MEMORY_GUARD") is not None:
        raise RuntimeError("EGGLOG_BENCH_MEMORY_GUARD must be absent, not empty")

    design = json.loads(DESIGN.read_text())
    source_identities = json.loads(SOURCE_IDENTITIES.read_text())
    inspection = json.loads(BINARY_INSPECTION.read_text())
    assert design["schema_version"] == 1 and design["revision"] == 1
    assert design["timed_samples_taken"] is False
    assert design["raytracing"] == "excluded"
    assert source_identities["timing_samples_taken"] is False
    assert source_identities["binary_identity_equal"] is True
    assert inspection["status"] == "passed" and inspection["performance_samples_taken"] is False
    assert design["source_identities_sha256"] == sha256(SOURCE_IDENTITIES)
    assert design["binary_inspection_sha256"] == sha256(BINARY_INSPECTION)
    for field in ("source", "compiler_source_archive", "compiler_delta_patch", "compiler_binary", "tiger_binary"):
        assert sha256(Path(design[field])) == design[field + "_sha256"]

    arms = {}
    for arm, identity in design["arms"].items():
        files = {}
        for field in ("binary", "emitted", "assembly"):
            path = Path(identity[field])
            assert sha256(path) == identity[field + "_sha256"]
            files[field] = str(path)
            files[field + "_sha256"] = identity[field + "_sha256"]
        actual = inspection["modes"][arm]["functions"]["process_main"]
        assert identity["process_main_instruction_sha256"] == actual["instruction_sha256"]
        assert identity["process_main_instruction_count"] == actual["instruction_count"]
        assert identity["process_main_backward_branches"] == len(actual["internal_backward_branches"])
        arms[arm] = files

    for group in design["same_code_groups"].values():
        assert {
            design["arms"][arm]["process_main_instruction_sha256"] for arm in group["arms"]
        } == {group["process_main_instruction_sha256"]}

    order_checks = verify_orders(design)
    ps = subprocess.run(
        ["/bin/ps", "-axo", "pid=,ppid=,%cpu=,%mem=,comm="],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=30,
        check=False,
    )
    result = {
        "schema_version": 1,
        "created_wall_time_ns": time.time_ns(),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "python": platform.python_version(),
        "design": str(DESIGN),
        "design_sha256": sha256(DESIGN),
        "collector": str(COLLECTOR),
        "collector_sha256": sha256(COLLECTOR),
        "verifier": str(VERIFIER),
        "verifier_sha256": sha256(VERIFIER),
        "preparer": str(Path(__file__)),
        "preparer_sha256": sha256(Path(__file__)),
        "freezer": str(FREEZER),
        "freezer_sha256": sha256(FREEZER),
        "source_freezer_sha256": sha256(SOURCE_FREEZER),
        "binary_inspector_sha256": sha256(BINARY_INSPECTOR),
        "source_identities_sha256": sha256(SOURCE_IDENTITIES),
        "binary_inspection_sha256": sha256(BINARY_INSPECTION),
        "arms": arms,
        "order_checks": order_checks,
        "memory_guard_unset": True,
        "memory_pressure_is_not_an_admission_gate": True,
        "raytracing_excluded": True,
        "process_inventory": {
            "command": ["/bin/ps", "-axo", "pid=,ppid=,%cpu=,%mem=,comm="],
            "exit_code": ps.returncode,
            "stdout_sha256": hashlib.sha256(ps.stdout).hexdigest(),
            "stderr": ps.stderr.decode(errors="replace"),
            "descriptive_only": True,
        },
        "timing_outputs_absent": True,
        "all_identity_and_order_checks_passed": True,
    }
    PREFLIGHT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"preflight": str(PREFLIGHT), "sha256": sha256(PREFLIGHT), "checks_passed": True}, indent=2))


if __name__ == "__main__":
    main()
