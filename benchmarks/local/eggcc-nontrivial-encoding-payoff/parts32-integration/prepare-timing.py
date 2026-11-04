#!/usr/bin/env python3
"""Freeze and verify the Parts32 timing cohort before sampling."""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import platform
import time
from collections import Counter
from pathlib import Path
from typing import Any

from timing import capture_process_snapshot, json_sha256

ROOT = Path(__file__).resolve().parent
DESIGN = ROOT / "prospective-timing-design-frozen.json"
PRODUCER = ROOT / "timing.py"
VERIFIER = ROOT / "verify-timing.py"
PREFLIGHT = ROOT / "timing-preflight.json"
LOCK = ROOT / "timing-measurement.lock"
SOURCE_IDENTITIES = ROOT / "final-source-identities.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_order(design: dict[str, Any]) -> dict[str, Any]:
    arm_names = set(design["arms"])
    workload_names = {item["name"] for item in design["workloads"]}
    checks = {}
    for session in design["session_orders"]:
        positions = Counter()
        predecessors = Counter()
        workload_positions = Counter()
        for declared in session["cycle_order"]:
            assert declared["cycle"] // design["joint_block_cycles"] == declared["joint_block"]
            assert set(declared["arm_order"]) == arm_names
            assert set(declared["workload_order"]) == workload_names
            for position, arm in enumerate(declared["arm_order"]):
                positions[(arm, position)] += 1
            predecessors.update(zip(declared["arm_order"], declared["arm_order"][1:]))
            for position, workload in enumerate(declared["workload_order"]):
                workload_positions[(workload, position)] += 1
        assert len(session["cycle_order"]) == design["cycles"]
        assert set(positions.values()) == {18}
        assert len(predecessors) == 20 and set(predecessors.values()) == {18}
        assert set(workload_positions.values()) == {30}
        checks[str(session["session"])] = {
            "arm_position_count": 18,
            "directed_predecessor_pair_count": 18,
            "workload_position_count": 30,
        }
    return checks


def main() -> None:
    if not __debug__:
        raise RuntimeError("optimized Python disables required preflight assertions")
    if PREFLIGHT.exists():
        raise RuntimeError(f"refusing to overwrite {PREFLIGHT}")
    timing_root = ROOT / "timing"
    if timing_root.exists() and any(timing_root.iterdir()):
        raise RuntimeError("timing artifacts already exist")
    design = json.loads(DESIGN.read_text())
    assert design["revision"] == 5
    assert design["timed_samples_taken"] is False
    assert design["cycles"] == 90
    assert design["joint_block_cycles"] == 15
    assert design["joint_blocks_per_session"] == 6
    assert os.environ.get("EGGLOG_BENCH_MEMORY_GUARD") is None

    lock_stream = LOCK.open("a+")
    try:
        fcntl.flock(lock_stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as error:
        raise RuntimeError("the Parts32 timing lock is held") from error
    process_snapshot = capture_process_snapshot()
    if not process_snapshot["passed"]:
        rejection = ROOT / f"timing-preflight-rejected-{time.time_ns()}.json"
        with rejection.open("x") as stream:
            stream.write(
                json.dumps(
                    {
                        "process_snapshot": process_snapshot,
                        "process_snapshot_sha256": json_sha256(process_snapshot),
                    },
                    indent=2,
                    sort_keys=True,
                )
                + "\n"
            )
            stream.flush()
            os.fsync(stream.fileno())
        raise RuntimeError(f"process admission failed; retained full inventory in {rejection}")

    arms = {}
    for arm, identity in design["arms"].items():
        files = {}
        for field in ("binary", "emitted", "main_assembly", "bril_main_assembly"):
            path = Path(identity[field])
            actual = sha256(path)
            assert actual == identity[f"{field}_sha256"]
            files[field] = str(path)
            files[f"{field}_sha256"] = actual
        arms[arm] = files

    baseline = {
        tuple(arms[arm][field + "_sha256"] for field in ("emitted", "main_assembly", "bril_main_assembly"))
        for arm in ("U0", "B1", "SeedOnly")
    }
    winning = {
        tuple(arms[arm][field + "_sha256"] for field in ("emitted", "main_assembly", "bril_main_assembly"))
        for arm in ("Manual", "Encoding")
    }
    assert len(baseline) == 1 and len(winning) == 1
    source = Path(design["source"])
    compiler = Path(design["compiler_binary"])
    archive = Path(design["compiler_source_snapshot"])
    assert sha256(source) == design["source_sha256"]
    assert sha256(compiler) == design["compiler_binary_sha256"]
    assert sha256(archive) == design["compiler_source_snapshot_sha256"]

    result = {
        "schema_version": 1,
        "created_wall_time_ns": time.time_ns(),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "python": platform.python_version(),
        "design": str(DESIGN),
        "design_sha256": sha256(DESIGN),
        "timing": str(PRODUCER),
        "timing_sha256": sha256(PRODUCER),
        "verifier": str(VERIFIER),
        "verifier_sha256": sha256(VERIFIER),
        "preparer": str(Path(__file__)),
        "preparer_sha256": sha256(Path(__file__)),
        "source_identities": str(SOURCE_IDENTITIES),
        "source_identities_sha256": sha256(SOURCE_IDENTITIES),
        "source_sha256": sha256(source),
        "compiler_binary_sha256": sha256(compiler),
        "compiler_source_snapshot_sha256": sha256(archive),
        "arms": arms,
        "baseline_code_identity_verified": len(baseline) == 1,
        "winning_code_identity_verified": len(winning) == 1,
        "order_balance": verify_order(design),
        "memory_guard_unset": True,
        "measurement_lock_available": True,
        "process_snapshot": process_snapshot,
        "process_snapshot_sha256": json_sha256(process_snapshot),
        "timing_outputs_absent": True,
    }
    with PREFLIGHT.open("x") as stream:
        stream.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        stream.flush()
        os.fsync(stream.fileno())
    fcntl.flock(lock_stream, fcntl.LOCK_UN)
    lock_stream.close()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
