#!/usr/bin/env python3
"""Create the prospective QR7 timing design before any actual-integration samples."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT / "prospective-timing-design-r1.json"
MATRIX = ROOT / "final-r1/matrix/positive"
SOURCE = ROOT / "fixtures/source.bril"
SOURCE_IDENTITIES = ROOT / "source-identities-r1.json"
BINARY_INSPECTION = ROOT / "actual-binary-inspection-r1.json"

MODES = [
    "u0",
    "off",
    "seed-only",
    "primitive-only",
    "encoding",
    "manual",
    "cancellation-off",
    "identity-off",
    "x-rescue",
    "key-rescue",
    "query-off",
    "transport-off",
    "bridge-off",
    "consumer-off",
]
WILLIAMS_BASE = [0, 1, 13, 2, 12, 3, 11, 4, 10, 5, 9, 6, 8, 7]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def williams_row(row: int) -> list[str]:
    return [MODES[(index + row) % len(MODES)] for index in WILLIAMS_BASE]


def block_rows(block: int) -> list[int]:
    rows = list(range(len(MODES)))
    shift = block % len(rows)
    rows = rows[shift:] + rows[:shift]
    if block % 2:
        rows.reverse()
    return rows


def session(name: str, cycles: int) -> dict[str, object]:
    assert cycles % len(MODES) == 0
    cycle_order = []
    for cycle in range(cycles):
        block = cycle // len(MODES)
        within = cycle % len(MODES)
        row = block_rows(block)[within]
        workloads = ["hot-equal-key", "neutral-zero-trip"]
        if cycle % 2:
            workloads.reverse()
        cycle_order.append(
            {
                "cycle": cycle,
                "complete_block": block,
                "williams_row": row,
                "arm_order": williams_row(row),
                "workload_order": workloads,
            }
        )
    return {"name": name, "cycles": cycles, "complete_blocks": cycles // len(MODES), "cycle_order": cycle_order}


def main() -> None:
    if OUTPUT.exists():
        raise RuntimeError(f"refusing to overwrite {OUTPUT}")
    inspection = json.loads(BINARY_INSPECTION.read_text())
    assert inspection["status"] == "passed"
    assert json.loads(SOURCE_IDENTITIES.read_text())["timing_samples_taken"] is False

    arms = {}
    for mode in MODES:
        binary = MATRIX / mode / "native/program"
        emitted = MATRIX / mode / "optimized.bril"
        assembly = MATRIX / mode / "native/program.asm"
        actual = inspection["modes"][mode]
        assert sha256(binary) == actual["binary_sha256"]
        assert sha256(assembly) == actual["assembly_sha256"]
        arms[mode] = {
            "mode": mode,
            "binary": str(binary),
            "binary_sha256": sha256(binary),
            "emitted": str(emitted),
            "emitted_sha256": sha256(emitted),
            "assembly": str(assembly),
            "assembly_sha256": sha256(assembly),
            "process_main_instruction_sha256": actual["functions"]["process_main"]["instruction_sha256"],
            "process_main_instruction_count": actual["functions"]["process_main"]["instruction_count"],
            "process_main_backward_branches": len(actual["functions"]["process_main"]["internal_backward_branches"]),
        }

    design = {
        "schema_version": 1,
        "revision": 1,
        "frozen_utc": datetime.now(timezone.utc).isoformat(),
        "timed_samples_taken": False,
        "status": "prospective design frozen before QR7 actual-integration timing",
        "source": str(SOURCE),
        "source_sha256": sha256(SOURCE),
        "source_identities": str(SOURCE_IDENTITIES),
        "source_identities_sha256": sha256(SOURCE_IDENTITIES),
        "compiler_source_archive": str(ROOT / "corrected-source-r1.tar"),
        "compiler_source_archive_sha256": sha256(ROOT / "corrected-source-r1.tar"),
        "compiler_delta_patch": str(ROOT / "eggcc-candidate-r1.patch"),
        "compiler_delta_patch_sha256": sha256(ROOT / "eggcc-candidate-r1.patch"),
        "compiler_binary": str(ROOT / "bin-r1/eggcc"),
        "compiler_binary_sha256": sha256(ROOT / "bin-r1/eggcc"),
        "tiger_binary": str(ROOT / "bin-r1/tiger"),
        "tiger_binary_sha256": sha256(ROOT / "bin-r1/tiger"),
        "binary_inspection": str(BINARY_INSPECTION),
        "binary_inspection_sha256": sha256(BINARY_INSPECTION),
        "native_backend": "untouched admitted U0 lowering with LLVM 18 O3_O3 and optimize-egglog=false",
        "endpoint": "fresh-process execution of generated Mach-O programs; compiler and lowering time excluded",
        "clock": "Python time.perf_counter_ns around ten serial fresh processes",
        "child_environment": {"PATH": "/usr/bin:/bin:/usr/sbin:/sbin", "LC_ALL": "C", "LANG": "C"},
        "memory_guard": "EGGLOG_BENCH_MEMORY_GUARD must be absent from parent and child environments",
        "memory_pressure_policy": "recorded descriptively and never used to block or discard a session",
        "raytracing": "excluded",
        "outlier_policy": "retain every completed observation; no exclusions or adaptive reruns",
        "failure_policy": "retain partial artifacts and stop on timeout, signal, nonzero exit, stderr, or wrong stdout",
        "workloads": [
            {"name": "hot-equal-key", "args": [12, 12, 10_000_000], "expected_stdout": "49999995000000\n", "acceptance_role": "primary runtime payoff"},
            {"name": "neutral-zero-trip", "args": [12, 12, 0], "expected_stdout": "0\n", "acceptance_role": "reported neutral control; no speedup required"},
        ],
        "arms": arms,
        "arm_order_design": "14-treatment even Williams square; every complete block balances positions and directed immediate predecessors",
        "williams_base_indices": WILLIAMS_BASE,
        "sessions": [session("screen", 14), session("confirmation", 112)],
        "warmups_per_arm_per_workload_per_session": 1,
        "invocations_per_observation": 10,
        "timeout_s_per_process": 30,
        "bootstrap_draws": 10_000,
        "bootstrap_seed": 7_019,
        "bootstrap_unit": "complete 14-cycle Williams block",
        "primary_hot_comparisons": [
            ["encoding", "u0"],
            ["encoding", "off"],
            ["encoding", "seed-only"],
            ["encoding", "primitive-only"],
            ["manual", "u0"],
        ],
        "screen_gate": "every primary hot paired median ratio is below 0.99",
        "confirmation_gate": "every primary hot complete-block bootstrap 95% upper bound is below 0.99",
        "same_code_gate": "on confirmation hot workload, every arm median in each instruction-identical group is within 2% of that group's reference",
        "same_code_groups": {
            "baseline": {
                "reference": "u0",
                "arms": inspection["groups"]["baseline"]["modes"],
                "process_main_instruction_sha256": inspection["groups"]["baseline"]["process_main_instruction_sha256"],
            },
            "winning": {
                "reference": "encoding",
                "arms": inspection["groups"]["winning"]["modes"],
                "process_main_instruction_sha256": inspection["groups"]["winning"]["process_main_instruction_sha256"],
            },
        },
        "transport_off_interpretation": "export-gate placebo; current source does not disable transport computation",
        "compiler_timing_excluded_reason": "audit-only manual closure also runs in encoding and the manual arm also materializes the engine graph",
    }
    OUTPUT.write_text(json.dumps(design, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"path": str(OUTPUT), "sha256": sha256(OUTPUT), "arms": len(arms), "screen_cycles": 14, "confirmation_cycles": 112}, indent=2))


if __name__ == "__main__":
    main()
