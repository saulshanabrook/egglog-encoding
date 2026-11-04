#!/usr/bin/env python3
"""Independently verify the frozen same-mask native and timing evidence."""

from __future__ import annotations

import hashlib
import json
import random
import statistics
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parent
MASK64 = (1 << 64) - 1


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def wrap(value: int) -> int:
    value &= MASK64
    return value - (1 << 64) if value >= 1 << 63 else value


def bitand(left: int, right: int) -> int:
    return wrap((left & MASK64) & (right & MASK64))


def oracle(n: int, x: int, y: int, mask: int) -> str:
    total = 0
    i = 0
    while i < n:
        if bitand(x, mask) == bitand(y, mask):
            delta = 3
        else:
            delta = 99 if wrap(x + 7) == wrap(y + 7) else 7
        total = wrap(total + delta)
        x = wrap(wrap(x * 3) + 1)
        y = wrap(wrap(y * 5) + 7)
        i += 1
    return f"{total}\n"


def hot_cycle_oracle(n: int, x: int, y: int, mask: int) -> tuple[str, dict[str, object]]:
    """Evaluate the frozen hot case from its finite low-bit recurrence."""
    assert mask == 6 and x == 0 and y == 1
    modulus = 8
    initial = (x % modulus, y % modulus)
    state = initial
    deltas = []
    while True:
        low_x, low_y = state
        deltas.append(3 if (low_x & mask) == (low_y & mask) else 7)
        state = ((low_x * 3 + 1) % modulus, (low_y * 5 + 7) % modulus)
        if state == initial:
            break
        assert len(deltas) <= modulus * modulus
    periods, remainder = divmod(max(n, 0), len(deltas))
    total = wrap(periods * sum(deltas) + sum(deltas[:remainder]))
    return f"{total}\n", {
        "state_modulus": modulus,
        "period": len(deltas),
        "deltas": deltas,
        "period_sum": sum(deltas),
        "periods": periods,
        "remainder": remainder,
    }


def run(binary: Path, args: list[int], expected: str, timeout: int = 10) -> dict[str, object]:
    argv = [str(binary), *(str(value) for value in args)]
    result = subprocess.run(argv, capture_output=True, text=True, timeout=timeout, check=False)
    return {
        "argv": argv,
        "exit_code": result.returncode,
        "stdout": result.stdout,
        "stderr": result.stderr,
        "expected_stdout": expected,
        "correct": result.returncode == 0 and result.stdout == expected and result.stderr == "",
    }


def bootstrap(values: list[float]) -> list[float]:
    rng = random.Random(20261019)
    samples = [statistics.median(rng.choices(values, k=len(values))) for _ in range(10_000)]
    samples.sort()
    return [samples[249], samples[9749]]


def main() -> None:
    design_path = ROOT / "confirmation-design.json"
    summary_path = ROOT / "confirmation-summary.json"
    raw_path = ROOT / "confirmation-samples.jsonl"
    design = json.loads(design_path.read_text())
    raw = [json.loads(line) for line in raw_path.read_text().splitlines() if line]

    arms = {name: Path(value["binary"]) for name, value in design["arms"].items()}
    for name, binary in arms.items():
        actual = sha256(binary)
        expected = design["arms"][name]["binary_sha256"]
        assert actual == expected, (name, actual, expected)

    rng = random.Random(760_019)
    cases = [
        [0, 0, 1, 6],
        [1, 0, 1, 1],
        [8, 0, 1, 6],
        [17, -(1 << 63), (1 << 63) - 1, -1],
        [31, (1 << 63) - 1, -(1 << 63), 0],
        [32, -1, 0, 0xFFFF_FFFF],
        [19, 0, 0, -1],
        [23, -7, 7, 6],
    ]
    while len(cases) < 40:
        cases.append(
            [
                rng.randrange(0, 33),
                rng.randrange(-(1 << 63), 1 << 63),
                rng.randrange(-(1 << 63), 1 << 63),
                rng.randrange(-(1 << 63), 1 << 63),
            ]
        )

    executions = []
    for args in cases:
        expected = oracle(*args)
        for name, binary in arms.items():
            row = run(binary, args, expected)
            row["arm"] = name
            executions.append(row)
    winning_args = list(design["args"])
    winning_expected, winning_cycle = hot_cycle_oracle(*winning_args)
    assert winning_expected == design["expected_stdout"]
    winning = []
    for name, binary in arms.items():
        row = run(binary, winning_args, winning_expected, timeout=30)
        row["arm"] = name
        winning.append(row)

    measured = [row for row in raw if row["phase"] == "measure"]
    warmups = [row for row in raw if row["phase"] == "warmup"]
    cycles: dict[int, dict[str, int]] = {}
    for row in measured:
        cycles.setdefault(row["cycle"], {})[row["arm"]] = row["elapsed_ns"]
    assert len(cycles) == 32
    assert all(set(row) == set(arms) for row in cycles.values())
    ratios = {}
    for name in ("B1", "Manual", "Encoding"):
        values = [cycles[i][name] / cycles[i]["U0"] for i in range(32)]
        ratios[f"{name}/U0"] = {
            "median": statistics.median(values),
            "bootstrap95": bootstrap(values),
            "all_faster": all(value < 1 for value in values),
        }

    paths = {
        "u0_emitted": ROOT / "matrix-supplement/hot-u0/off/optimized.bril",
        "b1_emitted": ROOT / "matrix-invariants/hot/off/optimized.bril",
        "manual_emitted": ROOT / "matrix-invariants/hot/manual/optimized.bril",
        "encoding_emitted": ROOT / "matrix-invariants/hot/encoding/optimized.bril",
        "b1_assembly": ROOT / "matrix-invariants/hot/off/native/main.asm",
        "manual_assembly": ROOT / "matrix-invariants/hot/manual/native/main.asm",
        "encoding_assembly": ROOT / "matrix-invariants/hot/encoding/native/main.asm",
    }
    result = {
        "design_sha256": sha256(design_path),
        "summary_sha256": sha256(summary_path),
        "raw_sha256": sha256(raw_path),
        "raw_rows": len(raw),
        "warmup_rows": len(warmups),
        "measured_rows": len(measured),
        "all_raw_correct": all(
            row["exit_code"] == 0
            and not row["timed_out"]
            and row["correct"]
            and row["stdout"] == row["expected_stdout"]
            for row in raw
        ),
        "ratios": ratios,
        "frozen_gate_passed": ratios["Encoding/U0"]["bootstrap95"][1] < 0.99,
        "random_case_count": len(cases),
        "random_execution_count": len(executions),
        "all_random_executions_correct": all(row["correct"] for row in executions),
        "winning_expected_stdout": winning_expected,
        "winning_cycle_oracle": winning_cycle,
        "all_winning_executions_correct": all(row["correct"] for row in winning),
        "u0_b1_emitted_identical": paths["u0_emitted"].read_bytes()
        == paths["b1_emitted"].read_bytes(),
        "manual_encoding_emitted_identical": paths["manual_emitted"].read_bytes()
        == paths["encoding_emitted"].read_bytes(),
        "manual_encoding_assembly_identical": paths["manual_assembly"].read_bytes()
        == paths["encoding_assembly"].read_bytes(),
        "artifact_sha256": {name: sha256(path) for name, path in paths.items()},
        "binary_sha256": {name: sha256(path) for name, path in arms.items()},
        "executions": executions,
        "winning_executions": winning,
    }
    output = ROOT / "independent-verification.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: result[key] for key in (
        "raw_rows", "all_raw_correct", "ratios", "frozen_gate_passed",
        "random_execution_count", "all_random_executions_correct",
        "all_winning_executions_correct", "u0_b1_emitted_identical",
        "manual_encoding_emitted_identical", "manual_encoding_assembly_identical",
    )}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
