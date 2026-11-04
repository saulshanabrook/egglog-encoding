#!/usr/bin/env python3
"""Bind QR7 timing admission to instructions from the actual native binaries."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent
MATRIX = ROOT / "final-r1/matrix/positive"
OUTPUT = ROOT / "actual-binary-inspection-r1.json"
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
BASELINE = {
    "u0",
    "off",
    "seed-only",
    "primitive-only",
    "cancellation-off",
    "identity-off",
    "query-off",
    "transport-off",
    "bridge-off",
    "consumer-off",
}
WINNING = {"encoding", "manual", "x-rescue", "key-rescue"}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def extract_function(text: str, symbol: str) -> dict[str, object]:
    match = re.search(r"^([0-9a-f]+) <" + re.escape(symbol) + r">:\n", text, re.M)
    if match is None:
        raise RuntimeError(f"missing symbol {symbol}")
    following = re.search(r"^[0-9a-f]+ <[^>]+>:\n", text[match.end() :], re.M)
    end = match.end() + (following.start() if following is not None else len(text) - match.end())
    lines = [line for line in text[match.end() : end].splitlines() if line]
    body = "\n".join(lines) + "\n"
    start = int(match.group(1), 16)
    addresses = []
    backward = []
    for line in lines:
        instruction = re.match(r"^([0-9a-f]+):\s+([^\s]+)(?:\s+0x([0-9a-f]+))?", line)
        if instruction is None:
            raise RuntimeError(f"unparsed instruction in {symbol}: {line}")
        address = int(instruction.group(1), 16)
        addresses.append(address)
        target_text = instruction.group(3)
        opcode = instruction.group(2)
        if target_text is not None and (opcode == "b" or opcode.startswith("b.")):
            target = int(target_text, 16)
            if start <= target < address:
                backward.append({"address": hex(address), "target": hex(target), "opcode": opcode})
    return {
        "instruction_count": len(lines),
        "instruction_sha256": hashlib.sha256(body.encode()).hexdigest(),
        "start": hex(start),
        "end": hex(max(addresses) + 4),
        "internal_backward_branches": backward,
    }


def main() -> None:
    if OUTPUT.exists():
        raise RuntimeError(f"refusing to overwrite {OUTPUT}")
    modes = {}
    for mode in MODES:
        folder = MATRIX / mode / "native"
        binary = folder / "program"
        assembly = folder / "program.asm"
        text = assembly.read_text()
        modes[mode] = {
            "binary": str(binary),
            "binary_sha256": sha256(binary),
            "assembly": str(assembly),
            "assembly_sha256": sha256(assembly),
            "functions": {
                "bril_main": extract_function(text, "__main"),
                "process_main": extract_function(text, "_main"),
            },
        }

    baseline_hashes = {
        modes[mode]["functions"]["process_main"]["instruction_sha256"] for mode in BASELINE
    }
    winning_hashes = {
        modes[mode]["functions"]["process_main"]["instruction_sha256"] for mode in WINNING
    }
    assert len(baseline_hashes) == 1
    assert len(winning_hashes) == 1
    assert baseline_hashes.isdisjoint(winning_hashes)
    assert {len(modes[mode]["functions"]["process_main"]["internal_backward_branches"]) for mode in BASELINE} == {2}
    assert {len(modes[mode]["functions"]["process_main"]["internal_backward_branches"]) for mode in WINNING} == {0}

    emitted = {
        mode: sha256(MATRIX / mode / "optimized.bril")
        for mode in MODES
    }
    assert len({emitted[mode] for mode in BASELINE}) == 1
    assert len({emitted[mode] for mode in WINNING}) == 1
    assert emitted["u0"] != emitted["encoding"]

    result = {
        "schema_version": 1,
        "status": "passed",
        "scope": "retained llvm-objdump disassembly of the actual Mach-O executables",
        "modes": modes,
        "emitted_bril_sha256": emitted,
        "groups": {
            "baseline": {
                "modes": sorted(BASELINE),
                "process_main_instruction_sha256": next(iter(baseline_hashes)),
                "instruction_count": modes["u0"]["functions"]["process_main"]["instruction_count"],
                "internal_backward_branch_count": 2,
            },
            "winning": {
                "modes": sorted(WINNING),
                "process_main_instruction_sha256": next(iter(winning_hashes)),
                "instruction_count": modes["encoding"]["functions"]["process_main"]["instruction_count"],
                "internal_backward_branch_count": 0,
            },
        },
        "global_executable_hashes_are_expected_to_differ": len(
            {modes[mode]["binary_sha256"] for mode in MODES}
        )
        == len(MODES),
        "transport_off_label_limit": (
            "transport-off suppresses export at the same gate as bridge-off; it is an export-gate "
            "placebo, not a direct transport-computation ablation"
        ),
        "performance_samples_taken": False,
    }
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result["groups"], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
