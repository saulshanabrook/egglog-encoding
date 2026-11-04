#!/usr/bin/env python3
"""Check process admission using synthetic ps output; never launch a process."""

from __future__ import annotations

import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
# This directory contains inspect.py; keep it out of stdlib import resolution.
# Producer and verifier are loaded explicitly by absolute path below.
sys.path = [entry for entry in sys.path if Path(entry or Path.cwd()).resolve() != ROOT]

import copy
import importlib.util
import json
from unittest.mock import MagicMock, patch

REJECTION = ROOT / "timing-preflight-rejected-1792434879825091000.json"
modules = []
for filename in ("timing.py", "verify-timing.py"):
    spec = importlib.util.spec_from_file_location(filename.removesuffix(".py"), ROOT / filename)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    modules.append(module)
producer, verifier = modules


def check_inventory(rows: list[dict], expected: list[tuple[str, list[str]]]) -> None:
    """Exercise the real parser and independent verifier with mocked ps only."""
    inventory = MagicMock()
    inventory.__enter__.return_value = inventory
    inventory.pid = 2_000_000_001
    inventory.returncode = 0
    rows = [
        {"pid": os.getpid(), "ppid": os.getppid(), "cpu_percent": 200.0, "memory_percent": 0.1, "comm": "rustc"},
        {"pid": inventory.pid, "ppid": os.getpid(), "cpu_percent": 200.0, "memory_percent": 0.1, "comm": "clang"},
        *rows,
    ]
    inventory.communicate.return_value = (
        "\n".join(
            f"{row['pid']} {row['ppid']} {row['cpu_percent']} {row['memory_percent']} {row['comm']}" for row in rows
        ),
        "",
    )
    with patch.object(producer.subprocess, "Popen", return_value=inventory) as spawn:
        snapshot = producer.capture_process_snapshot()
    spawn.assert_called_once_with(producer.PROCESS_COMMAND, stdout=-1, stderr=-1, text=True)
    assert snapshot["inventory_error"] is None
    assert snapshot["passed"] is (not expected)
    assert [(Path(row["comm"]).name, row["reasons"]) for row in snapshot["competitors"]] == expected
    if expected:
        # Hide the producer's rejection: the verifier must reconstruct it itself.
        forged = copy.deepcopy(snapshot)
        forged["passed"] = True
        forged["competitors"] = []
        try:
            verifier.verify_process_snapshot(forged, Path(__file__))
        except AssertionError:
            pass
        else:
            raise AssertionError("verifier admitted a forged passing inventory")
    else:
        assert verifier.verify_process_snapshot(snapshot, Path(__file__)) == producer.json_sha256(snapshot)


def main() -> None:
    if not __debug__:
        raise RuntimeError("optimized Python disables required synthetic assertions")
    assert len(sys.argv) == 1
    assert producer.PROCESS_POLICY["version"] == 2
    assert producer.PROCESS_POLICY["material_cpu_percent"] == 75.0
    rejection_bytes = REJECTION.read_bytes()
    rejected = json.loads(rejection_bytes)["process_snapshot"]
    assert rejected["policy"]["version"] == 1
    assert rejected["policy"]["material_cpu_percent"] == 10.0
    for field in ("known_job_names", "known_job_prefixes", "exemptions"):
        assert producer.PROCESS_POLICY[field] == rejected["policy"][field]
    assert not (ROOT / "timing-preflight.json").exists()
    assert not any(path.is_file() for path in (ROOT / "timing").rglob("*"))

    cases = 0
    for cpu, blocked in ((0.0, False), (10.0, False), (49.6, False), (74.9, False), (75.0, True), (98.4, True), (200.0, True)):
        row = {"pid": 2_000_000_002, "ppid": 1, "cpu_percent": cpu, "memory_percent": 0.1, "comm": "/tmp/unknown-job"}
        check_inventory([row], [("unknown-job", ["material_cpu"])] if blocked else [])
        cases += 1
    for name in [*producer.PROCESS_POLICY["known_job_names"], *(prefix + "synthetic" for prefix in producer.PROCESS_POLICY["known_job_prefixes"])]:
        row = {"pid": 2_000_000_002, "ppid": 1, "cpu_percent": 0.0, "memory_percent": 0.1, "comm": f"/tmp/{name}"}
        check_inventory([row], [(name, ["known_compiler_or_benchmark"])])
        cases += 1
    check_inventory(
        [{"pid": 2_000_000_002, "ppid": 1, "cpu_percent": 75.0, "memory_percent": 0.1, "comm": "/tmp/rustc"}],
        [("rustc", ["known_compiler_or_benchmark", "material_cpu"])],
    )
    cases += 1

    # Replay retained data without re-inventorying the host or changing evidence.
    original_owners = {rejected["self"]["pid"], rejected["inventory_pid"]}
    retained_rows = [row for row in rejected["processes"] if row["pid"] not in original_owners]
    protobuf = "protobuf-3080012d9de58429"
    check_inventory(retained_rows, [(protobuf, ["material_cpu"])])
    check_inventory([row for row in retained_rows if Path(row["comm"]).name != protobuf], [])
    later_gui = [
        {"pid": 2_000_000_002, "ppid": 1, "cpu_percent": 28.6, "memory_percent": 0.1, "comm": "/System/WindowServer"},
        {"pid": 2_000_000_003, "ppid": 1, "cpu_percent": 48.2, "memory_percent": 0.1, "comm": "/Applications/iTerm2"},
    ]
    check_inventory(later_gui, [])
    cases += 3
    assert REJECTION.read_bytes() == rejection_bytes
    assert not (ROOT / "timing-preflight.json").exists()
    assert not any(path.is_file() for path in (ROOT / "timing").rglob("*"))
    print(json.dumps({"synthetic_only": True, "policy_version": 2, "material_cpu_percent": 75.0, "cases_passed": cases}, sort_keys=True))


if __name__ == "__main__":
    main()
