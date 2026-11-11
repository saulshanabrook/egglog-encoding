"""Run bounded safety fixtures for the exact MISAAL known-launch supervisor.

This uses a Python-backed executable named racket, not Racket or Rosette. It
validates launch accounting and cleanup only; no source/corpus admission follows.
Only the public CLI owns the shared heavy-job lock. Materialization runs no child.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import signal
import socket
import subprocess
import sys
import time
import traceback
from dataclasses import asdict
from pathlib import Path
from types import FunctionType, ModuleType
from typing import Any

ROOT = next(parent for parent in Path(__file__).resolve().parents if (parent / "benchmarking/pilot.py").is_file())
sys.path.insert(0, str(ROOT))

from benchmarking.pilot import run_bounded_command  # noqa: E402
from scripts import reproduction_misaal_groups as groups  # noqa: E402
from scripts.reproduction_process import DISK_RESERVE_BYTES, exclusive_job  # noqa: E402

CASES = (
    "return-code",
    "aggregate-cap",
    "outer-timeout",
    "fast-orphan",
    "registration-interruption",
    "source-local-timeout",
    "monitor-failure",
    "guard-death",
)
RACKET_STAND_IN = """import json, os, signal, subprocess, sys, time
from pathlib import Path
folder = Path(__file__).parent
mode = json.loads((folder / "fixture.json").read_text())["mode"]
role = "grandchild" if len(sys.argv) > 1 else "racket"
(folder / (role + ".pid.json")).write_text(json.dumps({"pid": os.getpid(), "group": os.getpgrp()}))
if mode == "return-code":
    print("original stdout")
    print("original stderr", file=sys.stderr)
    sys.exit(7)
if mode == "source-local-timeout":
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
if role == "racket":
    subprocess.Popen([sys.executable, __file__, "grandchild"])
if mode == "aggregate-cap":
    while not (folder / "racket.pid.json").exists() or not (folder / "grandchild.pid.json").exists():
        time.sleep(0.01)
memory = bytearray(128 * 1024**2 if mode == "aggregate-cap" else 65536)
(folder / (role + ".ready")).write_text(str(len(memory)))
while True:
    time.sleep(0.02)
"""


def materialize(source: Path, output: Path) -> dict[str, Any]:
    """Freeze exact tested code and original launcher before any process runs."""
    source = source.resolve()
    if hashlib.sha256(source.read_bytes()).hexdigest() != groups.SOURCE_SHA256:
        raise ValueError("Diagnostic requires the exact pinned DSLInstructionUtils.py")
    output.mkdir(parents=True, exist_ok=False)
    (output / "bin").mkdir()
    (output / "bin/racket").symlink_to(Path(sys.executable).resolve())
    inputs = [source, Path(groups.__file__).resolve(), Path(__file__).resolve(), ROOT / "benchmarking/pilot.py"]
    hashes = {}
    for index, path in enumerate(inputs):
        retained = output / f"input-{index}-{path.name}"
        retained.write_bytes(path.read_bytes())
        hashes[str(path)] = hashlib.sha256(retained.read_bytes()).hexdigest()
    for mode in CASES:
        case = output / mode
        case.mkdir()
        (case / "fixture.rkt").write_text(RACKET_STAND_IN)
        (case / "fixture.json").write_text(json.dumps({"mode": mode}) + "\n")
    record = {
        "status": "materialized-unrun",
        "contract": groups.CONTRACT,
        "inputs": hashes,
        "python": str(Path(sys.executable).resolve()),
        "python_sha256": hashlib.sha256(Path(sys.executable).read_bytes()).hexdigest(),
        "fixture_sha256": hashlib.sha256(RACKET_STAND_IN.encode()).hexdigest(),
        "scope": "synthetic known-launch safety only; no Racket/Rosette or corpus validation",
        "cases": [],
    }
    (output / "diagnostic.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def child(mode: str, source: Path, case: Path, endpoint: Path | None) -> int:
    """Exercise the original launcher body or a declared protocol race fixture."""
    os.environ["PATH"] = str(case.parent / "bin") + os.pathsep + os.environ.get("PATH", "")
    (case / "source.pid.json").write_text(json.dumps({"pid": os.getpid(), "group": os.getpgrp()}))
    if mode == "guard-death":
        # This owner and source share the outer fixture group. Outer timeout
        # kills the lease owner itself; its detached Racket group must self-drain.
        owner = groups.RacketGroups(case / "inner-groups")
        subprocess.Popen(
            [
                sys.executable,
                str(Path(__file__).resolve()),
                "--child",
                "outer-timeout",
                "--source",
                str(source),
                "--output",
                str(case),
                "--endpoint",
                str(owner.endpoint),
            ]
        )
        while True:
            owner.sample(os.getpgrp())
            time.sleep(0.02)
    assert endpoint is not None
    if mode == "registration-interruption":
        # Reserve before fork exactly as production does, then interrupt before
        # the PID receipt. The supervisor may register but must never run work.
        control = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        control.settimeout(5)
        control.connect(str(endpoint))
        control.sendall(b'{"kind":"reserve"}\n')
        nonce = control.recv(128).decode().strip()
        if len(nonce) != 48:
            raise ValueError("Fixture did not receive a launch reservation")
        pending = subprocess.Popen(
            [
                sys.executable,
                "-I",
                "-S",
                str(Path(groups.__file__).resolve()),
                "--endpoint",
                str(endpoint),
                "--reservation",
                nonce,
                "--",
                "racket",
                str(case / "fixture.rkt"),
            ],
            start_new_session=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        (case / "pending.pid.json").write_text(json.dumps({"pid": pending.pid, "group": pending.pid}))
        os._exit(0)
    if mode == "fast-orphan":
        groups.launch_registered(
            ["racket", str(case / "fixture.rkt")],
            endpoint,
            sys.executable,
            start_new_session=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        os._exit(0)
    module = ModuleType("utils.DSLInstructionUtils")
    module.__file__ = str(source)
    module.__dict__.update(subprocess=subprocess, os=os, signal=signal)
    tree = ast.parse(source.read_text())
    classes = [node for node in tree.body if isinstance(node, ast.ClassDef) and node.name == "HelperCompletedProcess"]
    definitions = [
        node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == "run_command_child_processes"
    ]
    compiled = compile(source.read_text(), str(source), "exec", dont_inherit=True)
    code = [
        value
        for value in compiled.co_consts
        if isinstance(value, type(compiled)) and value.co_name == "run_command_child_processes"
    ]
    if len(classes) != 1 or len(definitions) != 1 or len(code) != 1:
        raise ValueError("Pinned native launcher/class not unique")
    exec(
        compile(ast.Module(body=list(classes), type_ignores=[]), str(source), "exec", dont_inherit=True),
        module.__dict__,
    )
    # Full-module import knowledge changes CPython 3.13 call opcodes. Retain the
    # exact compiled function instead of recompiling an AST without its imports.
    module.__dict__["run_command_child_processes"] = FunctionType(
        code[0],
        module.__dict__,
        code[0].co_name,
        tuple(ast.literal_eval(value) for value in definitions[0].args.defaults),
    )
    racket = case.parent / "bin/racket"
    request = {
        "checkout": str(source.parents[2]),
        "racket_group_containment": groups.CONTRACT,
        "source_hashes": {groups.SOURCE: groups.SOURCE_SHA256},
        "python": sys.executable,
        "racket": str(racket),
        "racket_sha256": hashlib.sha256(racket.read_bytes()).hexdigest(),
    }
    with groups.observe_racket_launch(module, request, endpoint):
        result = module.run_command_child_processes(
            ["racket", str(case / "fixture.rkt")], timeout=0.8 if mode == "source-local-timeout" else 180
        )
    (case / "source-result.json").write_text(json.dumps({"returncode": result.returncode, "parent_alive": True}))
    # Let the original source continue after local timeout; no new parent failure
    # is allowed solely because it used its own killpg fallback.
    time.sleep(0.15)
    return 0 if result.returncode == (7 if mode == "return-code" else 1) else 1


def run_diagnostic(source: Path, output: Path) -> dict[str, Any]:
    """Run serial real fixtures, halting on any unexpected outcome or survivor."""
    output, source = output.resolve(), source.resolve()
    record = materialize(source, output)
    phase = "fixture initialization"
    try:
        for mode in CASES:
            phase = f"{mode}: registry and source setup"
            case = output / mode
            registry = None if mode == "guard-death" else groups.RacketGroups(case / "groups")
            command = [
                sys.executable,
                str(Path(__file__).resolve()),
                "--child",
                mode,
                "--source",
                str(source),
                "--output",
                str(case),
            ]
            if registry is not None:
                command.extend(["--endpoint", str(registry.endpoint)])
            samples: list[dict[str, Any]] = []

            def sample(
                pid: int,
                registry: groups.RacketGroups | None = registry,
                samples: list[dict[str, Any]] = samples,
                mode: str = mode,
                case: Path = case,
            ) -> int:
                assert registry is not None
                value = registry.sample(pid)
                samples.append({"rss_bytes": value, "time_monotonic": time.monotonic()})
                if mode == "monitor-failure" and (case / "grandchild.ready").exists():
                    raise OSError("deliberate fixture monitoring failure")
                return value

            # A separate, intentionally unowned small bystander checks exact
            # cleanup. Its unreaped Popen handle retains PID identity until our
            # explicit final cleanup; it never starts descendants.
            phase = f"{mode}: start bystander"
            bystander = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"], start_new_session=True)
            try:
                monitored: dict[str, Any] = (
                    {} if registry is None else {"sample_rss": sample, "cleanup_descendants": registry.close}
                )
                limit = 256 * 1024**2 if mode == "aggregate-cap" else 5 * 1024**3
                phase = f"{mode}: guarded native fixture"
                process = run_bounded_command(
                    command,
                    ROOT,
                    case / "process",
                    timeout_sec=2 if mode in {"outer-timeout", "guard-death"} else 8,
                    memory_limit_bytes=limit,
                    require_guard=True,
                    allow_warning_pressure=True,
                    disk_reserve_bytes=DISK_RESERVE_BYTES,
                    **monitored,
                )
                (case / "process.json").write_text(json.dumps(asdict(process), indent=2, default=str) + "\n")
                phase = f"{mode}: verify live processes and source result"
                bystander_alive = bystander.poll() is None
                # Guard death is a crash, not a returning guard. Allow its exact
                # 50ms lease loop a bounded crash-response drain and record it.
                deadline = time.monotonic() + (2 if mode == "guard-death" else 0)
                while True:
                    rows = groups.process_snapshot()
                    pids = {json.loads(path.read_text())["pid"] for path in case.glob("*.pid.json")}
                    receipts = list(case.glob("*groups/groups.json"))
                    for receipt in receipts:
                        group_record = json.loads(receipt.read_text())
                        pids.update(entry["pid"] for entry in group_record["groups"])
                        pids.update(entry["pid"] for entry in group_record["launches"].values() if "pid" in entry)
                    survivors = sorted(pid for pid in pids if pid in rows and "Z" not in str(rows[pid]["state"]))
                    if not survivors or time.monotonic() >= deadline:
                        break
                    time.sleep(0.05)
                result = {
                    "mode": mode,
                    "process": asdict(process),
                    "samples": samples,
                    "bystander_alive": bystander_alive,
                    "survivors": survivors,
                    "guard_return_drain_seconds": 0
                    if mode != "guard-death"
                    else max(0, time.monotonic() - deadline + 2),
                }
                record["cases"].append(result)
                expected = {
                    "aggregate-cap": "memory-limit",
                    "outer-timeout": "timed-out",
                    "guard-death": "timed-out",
                    "monitor-failure": "resource-stopped",
                }.get(mode, "success")
                if process.status != expected or survivors or not bystander_alive:
                    raise ValueError(f"{mode}: unexpected status, surviving owned process, or harmed bystander")
                if mode == "aggregate-cap":
                    assert registry is not None
                    measured = registry.record["last_sample"]
                    if (
                        not (case / "grandchild.pid.json").exists()
                        or not measured["max_process_rss_bytes"] < limit < measured["rss_bytes"]
                    ):
                        raise ValueError("Fixture did not demonstrate an aggregate-only cap with a detached grandchild")
                if mode in {"return-code", "source-local-timeout"}:
                    expected_code = 7 if mode == "return-code" else 1
                    if json.loads((case / "source-result.json").read_text()) != {
                        "returncode": expected_code,
                        "parent_alive": True,
                    }:
                        raise ValueError("Original source result/fallback was not preserved")
                if mode == "registration-interruption" and (case / "racket.pid.json").exists():
                    raise ValueError("Native work began without the parent fork receipt")
                if (
                    mode in {"outer-timeout", "monitor-failure", "source-local-timeout", "guard-death"}
                    and not (case / "grandchild.ready").exists()
                ):
                    raise ValueError("Fixture did not reach a real detached child and grandchild")
            finally:
                operation_phase = phase
                phase = f"{mode}: final registry cleanup"
                try:
                    if registry is not None and not registry.closed:
                        registry.close()
                finally:
                    registry_phase = phase
                    phase = f"{mode}: final bystander cleanup"
                    try:
                        bystander.kill()
                    finally:
                        bystander.wait()
                    phase = registry_phase
                phase = operation_phase
        record["status"] = "success"
    except BaseException as error:
        record.update(
            status="failure",
            reason=f"{type(error).__name__}: {error}",
            failure_phase=phase,
            traceback=traceback.format_exc(),
        )
    finally:
        record["evidence_sha256"] = {
            str(path.relative_to(output)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(output.rglob("*"))
            if path.is_file() and path.name != "diagnostic.json"
        }
        (output / "diagnostic.json").write_text(json.dumps(record, indent=2, default=str) + "\n")
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--materialize-only", action="store_true")
    parser.add_argument("--child", choices=CASES)
    parser.add_argument("--endpoint", type=Path)
    args = parser.parse_args()
    if args.child:
        return child(args.child, args.source.resolve(), args.output.resolve(), args.endpoint)
    if args.materialize_only:
        record = materialize(args.source, args.output)
    else:
        with exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
            record = run_diagnostic(args.source, args.output)
    print(json.dumps(record, indent=2, default=str))
    return 0 if record["status"] in {"success", "materialized-unrun"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
