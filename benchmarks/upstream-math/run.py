#!/usr/bin/env python3
"""Run the standalone Math comparison with bounded, resumable subprocesses."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import tomllib
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
ENGINES = {"Egg": "egg-math", "Egglog": "egglog-math"}
GIB = 1024**3
HOST_RESERVE = 2 * GIB
DISK_RESERVE = 3 * GIB


def check_host(build_directory: Path | None = None) -> None:
    """Fail closed on host pressure, insufficient reserve, or unreadable monitors."""
    if sys.platform == "darwin":
        pressure = int(subprocess.check_output(["sysctl", "-n", "kern.memorystatus_vm_pressure_level"], timeout=3))
        if pressure != 1:
            raise RuntimeError(f"host memory pressure is not normal (kernel level {pressure})")
        vm = subprocess.check_output(["vm_stat"], text=True, timeout=3)
        page_size = int(re.search(r"page size of (\d+) bytes", vm).group(1))  # type: ignore[union-attr]
        available = 0
        for name in ("free", "inactive", "speculative"):
            available += int(re.search(rf"Pages {name}:\s+(\d+)", vm).group(1)) * page_size  # type: ignore[union-attr]
    elif sys.platform.startswith("linux"):
        available = int(re.search(r"MemAvailable:\s+(\d+)", Path("/proc/meminfo").read_text()).group(1)) * 1024  # type: ignore[union-attr]
    else:
        raise RuntimeError(f"host memory monitor is unsupported on {sys.platform}")
    if available < HOST_RESERVE:
        raise RuntimeError(f"host memory headroom {available / GIB:.2f} GiB is below the 2 GiB reserve")
    if build_directory is not None and shutil.disk_usage(build_directory).free < DISK_RESERVE:
        raise RuntimeError("build disk headroom is below the 3 GiB reserve")


def group_state(group: int) -> tuple[int, bool]:
    """Measure the owned process group, including children and grandchildren."""
    output = subprocess.check_output(["ps", "-axo", "pgid=,rss=,stat="], text=True, timeout=3)
    rss, live = 0, False
    for line in output.splitlines():
        pgid, kilobytes, state = line.split()
        if int(pgid) == group:
            rss += int(kilobytes) * 1024
            live |= not state.startswith("Z")
    return rss, live


def reap_child(process: subprocess.Popen[bytes], flags: int = 0) -> int | None:
    """Reap this child exactly once, retaining its exit code and RSS high-water mark."""
    if process.returncode is not None:
        return None
    pid, status, usage = os.wait4(process.pid, flags)
    if not pid:
        return None
    process.returncode = os.waitstatus_to_exitcode(status)
    return int(usage.ru_maxrss) * (1 if sys.platform == "darwin" else 1024)


def stop_group(process: subprocess.Popen[bytes]) -> int | None:
    """Kill only this launched session's group and reap its direct child."""
    peak = None
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    except PermissionError:
        # macOS can retain a departed group's zombie bookkeeping briefly.
        peak = reap_child(process, os.WNOHANG)
        if process.returncode is None or group_state(process.pid)[1]:
            raise
    return peak if peak is not None else reap_child(process)


def run_process(
    command: list[str], directory: Path, memory_bytes: int, timeout: float, *, build: bool = False
) -> tuple[dict[str, Any], bool]:
    """Return one outcome and whether the whole campaign must stop."""
    result: dict[str, Any] = {
        "status": "not-run",
        "wall_seconds": None,
        "peak_rss_bytes": 0,
        "reason": None,
    }
    try:
        check_host(directory if build else None)
    except (RuntimeError, OSError, ValueError, AttributeError, subprocess.SubprocessError) as error:
        result["reason"] = f"Safety stop before launch: {error}"
        return result, True
    with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
        environment = {**os.environ, "RUST_LOG": "error"}
        started = time.monotonic()
        try:
            process = subprocess.Popen(
                command,
                cwd=directory,
                stdout=stdout,
                stderr=stderr,
                start_new_session=True,
                env=environment,
            )
        except OSError as error:
            result.update(status="failure", reason=str(error))
            return result, False
        halt = False
        result["status"] = "success"
        finished = threading.Event()

        def monitor() -> None:
            nonlocal halt
            next_host_check = started
            try:
                while not finished.is_set():
                    rss, _ = group_state(process.pid)
                    result["peak_rss_bytes"] = max(result["peak_rss_bytes"], rss)
                    now = time.monotonic()
                    if finished.is_set():
                        return
                    if rss > memory_bytes:
                        result.update(
                            status="memory-limit", reason=f"process group exceeded {memory_bytes / GIB:g} GiB"
                        )
                        break
                    if now - started >= timeout:
                        result.update(status="timed-out", reason=f"process exceeded {timeout:g} seconds")
                        break
                    if now >= next_host_check:
                        check_host(directory if build else None)
                        next_host_check = now + 0.5
                    finished.wait(min(0.1, max(0, timeout - (time.monotonic() - started))))
            except (RuntimeError, OSError, ValueError, AttributeError, subprocess.SubprocessError) as error:
                if finished.is_set():
                    return
                result.update(status="resource-stopped", reason=f"Safety stop: {error}")
                halt = True
            if result["status"] != "success" and not finished.is_set():
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                except OSError as error:
                    if finished.wait(0.05):
                        return
                    halt = True
                    result.update(
                        status="resource-stopped",
                        reason=f"{result['reason']}; group signal failed ({error}); using owned-child fallback",
                    )
                    try:
                        os.kill(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    except OSError as fallback_error:
                        result["reason"] += f"; child signal also failed ({fallback_error})"
                        # Wake the main thread's blocking wait so a failed guard
                        # cannot silently leave the campaign waiting forever.
                        main_thread = threading.main_thread().ident
                        assert main_thread is not None
                        signal.pthread_kill(main_thread, signal.SIGINT)

        watchdog = threading.Thread(target=monitor, name="math-resource-watchdog", daemon=True)
        try:
            watchdog.start()
            _, status, usage = os.wait4(process.pid, 0)
            result["wall_seconds"] = time.monotonic() - started
            process.returncode = os.waitstatus_to_exitcode(status)
        except BaseException:
            finished.set()
            stop_group(process)
            raise
        finally:
            finished.set()
            if watchdog.ident is not None:
                watchdog.join()
            peak = stop_group(process)
            if peak is not None:
                result["peak_rss_bytes"] = max(result["peak_rss_bytes"], peak)
        result["peak_rss_bytes"] = max(
            result["peak_rss_bytes"], int(usage.ru_maxrss) * (1 if sys.platform == "darwin" else 1024)
        )
        if result["status"] == "success" and process.returncode == -signal.SIGKILL:
            halt = True
            result.update(status="resource-stopped", reason="Unexpected SIGKILL (cause unknown); campaign stopped")
        elif result["status"] == "success" and result["peak_rss_bytes"] > memory_bytes:
            result.update(
                status="memory-limit",
                reason=f"observed RSS peak exceeded {memory_bytes / GIB:g} GiB (detected after exit)",
            )
        elif result["status"] == "success" and result["wall_seconds"] >= timeout:
            result.update(status="timed-out", reason=f"process exceeded {timeout:g} seconds (detected after exit)")
        elif result["status"] == "success" and process.returncode:
            result.update(status="failure", reason=f"exit {process.returncode}")
        if not math.isfinite(result["wall_seconds"]) or result["wall_seconds"] <= 0:
            result.update(status="failure", wall_seconds=None, reason="external wall time must be finite and positive")
        if result["status"] != "success":
            # Keep diagnostics bounded even if a failed program floods its logs.
            for stream in (stderr, stdout):
                stream.seek(0, os.SEEK_END)
                stream.seek(max(0, stream.tell() - 4000))
                tail = stream.read(4000).decode(errors="replace").strip()
                if tail:
                    result["reason"] += f": {tail}"
                    break
        return result, halt


def metadata(directory: Path, binary_directory: Path, memory_bytes: int, timeout: float) -> dict[str, Any]:
    """Bind reusable observations to sources, executables, host, and limits."""
    files = ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "egg.rs", "egglog.rs", "math.egg", "run.py")
    sources = {name: hashlib.sha256((directory / name).read_bytes()).hexdigest() for name in files}
    manifest = tomllib.loads((directory / "Cargo.toml").read_text())
    engines = {}
    for engine, binary in ENGINES.items():
        path = binary_directory / binary
        dependency = manifest["dependencies"][engine.lower()]
        binary_hash = None
        if path.is_file():
            with path.open("rb") as binary_file:
                binary_hash = hashlib.file_digest(binary_file, "sha256").hexdigest()
        engines[engine] = {
            "git": dependency["git"],
            "rev": dependency["rev"],
            "binary_sha256": binary_hash,
        }
    return {
        "engines": engines,
        "source_sha256": sources,
        "host": {
            "system": platform.system(),
            "release": platform.release(),
            "machine": platform.machine(),
            "name": platform.node(),
        },
        "limits": {"memory_bytes": memory_bytes, "timeout_seconds": timeout, "host_reserve_bytes": HOST_RESERVE},
        "timing": (
            "external wall_seconds: monotonic immediately before Popen to blocking wait4 completion; "
            "watchdog join and cleanup excluded"
        ),
        "memory": "peak_rss_bytes: maximum of sampled process-group RSS and per-child wait4 high-water mark",
    }


def collect(
    directory: Path,
    binary_directory: Path,
    output: Path,
    iterations: int,
    rounds: int,
    memory_bytes: int,
    timeout: float,
) -> int:
    context = metadata(directory, binary_directory, memory_bytes, timeout)
    data: dict[str, Any] = {"metadata": context, "rows": []}
    if output.exists():
        data = json.loads(output.read_text())
        previous = {key: value for key, value in data["metadata"].items() if key != "requested"}
        if previous != context:
            raise ValueError(
                "cached source/binary/host/limits differ; preserve this file and choose a new --output path"
            )
    data["metadata"]["requested"] = {"iterations": iterations, "rounds": rounds}
    by_point = {(row["engine"], row["iterations"], row["run"]): row for row in data["rows"]}
    for cutoff in range(1, iterations + 1):
        for engine in ENGINES:
            for run in range(1, rounds + 1):
                key = engine, cutoff, run
                if key not in by_point:
                    row = {
                        "engine": engine,
                        "iterations": cutoff,
                        "run": run,
                        "status": "not-run",
                        "wall_seconds": None,
                        "peak_rss_bytes": 0,
                        "reason": "not attempted",
                    }
                    data["rows"].append(row)
                    by_point[key] = row

    def save() -> None:
        output.parent.mkdir(parents=True, exist_ok=True)
        temporary = output.with_name(output.name + ".tmp")
        temporary.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n")
        temporary.replace(output)

    save()  # A blocked host must still produce an honest, renderable grid.
    blocked: dict[str, int] = {}
    for row in data["rows"]:
        if row["status"] not in ("success", "not-run"):
            blocked[row["engine"]] = min(blocked.get(row["engine"], row["iterations"]), row["iterations"])
    halted: str | None = None
    for cutoff in range(1, iterations + 1):
        for engine, binary in ENGINES.items():
            for run in range(1, rounds + 1):
                row = by_point[engine, cutoff, run]
                if row["status"] != "not-run":
                    continue
                if halted:
                    row["reason"] = halted
                elif engine in blocked and cutoff >= blocked[engine]:
                    row["reason"] = f"not attempted after {engine} failure at cutoff {blocked[engine]}"
                else:
                    result, halt = run_process(
                        [str(binary_directory / binary), str(cutoff)], directory, memory_bytes, timeout
                    )
                    row.update(result)
                    print(
                        f"{engine} N={cutoff} run={run}: {row['status']}"
                        + (f" ({row['reason']})" if row["reason"] else ""),
                        file=sys.stderr,
                    )
                    if halt:
                        halted = str(row["reason"])
                    elif row["status"] != "success":
                        blocked[engine] = cutoff
                save()
    return (
        2
        if halted
        else int(
            any(
                by_point[e, n, r]["status"] != "success"
                for n in range(1, iterations + 1)
                for e in ENGINES
                for r in range(1, rounds + 1)
            )
        )
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("run", "build"), nargs="?", default="run")
    parser.add_argument("--iterations", type=int, default=13)
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--memory-gib", type=float, default=7)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--binary-dir", type=Path, default=ROOT / "target/release")
    parser.add_argument("--output", type=Path, default=ROOT / "results.json")
    args = parser.parse_args(argv)
    if (
        not 1 <= args.iterations <= 13
        or args.rounds < 1
        or not all(math.isfinite(v) and v > 0 for v in (args.memory_gib, args.timeout))
    ):
        parser.error("iterations must be 1–13; rounds, memory and timeout must be positive and finite")
    try:
        if args.command == "build":
            result, _ = run_process(
                ["cargo", "build", "--release", "--locked", "-j1"],
                ROOT,
                int(args.memory_gib * GIB),
                args.timeout,
                build=True,
            )
            print(json.dumps(result), file=sys.stderr)
            return 0 if result["status"] == "success" else 2
        return collect(
            ROOT,
            args.binary_dir.resolve(),
            args.output.resolve(),
            args.iterations,
            args.rounds,
            int(args.memory_gib * GIB),
            args.timeout,
        )
    except (OSError, ValueError, KeyError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
