"""Bound source builds in Docker itself, not merely in the host Docker client.

Images must already be acquired. Jobs run in disposable named containers with
kernel memory/swap limits; receipts retain the resolved image ID and final state.
These are acquisition diagnostics, never benchmark observations.
"""

from __future__ import annotations

import fcntl
import json
import re
import shutil
import subprocess
import time
import uuid
from collections.abc import Iterator, Mapping, Sequence
from contextlib import contextmanager
from pathlib import Path
from typing import Any

from benchmarking.memory_guard import HEADROOM_BYTES, MemoryGuard

DISK_RESERVE_BYTES = 10 * 1024**3
CONTAINER_MEMORY_BYTES = 5 * 1024**3


@contextmanager
def exclusive_job(lock_path: Path) -> Iterator[None]:
    """Serialize heavy reproduction stages across independent CLI invocations."""
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise ValueError("another reproduction job owns the heavy-process slot") from error
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def run_container(
    image: str,
    command: Sequence[str],
    output: Path,
    *,
    platform: str,
    mounts: Sequence[tuple[Path, str, bool]] = (),
    workdir: str = "/",
    environment: Mapping[str, str] | None = None,
    timeout_sec: float = 300,
    memory_bytes: int = CONTAINER_MEMORY_BYTES,
    allow_warning_pressure: bool = False,
    network: str = "none",
) -> dict[str, Any]:
    """Run one job, retaining logs and killing its owned container on any stop.

    Source mounts are explicit; the boolean means read-only. The workload gets
    no Docker socket or privileges. Zero swap avoids exhausting the small VM.
    Cgroup peak usage includes charged cache and is not native process RSS.
    """
    if platform not in ("linux/arm64", "linux/amd64") or timeout_sec <= 0 or memory_bytes <= 0:
        raise ValueError("require explicit supported platform and positive timeout/memory limits")
    output.mkdir(parents=True, exist_ok=True)
    if shutil.disk_usage(output).free < DISK_RESERVE_BYTES:
        raise ValueError("disk guard refused to launch: fewer than 10 GiB free")
    guard = MemoryGuard(allow_warning_pressure=allow_warning_pressure)
    if reason := guard.check(0):
        raise ValueError(f"resource guard refused to launch: {reason}")
    info = json.loads(
        subprocess.run(
            ["docker", "info", "--format", "{{json .}}"],
            check=True,
            capture_output=True,
            text=True,
            timeout=10,
        ).stdout
    )
    if not info["MemoryLimit"] or not info["SwapLimit"] or info["CgroupVersion"] != "2":
        raise ValueError("Docker must enforce cgroup v2 memory and swap limits")
    if memory_bytes + HEADROOM_BYTES > int(info["MemTotal"]):
        raise ValueError("container cap would leave less than 2 GiB of VM memory")
    image_info = json.loads(
        subprocess.run(
            ["docker", "image", "inspect", image, "--format", "{{json .}}"],
            check=True,
            capture_output=True,
            text=True,
            timeout=10,
        ).stdout
    )
    if f"{image_info['Os']}/{image_info['Architecture']}" != platform:
        raise ValueError("local image architecture differs from the requested platform")
    name = f"egglog-reproduction-{uuid.uuid4().hex}"
    # The shell waits for the actual command and saves counters before the
    # cgroup disappears. This detects a killed compiler child even if its parent
    # ignores that status and exits successfully between monitoring samples.
    wrapper = (
        '"$@"; result=$?; '
        "cat /sys/fs/cgroup/memory.peak > /reproduction-monitor/memory.peak; "
        "cat /sys/fs/cgroup/memory.events > /reproduction-monitor/memory.events; "
        'exit "$result"'
    )
    monitor = output / "monitor"
    monitor.mkdir(exist_ok=True)
    if list(monitor.iterdir()):
        raise ValueError("container output must be a new attempt directory")
    create = [
        "docker",
        "create",
        "--name",
        name,
        "--label",
        "egglog.reproduction=true",
        "--platform",
        platform,
        "--init",
        "--memory",
        str(memory_bytes),
        "--memory-swap",
        str(memory_bytes),
        "--cpus",
        "2",
        "--pids-limit",
        "512",
        "--network",
        network,
        "--workdir",
        workdir,
        "--mount",
        f"type=bind,src={monitor.resolve()},dst=/reproduction-monitor",
    ]
    for source, destination, read_only in mounts:
        create.extend(
            ["--mount", f"type=bind,src={source.resolve()},dst={destination}" + (",readonly" if read_only else "")]
        )
    for key, value in (environment or {}).items():
        create.extend(["--env", f"{key}={value}"])
    create.extend(["--entrypoint", "/bin/sh", image_info["Id"], "-c", wrapper, "reproduction", *command])
    record: dict[str, Any] = {
        "image": image_info["Id"],
        "image_requested": image,
        "platform": platform,
        "command": list(command),
        "workdir": workdir,
        "environment": dict(environment or {}),
        "mounts": [{"source": str(p.resolve()), "destination": d, "read_only": r} for p, d, r in mounts],
        "memory_limit_bytes": memory_bytes,
        "swap_limit_bytes": 0,
        "cpus": 2,
        "timeout_sec": timeout_sec,
        "allow_warning_pressure": allow_warning_pressure,
        "status": "failure",
        "returncode": None,
        "oom_killed": False,
        "cgroup_peak_bytes": 0,
        "message": None,
        "name": name,
    }
    container: str | None = None
    start = time.monotonic()
    try:
        container = subprocess.run(create, check=True, capture_output=True, text=True, timeout=15).stdout.strip()
        record["container_id"] = container
        subprocess.run(["docker", "start", container], check=True, capture_output=True, text=True, timeout=15)
        record["status"] = "success"
        while True:
            state = json.loads(
                subprocess.run(
                    ["docker", "inspect", "--format", "{{json .State}}", container],
                    check=True,
                    capture_output=True,
                    text=True,
                    timeout=5,
                ).stdout
            )
            if not state["Running"]:
                break
            if reason := guard.check(0):
                record.update(status="resource-stopped", message=reason)
                break
            if shutil.disk_usage(output).free < DISK_RESERVE_BYTES:
                record.update(status="resource-stopped", message="free disk fell below the 10 GiB reserve")
                break
            if time.monotonic() - start >= timeout_sec:
                record.update(status="timed-out", message=f"timed out after {timeout_sec:g} seconds")
                break
            sample = subprocess.run(
                [
                    "docker",
                    "exec",
                    container,
                    "/bin/sh",
                    "-c",
                    "cat /sys/fs/cgroup/memory.peak /sys/fs/cgroup/memory.events",
                ],
                capture_output=True,
                text=True,
                timeout=5,
            )
            if sample.returncode == 0:
                record["cgroup_peak_bytes"] = max(record["cgroup_peak_bytes"], int(sample.stdout.splitlines()[0]))
                if re.search(r"^oom_kill [1-9]\d*$", sample.stdout, re.M):
                    record.update(
                        status="memory-limit", oom_killed=True, message="container cgroup reported an OOM kill"
                    )
                    break
            else:
                # A normal exit racing docker exec is allowed; any other failed
                # monitor is checked on the next state inspection, then stops.
                final = json.loads(
                    subprocess.run(
                        ["docker", "inspect", "--format", "{{json .State}}", container],
                        check=True,
                        capture_output=True,
                        text=True,
                        timeout=5,
                    ).stdout
                )
                if final["Running"]:
                    raise ValueError(f"container memory monitoring failed: {sample.stderr.strip()}")
            time.sleep(min(0.5, timeout_sec))
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        record.update(status="resource-stopped", message=f"container supervision failed: {error}")
    except BaseException:
        record.update(status="cancelled", message="caller interrupted the acquisition")
        raise
    finally:
        record["wall_sec"] = time.monotonic() - start
        if container is not None:
            try:
                # Killing an already exited container is harmless. Never address
                # unrelated containers by wildcard or stop the entire daemon.
                subprocess.run(["docker", "kill", container], capture_output=True, timeout=10)
                state = json.loads(
                    subprocess.run(
                        ["docker", "inspect", "--format", "{{json .State}}", container],
                        check=True,
                        capture_output=True,
                        text=True,
                        timeout=5,
                    ).stdout
                )
                record["returncode"] = state["ExitCode"]
                if (monitor / "memory.peak").exists():
                    record["cgroup_peak_bytes"] = max(
                        record["cgroup_peak_bytes"], int((monitor / "memory.peak").read_text())
                    )
                child_oom = (monitor / "memory.events").exists() and re.search(
                    r"^oom_kill [1-9]\d*$",
                    (monitor / "memory.events").read_text(),
                    re.M,
                )
                if state["OOMKilled"] or child_oom:
                    record.update(
                        status="memory-limit", oom_killed=True, message="container cgroup reported an OOM kill"
                    )
                elif record["status"] == "success" and state["ExitCode"] != 0:
                    record.update(status="failure", message=f"container exited with status {state['ExitCode']}")
                with (output / "stdout.log").open("wb") as stdout, (output / "stderr.log").open("wb") as stderr:
                    subprocess.run(["docker", "logs", container], stdout=stdout, stderr=stderr, timeout=10, check=True)
            finally:
                try:
                    subprocess.run(["docker", "rm", "--force", container], check=True, capture_output=True, timeout=10)
                finally:
                    (output / "container.json").write_text(json.dumps(record, indent=2) + "\n")
        else:
            (output / "container.json").write_text(json.dumps(record, indent=2) + "\n")
    return record
