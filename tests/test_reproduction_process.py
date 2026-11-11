"""Reproduction guards supervise the workload, including VM descendants."""

from __future__ import annotations

import json
import os
import shutil
import signal
import subprocess
import sys
import time
from contextlib import suppress
from pathlib import Path
from typing import Any

import pytest

from benchmarking import memory_guard, pilot
from scripts import reproduction_process


@pytest.fixture(autouse=True)
def safe_host(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(memory_guard, "host_memory", lambda: (12 * 1024**3, 1))


def test_native_guard_is_mandatory_without_environment(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.delenv("EGGLOG_BENCH_MEMORY_GUARD", raising=False)
    monkeypatch.setattr(memory_guard, "host_memory", lambda: (12 * 1024**3, 4))
    with pytest.raises(ValueError, match="resource guard refused"):
        pilot.run_bounded_command(
            [sys.executable, "-c", "raise Exception('launched')"], tmp_path, tmp_path / "log", require_guard=True
        )
    assert not list(tmp_path.iterdir())


def test_native_disk_guard_stops_in_flight_child(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    marker = tmp_path / "started"
    original = shutil.disk_usage(tmp_path)
    monkeypatch.setattr(
        pilot.shutil, "disk_usage", lambda _: original._replace(free=0) if marker.exists() else original
    )
    result = pilot.run_bounded_command(
        [sys.executable, "-c", "import pathlib,time; pathlib.Path('started').touch(); time.sleep(30)"],
        tmp_path,
        tmp_path / "disk",
        require_guard=True,
        disk_reserve_bytes=1,
        timeout_sec=5,
    )
    assert result.status == "resource-stopped"
    assert "disk" in str(result.message)
    assert result.wall_sec < 5


def fake_docker(
    monkeypatch: pytest.MonkeyPatch,
    *,
    oom: bool = False,
    timeout: bool = False,
    telemetry: bool = True,
    child_oom: bool = False,
    vm_preflight_bytes: int = 8 * 1024**3,
    vm_available_bytes: int = 8 * 1024**3,
) -> list[list[str]]:
    commands: list[list[str]] = []
    started = False
    monitor: Path | None = None

    def docker(args: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        nonlocal started, monitor
        commands.append(args)
        command = args[1:]
        if command[0] == "info":
            result: Any = {"MemTotal": 8 * 1024**3, "MemoryLimit": True, "SwapLimit": True, "CgroupVersion": "2"}
        elif command[:2] == ["image", "inspect"]:
            result = {"Id": "sha256:locked", "Os": "linux", "Architecture": "amd64"}
        elif command[0] == "create":
            mount = args[args.index("--mount") + 1]
            monitor = Path(mount.split("src=", 1)[1].split(",dst=", 1)[0])
            return subprocess.CompletedProcess(args, 0, "owned-id\n", "")
        elif command[0] == "start":
            started = True
            assert monitor is not None
            (monitor / "vm-preflight-kib").write_text(str(vm_preflight_bytes // 1024) + "\n")
            if telemetry:
                (monitor / "memory.peak").write_text("1024\n")
                (monitor / "memory.events").write_text(f"oom_kill {int(child_oom)}\n")
                (monitor / "vm-meminfo").write_text(f"MemAvailable: {vm_available_bytes // 1024} kB\n")
            return subprocess.CompletedProcess(args, 0, "owned-id\n", "")
        elif command[0] == "kill":
            started = False
            return subprocess.CompletedProcess(args, 0, "owned-id\n", "")
        elif command[0] == "inspect":
            result = {"Running": started and timeout, "OOMKilled": oom, "ExitCode": 137 if oom else 0}
        elif command[0] == "exec":
            return subprocess.CompletedProcess(
                args, 0, f"1024\noom_kill 0\nMemAvailable: {vm_available_bytes // 1024} kB\n", ""
            )
        else:
            return subprocess.CompletedProcess(args, 0, "", "")
        return subprocess.CompletedProcess(args, 0, json.dumps(result), "")

    monkeypatch.setattr(reproduction_process.subprocess, "run", docker)
    return commands


def test_container_uses_kernel_limits_and_records_oom(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    commands = fake_docker(monkeypatch, oom=True)
    result = reproduction_process.run_container(
        "pinned:tag",
        ["compiler"],
        tmp_path,
        platform="linux/amd64",
        timeout_sec=5,
    )
    assert result["status"] == "memory-limit"
    assert result["oom_killed"]
    create = next(c for c in commands if c[1] == "create")
    assert create[create.index("--memory") + 1] == str(5 * 1024**3)
    assert create[create.index("--memory-swap") + 1] == str(5 * 1024**3)
    assert "sha256:locked" in create
    assert commands[-1] == ["docker", "rm", "--force", "owned-id"]
    assert json.loads((tmp_path / "container.json").read_text())["status"] == "memory-limit"


def test_container_timeout_kills_actual_container(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    commands = fake_docker(monkeypatch, timeout=True)
    result = reproduction_process.run_container(
        "pinned:tag",
        ["compiler"],
        tmp_path,
        platform="linux/amd64",
        timeout_sec=0.01,
    )
    assert result["status"] == "timed-out"
    assert ["docker", "kill", "owned-id"] in commands
    assert commands[-1] == ["docker", "rm", "--force", "owned-id"]


def test_low_disk_refuses_before_container_creation(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    commands = fake_docker(monkeypatch)
    usage = shutil.disk_usage(tmp_path)
    monkeypatch.setattr(reproduction_process.shutil, "disk_usage", lambda _: usage._replace(free=0))
    with pytest.raises(ValueError, match="disk"):
        reproduction_process.run_container("image", ["compiler"], tmp_path, platform="linux/amd64")
    assert not commands


def test_monitor_failure_stops_actual_container(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    commands = fake_docker(monkeypatch, timeout=True)
    original = reproduction_process.subprocess.run

    def docker(args: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        if args[1] == "exec":
            return subprocess.CompletedProcess(args, 1, "", "monitor unavailable")
        return original(args, **kwargs)

    monkeypatch.setattr(reproduction_process.subprocess, "run", docker)
    result = reproduction_process.run_container("image", ["compiler"], tmp_path, platform="linux/amd64")
    assert result["status"] == "resource-stopped"
    assert "monitoring failed" in result["message"]
    assert ["docker", "kill", "owned-id"] in commands
    assert commands[-1] == ["docker", "rm", "--force", "owned-id"]


def test_cancellation_still_removes_container_and_saves_receipt(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    commands = fake_docker(monkeypatch, timeout=True)
    original = reproduction_process.subprocess.run

    def docker(args: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        if args[1] == "exec":
            raise KeyboardInterrupt
        return original(args, **kwargs)

    monkeypatch.setattr(reproduction_process.subprocess, "run", docker)
    with pytest.raises(KeyboardInterrupt):
        reproduction_process.run_container("image", ["compiler"], tmp_path, platform="linux/amd64")
    assert commands[-1] == ["docker", "rm", "--force", "owned-id"]
    assert json.loads((tmp_path / "container.json").read_text())["status"] == "cancelled"


def test_uncertain_create_still_removes_its_unique_owned_name(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    commands = fake_docker(monkeypatch)
    original = reproduction_process.subprocess.run

    def docker(args: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        if args[1] == "create":
            original(args, **kwargs)  # daemon-side creation happened; client response was lost
            raise subprocess.TimeoutExpired(args, 15)
        return original(args, **kwargs)

    monkeypatch.setattr(reproduction_process.subprocess, "run", docker)
    result = reproduction_process.run_container("image", ["compiler"], tmp_path, platform="linux/amd64")
    name = next(c for c in commands if c[1] == "create")[3]
    assert name.startswith("egglog-reproduction-")
    assert ["docker", "kill", name] in commands
    assert commands[-1] == ["docker", "rm", "--force", name]
    assert result["status"] == "resource-stopped"
    assert result["cleanup_confirmed"]
    assert not any(c[1] == "start" for c in commands)


def test_fast_zero_exit_requires_final_memory_telemetry(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    commands = fake_docker(monkeypatch, telemetry=False)
    result = reproduction_process.run_container("image", ["compiler"], tmp_path, platform="linux/amd64")
    assert result["status"] == "resource-stopped"
    assert "telemetry" in result["message"]
    assert result["returncode"] == 0
    assert not any(command[1] == "exec" for command in commands)
    assert result["cleanup_confirmed"]


def test_fast_parent_cannot_hide_an_oom_killed_child(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    fake_docker(monkeypatch, child_oom=True)
    result = reproduction_process.run_container("image", ["compiler"], tmp_path, platform="linux/amd64")
    assert result["returncode"] == 0
    assert result["status"] == "memory-limit"
    assert result["oom_killed"]
    assert result["cleanup_confirmed"]


@pytest.mark.parametrize("available_gib,missing_events,expected_exit", [(6, False, 125), (8, True, 125), (8, False, 0)])
def test_wrapper_checks_vm_before_work_and_rejects_failed_counter_copy(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, available_gib: int, missing_events: bool, expected_exit: int
) -> None:
    real_run = subprocess.run
    commands = fake_docker(monkeypatch)
    reproduction_process.run_container("image", ["compiler"], tmp_path / "capture", platform="linux/amd64")
    create = next(c for c in commands if c[1] == "create")
    wrapper = create[create.index("-c") + 1]
    local = tmp_path / "shell-fixture"
    local.mkdir()
    monitor = local / "monitor"
    monitor.mkdir()
    (local / "meminfo").write_text(f"MemAvailable: {available_gib * 1024**2} kB\n")
    (local / "memory.peak").write_text("4096\n")
    if not missing_events:
        (local / "memory.events").write_text("oom_kill 0\n")
    wrapper = wrapper.replace("/reproduction-monitor", str(monitor))
    wrapper = wrapper.replace("/proc/meminfo", str(local / "meminfo"))
    wrapper = wrapper.replace("/sys/fs/cgroup", str(local))
    ran = local / "workload-started"
    # Execute only this bounded synthetic shell/marker fixture, never Docker.
    result = real_run(
        ["/bin/sh", "-c", wrapper, "fixture", "/usr/bin/touch", str(ran)], capture_output=True, text=True, timeout=5
    )
    assert result.returncode == expected_exit
    assert ran.exists() == (available_gib >= 7)
    if expected_exit:
        assert (monitor / "supervision-error").read_text()
    else:
        assert (monitor / "memory.peak").read_text() == "4096\n"
        assert (monitor / "memory.events").read_text() == "oom_kill 0\n"


@pytest.mark.parametrize("sample", ["", "123\noom_kill 0\n", "123\nMemAvailable: 9999999 kB\n"])
def test_partial_telemetry_fails_closed(sample: str) -> None:
    with pytest.raises(ValueError, match="incomplete container memory telemetry"):
        reproduction_process.parse_memory_sample(sample)


@pytest.mark.parametrize("running", [False, True])
def test_vm_current_availability_is_required_in_addition_to_configured_total(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, running: bool
) -> None:
    commands = fake_docker(
        monkeypatch,
        timeout=running,
        vm_preflight_bytes=8 * 1024**3 if running else 6 * 1024**3,
        vm_available_bytes=1024**3 if running else 8 * 1024**3,
    )
    result = reproduction_process.run_container("image", ["compiler"], tmp_path, platform="linux/amd64")
    assert result["status"] == "resource-stopped"
    assert "VM" in result["message"]
    create = next(c for c in commands if c[1] == "create")
    wrapper = create[create.index("-c") + 1]
    assert wrapper.index("MemAvailable:") < wrapper.index('"$@"; result=$?')
    assert str(7 * 1024**2) in wrapper  # 5 GiB cap + 2 GiB reserve, expressed in KiB
    assert result["cleanup_confirmed"]


@pytest.mark.parametrize("phase", ["kill", "inspect", "logs", "rm"])
def test_cleanup_failure_never_leaves_a_success_receipt(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, phase: str
) -> None:
    commands = fake_docker(monkeypatch)
    original = reproduction_process.subprocess.run
    inspections = 0

    def docker(args: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        nonlocal inspections
        if args[1] == "inspect":
            inspections += 1
        if args[1] == phase and (phase != "inspect" or inspections > 1):
            commands.append(args)
            raise subprocess.TimeoutExpired(args, 10)
        return original(args, **kwargs)

    monkeypatch.setattr(reproduction_process.subprocess, "run", docker)
    result = reproduction_process.run_container("image", ["compiler"], tmp_path, platform="linux/amd64")
    assert result["status"] == "resource-stopped"
    assert result["cleanup_errors"]
    assert result["cleanup_confirmed"] == (phase != "rm")
    assert commands[-1] == ["docker", "rm", "--force", "owned-id"]
    assert json.loads((tmp_path / "container.json").read_text())["status"] == "resource-stopped"


@pytest.mark.parametrize("stop", ["parent-exit", "timeout", "disk-monitor-error"])
def test_native_guard_kills_surviving_grandchildren(monkeypatch: pytest.MonkeyPatch, tmp_path: Path, stop: str) -> None:
    pid_path = tmp_path / "grandchild.pid"
    child = "import os,pathlib,time; pathlib.Path('grandchild.pid').write_text(str(os.getpid())); time.sleep(30)"
    parent = (
        f"import pathlib,subprocess,sys,time; subprocess.Popen([sys.executable, '-c', {child!r}]); "
        "\nwhile not pathlib.Path('grandchild.pid').exists(): time.sleep(0.01)\n"
        + ("" if stop == "parent-exit" else "time.sleep(30)\n")
    )
    usage = shutil.disk_usage(tmp_path)

    def disk_usage(_: Any) -> Any:
        if stop == "disk-monitor-error" and pid_path.exists():
            raise OSError("simulated filesystem monitor failure")
        return usage

    monkeypatch.setattr(pilot.shutil, "disk_usage", disk_usage)
    try:
        result = pilot.run_bounded_command(
            [sys.executable, "-c", parent],
            tmp_path,
            tmp_path / "descendants",
            require_guard=True,
            disk_reserve_bytes=1,
            timeout_sec=0.6,
        )
        assert (
            result.status
            == {"parent-exit": "success", "timeout": "timed-out", "disk-monitor-error": "resource-stopped"}[stop]
        )
        if stop == "disk-monitor-error":
            assert "disk monitoring failed" in str(result.message)
        assert pid_path.exists()
        pid = int(pid_path.read_text())
        # An orphan may briefly be a zombie until init reaps it; it cannot run
        # or allocate memory. Both absent and zombie states establish termination.
        state = ""
        for _ in range(40):
            state = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], capture_output=True, text=True).stdout.strip()
            if not state or state.startswith("Z"):
                break
            time.sleep(0.025)
        assert not state or state.startswith("Z"), f"grandchild {pid} survived guard cleanup: {state}"
    finally:
        if pid_path.exists():
            with suppress(ProcessLookupError):
                os.kill(int(pid_path.read_text()), signal.SIGKILL)
