"""Reproduction guards supervise the workload, including VM descendants."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
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


def fake_docker(monkeypatch: pytest.MonkeyPatch, *, oom: bool = False, timeout: bool = False) -> list[list[str]]:
    commands: list[list[str]] = []
    started = False

    def docker(args: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        nonlocal started
        commands.append(args)
        command = args[1:]
        if command[0] == "info":
            result: Any = {"MemTotal": 8 * 1024**3, "MemoryLimit": True, "SwapLimit": True, "CgroupVersion": "2"}
        elif command[:2] == ["image", "inspect"]:
            result = {"Id": "sha256:locked", "Os": "linux", "Architecture": "amd64"}
        elif command[0] == "create":
            return subprocess.CompletedProcess(args, 0, "owned-id\n", "")
        elif command[0] == "start":
            started = True
            return subprocess.CompletedProcess(args, 0, "owned-id\n", "")
        elif command[0] == "inspect":
            result = {"Running": started and timeout, "OOMKilled": oom, "ExitCode": 137 if oom else 0}
        elif command[0] == "exec":
            return subprocess.CompletedProcess(args, 0, "1024\noom_kill 0\n", "")
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
