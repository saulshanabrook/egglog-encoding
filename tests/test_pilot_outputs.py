"""Protect admission evidence and measured rows from coverage output collisions."""

from __future__ import annotations

import json
import signal
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from benchmarking import pilot
from benchmarking.targets import sha256_file

from .report_fixtures import make_record


@pytest.mark.parametrize("mode", ["default", "sample-error", "cleanup-error", "immediate-exit", "cleanup-interrupt"])
def test_optional_descendant_hooks_always_preserve_root_cleanup(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mode: str
) -> None:
    events: list[Any] = []
    polls = iter([0] if mode == "immediate-exit" else [None, 0])
    process = SimpleNamespace(pid=123, returncode=0, poll=lambda: next(polls), wait=lambda: events.append("wait"))
    monkeypatch.setattr(pilot.subprocess, "Popen", lambda *_args, **_kwargs: process)
    exits = iter([SimpleNamespace(si_pid=123)] if mode == "immediate-exit" else [None, SimpleNamespace(si_pid=123)])
    monkeypatch.setattr(pilot.os, "waitid", lambda *_: next(exits))
    monkeypatch.setattr(pilot.MemoryGuard, "from_environment", lambda **_: None)

    def default_sample(pid: int) -> int:
        events.append(("default-rss", pid))
        return 5

    monkeypatch.setattr(pilot, "group_rss_bytes", default_sample)
    monkeypatch.setattr(pilot.os, "killpg", lambda *args: events.append(("killpg", *args)))
    monkeypatch.setattr(pilot.time, "sleep", lambda _: None)

    def sample(pid: int) -> int:
        events.append(("custom-rss", pid))
        if mode == "sample-error":
            raise RuntimeError("custom monitor failed")
        return 7

    def cleanup() -> None:
        events.append("descendant-cleanup")
        if mode == "cleanup-error":
            raise RuntimeError("custom cleanup failed")
        if mode == "cleanup-interrupt":
            raise KeyboardInterrupt

    kwargs: dict[str, Any] = {} if mode == "default" else {"sample_rss": sample, "cleanup_descendants": cleanup}
    if mode == "cleanup-interrupt":
        with pytest.raises(KeyboardInterrupt):
            pilot.run_bounded_command(["never-executed"], tmp_path, tmp_path / "output", **kwargs)
    else:
        result = pilot.run_bounded_command(["never-executed"], tmp_path, tmp_path / "output", **kwargs)
        if mode in {"sample-error", "cleanup-error"}:
            assert result.status == "resource-stopped" and "failed" in str(result.message)
        else:
            assert result.status == "success"
    assert events[-2:] == [("killpg", 123, signal.SIGKILL), "wait"]
    if mode == "default":
        assert events[0] == ("default-rss", 123) and "descendant-cleanup" not in events
    else:
        assert "descendant-cleanup" in events
    if mode == "immediate-exit":
        assert not any(isinstance(event, tuple) and event[0] == "custom-rss" for event in events)


def test_pilot_evidence_cannot_alias_an_empty_measured_cache(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: Any
) -> None:
    report = tmp_path / "measurements.jsonl"
    report.write_text("")
    evidence = tmp_path / "evidence.jsonl"
    evidence.symlink_to(report)
    monkeypatch.setattr(
        pilot, "resolve_suite", lambda *_args: pytest.fail("collision must fail before suite resolution")
    )
    monkeypatch.setattr(pilot, "run_bounded_command", lambda *_args, **_kwargs: pytest.fail("must not run an engine"))

    result = pilot.main(["--suite", "eggcc", "--report", str(report), "--evidence", str(evidence)])

    assert result == 2
    assert "pilot evidence must differ from the benchmark report" in capsys.readouterr().err
    assert report.read_bytes() == b""


@pytest.mark.parametrize("protected_input", ["report", "evidence"])
@pytest.mark.parametrize("colliding_output", ["json", "markdown"])
def test_coverage_outputs_cannot_overwrite_inputs_before_pilot_execution(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
    protected_input: str,
    colliding_output: str,
) -> None:
    inputs = {name: tmp_path / f"{name}.jsonl" for name in ("report", "evidence")}
    if colliding_output == "markdown":
        inputs[protected_input] = inputs[protected_input].with_suffix(".md")
    inputs["report"].write_text(json.dumps(make_record(0, started_at="2026-09-21T00:00:00Z")) + "\n")
    inputs["evidence"].write_text(json.dumps({"identity": {}, "status": "admitted", "reason": None}) + "\n")
    output = inputs[protected_input]
    if colliding_output == "markdown":
        output = output.with_suffix(".json")
    for path in (output, output.with_suffix(".md")):
        if not path.exists():
            path.write_text("previous coverage output\n")
    before = {path: path.read_bytes() for path in tmp_path.iterdir()}
    monkeypatch.setattr(pilot, "__file__", str(tmp_path / "benchmarking/pilot.py"))
    monkeypatch.setattr(
        pilot, "resolve_suite", lambda *_args: pytest.fail("collision must fail before suite resolution")
    )
    monkeypatch.setattr(pilot, "run_bounded_command", lambda *_args, **_kwargs: pytest.fail("must not run an engine"))

    result = pilot.main(
        [
            "--suite",
            "eggcc",
            "--report",
            str(inputs["report"]),
            "--evidence",
            str(inputs["evidence"]),
            "--coverage-output",
            str(output),
        ]
    )

    assert result == 2
    assert "coverage output must differ" in capsys.readouterr().err
    assert {path: path.read_bytes() for path in tmp_path.iterdir()} == before


def test_coverage_json_and_markdown_cannot_share_an_output_path(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
) -> None:
    output = tmp_path / "coverage.md"
    monkeypatch.setattr(
        pilot, "resolve_suite", lambda *_args: pytest.fail("collision must fail before suite resolution")
    )

    result = pilot.main(["--suite", "eggcc", "--coverage-output", str(output)])

    assert result == 2
    assert "coverage JSON and Markdown outputs must use different paths" in capsys.readouterr().err
    assert not output.exists()


@pytest.mark.parametrize("coverage_only", [False, True])
def test_coverage_includes_normal_only_calls_but_pilot_never_prepares_them(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, coverage_only: bool
) -> None:
    (tmp_path / "benchmarks").mkdir()
    (tmp_path / "paired.egg").write_text("(check (= 1 1))\n")
    normal = tmp_path / "normal.egg"
    normal.write_text("(run 1)\n")
    (tmp_path / "benchmarks/catalog.json").write_text(
        json.dumps(
            {
                "families": {"dialegg": {}},
                "cases": [
                    {
                        "id": "application",
                        "family": "dialegg",
                        "source": "application.mlir",
                        "status": "captured",
                        "workloads": ["paired.egg"],
                        "normal_workloads": [
                            {"path": "normal.egg", "proof_blocker": "No derived query", "invocation": 1}
                        ],
                    }
                ],
            }
        )
    )
    binary = tmp_path / "egglog"
    binary.write_bytes(b"fixture executable identity; never run")
    report = tmp_path / "measurements.jsonl"
    report.write_text(
        json.dumps(
            make_record(
                0,
                started_at="2026-09-24T00:00:00Z",
                file_sha256=sha256_file(normal),
                binary_sha256=sha256_file(binary),
                treatment="off",
            )
        )
        + "\n"
    )
    before = report.read_bytes()
    output = tmp_path / "coverage.json"
    prepared: list[str] = []

    def prepare(
        file: Any, family: str, _binaries: Any, hashes: Any, root: Path, _logs: Any, policy: Any, **_kw: Any
    ) -> Any:
        prepared.append(file.display_path)
        return {
            "identity": pilot.pilot_identity(file, family, hashes, policy, root),
            "status": "admitted",
            "reason": None,
        }

    monkeypatch.setattr(pilot, "__file__", str(tmp_path / "benchmarking/pilot.py"))
    monkeypatch.setattr(pilot, "git_sha", lambda _root: "fixture")
    monkeypatch.setattr(pilot, "git_dirty", lambda _root: False)
    monkeypatch.setattr(pilot, "pilot_workload", prepare)
    monkeypatch.setattr(pilot, "run_bounded_command", lambda *_args, **_kwargs: pytest.fail("must not run an engine"))
    args = [
        "--suite",
        "dialegg",
        "--egglog-binary",
        str(binary),
        "--report",
        str(report),
        "--coverage-output",
        str(output),
    ]
    if coverage_only:
        args.append("--coverage-only")
    assert pilot.main(args) == 0
    coverage = json.loads(output.read_text())
    assert coverage["expected_cases"] == 1
    assert coverage["unique_captured_workloads"] == (2 if coverage_only else 1)
    assert prepared == ([] if coverage_only else ["paired.egg"])
    assert report.read_bytes() == before
    if coverage_only:
        result = coverage["cases"][0]["workloads"][1]
        assert result["preparation_status"] == "proof-query-blocked"
        assert result["preparation_reason"] == "No derived query"
        assert result["measurements"] == [{"treatment": "off", "status": "success", "timeout_sec": 120, "rows": 1}]


@pytest.mark.parametrize("failure", [None, "waitid", "cleanup", "interrupt"])
def test_scoped_cleanup_retains_root_identity_and_stops_root_before_drain(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, failure: str | None
) -> None:
    events: list[Any] = []
    process = SimpleNamespace(
        pid=123, returncode=None, poll=lambda: pytest.fail("custom cleanup must not reap with poll")
    )

    def wait() -> int:
        events.append("wait")
        process.returncode = 7
        return 7

    process.wait = wait
    monkeypatch.setattr(pilot.subprocess, "Popen", lambda *_a, **_k: process)
    monkeypatch.setattr(pilot.MemoryGuard, "from_environment", lambda **_: None)
    monkeypatch.setattr(pilot.os, "killpg", lambda *args: events.append(("kill", *args)))

    def waitid(kind: int, pid: int, flags: int) -> Any:
        events.append(("waitid", kind, pid, flags))
        assert flags & pilot.os.WNOWAIT
        if failure == "waitid":
            raise OSError("cannot observe root")
        return SimpleNamespace(si_pid=pid)

    monkeypatch.setattr(pilot.os, "waitid", waitid)

    def cleanup() -> None:
        events.append("drain")
        if failure == "cleanup":
            raise ValueError("cleanup failed")
        if failure == "interrupt":
            raise KeyboardInterrupt

    if failure == "interrupt":
        with pytest.raises(KeyboardInterrupt):
            pilot.run_bounded_command(["fake"], tmp_path, tmp_path / "run", cleanup_descendants=cleanup)
    else:
        result = pilot.run_bounded_command(["fake"], tmp_path, tmp_path / "run", cleanup_descendants=cleanup)
        assert result.returncode == 7  # Actual final wait, never the waitid status.
        assert result.status == ("resource-stopped" if failure else "failure")
    assert events[1:] == [("kill", 123, signal.SIGKILL), "drain", ("kill", 123, signal.SIGKILL), "wait"]


def test_scoped_cleanup_requires_wnowait_before_spawning(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delattr(pilot.os, "WNOWAIT")
    monkeypatch.setattr(pilot.subprocess, "Popen", lambda *_a, **_k: pytest.fail("unsupported guard must not spawn"))
    with pytest.raises(ValueError, match="non-consuming root exit"):
        pilot.run_bounded_command(["fake"], tmp_path, tmp_path / "run", cleanup_descendants=lambda: None)


def test_default_runner_still_propagates_unexpected_monitor_bug(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events = []
    process = SimpleNamespace(pid=123, returncode=None, poll=lambda: None, wait=lambda: events.append("wait"))
    monkeypatch.setattr(pilot.subprocess, "Popen", lambda *_a, **_kw: process)
    monkeypatch.setattr(pilot.MemoryGuard, "from_environment", lambda **_: SimpleNamespace(check=lambda _: None))
    monkeypatch.setattr(pilot.os, "killpg", lambda *_: events.append("kill"))

    def broken(_pid: int) -> int:
        raise RuntimeError("unexpected implementation bug")

    monkeypatch.setattr(pilot, "group_rss_bytes", broken)
    with pytest.raises(RuntimeError, match="unexpected implementation bug"):
        pilot.run_bounded_command(["fake"], tmp_path, tmp_path / "run")
    assert events == ["kill", "wait"]


@pytest.mark.parametrize(
    "group",
    [
        "empty",
        "zombie",
        "unrelated-live",
        "live-child",
        "unknown-state",
        "malformed",
        "duplicate",
        "monitor-error",
        "root-running",
        "wrong-root",
        "linux",
    ],
)
def test_permission_error_is_waived_only_for_confirmed_exited_empty_macos_group(
    monkeypatch: pytest.MonkeyPatch, group: str
) -> None:
    monkeypatch.setattr(pilot.sys, "platform", "linux" if group == "linux" else "darwin")

    def denied(*_args: Any) -> None:
        raise PermissionError(1, "Operation not permitted")

    monkeypatch.setattr(pilot.os, "killpg", denied)

    def exited(_kind: int, pid: int, flags: int) -> Any:
        assert flags & pilot.os.WNOWAIT
        return None if group == "root-running" else SimpleNamespace(si_pid=999 if group == "wrong-root" else pid)

    monkeypatch.setattr(pilot.os, "waitid", exited)
    snapshots = {
        "empty": "",
        "zombie": "123 123 Z\n",
        "unrelated-live": "123 123 Z+\n999 999 R\n",
        "live-child": "123 123 Z\n124 123 S\n",
        "unknown-state": "123 123 ?\n",
        "malformed": "123 123\n",
        "duplicate": "123 123 Z\n123 123 Z\n",
    }

    def snapshot(*args: Any, **kwargs: Any) -> Any:
        assert args == (["ps", "-axo", "pid=,pgid=,stat="],) and kwargs["check"] and kwargs["timeout"] == 1
        if group == "monitor-error":
            raise OSError("monitor unavailable")
        if group not in snapshots:
            pytest.fail("unconfirmed root must not waive EPERM using telemetry")
        return SimpleNamespace(stdout=snapshots[group])

    monkeypatch.setattr(pilot.subprocess, "run", snapshot)
    if group in {"empty", "zombie", "unrelated-live"}:
        pilot._kill_retained_root_group(123)
    else:
        with pytest.raises((PermissionError, OSError, ValueError)):
            pilot._kill_retained_root_group(123)


@pytest.mark.parametrize("failed_signals", [{1}, {2}, {1, 2}])
@pytest.mark.parametrize("callback_fails", [False, True])
def test_signal_failures_cannot_skip_callback_or_wait_and_remain_failures(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, failed_signals: set[int], callback_fails: bool
) -> None:
    events: list[str] = []
    process = SimpleNamespace(pid=123, returncode=None, poll=lambda: pytest.fail("must retain root"))

    def wait() -> int:
        events.append("wait")
        process.returncode = 0
        return 0

    process.wait = wait
    monkeypatch.setattr(pilot.subprocess, "Popen", lambda *_a, **_k: process)
    monkeypatch.setattr(pilot.MemoryGuard, "from_environment", lambda **_: None)
    monkeypatch.setattr(pilot.os, "waitid", lambda *_: SimpleNamespace(si_pid=123))
    count = 0

    def signal_root(_pid: int) -> None:
        nonlocal count
        count += 1
        events.append(f"signal{count}")
        if count in failed_signals:
            raise PermissionError(1, f"denied phase {count}")

    monkeypatch.setattr(pilot, "_kill_retained_root_group", signal_root)

    def cleanup() -> None:
        events.append("callback")
        if callback_fails:
            raise ValueError("callback failure")

    result = pilot.run_bounded_command(["fake"], tmp_path, tmp_path / "run", cleanup_descendants=cleanup)
    assert events == ["signal1", "callback", "signal2", "wait"]
    assert result.status == "resource-stopped" and result.returncode == 0
    for number in failed_signals:
        assert f"denied phase {number}" in str(result.message)
    assert ("callback failure" in str(result.message)) is callback_fails


@pytest.mark.parametrize("interrupted_signal", [1, 2])
def test_signal_interruption_still_runs_callback_and_final_wait(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, interrupted_signal: int
) -> None:
    events: list[str] = []
    process = SimpleNamespace(pid=123, returncode=0, wait=lambda: events.append("wait"))
    monkeypatch.setattr(pilot.subprocess, "Popen", lambda *_a, **_k: process)
    monkeypatch.setattr(pilot.MemoryGuard, "from_environment", lambda **_: None)
    monkeypatch.setattr(pilot.os, "waitid", lambda *_: SimpleNamespace(si_pid=123))
    count = 0

    def signal_root(_pid: int) -> None:
        nonlocal count
        count += 1
        events.append(f"signal{count}")
        if count == interrupted_signal:
            raise KeyboardInterrupt

    monkeypatch.setattr(pilot, "_kill_retained_root_group", signal_root)
    with pytest.raises(KeyboardInterrupt):
        pilot.run_bounded_command(
            ["fake"], tmp_path, tmp_path / "run", cleanup_descendants=lambda: events.append("callback")
        )
    assert events == ["signal1", "callback", "signal2", "wait"]
