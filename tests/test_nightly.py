"""Bound complete nightly jobs without tool bootstrap, builds or benchmarks."""

from __future__ import annotations

import argparse
import ast
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from benchmarking import collection, models, processes, targets, workloads
from benchmarking.reports.store import ReportStore
from scripts import nightly_bench as nightly

from .report_fixtures import make_target, make_timing_summary


@pytest.fixture
def nightly_case(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    path = tmp_path / "file.egg"
    path.write_text("(check (= 1 1))\n")
    file = models.FileSpec("file.egg", path, targets.sha256_file(path))
    resolved = {}
    for label in ("branch", "main"):
        binary = tmp_path / label
        binary.write_text(label)
        resolved[label] = make_target(target_label=label, binary_path=binary, binary_sha256=targets.sha256_file(binary))
    case: dict[str, Any] = {
        "targets": resolved,
        "builds": [],
        "runs": [],
        "preflights": [],
        "fetches": [],
        "file": file,
    }

    def resolve(groups: Any, *_args: Any, **_kwargs: Any) -> dict[models.TargetRequest, models.ResolvedTarget]:
        request, endpoints = groups[0]
        case["builds"].append(request.label)
        assert processes.COLLECTION_DEADLINE.get() is not None
        assert [endpoint.treatment for endpoint in endpoints] == ["off", "proof-testing"]
        return {request: resolved[request.label]}

    def measure(
        binary: Path, _cwd: Path, _file: models.FileSpec, treatment: str, *_args: Any
    ) -> collection.ProcessObservation:
        case["runs"].append((binary.name, treatment))
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(0.01, 1000), None), make_timing_summary()
        )

    monkeypatch.setattr(workloads, "resolve_files", lambda *_args: (file,))
    monkeypatch.setattr(collection, "resolve_targets", resolve)
    monkeypatch.setattr(
        collection, "preflight_collection", lambda plan, *_args: case["preflights"].append(plan.target.display_label)
    )
    monkeypatch.setattr(collection, "run_process", measure)
    monkeypatch.setattr(targets, "run_text", lambda command, *_a, **_k: case["fetches"].append(command))
    return case


def worker_args(output: Path) -> argparse.Namespace:
    output.mkdir(exist_ok=True)
    return argparse.Namespace(output_dir=output, rounds=1, timeout_sec=120, deadline=time.monotonic() + 60)


def test_worker_collects_only_checked_and_off_builds_once_and_renders_cached_reports(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any]
) -> None:
    args = worker_args(tmp_path / "output")
    assert nightly._collect(args) == 0
    assert nightly_case["builds"] == ["branch", "main"]
    assert nightly_case["fetches"] == [["git", "fetch", "origin", "+refs/heads/main:refs/remotes/origin/main"]]
    assert nightly_case["runs"] == [
        (label, treatment) for label in ("branch", "main") for treatment in ("off", "proof-testing")
    ]
    records = ReportStore(args.output_dir / "index.jsonl").records
    assert len(records) == 4 and {row["timeout_sec"] for row in records} == {120}
    assert processes.COLLECTION_DEADLINE.get() is None
    monkeypatch.setattr(collection, "resolve_targets", lambda *a, **k: pytest.fail("render must not resolve/build"))
    monkeypatch.setattr(collection, "collect_rows", lambda *a, **k: pytest.fail("render must not collect"))
    assert nightly._render(args) == 0
    assert (args.output_dir / "index.html").is_file()
    assert "proof-testing" in (args.output_dir / "branch-vs-main.md").read_text()


@pytest.mark.parametrize("after_rows", [0, 1, 2])
def test_worker_budget_keeps_completed_rows_and_renders_missing_endpoints(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any], after_rows: int
) -> None:
    measure = collection.run_process
    calls = 0

    def interrupted(*args: Any) -> collection.ProcessObservation:
        nonlocal calls
        calls += 1
        if calls > after_rows:
            raise processes.BudgetExpired("test collection deadline")
        return measure(*args)

    monkeypatch.setattr(collection, "run_process", interrupted)
    args = worker_args(tmp_path / "output")
    assert nightly._collect(args) == 1
    assert ReportStore(args.output_dir / "index.jsonl").row_count == after_rows
    assert calls == after_rows + 1
    assert nightly._render(args) == 0
    assert (args.output_dir / "index.html").is_file()
    assert "test collection deadline" in (args.output_dir / "status.txt").read_text()


def test_launched_workload_budget_expiry_is_retained_once_before_global_stop(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any]
) -> None:
    calls = []
    results = []

    def measure(
        binary: Path, _cwd: Path, _file: models.FileSpec, treatment: str, *_args: Any
    ) -> collection.ProcessObservation:
        calls.append((binary.name, treatment))
        result = processes.run_command([sys.executable, "-c", "import time; time.sleep(30)"], tmp_path, 120)
        results.append(result)
        return collection.ProcessObservation(result, None)

    monkeypatch.setattr(collection, "run_process", measure)
    args = worker_args(tmp_path / "output")
    args.deadline = time.monotonic() + 0.3
    assert nightly._collect(args) == 1
    rows = ReportStore(args.output_dir / "index.jsonl").records
    assert len(rows) == len(results) == 1
    result = results[0]
    assert result.stop_collection
    assert result.error is not None and "budget exhausted during workload" in result.error.message
    row = rows[0]
    assert row["status"] == "failure"
    assert row["timeout_sec"] == 120
    assert row["wall_sec"] is not None and 0 < row["wall_sec"] < 5
    assert row["max_rss_bytes"] is None
    assert row["error_message"] == result.error.message
    assert calls == [("branch", "off")]
    assert nightly_case["builds"] == ["branch"]
    assert nightly._render(args) == 0


def test_requested_workload_timeout_is_still_a_local_timeout(tmp_path: Path) -> None:
    token = processes.COLLECTION_DEADLINE.set(time.monotonic() + 10)
    try:
        result = processes.run_command([sys.executable, "-c", "import time; time.sleep(30)"], tmp_path, 1)
    finally:
        processes.COLLECTION_DEADLINE.reset(token)
    assert result.status == "timed-out"
    assert not result.stop_collection
    assert result.error is not None and result.error.message == "timed out after 1 seconds"
    assert result.timing == processes.TimingRow()


def test_unsupported_main_is_fatal_and_preserves_branch_rows(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any]
) -> None:
    def preflight(plan: collection.CollectionPlan, *_args: Any) -> None:
        if plan.target.display_label == "main":
            raise ValueError("main does not support --memory-limit-bytes")

    monkeypatch.setattr(collection, "preflight_collection", preflight)
    args = worker_args(tmp_path / "output")
    assert nightly._collect(args) == 1
    assert nightly_case["runs"] == [("branch", "off"), ("branch", "proof-testing")]
    assert ReportStore(args.output_dir / "index.jsonl").row_count == 2
    assert nightly._render(args) == 0
    assert "missing" in (args.output_dir / "branch-vs-main.md").read_text().lower()


def test_fetch_deadline_preserves_branch_and_never_builds_main(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any]
) -> None:
    def expired(*_args: Any, **_kwargs: Any) -> str:
        raise processes.BudgetExpired("fetch deadline")

    monkeypatch.setattr(targets, "run_text", expired)
    args = worker_args(tmp_path / "output")
    assert nightly._collect(args) == 1
    assert nightly_case["builds"] == ["branch"]
    assert nightly_case["runs"] == [("branch", "off"), ("branch", "proof-testing")]
    assert ReportStore(args.output_dir / "index.jsonl").row_count == 2
    assert nightly._render(args) == 0
    assert "fetch deadline" in (args.output_dir / "status.txt").read_text()


def test_identical_binaries_share_rows_without_fabricated_distinct_endpoints(
    tmp_path: Path, nightly_case: dict[str, Any]
) -> None:
    nightly_case["targets"]["main"] = nightly_case["targets"]["branch"]
    args = worker_args(tmp_path / "output")
    assert nightly._collect(args) == 0
    assert len(nightly_case["runs"]) == 2
    assert nightly._render(args) == 0
    assert "same executable" in (args.output_dir / "branch-vs-main.md").read_text()


@pytest.mark.parametrize("expired_phase", [None, "bootstrap", "collect", "render"])
def test_supervisor_budget_covers_bootstrap_workers_and_final_render(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, expired_phase: str | None
) -> None:
    now = [100.0]
    phases = []
    output = tmp_path / "output"
    monkeypatch.setattr(nightly, "time", SimpleNamespace(monotonic=lambda: now[0]))
    monkeypatch.setattr(nightly, "_worker_command", lambda args, phase, deadline: [phase, str(deadline)])

    def run(command: Any, deadline: float, env: Any) -> int:
        phase = "bootstrap" if command == nightly.BOOTSTRAP_COMMAND else command[0]
        phases.append((phase, deadline))
        assert now[0] < deadline
        if phase == "collect":
            (output / nightly.STATE_NAME).write_text("{}")
        if phase == expired_phase:
            now[0] = deadline
            raise subprocess.TimeoutExpired(command, 1)
        now[0] += 1
        return 0

    monkeypatch.setattr(nightly, "_run_phase", run)
    assert nightly.main([str(output), "--budget-sec", "130"]) == int(expired_phase is not None)
    assert phases[0] == ("bootstrap", 105.0)
    if expired_phase != "bootstrap":
        assert phases[1] == ("collect", 110.0)
        assert phases[2] == ("render", 230.0)
    assert (output / "index.html").is_file()


@pytest.mark.parametrize("spawn_sec", [3, 12])
def test_phase_spawn_time_consumes_the_absolute_deadline(monkeypatch: pytest.MonkeyPatch, spawn_sec: int) -> None:
    now = [100.0]
    waits = []
    killed = []
    monkeypatch.setattr(nightly, "time", SimpleNamespace(monotonic=lambda: now[0]))

    def wait(timeout: float | None = None) -> int:
        waits.append(timeout)
        if timeout is not None:
            raise subprocess.TimeoutExpired("render", timeout)
        return 0

    def spawn(*_args: Any, **_kwargs: Any) -> SimpleNamespace:
        now[0] += spawn_sec
        return SimpleNamespace(pid=12345, wait=wait)

    monkeypatch.setattr(subprocess, "Popen", spawn)
    monkeypatch.setattr(os, "killpg", lambda pid, sig: killed.append(pid))
    with pytest.raises(subprocess.TimeoutExpired):
        nightly._run_phase(["render"], 110, {})
    assert waits == [max(0, 10 - spawn_sec), None]
    assert killed == [12345]


@pytest.mark.parametrize("failed_phase,context_saved", [("collect", False), ("collect", True), ("render", True)])
def test_nonzero_worker_exits_are_reported_without_losing_partial_rows(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, failed_phase: str, context_saved: bool
) -> None:
    output = tmp_path / "output"
    phases = []
    monkeypatch.setattr(nightly, "_worker_command", lambda args, phase, deadline: [phase])

    def run(command: Any, _deadline: float, _env: Any) -> int:
        phase = "bootstrap" if command == nightly.BOOTSTRAP_COMMAND else command[0]
        phases.append(phase)
        if phase == "collect":
            (output / "index.jsonl").write_text('{"completed":true}\n')
            if context_saved:
                (output / nightly.STATE_NAME).write_text("{}")
        return 23 if phase == failed_phase else 0

    monkeypatch.setattr(nightly, "_run_phase", run)
    assert nightly.main([str(output)]) == 1
    label = "collection" if failed_phase == "collect" else "render"
    assert f"{label} worker exited with status 23" in (output / nightly.STATUS_NAME).read_text()
    assert json.loads((output / "index.jsonl").read_text()) == {"completed": True}
    assert phases == ["bootstrap", "collect", *(["render"] if context_saved else [])]


def test_host_entrypoint_is_stdlib_python38_and_make_starts_it_before_bootstrap() -> None:
    source = Path(nightly.__file__).read_text()
    ast.parse(source, feature_version=(3, 8))
    makefile = (nightly.REPO_ROOT / "Makefile").read_text()
    assert "nightly: nightly-uv" not in makefile
    assert "nightly-local: nightly-uv" not in makefile
    assert "$(HOST_PYTHON) scripts/nightly_bench.py" in makefile
    assert len(nightly.WORKLOADS) == 7 and len(set(nightly.WORKLOADS)) == 7
    assert all((nightly.REPO_ROOT / path).is_file() for path in nightly.WORKLOADS)


def test_override_cannot_extend_two_hour_budget(tmp_path: Path) -> None:
    with pytest.raises(SystemExit):
        nightly.main([str(tmp_path), "--budget-sec", "7201", "--rounds", "1000"])


def test_supervisor_final_timeout_reaps_fake_render_process(tmp_path: Path) -> None:
    pidfile = tmp_path / "render.pid"
    command = [
        sys.executable,
        "-c",
        f"import os,time;open({str(pidfile)!r},'w').write(str(os.getpid()));time.sleep(30)",
    ]
    with pytest.raises(subprocess.TimeoutExpired):
        nightly._run_phase(command, time.monotonic() + 0.3, os.environ.copy())
    pid = int(pidfile.read_text())
    with pytest.raises(ProcessLookupError):
        os.kill(pid, 0)


def test_real_fake_job_reaps_separately_sessioned_workload_before_partial_render(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    output = tmp_path / "output"
    child_pid = tmp_path / "measured.pid"
    measured_program = f"import os,time;open({str(child_pid)!r},'w').write(str(os.getpid()));time.sleep(30)"
    worker = tmp_path / "worker.py"
    worker.write_text(
        "import json,sys,time\nfrom pathlib import Path\n"
        f"sys.path.insert(0,{str(nightly.REPO_ROOT)!r})\n"
        "from benchmarking.processes import COLLECTION_DEADLINE,run_command\n"
        "phase,out,deadline=sys.argv[1],Path(sys.argv[2]),float(sys.argv[3])\n"
        "if phase=='collect':\n"
        " (out/'index.jsonl').write_text('{\"completed\":true}\\n')\n"
        " (out/'nightly-context.json').write_text('{}')\n"
        " COLLECTION_DEADLINE.set(deadline)\n"
        f" result=run_command([sys.executable,'-c',{measured_program!r}],out,30)\n"
        " assert result.stop_collection and result.error is not None\n"
        " assert 'budget exhausted during workload' in result.error.message\n"
        " (out/'owner-cleaned').write_text('yes')\n"
        "else:\n"
        " assert (out/'owner-cleaned').read_text()=='yes'\n"
        " (out/'index.html').write_text('retained partial data')\n"
    )
    monkeypatch.setattr(nightly, "BOOTSTRAP_COMMAND", (sys.executable, "-c", "pass"))
    monkeypatch.setattr(nightly, "RENDER_RESERVE_SEC", 0.5)
    monkeypatch.setattr(nightly, "CLEANUP_RESERVE_SEC", 0.25)
    monkeypatch.setattr(
        nightly,
        "_worker_command",
        lambda args, phase, deadline: [sys.executable, str(worker), phase, str(args.output_dir), str(deadline)],
    )
    started = time.monotonic()
    assert nightly.main([str(output), "--budget-sec", "3"]) == 0
    assert time.monotonic() - started < 4
    assert (output / "index.html").read_text() == "retained partial data"
    assert json.loads((output / "index.jsonl").read_text()) == {"completed": True}
    with pytest.raises(ProcessLookupError):
        os.kill(int(child_pid.read_text()), 0)


def test_supervisor_cancellation_gives_owner_time_to_reap_separate_session(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    pidfile = tmp_path / "measured.pid"
    cleanup = tmp_path / "cleaned"
    program = f"import os,time;open({str(pidfile)!r},'w').write(str(os.getpid()));time.sleep(30)"
    owner = tmp_path / "owner.py"
    owner.write_text(
        "import signal,sys\nfrom pathlib import Path\n"
        f"sys.path.insert(0,{str(nightly.REPO_ROOT)!r})\n"
        "from benchmarking.processes import run_command\n"
        "def interrupted(*args): raise KeyboardInterrupt\n"
        "signal.signal(signal.SIGTERM,interrupted)\n"
        "try:\n"
        f" run_command([sys.executable,'-c',{program!r}],Path.cwd(),30)\n"
        "except KeyboardInterrupt:\n"
        f" Path({str(cleanup)!r}).write_text('reaped')\n"
    )
    popen = subprocess.Popen

    def cancel_after_child_starts(*args: Any, **kwargs: Any) -> subprocess.Popen[Any]:
        process = popen(*args, **kwargs)
        wait = process.wait
        first = True

        def wait_then_cancel(timeout: float | None = None) -> int:
            nonlocal first
            if first:
                first = False
                deadline = time.monotonic() + 2
                while not pidfile.is_file() and time.monotonic() < deadline:
                    time.sleep(0.01)
                assert pidfile.is_file(), "fake measurement did not start"
                raise KeyboardInterrupt
            return wait(timeout)

        monkeypatch.setattr(process, "wait", wait_then_cancel)
        return process

    monkeypatch.setattr(subprocess, "Popen", cancel_after_child_starts)
    with pytest.raises(KeyboardInterrupt):
        nightly._run_phase([sys.executable, str(owner)], time.monotonic() + 4, os.environ.copy())
    assert cleanup.read_text() == "reaped"
    with pytest.raises(ProcessLookupError):
        os.kill(int(pidfile.read_text()), 0)


def test_ordinary_workload_failure_keeps_other_conditions(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any]
) -> None:
    measure = collection.run_process

    def fails_once(*args: Any) -> collection.ProcessObservation:
        result = measure(*args)
        if args[0].name == "branch" and args[3] == "proof-testing":
            return collection.ProcessObservation(
                processes.TimingResult("failure", processes.TimingRow(0.01), processes.ErrorRow("bad proof")), None
            )
        return result

    monkeypatch.setattr(collection, "run_process", fails_once)
    args = worker_args(tmp_path / "output")
    assert nightly._collect(args) == 0
    rows = ReportStore(args.output_dir / "index.jsonl").records
    assert len(rows) == 4 and sum(row["status"] == "failure" for row in rows) == 1
    assert nightly_case["runs"][-2:] == [("main", "off"), ("main", "proof-testing")]


def test_expired_owner_deadlines_prevent_setup_and_workload_spawns(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("expired budget must not spawn"))
    token = processes.COLLECTION_DEADLINE.set(time.monotonic() - 1)
    try:
        with pytest.raises(processes.BudgetExpired):
            processes.run_command(["engine"], tmp_path, 120)
        with pytest.raises(processes.BudgetExpired):
            targets.run_text(["git", "fetch"], tmp_path)
    finally:
        processes.COLLECTION_DEADLINE.reset(token)


def test_setup_owner_timeout_reaps_its_process_group(tmp_path: Path) -> None:
    pidfile = tmp_path / "setup.pid"
    command = [
        sys.executable,
        "-c",
        f"import os,time;open({str(pidfile)!r},'w').write(str(os.getpid()));time.sleep(30)",
    ]
    token = processes.COLLECTION_DEADLINE.set(time.monotonic() + 0.3)
    try:
        with pytest.raises(processes.BudgetExpired):
            targets.run_text(command, tmp_path)
    finally:
        processes.COLLECTION_DEADLINE.reset(token)
    with pytest.raises(ProcessLookupError):
        os.kill(int(pidfile.read_text()), 0)


def test_build_uses_the_same_owned_setup_deadline(monkeypatch: pytest.MonkeyPatch) -> None:
    from rich.console import Console

    calls = []

    def expired(command: Any, cwd: Path, **kwargs: Any) -> str:
        calls.append((command, kwargs))
        assert processes.COLLECTION_DEADLINE.get() is not None
        raise processes.BudgetExpired("build budget")

    monkeypatch.setattr(targets, "run_text", expired)
    token = processes.COLLECTION_DEADLINE.set(time.monotonic() + 1)
    try:
        with pytest.raises(processes.BudgetExpired):
            targets.build_target(make_target().row, Console())
    finally:
        processes.COLLECTION_DEADLINE.reset(token)
    assert calls[0][0][:2] == ["cargo", "build"]
    assert calls[0][1] == {"capture_output": False}
