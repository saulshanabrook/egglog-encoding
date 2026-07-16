"""Test subprocess accounting and same-run timing-summary capture."""

from __future__ import annotations

import io
import json
import resource
import signal
import sys
from pathlib import Path

import pytest

from benchmarking import collection, models, processes, targets
from benchmarking import output as runner_output

from .conftest import (
    ROOT,
)


def test_ru_maxrss_to_bytes_normalizes_platform_units() -> None:
    assert processes.ru_maxrss_to_bytes(123, platform="darwin") == 123
    assert processes.ru_maxrss_to_bytes(123, platform="linux") == 123 * 1024
    assert processes.ru_maxrss_to_bytes(0, platform="linux") is None


def test_run_command_records_signal_separately_from_exit_code() -> None:
    result = processes.run_command(
        [sys.executable, "-c", "import os, signal; os.kill(os.getpid(), signal.SIGTERM)"],
        ROOT,
        120,
    )

    assert result.status == "failure"
    assert result.error is not None
    assert result.error.exit_code is None
    assert result.error.signal == signal.SIGTERM


def test_run_process_passes_backend_flag_only_for_dd(monkeypatch: pytest.MonkeyPatch) -> None:
    commands: list[list[str]] = []
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")

    def fake_run_command(command: list[str], checkout_path: Path, timeout_sec: int) -> processes.TimingResult:
        commands.append(command)
        assert checkout_path == ROOT
        assert timeout_sec == 120
        summary_path = Path(command[command.index("--timing-summary") + 1])
        summary_path.write_text(
            json.dumps(
                {
                    "schema_version": 1,
                    "rulesets": [
                        {
                            "name": "rules",
                            "search_ns": 4,
                            "apply_ns": 6,
                            "merge_ns": 20,
                            "rebuild_ns": 30,
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
        return processes.TimingResult("success", processes.TimingRow(wall_sec=1.0), None)

    monkeypatch.setattr(collection, "run_command", fake_run_command)

    main = collection.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "main", "off", 120)
    dd = collection.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "dd", "proofs", 120)

    assert "--backend" not in commands[0]
    assert commands[1][commands[1].index("--backend") : commands[1].index("--backend") + 2] == [
        "--backend",
        "dd",
    ]
    assert "--proofs" in commands[1]
    assert main.timing_summary is not None
    assert main.timing_summary["rulesets"][0]["search_ns"] == 4
    assert main.timing_summary["rulesets"][0]["apply_ns"] == 6
    assert main.timing_summary["rulesets"][0]["merge_ns"] == 20
    assert dd.timing_summary is not None


def test_run_process_rejects_success_without_timing_summary(monkeypatch: pytest.MonkeyPatch) -> None:
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    monkeypatch.setattr(
        collection,
        "run_command",
        lambda *_args: processes.TimingResult("success", processes.TimingRow(wall_sec=1.0), None),
    )

    with pytest.raises(ValueError, match="did not produce --timing-summary"):
        collection.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "main", "off", 120)


def test_run_process_does_not_require_summary_after_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    failure = processes.TimingResult("failure", processes.TimingRow(wall_sec=1.0), processes.ErrorRow("failed"))
    monkeypatch.setattr(collection, "run_command", lambda *_args: failure)

    observation = collection.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "main", "off", 120)

    assert observation.result is failure
    assert observation.timing_summary is None


def test_workload_command_matches_benchmark_behavior() -> None:
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")

    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "main", "off") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        str(file_spec.absolute_path),
    ]
    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "dd", "proofs") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        "--backend",
        "dd",
        "--proofs",
        str(file_spec.absolute_path),
    ]

    facts = ROOT / "facts"
    file_with_facts = models.FileSpec(
        "file.egg",
        ROOT / "file.egg",
        "sha256:file",
        facts,
        "sha256:facts",
    )
    command = targets.workload_command(ROOT / "egglog-experimental", file_with_facts, "main", "proofs")
    assert command[5:7] == ["--fact-directory", str(facts)]


def test_run_command_records_peak_rss() -> None:
    result = processes.run_command([sys.executable, "-c", "print('ok')"], ROOT, 120)

    assert result.status == "success"
    assert result.timing.max_rss_bytes is not None
    assert result.timing.max_rss_bytes > 0


def test_run_command_can_require_capability_output() -> None:
    present = processes.run_command(
        [sys.executable, "-c", "print('--timing-summary PATH')"],
        ROOT,
        120,
        required_output="--timing-summary",
    )
    missing = processes.run_command(
        [sys.executable, "-c", "print('usage')"],
        ROOT,
        120,
        required_output="--timing-summary",
    )

    assert present.status == "success"
    assert missing.status == "failure"
    assert missing.error is not None
    assert "did not contain" in missing.error.message


def test_timing_from_usage_records_peak_rss() -> None:
    usage = resource.struct_rusage((1.0, 2.0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0))

    timing = processes.timing_from_usage(usage, 1.0)

    assert timing.max_rss_bytes == processes.ru_maxrss_to_bytes(3)


def test_runner_output_routes_status_to_stderr(monkeypatch: pytest.MonkeyPatch) -> None:
    stream = io.StringIO()
    monkeypatch.setattr(sys, "stderr", stream)
    output = runner_output.RunnerOutput()

    target_label = "build [red]literal[/red] x[/blue]"
    output.build_start(
        models.TargetRow(
            source=".",
            path=str(ROOT),
            git_ref="HEAD",
            git_sha="abc123",
            is_dirty=False,
            label=target_label,
        )
    )
    error_message = "bad [yellow]literal[/yellow] y[/red]"
    output.print_error(ValueError(error_message))

    rendered = stream.getvalue()
    assert "Building" in rendered
    assert target_label in rendered
    assert error_message in rendered
