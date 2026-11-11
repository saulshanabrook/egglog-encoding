"""Protect admission evidence and measured rows from coverage output collisions."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

from benchmarking import pilot
from benchmarking.targets import sha256_file

from .report_fixtures import make_record


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
