"""Exercise the case-study evidence boundary with test-only compiler stand-ins."""

from __future__ import annotations

import importlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

study = importlib.import_module("scripts.eggcc_encoding_case_study")
SCRIPT_PATH = Path(__file__).resolve().parents[1] / "scripts/eggcc_encoding_case_study.py"


@pytest.fixture
def paths(tmp_path: Path) -> tuple[Path, Path]:
    binary = tmp_path / "test-only-compiler"
    binary.write_text(
        f"#!{sys.executable}\n"
        "import json, os, sys, time\n"
        "from pathlib import Path\n"
        "mode = os.environ.get('CASE_STUDY_TEST_MODE', '')\n"
        "if mode == 'exit': sys.exit(7)\n"
        "if mode == 'timeout': time.sleep(60)\n"
        "interpreted = '--interp' in sys.argv\n"
        "receipt = {'original_interpreted': '42\\n' if interpreted else None,\n"
        "           'result_interpreted': '42\\n' if interpreted else None,\n"
        "           'eggcc_compile_time': {'secs': 0, 'nanos': 1}}\n"
        "if mode == 'mismatch': receipt['result_interpreted'] = 'wrong\\n'\n"
        "if mode == 'missing': receipt['original_interpreted'] = None\n"
        "if mode == 'malformed': receipt = {'not': 'an eggcc receipt'}\n"
        "out = Path(sys.argv[sys.argv.index('--run-data-out') + 1])\n"
        "if mode == 'measured-exit' and out.name.startswith('measurement-'): sys.exit(9)\n"
        "out.write_text(json.dumps(receipt))\n",
        encoding="utf-8",
    )
    binary.chmod(0o755)
    (tmp_path / "test-only-input.bril").write_text("# ARGS: 42\n# test-only fixture, not a study case\n")
    manifest = {
        "schema_version": 1,
        "study_id": "test-only-not-study-measurements",
        "warmups": 1,
        "observations": 2,
        "timeout_sec": 1,
        "cases": [{"id": "fixture", "input": "test-only-input.bril", "origin": "pytest-generated test double"}],
        "arms": [
            {
                "id": arm,
                "binary": "test-only-compiler",
                "cwd": ".",
                "engine": "pytest stand-in, not eggcc",
                "configuration": "test-only collection protocol",
                "args": ["--run-mode", "optimize"],
                "env": {"CASE_STUDY_TEST_MODE": ""},
            }
            for arm in ("A", "B")
        ],
    }
    study_path = tmp_path / "study.json"
    study_path.write_text(json.dumps(manifest), encoding="utf-8")
    return study_path, tmp_path / "results.json"


def test_collect_separates_correctness_interleaves_and_binds_provenance(paths: tuple[Path, Path]) -> None:
    study_path, results_path = paths
    result = study.collect(study_path, results_path)
    assert study.verify(study_path, results_path) == result
    assert result["status"] == "complete"
    assert [(row["phase"], row["arm"]) for row in result["rows"]] == [
        ("correctness", "A"),
        ("correctness", "B"),
        ("warmup", "A"),
        ("warmup", "B"),
        ("measurement", "A"),
        ("measurement", "B"),
        ("measurement", "B"),
        ("measurement", "A"),
    ]
    for row in result["rows"]:
        assert ("--interp" in row["command"]) == (row["phase"] == "correctness")
        assert (row["wall_sec"] is None) == (row["phase"] == "correctness")
        assert row["exit_code"] == 0
        assert row["environment_sha256"]["RUST_LOG"]
        assert row["rss_scope"] == study.RSS_SCOPE
        assert row["cwd"] == str(study_path.parent)
        assert Path(row["receipt_path"]).is_file()
    assert {entry["kind"] for entry in result["provenance"]} == {"binary", "input"}
    with pytest.raises(ValueError, match="results already exist"):
        study.collect(study_path, results_path)


@pytest.mark.parametrize(
    ("mode", "message", "status", "exit_code"),
    [
        ("mismatch", "interpreter outputs differ", "failure", 0),
        ("missing", "missing non-null", "failure", 0),
        ("malformed", "missing or inconsistent", "failure", 0),
        ("exit", "incomplete compiler run", "failure", 7),
        ("timeout", "incomplete compiler run", "timed-out", None),
    ],
)
def test_failure_is_retained_and_prevents_timing(
    paths: tuple[Path, Path], mode: str, message: str, status: str, exit_code: int | None
) -> None:
    study_path, results_path = paths
    manifest = json.loads(study_path.read_text())
    manifest["arms"][0]["env"]["CASE_STUDY_TEST_MODE"] = mode
    study_path.write_text(json.dumps(manifest))
    with pytest.raises(ValueError, match=message):
        study.collect(study_path, results_path)
    result = json.loads(results_path.read_text())
    assert result["status"] == "failure"
    assert len(result["rows"]) == 1
    assert result["rows"][0]["status"] == status
    assert result["rows"][0]["exit_code"] == exit_code
    assert result["rows"][0]["phase"] == "correctness"
    with pytest.raises(ValueError, match="collection is incomplete"):
        study.verify(study_path, results_path)


@pytest.mark.parametrize("file", ["test-only-compiler", "test-only-input.bril"])
def test_changed_input_or_binary_provenance_is_rejected(paths: tuple[Path, Path], file: str) -> None:
    study_path, results_path = paths
    study.collect(study_path, results_path)
    with (study_path.parent / file).open("a") as handle:
        handle.write("\n# changed after collection\n")
    with pytest.raises(ValueError, match="provenance mismatch"):
        study.verify(study_path, results_path)


def test_failed_measurement_retains_partial_evidence_and_stops(paths: tuple[Path, Path]) -> None:
    study_path, results_path = paths
    manifest = json.loads(study_path.read_text())
    manifest["arms"][0]["env"]["CASE_STUDY_TEST_MODE"] = "measured-exit"
    study_path.write_text(json.dumps(manifest))
    with pytest.raises(ValueError, match="incomplete compiler run"):
        study.collect(study_path, results_path)
    result = json.loads(results_path.read_text())
    assert result["status"] == "failure"
    assert len(result["rows"]) == 5
    assert all(row["status"] == "success" for row in result["rows"][:-1])
    assert result["rows"][-1]["phase"] == "measurement"
    assert result["rows"][-1]["exit_code"] == 9
    assert result["rows"][-1]["wall_sec"] > 0
    with pytest.raises(ValueError, match="collection is incomplete"):
        study.verify(study_path, results_path)


@pytest.mark.parametrize(
    "corruption", ["missing-row", "incomplete", "missing-wall", "missing-rss", "wrong-command", "wrong-label"]
)
def test_incomplete_or_unmeasured_rows_are_rejected(paths: tuple[Path, Path], corruption: str) -> None:
    study_path, results_path = paths
    result = study.collect(study_path, results_path)
    row = result["rows"][-1]
    if corruption == "missing-row":
        result["rows"].pop()
    elif corruption == "incomplete":
        result["status"] = "collecting"
    elif corruption == "missing-wall":
        row["wall_sec"] = None
    elif corruption == "missing-rss":
        row["max_rss_bytes"] = None
    elif corruption == "wrong-command":
        row["command"].insert(1, "--interp")
    else:
        row["configuration"] = "different treatment"
    study.write_json(results_path, result)
    with pytest.raises(ValueError):
        study.verify(study_path, results_path)


def test_changed_manifest_or_compiler_receipt_is_rejected(paths: tuple[Path, Path]) -> None:
    study_path, results_path = paths
    result = study.collect(study_path, results_path)
    receipt = Path(result["rows"][0]["receipt_path"])
    receipt.write_text("{}")
    with pytest.raises(ValueError, match="changed compiler receipt"):
        study.verify(study_path, results_path)
    study_path.write_text(study_path.read_text() + "\n")
    with pytest.raises(ValueError, match="manifest provenance mismatch"):
        study.verify(study_path, results_path)


@pytest.mark.parametrize("count", [0, 1])
def test_selected_test_receipts_require_nonzero_success(
    paths: tuple[Path, Path], count: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    study_path, results_path = paths
    tests = study_path.parent / "focused-test-receipt.json"
    tests.write_text(json.dumps({"status": "success", "selected_tests": count}))
    manifest = json.loads(study_path.read_text())
    manifest["artifacts"] = [
        {"id": "focused-tests", "kind": "tests", "path": tests.name, "origin": "pytest-generated receipt"}
    ]
    study_path.write_text(json.dumps(manifest))
    if count:
        study.collect(study_path, results_path)
        study.verify(study_path, results_path)
    else:

        def forbidden_run(*args: Any, **kwargs: Any) -> None:
            pytest.fail("a zero-selected-tests precondition must prevent every compiler invocation")

        monkeypatch.setattr(study, "run_command", forbidden_run)
        with pytest.raises(ValueError, match="nonzero selected_tests"):
            study.collect(study_path, results_path)
        assert not results_path.exists()


def test_claims_require_retained_conditional_evidence(paths: tuple[Path, Path]) -> None:
    study_path, _ = paths
    manifest = json.loads(study_path.read_text())
    manifest["claims"] = {
        "real_bug": {"description": "test only", "violated_invariant": "test only", "baseline_reproducer": "missing"},
        "optimization": None,
    }
    study_path.write_text(json.dumps(manifest))
    with pytest.raises(ValueError, match="retained baseline_reproducer"):
        study.load_study(study_path)


def test_default_sampling_and_unused_positional_arguments(paths: tuple[Path, Path]) -> None:
    study_path, _ = paths
    manifest = json.loads(study_path.read_text())
    manifest.pop("warmups")
    manifest.pop("observations")
    study_path.write_text(json.dumps(manifest))
    loaded = study.load_study(study_path)
    assert loaded["warmups"] == 1
    assert loaded["observations"] == 10
    assert len(list(study.schedule(loaded))) == 24
    manifest["cases"][0]["args"] = ["42"]
    study_path.write_text(json.dumps(manifest))
    with pytest.raises(ValueError, match="positional CLI arguments are unused"):
        study.load_study(study_path)


def test_interruption_retains_incomplete_checkpoint(paths: tuple[Path, Path], monkeypatch: pytest.MonkeyPatch) -> None:
    study_path, results_path = paths

    def interrupted_run(*args: Any, **kwargs: Any) -> None:
        raise KeyboardInterrupt

    monkeypatch.setattr(study, "run_command", interrupted_run)
    with pytest.raises(KeyboardInterrupt):
        study.collect(study_path, results_path)
    result = json.loads(results_path.read_text())
    assert result["status"] == "interrupted"
    assert len(result["rows"]) == 1
    with pytest.raises(ValueError, match="collection is incomplete"):
        study.verify(study_path, results_path)


def test_cli_collection_and_verification_from_another_directory(paths: tuple[Path, Path]) -> None:
    study_path, results_path = paths
    for operation in ("collect", "verify"):
        process = subprocess.run(
            [sys.executable, str(SCRIPT_PATH), operation, str(study_path), str(results_path)],
            cwd=study_path.parent,
            capture_output=True,
            text=True,
            check=False,
        )
        assert process.returncode == 0, process.stderr
        assert process.stdout == ""
        assert f"{operation}:" in process.stderr


def test_figures_export_raw_rows_and_variability_without_aggregate(paths: tuple[Path, Path]) -> None:
    pytest.importorskip("matplotlib")
    study_path, results_path = paths
    result = study.collect(study_path, results_path)
    output = study_path.parent / "figures"
    study.figures(study_path, results_path, output)
    data: dict[str, Any] = json.loads((output / "figure-data.json").read_text())
    assert data["results_sha256"] == study.sha256(results_path)
    assert len(data["summaries"]) == 2
    for summary in data["summaries"]:
        raw = [
            row["wall_sec"] for row in result["rows"] if row["phase"] == "measurement" and row["arm"] == summary["arm"]
        ]
        assert summary["wall_sec"]["raw"] == raw
        assert summary["wall_sec"]["median"] == sum(raw) / 2
        assert summary["wall_sec"]["stdev"] is not None
    svg = (output / "fixture.svg").read_text()
    assert "Compiler elapsed time (s)" in svg
    assert "wait4 child peak RSS (MiB)" in svg
    assert "not simultaneous process-group peak" in svg
    assert (output / "fixture.pdf").read_bytes().startswith(b"%PDF")
    assert "| fixture | A | 2 |" in (output / "table.md").read_text()
    assert not list(output.glob("*aggregate*"))
    # A new output directory regenerates solely from the same rows, without collection.
    process = subprocess.run(
        [
            sys.executable,
            str(SCRIPT_PATH),
            "figures",
            str(study_path),
            str(results_path),
            str(study_path.parent / "figures-again"),
        ],
        cwd=study_path.parent,
        capture_output=True,
        text=True,
        check=False,
    )
    assert process.returncode == 0, process.stderr
    assert process.stdout == ""
    assert (output / "figure-data.json").read_bytes() == (
        study_path.parent / "figures-again/figure-data.json"
    ).read_bytes()


def test_cli_returns_failure_status_for_incomplete_results(
    paths: tuple[Path, Path], capsys: pytest.CaptureFixture[str]
) -> None:
    study_path, results_path = paths
    assert study.main(["verify", str(study_path), str(results_path)]) == 1
    assert "verify:" in capsys.readouterr().err
