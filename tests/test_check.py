"""Check validation ordering, subprocess boundaries, and Make compatibility."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

import pytest

from scripts import check


@dataclass
class Command:
    args: tuple[str, ...]
    cwd: Path
    env: dict[str, str]


@pytest.fixture
def commands(monkeypatch: pytest.MonkeyPatch) -> list[Command]:
    recorded: list[Command] = []

    def run(args: tuple[str, ...], *, cwd: Path, env: dict[str, str], check: bool) -> None:
        assert check
        recorded.append(Command(args, cwd, env))

    monkeypatch.setattr(subprocess, "run", run)
    monkeypatch.delenv("RUST_TEST_ARGS", raising=False)
    monkeypatch.delenv("LEAN_BIN_DIR", raising=False)
    monkeypatch.delenv("LEAN_CERTIFICATES", raising=False)
    return recorded


def test_default_check_runs_all_hygiene_before_tests(commands: list[Command]) -> None:
    assert check.main([]) == 0
    first_test = next(i for i, command in enumerate(commands) if "pytest" in command.args)
    assert all("test" not in command.args and "pytest" not in command.args for command in commands[:first_test])
    assert any("mypy" in command.args for command in commands[:first_test])
    assert any(command.args[:2] == ("cargo", "doc") for command in commands[:first_test])
    rust_tests = [command.args for command in commands if command.args[:2] == ("cargo", "test")]
    assert rust_tests == [
        ("cargo", "test", "--workspace", "--"),
        ("cargo", "test", "--manifest-path", "slotted/xmulti/Cargo.toml", "--"),
    ]


def test_overlapping_targets_do_not_repeat_completed_checks(commands: list[Command]) -> None:
    assert check.main(["python-nits", "check"]) == 0
    assert sum(command.args[:3] == ("uv", "lock", "--check") for command in commands) == 1
    assert sum("pytest" in command.args for command in commands) == 1


def test_ci_suites_preserve_full_test_coverage(commands: list[Command]) -> None:
    assert check.main(["test"]) == 0
    full_suite = commands.copy()
    commands.clear()
    for target in ("python-test", "rust-test", "slotted-test"):
        assert check.main([target]) == 0
    assert commands == full_suite


def test_failure_stops_immediately_and_preserves_exit_status(monkeypatch: pytest.MonkeyPatch) -> None:
    calls = 0

    def fail(*args: object, **kwargs: object) -> None:
        nonlocal calls
        calls += 1
        raise subprocess.CalledProcessError(17, "uv")

    monkeypatch.setattr(subprocess, "run", fail)
    assert check.main(["check"]) == 17
    assert calls == 1


def test_rust_arguments_are_argv_and_do_not_affect_thread_defaults(
    commands: list[Command], monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("RUST_TEST_ARGS", '--test-threads=1 --skip "name with `backticks` and $(substitution)"')
    monkeypatch.setenv("RAYON_NUM_THREADS", "7")
    assert check.main(["rust-test", "proof-tests"]) == 0
    for command in commands:
        assert command.args[-3:] == ("--test-threads=1", "--skip", "name with `backticks` and $(substitution)")
        assert command.env["RAYON_NUM_THREADS"] == "7"
    assert "proofs/" in commands[-1].args


def test_lean_checks_build_the_shared_generator_once(commands: list[Command]) -> None:
    assert check.main(["lean-congruence-test", "lean-provenance-test", "lean-resugar-test"]) == 0
    assert sum(command.args == ("lake", "build", "difftest") for command in commands) == 1
    assert [command.args[1] for command in commands if command.args[0].endswith("/difftest")] == [
        "congruence",
        "provenance",
        "resugar",
    ]


def test_configured_paths_are_consistent_across_working_directories(
    commands: list[Command], monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    monkeypatch.setattr(check, "ROOT", tmp_path)
    monkeypatch.setenv("LEAN_BIN_DIR", "tool bins/elan")
    monkeypatch.setenv("LEAN_CERTIFICATES", "reports/lifted proofs.json")
    assert check.main(["lean-certificate-test"]) == 0
    certificates = str(tmp_path / "reports/lifted proofs.json")
    for command in commands:
        if command.cwd == tmp_path / "semantics":
            assert command.env["PATH"].startswith(str(tmp_path / "tool bins/elan") + os.pathsep)
        if any(arg.startswith("export-") for arg in command.args) or command.args[0] == "cmp":
            assert certificates in command.args
    assert commands[-1].env["EGGLOG_LEAN_CERTIFICATES"] == certificates


def test_empty_make_exports_retain_lean_defaults(commands: list[Command], monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("LEAN_BIN_DIR", "")
    monkeypatch.setenv("LEAN_CERTIFICATES", "")
    assert check.main(["lean-congruence-test"]) == 0
    assert commands[0].env["PATH"].startswith(str(Path.home() / ".elan/bin") + os.pathsep)


def test_paper_build_checks_proofs_before_extracting_and_compiling(commands: list[Command]) -> None:
    assert check.main(["paper"]) == 0
    assert len(commands) == 3
    assert commands[0].args[:3] == ("lake", "build", "EgglogPaper")
    assert "EgglogSemantics.Spec.Eval:blueprint" in commands[0].args
    assert commands[1].args[:2] == ("lake", "env")
    assert commands[1].args[-1] == ",".join(check.PAPER_MODULES)
    assert commands[2].args[0] == "latexmk" and "-Werror" in commands[2].args
    assert all(command.cwd == check.ROOT / "semantics" for command in commands)


def test_dry_run_has_no_process_or_directory_side_effects(
    commands: list[Command], monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    destination = tmp_path / "missing/certificates.json"
    monkeypatch.setenv("LEAN_CERTIFICATES", str(destination))
    assert check.main(["--dry-run", "lean-certificate-test", "paper"]) == 0
    assert not commands and not destination.parent.exists()


def test_lean_proof_hole_blocks_native_tests(
    commands: list[Command], monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(check, "ROOT", tmp_path)
    sources = tmp_path / "semantics/EgglogSemantics"
    sources.mkdir(parents=True)
    (sources / "Example.lean").write_text("-- Reject `sorry` below.\ntheorem unfinished : True := by sorry\n")
    assert check.main(["lean-check"]) == 1
    assert [command.args for command in commands] == [("lake", "build")]
    assert "Example.lean:2" in capsys.readouterr().err


def test_make_forwards_configuration_without_shell_interpolation(tmp_path: Path) -> None:
    python = tmp_path / "python3"
    record = tmp_path / "invocation.json"
    python.write_text(
        f"#!{sys.executable}\n"
        "import json, os, pathlib, sys\n"
        "pathlib.Path(os.environ['CHECK_RECORD']).write_text(json.dumps([sys.argv[1:], dict(os.environ)]))\n"
    )
    python.chmod(0o755)
    injected = tmp_path / "must-not-exist"
    rust_args = f'--skip "test with `touch {injected}`"'
    result = subprocess.run(
        [
            "make",
            "rust-test",
            f"RUST_TEST_ARGS={rust_args}",
            "LEAN_BIN_DIR=lean bins",
            "LEAN_CERTIFICATES=proofs file.json",
        ],
        cwd=check.ROOT,
        env={**os.environ, "PATH": f"{tmp_path}{os.pathsep}{os.environ['PATH']}", "CHECK_RECORD": str(record)},
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    args, env = json.loads(record.read_text())
    assert args == ["scripts/check.py", "rust-test"]
    assert env["RUST_TEST_ARGS"] == rust_args
    assert env["LEAN_BIN_DIR"] == "lean bins"
    assert env["LEAN_CERTIFICATES"] == "proofs file.json"
    assert not injected.exists()
