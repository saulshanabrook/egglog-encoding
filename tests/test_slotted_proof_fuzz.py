"""A failed proof-output check must retain a replayable, separate reproduction."""

import importlib
import subprocess
import sys
from pathlib import Path
from typing import Any, TextIO

import pytest


@pytest.mark.parametrize("output", ["", "("])
def test_output_failures_keep_each_runs_source_and_replay_flags(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, output: str
) -> None:
    fuzz = importlib.import_module("slotted.xdiff.proofs")
    monkeypatch.setattr(fuzz.driver, "compile_source", lambda *_, **__: "")
    monkeypatch.setattr(
        fuzz.driver,
        "run_encoding",
        lambda _, probes, __: ("OK", "".join(f"[{i}]" for i in range(probes)) + " missing[[]]"),
    )

    def run(command: list[str], *, stdout: TextIO, **_: Any) -> subprocess.CompletedProcess[str]:
        stdout.write(output)
        return subprocess.CompletedProcess(command, 0, stderr="")

    monkeypatch.setattr(fuzz.subprocess, "run", run)
    monkeypatch.setattr(
        sys, "argv", ["proofs.py", "1", "0", "--language", "array", "--no-aliasing", "--failures", str(tmp_path)]
    )
    assert fuzz.main() == 1
    assert fuzz.main() == 1
    runs = list(tmp_path.iterdir())
    assert len(runs) == 2
    for directory in runs:
        assert "(check (renaming-= _p" in (directory / "fuzz0.egg").read_text()
        assert (directory / "fuzz0.proof.txt").read_text() == output
        diagnostic = (directory / "fuzz0.log").read_text()
        assert "--slotted-no-aliasing" in diagnostic
        assert str(directory / "fuzz0.egg") in diagnostic
        expected = "invalid proof output" if output else "0 proofs for"
        assert expected in diagnostic
