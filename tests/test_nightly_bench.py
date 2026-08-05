"""Test nightly endpoint command construction."""

from __future__ import annotations

import subprocess
from typing import Any

import pytest

from scripts import nightly_bench


@pytest.mark.parametrize(
    ("treatment", "excludes_herbie"),
    [("sliced-proofs", True), ("proofs", False)],
)
def test_nightly_excludes_herbie_only_from_sliced_proofs(
    treatment: str,
    excludes_herbie: bool,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    commands: list[list[str]] = []

    def fake_run(command: list[str], **_kwargs: Any) -> subprocess.CompletedProcess[str]:
        commands.append(command)
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(nightly_bench.subprocess, "run", fake_run)

    assert (
        nightly_bench._run(
            ("branch", "."),
            ("main", treatment),
            open_report=False,
            rounds=1,
        )
        == 0
    )
    assert commands
    excluded_names = [
        commands[0][index + 1] for index, argument in enumerate(commands[0][:-1]) if argument == "--exclude-name"
    ]
    assert ("herbie.egg" in excluded_names) is excludes_herbie
