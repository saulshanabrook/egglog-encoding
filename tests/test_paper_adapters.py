"""Test the production paper lane matrix without running external tools."""

from __future__ import annotations

from pathlib import Path

from paper_benchmarking.adapters import math_lanes, pointer_lanes
from paper_benchmarking.rust_artifact import RUST_ARTIFACT_TOOLCHAIN

from .paper_fixtures import ROOT


def test_quick_math_matrix_has_historical_and_all_current_treatments(tmp_path: Path) -> None:
    lanes = math_lanes(ROOT, tmp_path / "artifact", "quick")

    assert [lane.name for lane in lanes] == [
        "artifact-egg-n010",
        "artifact-eqlog-n010",
        "current-off-n010",
        "current-term-n010",
        "current-proofs-n010",
    ]
    for lane in lanes[:2]:
        assert [command.label for command in lane.build] == ["paper-math-stage", "paper-math"]
        assert lane.build[1].env["RUSTUP_TOOLCHAIN"] == RUST_ARTIFACT_TOOLCHAIN
        assert lane.build[1].env["RUSTC_WRAPPER"] == ""
        assert lane.observations[0].cwd == ROOT / ".paper-build/artifact-math-work/micro-benchmarks"
        assert lane.observations[0].argv[0].endswith("eqlog-benchmark")
    assert lanes[0].observations[0].expected_stdout_csv_record == ("math-run-10", "Egg", 13_106)
    assert lanes[1].observations[0].expected_stdout_csv_record == ("math-run-10", "Eqlog", 21_052)
    expected_sizes = ("1857", "3771", "6893", "1838", "6676", "3", "2", "1", "1", "1", "1", "5", "3")
    assert all(lane.observations[0].expected_stdout_lines == expected_sizes for lane in lanes[2:])
    assert lanes[-1].validate[0].argv[-1].endswith("math-run-010.egg")
    assert "--proof-testing" in lanes[-1].validate[0].argv


def test_pointer_matrix_uses_exact_output_gates(tmp_path: Path) -> None:
    lanes = pointer_lanes(ROOT, tmp_path / "artifact", "quick")

    assert [lane.name for lane in lanes] == [
        "artifact-eqlog-initdb",
        "current-off-initdb",
        "current-term-initdb",
        "current-proofs-initdb",
    ]
    assert lanes[0].observations[0].expected_stdout_lines == (
        "Function expr_points_to has size 5832",
        "Function ptr_points_to has size 342",
    )
    assert all(lane.observations[0].expected_stdout_lines == ("5832", "342") for lane in lanes[1:])
    assert "--proof-testing" in lanes[-1].validate[0].argv


def test_artifact_full_math_matrix_covers_every_checkpoint_once(tmp_path: Path) -> None:
    lanes = math_lanes(ROOT, tmp_path / "artifact", "artifact-full")

    assert len(lanes) == 55
    assert all(len(lane.observations) == 1 for lane in lanes)
