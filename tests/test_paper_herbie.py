"""Test the bounded, end-to-end paper Herbie adapter."""

from __future__ import annotations

from pathlib import Path

import pytest

from paper_benchmarking.hashing import sha256_file
from paper_benchmarking.herbie import (
    HERBIE_CORPUS_SHA256,
    HERBIE_LOCK_SHA256,
    herbie_lanes,
    stage_artifact,
    validate_herbie_output,
)
from paper_benchmarking.models import Preset

from .paper_fixtures import ROOT

_CORPUS = """(FPCore (x eps)
 :name "2cos (problem 3.3.5)"
 (- (cos (+ x eps)) (cos x)))
"""

_SUCCESS = """;; seed: 0

(FPCore (x eps)
 :herbie-status imp-start
 :herbie-time 1.25
 :herbie-error-input ((64 42.4) (8000 39.4))
 :herbie-error-output ((64 0.39) (8000 0.59))
 :name "2cos (problem 3.3.5)"
 :precision binary64
 :herbie-conversions ()
 (+ x eps))
"""

_PROGRESS = "Starting Herbie on 1 problems (seed: 0)...\n  1/1\t[1.25s] 39->1\t2cos (problem 3.3.5)\n"


def _artifact_source(tmp_path: Path) -> Path:
    root = tmp_path / "artifact"
    herbie = root / "herbie-eqlog"
    (herbie / "egg-herbie").mkdir(parents=True)
    (herbie / "egg-herbie/Cargo.toml").write_text(
        '[package]\nname = "egg-herbie-fixture"\n',
        encoding="utf-8",
    )
    (herbie / "2cos.fpcore").write_text(_CORPUS, encoding="utf-8")
    eqlog = root / "eqlog-herbie-tweaks"
    eqlog.mkdir()
    (eqlog / "Cargo.toml").write_text('[package]\nname = "fixture"\n', encoding="utf-8")
    return root


def test_herbie_quick_lane_is_bounded_and_provenanced(tmp_path: Path) -> None:
    artifact = _artifact_source(tmp_path)

    (lane,) = herbie_lanes(ROOT, artifact, "quick")

    assert lane.name == "artifact-eqlog-2cos"
    assert len(lane.observations) == 1
    assert lane.observations[0].timeout_sec == 60
    assert lane.observations[0].argv[-3:] == (
        "run",
        "--source-root",
        str(ROOT / ".paper-build/herbie/work/herbie-eqlog"),
    )
    assert any(command.label == "cargo" and "--locked" in command.argv for command in lane.build)
    assert any(command.label == "packages" for command in lane.prepare)
    assert lane.observations[0].runtime_executables == ("racket",)
    assert ROOT / ".paper-build/herbie/racket-home" in lane.observations[0].runtime_artifacts
    assert lane.versions["cargo-lock-sha256"] == HERBIE_LOCK_SHA256
    assert artifact / "herbie-eqlog" in lane.input_paths
    assert artifact / "eqlog-herbie-tweaks" in lane.input_paths


@pytest.mark.parametrize("preset", ["representative", "artifact-full"])
def test_herbie_rejects_unimplemented_broad_presets(tmp_path: Path, preset: Preset) -> None:
    with pytest.raises(ValueError, match="supports only the quick preset"):
        herbie_lanes(ROOT, _artifact_source(tmp_path), preset)


def test_stage_copies_sources_and_replaces_previous_work_tree(tmp_path: Path) -> None:
    artifact = _artifact_source(tmp_path)
    lockfile = ROOT / "paper_benchmarking/assets/herbie/Cargo.lock"
    destination = tmp_path / "build/work"
    cargo_target = tmp_path / "build/cargo-target"
    racket_home = tmp_path / "build/racket-home"

    stage_artifact(artifact, destination, lockfile, cargo_target, racket_home)
    stale = destination / "stale"
    stale.write_text("old\n", encoding="utf-8")
    stale_racket = racket_home / "stale"
    stale_racket.write_text("old\n", encoding="utf-8")
    stage_artifact(artifact, destination, lockfile, cargo_target, racket_home)

    assert not stale.exists()
    assert not stale_racket.exists()
    assert sha256_file(destination / "herbie-eqlog/egg-herbie/Cargo.lock") == HERBIE_LOCK_SHA256
    assert sha256_file(destination / "herbie-eqlog/2cos.fpcore") == HERBIE_CORPUS_SHA256
    assert (destination / "herbie-eqlog/egg-herbie/target").resolve() == cargo_target.resolve()
    assert not (artifact / "herbie-eqlog/egg-herbie/Cargo.lock").exists()


def test_semantic_validator_accepts_improving_one_problem_result(tmp_path: Path) -> None:
    corpus = tmp_path / "2cos.fpcore"
    corpus.write_text(_CORPUS, encoding="utf-8")

    validate_herbie_output(corpus, _SUCCESS, _PROGRESS)


@pytest.mark.parametrize(
    ("stdout", "stderr", "message"),
    [
        (_SUCCESS.replace("imp-start", "timeout"), _PROGRESS, "unexpected Herbie status"),
        (_SUCCESS.replace("0.59", "40.0"), _PROGRESS, "did not improve"),
        (_SUCCESS, "Starting Herbie on 1 problems (seed: 0)...\n", "does not show completion"),
    ],
)
def test_semantic_validator_rejects_unsuccessful_results(
    tmp_path: Path,
    stdout: str,
    stderr: str,
    message: str,
) -> None:
    corpus = tmp_path / "2cos.fpcore"
    corpus.write_text(_CORPUS, encoding="utf-8")

    with pytest.raises(ValueError, match=message):
        validate_herbie_output(corpus, stdout, stderr)
