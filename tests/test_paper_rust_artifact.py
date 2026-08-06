"""Test immutable staging for the paper artifact's historical Rust crates."""

from __future__ import annotations

from pathlib import Path

import pytest

from paper_benchmarking.rust_artifact import RUST_ARTIFACT_COMPATIBILITY, stage_rust_artifact

_DESUGAR = """fn desugar() {
            Rule {
            }
}
fn parenthesize_globals(rule: Rule, globals: &HashSet<Symbol>) -> Rule {
}
fn flatten_rule(rule_in: Rule, globals: &HashSet<Symbol>) -> NormRule {
}
"""

_MATH_DRIVER = """struct Opt {
    #[structopt(long)]
    disable_eqlog: bool,
}
fn run() {
        if !opt.disable_eqlog {
            let mut durations = vec![];
            let mut size = 0;
            for _ in 0..opt.repeat {
                let eqlognaive_start_time = now();
            }
        }
        if !opt.disable_egg && !opt.disable_eqlog {
        }
        if opt.disable_egg && !opt.disable_eqlog {
        }
    for i in 1..opt.iter_size + 1 {
    }
}
"""


def _artifact_source(tmp_path: Path) -> Path:
    root = tmp_path / "artifact"
    eqlog = root / "eqlog"
    (eqlog / "src").mkdir(parents=True)
    (eqlog / "src/desugar.rs").write_text(_DESUGAR, encoding="utf-8")
    (eqlog / "Cargo.toml").write_text('[package]\nname = "eqlog"\n', encoding="utf-8")
    math = root / "micro-benchmarks"
    (math / "src").mkdir(parents=True)
    (math / "Cargo.toml").write_text('[package]\nname = "eqlog-benchmark"\n', encoding="utf-8")
    (math / "src/main.rs").write_text(_MATH_DRIVER, encoding="utf-8")
    return root


def test_math_stage_applies_only_the_declared_compatibility_boundary(tmp_path: Path) -> None:
    artifact = _artifact_source(tmp_path)
    destination = tmp_path / "work"

    stage_rust_artifact(artifact, destination, "math")

    staged = (destination / "eqlog/src/desugar.rs").read_text(encoding="utf-8")
    assert staged.count("ast::Rule") == 4
    assert (destination / "micro-benchmarks/Cargo.toml").read_text(encoding="utf-8").endswith("\n[workspace]\n")
    assert (artifact / "eqlog/src/desugar.rs").read_text(encoding="utf-8") == _DESUGAR
    driver = (destination / "micro-benchmarks/src/main.rs").read_text(encoding="utf-8")
    assert "disable_eqlog_naive" in driver
    assert "only_iter" in driver
    assert RUST_ARTIFACT_COMPATIBILITY == "qualify-ast-rule-bounded-driver-and-standalone-workspace-v1"


def test_stage_replaces_previous_adapter_work_tree(tmp_path: Path) -> None:
    artifact = _artifact_source(tmp_path)
    destination = tmp_path / "work"
    stage_rust_artifact(artifact, destination, "eqlog")
    stale = destination / "stale"
    stale.write_text("old\n", encoding="utf-8")

    stage_rust_artifact(artifact, destination, "eqlog")

    assert not stale.exists()
    assert (destination / "eqlog/Cargo.toml").read_text(encoding="utf-8").endswith("\n[workspace]\n")
    assert not (destination / "micro-benchmarks").exists()


def test_stage_fails_closed_when_the_historical_patch_surface_changes(tmp_path: Path) -> None:
    artifact = _artifact_source(tmp_path)
    (artifact / "eqlog/src/desugar.rs").write_text("changed\n", encoding="utf-8")

    with pytest.raises(ValueError, match="compatibility source changed"):
        stage_rust_artifact(artifact, tmp_path / "work", "eqlog")
