"""Check frozen slotted inputs, backend selection, cache identities, and shared collection."""

from __future__ import annotations

import json
import subprocess
import sys
from dataclasses import replace
from pathlib import Path

import pytest
from rich.console import Console

from benchmarking import collection, figures, models, targets, workloads
from benchmarking.engines import Treatment, validate_engine_workload
from benchmarking.processes import TimingRow
from benchmarking.reports.store import CacheKey, ReportStore
from benchmarks.slotted.generate import INPUTS, ROOT, frozen_inputs
from tests.report_fixtures import make_target, make_timing_summary


def test_frozen_sources_are_current_complete_and_self_contained() -> None:
    generated = frozen_inputs()
    assert set(generated) == {path.relative_to(INPUTS) for path in INPUTS.rglob("*") if path.is_file()}
    assert len(generated) == 46
    for relative, source in generated.items():
        path = INPUTS / relative
        assert path.read_text() == source, f"regenerate {relative} with python -m benchmarks.slotted.generate"
        if relative.suffix == ".egg":
            assert "(include " not in source
            assert "(run " in source and "(check " in source
            assert not workloads.file_contains_executable_prove_command(path)
        else:
            data = json.loads(source)
            assert data["multi"].startswith("rounds ") and "\ngoal " in data["multi"]
            assert (data["nested"] is None) == (relative.parts[0] == "logic")


def test_collection_imports_neither_generators_nor_graph_verification() -> None:
    result = subprocess.run(
        [
            sys.executable,
            "-c",
            "import sys, benchmarking.figures, benchmarking.collection; "
            "assert not any(name == 'slotted' or name.startswith('slotted.') "
            "or name.startswith('benchmarks.slotted') for name in sys.modules)",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=15,
    )
    assert result.returncode == 0, result.stderr


def test_catalog_retains_all_families_without_launching_unsupported_nested_workloads() -> None:
    config = figures.load_config(figures.DEFAULT_CONFIG)
    multi, nested = figures.resolve_figures(config, ("slotted-runtime", "slotted-nested-runtime"), ROOT)
    assert len(multi.files) == 23 and len(nested.files) == 21
    assert {file.absolute_path.parent.name for file in multi.files} == {"array", "sdql", "logic"}
    assert {file.absolute_path.parent.name for file in nested.files} == {"array", "sdql"}
    assert set(nested.files) < set(multi.files)
    assert multi.figure.treatments == ("slotted-ref-multi", "slotted")
    assert nested.figure.treatments == ("slotted-ref-nested", "slotted-no-aliasing")


def test_native_identity_uses_the_frozen_reference_and_selected_binary(tmp_path: Path) -> None:
    source = INPUTS / "array/goal-2d-4f-N0.egg"
    (logical,) = workloads.resolve_files([str(source)], ROOT)
    native = logical.for_engine("slotted")
    assert native.absolute_path == source.with_suffix(".ref")
    assert native.sha256 == targets.sha256_file(native.absolute_path) != logical.sha256
    binary = tmp_path / "xmulti"
    target = replace(make_target(), engine_binaries=(models.EngineBinary("slotted", "sha256:reference", binary),))
    endpoint = models.BenchmarkEndpoint(target, "slotted-ref-multi")
    identity = CacheKey.for_endpoint(endpoint, logical)
    assert identity.binary_sha256 == "sha256:reference"
    assert identity.file_sha256 == native.sha256
    plan = collection.build_collection_plan(
        ReportStore(tmp_path / "report.jsonl"), target, (endpoint,), (logical,), 1, 10, False
    )
    assert plan.runs[0].file == native
    assert targets.workload_command(binary, logical, "slotted-ref-multi") == [
        str(binary),
        "--matcher",
        "multi",
        "--substitution",
        "snapshot",
        str(native.absolute_path),
    ]
    assert targets.workload_command(binary, logical, "slotted-ref-nested")[1:5] == [
        "--matcher",
        "nested",
        "--substitution",
        "syntactic",
    ]


def test_unsupported_nested_inputs_are_rejected_before_any_execution() -> None:
    (logical,) = workloads.resolve_files([str(INPUTS / "logic/first-order-logic.egg")], ROOT)
    cases: tuple[tuple[Treatment, models.FileSpec], ...] = (
        ("slotted-no-aliasing", logical),
        ("slotted-ref-nested", logical.for_engine("slotted")),
    )
    for treatment, physical in cases:
        with pytest.raises(ValueError, match="single nested pattern"):
            validate_engine_workload(physical, treatment)


@pytest.mark.parametrize("profile", ["release", "profiling"])
def test_reference_build_selects_unchecked_binary(
    profile: targets.BuildProfile, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    binary = tmp_path / "slotted/xmulti/target" / profile / "xmulti"
    binary.parent.mkdir(parents=True)
    binary.write_text("reference")
    commands: list[list[str]] = []
    monkeypatch.setattr(targets, "run_text", lambda command, **_kw: commands.append(command))
    row = models.TargetRow(".", str(tmp_path), "HEAD", "abc", False)
    assert targets.build_target(row, Console(quiet=True), profile, "slotted")[0] == binary
    assert commands == [
        [
            "cargo",
            "build",
            *(["--release"] if profile == "release" else ["--profile", profile]),
            "--locked",
            "--no-default-features",
            "--manifest-path",
            str(tmp_path / "slotted/xmulti/Cargo.toml"),
        ]
    ]


def test_reference_execution_collects_one_process_summary_and_native_limit(tmp_path: Path) -> None:
    source = tmp_path / "input.ref"
    source.write_text(json.dumps({"multi": "rounds 0", "nested": "rounds 0"}))
    binary = tmp_path / "reference"
    binary.write_text(
        f"#!{sys.executable}\nimport json,sys\nfrom pathlib import Path\n"
        "assert any(arg.startswith('--memory-limit-bytes=') for arg in sys.argv)\n"
        "assert sys.argv[-1].endswith('input.ref')\n"
        "assert '--matcher' in sys.argv and '--substitution' in sys.argv\n"
        f"Path(sys.argv[sys.argv.index('--timing-summary')+1]).write_text({json.dumps(make_timing_summary())!r})\n"
    )
    binary.chmod(0o755)
    file = models.FileSpec(source.name, source, targets.sha256_file(source))
    observation = collection.run_process(binary, tmp_path, file, "slotted-ref-multi", 10)
    assert observation.result.status == "success"
    assert observation.timing_summary == make_timing_summary()
    source.write_text(json.dumps({"multi": "rounds 1", "nested": "rounds 0"}))
    with pytest.raises(ValueError, match="workload changed during execution"):
        workloads.require_workload_unchanged(file)


def test_reference_capability_preflight_requires_protocol_and_limit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    binary = tmp_path / "xmulti"
    target = replace(make_target(), engine_binaries=(models.EngineBinary("slotted", "ref", binary),))
    file = models.FileSpec("input.ref", tmp_path / "input.ref", "ref-input")
    plan = collection.CollectionPlan(target, (collection.BenchmarkRunPlan(file, "slotted-ref-multi", 1, (), 1),))
    seen: list[tuple[list[str], dict[str, object]]] = []

    def execute(command: list[str], cwd: Path, timeout: int, **kwargs: object) -> collection.TimingResult:
        seen.append((command, kwargs))
        return collection.TimingResult(
            status="success",
            timing=TimingRow(wall_sec=0.01),
            error=None,
        )

    monkeypatch.setattr(collection, "run_command", execute)
    collection.preflight_collection(plan, 10)
    assert seen == [
        (
            [str(binary), "--help"],
            {
                "required_output": ("--timing-summary", "--memory-limit-bytes", "--matcher", "--substitution"),
                "native_limit": True,
            },
        )
    ]
