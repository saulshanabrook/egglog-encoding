"""Compile-only AST identity, resource stops, coverage, and portable graph binding."""

from __future__ import annotations

import io
import json
import subprocess
from pathlib import Path
from typing import Any

import pytest
from rich.console import Console

from benchmarking import pilot_ast, pilot_figures, translation_ast
from benchmarking.models import FileSpec
from benchmarking.native_memory import NATIVE_ALLOCATOR_ENV
from benchmarking.targets import sha256_file
from benchmarking.translation_ast import TranslationRequest

from .test_pilot_figures import snapshot_fixture


@pytest.fixture
def compiler_case(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    source = tmp_path / "source.egg"
    source.write_text("(sort U)\n")
    compiler = tmp_path / "compiler"
    compiler.write_bytes(b"compiler fixture")
    selected = FileSpec("source.egg", source, sha256_file(source))
    launches: list[dict[str, Any]] = []
    case: dict[str, Any] = {
        "file": selected,
        "compiler": compiler,
        "cache": tmp_path / "ast.jsonl",
        "exit": 0,
        "launches": launches,
    }

    class Process:
        def __init__(self, command: list[str], **kwargs: Any) -> None:
            launches.append({"command": command, **kwargs})
            self.command = command
            self.returncode = case["exit"]

        def __enter__(self) -> Process:
            return self

        def __exit__(self, *_args: Any) -> None:
            pass

        def communicate(self, timeout: int | None = None) -> tuple[str, str]:
            if timeout is not None and case["exit"] is None:
                raise subprocess.TimeoutExpired(self.command, timeout)
            profile = self.command[self.command.index("--profile") + 1]
            return json.dumps(
                {
                    "version": 1,
                    "status": "ok",
                    "file": str(source),
                    "profile": profile,
                    "no_aliasing": True if profile in ("s", "scp") else None,
                    "source_ast_nodes": 4,
                    "normalized_source_ast_nodes": None,
                    "output_ast_nodes": 40,
                    "include_files": [],
                    "source_normalization": "self-contained-source-v1",
                    "count_convention": "sexp-list-atom-literal-v1",
                    "error": None,
                    "error_stage": None,
                }
            ), "allocation fixture failure"

    monkeypatch.setattr(translation_ast.subprocess, "Popen", Process)
    monkeypatch.setattr(translation_ast, "terminate_process_group", lambda _process: None)
    monkeypatch.setattr(translation_ast, "git_sha", lambda _root: "recorded-source")
    monkeypatch.setattr(translation_ast, "git_dirty", lambda _root: True)
    return case


def test_each_profile_is_one_bounded_process_and_cache_identity_is_strict(compiler_case: dict[str, Any]) -> None:
    case = compiler_case
    requests = [TranslationRequest(case["file"], profile, "Math") for profile in ("c", "cp")]
    records = translation_ast.translation_ast_records(requests, case["cache"], collect=True, compiler=case["compiler"])
    assert len(records) == len(case["launches"]) == 2
    original = case["cache"].read_bytes()
    for launch, record in zip(case["launches"], records, strict=True):
        assert launch["command"][1] == "--memory-limit-bytes=17179869184"
        assert all(launch["env"][key] == value for key, value in NATIVE_ALLOCATOR_ENV.items())
        assert launch["command"][-1] == str(case["file"].absolute_path)
        assert Path(launch["command"][0]) != case["compiler"]
        assert record["compiler_binary_sha256"] == sha256_file(case["compiler"])
        assert record["dependency_boundary"]["include_files"] == []
        assert record["source_revision"] == "recorded-source" and record["source_dirty"]
        assert "programs" not in record["row"]
    assert (
        translation_ast.translation_ast_records(requests, case["cache"], collect=True, compiler=case["compiler"])
        == records
    )
    assert case["cache"].read_bytes() == original and len(case["launches"]) == 2
    case["compiler"].write_bytes(b"different compiler")
    changed = translation_ast.translation_ast_records(requests, case["cache"], collect=True, compiler=case["compiler"])
    assert changed[0]["compiler_binary_sha256"] != records[0]["compiler_binary_sha256"]
    assert len(case["launches"]) == 4 and len(case["cache"].read_bytes().splitlines()) == 4


@pytest.mark.parametrize(
    "exit_code,status", [(86, "memory-limited"), (87, "safety-failure"), (-9, "safety-failure"), (None, "timed-out")]
)
def test_recorded_resource_failure_stops_fresh_work_without_retrying_under_a_new_cap(
    compiler_case: dict[str, Any],
    exit_code: int | None,
    status: str,
) -> None:
    case = compiler_case
    case["exit"] = exit_code
    requests = [TranslationRequest(case["file"], profile, "Math") for profile in ("c", "cp")]
    records = translation_ast.translation_ast_records(requests, case["cache"], collect=True, compiler=case["compiler"])
    assert len(records) == len(case["launches"]) == 1
    assert records[0]["status"] == status and records[0]["row"]["output_ast_nodes"] is None
    case["exit"] = 0
    repeated = translation_ast.translation_ast_records(
        requests,
        case["cache"],
        collect=True,
        compiler=case["compiler"],
        memory_limit_bytes=None,
    )
    assert repeated == records and len(case["launches"]) == 1


def test_snapshot_cache_replay_needs_no_inputs_compiler_or_checkout(
    compiler_case: dict[str, Any],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    case = compiler_case
    requests = [TranslationRequest(case["file"], "c", "Math")]
    records = translation_ast.translation_ast_records(requests, case["cache"], collect=True, compiler=case["compiler"])
    before = case["cache"].read_bytes()
    case["file"].absolute_path.unlink()
    case["compiler"].unlink()
    monkeypatch.setattr(translation_ast, "git_sha", lambda *_a: pytest.fail("cache replay inspected git"))
    assert translation_ast.translation_ast_records(requests, case["cache"]) == records
    assert case["cache"].read_bytes() == before and len(case["launches"]) == 1


def test_external_dependencies_rejected_before_compilation(compiler_case: dict[str, Any]) -> None:
    case = compiler_case
    case["file"].absolute_path.write_text('(include "other.egg")\n')
    with pytest.raises(ValueError, match="self-contained"):
        translation_ast.translation_ast_records(
            [TranslationRequest(case["file"], "c", "Math")],
            case["cache"],
            collect=True,
            compiler=case["compiler"],
        )
    assert not case["launches"] and not case["cache"].exists()


def test_broad_plan_keeps_all_486_applications_plus_extension_configurations(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    names = [f"benchmarks/corpus/project/app-{i}.egg" for i in range(486)]
    slotted = [f"benchmarks/slotted/case-{i}.egg" for i in range(10)]
    selected = [*names, *slotted, "math.egg", "parameter.egg"]
    files = {name: FileSpec(name, tmp_path / name, f"sha256:{name}") for name in selected}
    config = {
        "experiments": [
            {"id": "corpus-congruence", "files": names},
            {"id": "math", "files": ["math.egg"]},
            {"id": "disequality", "files": ["parameter.egg"]},
            {"id": "slotted", "files": slotted},
            {"id": "slotted-complete", "files": slotted},
        ]
    }
    monkeypatch.setattr(pilot_ast, "translation_ast_records", lambda *_args, **_kwargs: ())
    snapshot = pilot_ast.translation_program_size_snapshot(config, files, tmp_path / "missing", collect=False)
    result = pilot_ast.translation_program_size_results(snapshot)
    assert len(result["rows"]) == 1016 and result["points"] == []
    assert [row["planned"] for row in result["coverage"]] == [487, 487, 1, 1, 10, 10, 10, 10]
    assert len({(row["file_sha256"], row["profile"], row["no_aliasing"]) for row in result["rows"]}) == 1016
    assert {row["configuration"] for row in result["rows"] if row["no_aliasing"] is True} == {"egglog+s′", "egglog+s′p"}
    assert {row["configuration"] for row in result["rows"] if row["no_aliasing"] is False} == {"egglog+s", "egglog+sp"}
    assert all(row["status"] == "pending" for row in result["rows"])


def test_graph_fits_each_log_axis_and_clips_guides_without_confidence_intervals(compiler_case: dict[str, Any]) -> None:
    case = compiler_case
    records = translation_ast.translation_ast_records(
        [TranslationRequest(case["file"], "c", "Math")],
        case["cache"],
        collect=True,
        compiler=case["compiler"],
    )
    planned = [{key: records[0][key] for key in ("file", "file_sha256", "profile", "no_aliasing", "family", "project")}]
    planned.append({**planned[0], "profile": "cp"})
    snapshot = {"status": "pending", "inputs": planned, "records": list(records), "issue": None}
    result = pilot_ast.translation_program_size_results(snapshot)
    spec = pilot_ast.translation_program_size_spec(result)
    assert len(result["points"]) == 1 and len(result["rows"]) == 2
    assert result["points"][0]["growth"] == 10
    assert result["points"][0]["configuration"] == "corelog+c"
    marks = spec["layer"][-1]
    assert marks["mark"]["type"] == "circle" and marks["mark"]["filled"]
    assert "shape" not in marks["encoding"]
    color = marks["encoding"]["color"]
    assert color["legend"]["direction"] == "horizontal"
    assert len(color["scale"]["domain"]) == len(set(color["scale"]["range"])) == 8
    x_domain = marks["encoding"]["x"]["scale"]["domain"]
    y_domain = marks["encoding"]["y"]["scale"]["domain"]
    assert x_domain != y_domain
    assert x_domain[0] < 4 < x_domain[1] and y_domain[0] < 40 < y_domain[1]
    for layer in spec["layer"]:
        for axis in ("x", "y"):
            assert not layer["encoding"][axis]["axis"]["grid"]
            assert len(layer["encoding"][axis]["axis"]["values"]) <= 6
    assert spec["layer"][-1]["encoding"]["x"]["scale"]["type"] == "log"
    assert "x_low" not in json.dumps(spec) and "y_low" not in json.dumps(spec)
    assert [row["label"] for row in spec["layer"][0]["data"]["values"]] == ["10×"]
    for guide in spec["layer"][0]["data"]["values"]:
        for x_key, y_key in (("x", "y"), ("x2", "y2")):
            assert x_domain[0] <= guide[x_key] <= x_domain[1]
            assert y_domain[0] <= guide[y_key] <= y_domain[1]
            assert guide[y_key] / guide[x_key] == pytest.approx(float(guide["label"].removesuffix("×")))
        label = next(row for row in spec["layer"][1]["data"]["values"] if row["label"] == guide["label"])
        assert label["x"] == guide["x2"] and label["y"] == guide["y2"]
        assert label["edge"] in ("top", "right")
        assert label["y"] / label["x"] == pytest.approx(guide["y"] / guide["x"])


def test_portable_bundle_redraws_ast_without_collectors_inputs_or_cache(
    compiler_case: dict[str, Any],
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    case = compiler_case
    records = translation_ast.translation_ast_records(
        [TranslationRequest(case["file"], "c", "Math")],
        case["cache"],
        collect=True,
        compiler=case["compiler"],
    )
    planned = [{key: records[0][key] for key in ("file", "file_sha256", "profile", "no_aliasing", "family", "project")}]
    snapshot = snapshot_fixture()
    snapshot["translation_program_size"] = {
        "status": "complete",
        "inputs": planned,
        "records": list(records),
        "issue": None,
    }
    monkeypatch.setattr(pilot_figures, "renderer_metadata", lambda: {"git_sha": "renderer", "is_dirty": True})
    source = tmp_path / "source"
    pilot_figures.export_pilot(snapshot, source, Console(file=io.StringIO()), images=False)
    case["file"].absolute_path.unlink()
    case["compiler"].unlink()
    case["cache"].unlink()
    monkeypatch.setattr(pilot_figures, "load_experiments", lambda *_a: pytest.fail("portable replay opened inputs"))
    monkeypatch.setattr(pilot_figures, "ReportStore", lambda *_a: pytest.fail("portable replay opened cache"))
    monkeypatch.setattr(
        pilot_ast, "translation_ast_records", lambda *_a, **_k: pytest.fail("portable replay collected")
    )
    original = pilot_figures.export_pilot
    monkeypatch.setattr(
        pilot_figures, "export_pilot", lambda saved, dest, console: original(saved, dest, console, images=False)
    )
    destination = tmp_path / "redrawn"
    assert pilot_figures.main(["--reuse-from", str(source), "--no-runs", "--output-dir", str(destination)]) == 0
    results = json.loads((destination / "program-size.results.json").read_text())
    assert results["translation_program_size_snapshot"] == snapshot["translation_program_size"]
    assert results["points"][0]["y"] == 40
    assert (source / "program-size.bound.vl.json").read_bytes() == (
        destination / "program-size.bound.vl.json"
    ).read_bytes()
    paired = json.loads((destination / "extensions-runtime-size.results.json").read_bytes())
    spec = json.loads((destination / "extensions-runtime-size.bound.vl.json").read_bytes())
    assert paired["pilot_snapshot"] == snapshot
    assert (
        paired["runtime"]["selection_sha256"]
        == json.loads((destination / "extensions-runtime.results.json").read_bytes())["selection_sha256"]
    )
    assert len(paired["program_size"]["points"]) == 1
    assert spec["resolve"]["scale"] == {"x": "independent", "y": "independent", "color": "shared"}
    left, right = spec["hconcat"]
    assert left["layer"][-1]["encoding"]["color"] == right["layer"][-1]["encoding"]["color"]
    assert left["layer"][-1]["encoding"]["color"]["legend"]["columns"] == 4
    assert all("x_low" in point for point in left["data"]["values"])
    assert all("x_low" not in point for point in right["layer"][-1]["data"]["values"])
    assert "extlog_" not in json.dumps(spec)
