"""AST collection is identity-cached and rendering uses persisted measurements only."""

from __future__ import annotations

import json
import subprocess
from dataclasses import replace
from pathlib import Path
from typing import Any

import pytest

from benchmarking import pilot_ast, slotted_ast
from benchmarking.models import FileSpec
from benchmarking.targets import sha256_file


@pytest.fixture
def ast_case(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    file = tmp_path / "case_1st.egg"
    file.write_text("(sort U)\n")
    native = file.with_suffix(".ref")
    native.write_text("native fixture")
    compiler = tmp_path / "compiler"
    compiler.write_text("compiler fixture")
    physical = FileSpec(str(native), native, sha256_file(native))
    selected = FileSpec(str(file), file, sha256_file(file), (("slotted-reference", physical),))
    measured: dict[str, Any] = {
        "file": str(file),
        "benchmark": file.stem,
        "compiler_binary": str(compiler),
        "programs": {"source": file.read_text(), "slotted": "(sort U) (rule () ())", "proof_congruence": None},
        "source_ast_nodes": 4,
        "slotted_ast_nodes": 8,
        "proof_compatible_slotted_ast_nodes": 12,
        "proof_congruence_ast_nodes": None,
        "proof_congruence_error": "uses subst, which has no proof translation",
        "proof_congruence_error_debug": "Source(UnsupportedProofFeature { feature: Substitution })",
        "proof_congruence_error_stage": "source-slotted-proofs",
        "congruence_ast_nodes": None,
        "congruence_error": "primitive lacks a validator",
    }
    launches = []

    def measure(args: list[str], **_kwargs: Any) -> Any:
        assert args == [str(compiler), str(file)]
        launches.append(args)
        return subprocess.CompletedProcess(args, 0, json.dumps(measured) + "\n")

    monkeypatch.setattr(slotted_ast.subprocess, "run", measure)
    monkeypatch.setattr(slotted_ast, "git_sha", lambda _root: "recorded-source-revision")
    return {
        "file": selected,
        "compiler": compiler,
        "cache": tmp_path / "cache.jsonl",
        "measured": measured,
        "launches": launches,
    }


def test_warm_cached_render_needs_no_inputs_or_compiler(
    ast_case: dict[str, Any], tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    case = ast_case
    records = slotted_ast.slotted_ast_records([case["file"]], case["cache"], collect=True, compiler=case["compiler"])
    original = case["cache"].read_bytes()
    assert len(original.splitlines()) == 1 and "programs" not in records[0]["row"]
    assert records[0]["row"]["reference_sha256"] == case["file"].for_binary("slotted-reference").sha256
    assert records[0]["compiler_binary_sha256"] == sha256_file(case["compiler"])
    monkeypatch.setattr(
        slotted_ast.subprocess, "run", lambda *_args, **_kw: pytest.fail("warm cache launched a compiler")
    )
    monkeypatch.setattr(slotted_ast, "git_sha", lambda *_args: pytest.fail("renderer inspected the checkout"))
    assert (
        slotted_ast.slotted_ast_records([case["file"]], case["cache"], collect=True, compiler=case["compiler"])
        == records
    )
    case["compiler"].unlink()
    case["file"].absolute_path.unlink()
    assert slotted_ast.slotted_ast_records([case["file"]], case["cache"]) == records
    outputs = slotted_ast.export_slotted_ast(records, tmp_path / "out")
    report = json.loads((tmp_path / "out/slotted-runtime.ast.json").read_text())
    assert report["source_revision"] == "recorded-source-revision"
    assert report["rows"][0]["proof_congruence_ast_nodes"] is None
    assert report["rows"][0]["proof_congruence_error_stage"] == "source-slotted-proofs"
    assert "UnsupportedProofFeature" in report["rows"][0]["proof_congruence_error_debug"]
    assert "Unsupported" in (tmp_path / "out/slotted-runtime.ast.tex").read_text()
    assert (tmp_path / "out/slotted-runtime.files.txt").read_text() == (
        f"{case['file'].display_path}\t{case['file'].for_binary('slotted-reference').display_path}\n"
    )
    assert len(outputs) == 5 and not (tmp_path / "out/slotted-runtime.ast-programs.json").exists()
    assert case["cache"].read_bytes() == original


def test_pilot_program_sizes_keep_fresh_records_and_replay_under_new_names(
    ast_case: dict[str, Any], tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    case = ast_case
    case["measured"].update(
        proof_congruence_ast_nodes=16,
        proof_congruence_error=None,
        proof_congruence_error_debug=None,
        proof_congruence_error_stage=None,
    )
    case["measured"]["programs"]["proof_congruence"] = "(sort Proof)"
    records = slotted_ast.slotted_ast_records([case["file"]], case["cache"], collect=True, compiler=case["compiler"])
    calls = []

    def select(files: tuple[FileSpec, ...], cache: Path, *, collect: bool) -> tuple[dict[str, Any], ...]:
        calls.append((files, cache, collect))
        return records

    monkeypatch.setattr(pilot_ast, "slotted_ast_records", select)
    snapshot = pilot_ast.program_size_snapshot((case["file"],), case["cache"], collect=True)
    assert calls == [((case["file"],), case["cache"], True)]
    case["compiler"].unlink()
    case["file"].absolute_path.unlink()
    outputs = pilot_ast.export_program_size(snapshot, tmp_path / "pilot")
    assert len(outputs) == 5
    table = (tmp_path / "pilot/slotted-program-size.table.tex").read_text()
    assert "16" in table and "Unsupported" not in table
    report = json.loads((tmp_path / "pilot/slotted-program-size.results.json").read_text())
    assert report["figure"] == "slotted-program-size"
    assert report["program_size_snapshot"] == snapshot
    assert report["rows"][0]["program_sha256"]["proof_congruence"]
    assert report["rows"][0]["measurement_source"]["source_revision"] == "recorded-source-revision"
    assert not list((tmp_path / "pilot").glob("slotted-runtime.*"))


def test_missing_pilot_size_cache_is_pending_without_building(
    ast_case: dict[str, Any], tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(slotted_ast.subprocess, "run", lambda *_a, **_k: pytest.fail("pending export built a compiler"))
    snapshot = pilot_ast.program_size_snapshot((ast_case["file"],), ast_case["cache"], collect=False)
    assert snapshot["status"] == "pending" and not snapshot["records"]
    pilot_ast.export_program_size(snapshot, tmp_path / "pilot")
    table = (tmp_path / "pilot/slotted-program-size.table.tex").read_text()
    assert "pending" in table and "Unsupported" not in table


@pytest.mark.parametrize("changed", ["input", "compiler", "options", "version"])
def test_identity_changes_miss_the_cache(
    ast_case: dict[str, Any], monkeypatch: pytest.MonkeyPatch, changed: str
) -> None:
    case = ast_case
    slotted_ast.slotted_ast_records([case["file"]], case["cache"], collect=True, compiler=case["compiler"])
    file = case["file"]
    if changed == "input":
        file = replace(file, sha256="sha256:changed-input")
    elif changed == "compiler":
        case["compiler"].write_text("new compiler")
    elif changed == "options":
        monkeypatch.setattr(slotted_ast, "PIPELINE", {**slotted_ast.PIPELINE, "no_aliasing": False})
    else:
        monkeypatch.setattr(slotted_ast, "CACHE_VERSION", 2)
    with pytest.raises(ValueError, match="missing 1 inputs"):
        slotted_ast.slotted_ast_records([file], case["cache"], compiler=case["compiler"])
    assert len(case["launches"]) == 1


@pytest.mark.parametrize("error", [subprocess.CalledProcessError(1, ["cargo"]), KeyboardInterrupt()])
def test_build_failures_and_interruptions_are_not_cached(
    ast_case: dict[str, Any], monkeypatch: pytest.MonkeyPatch, error: BaseException
) -> None:
    def fail(*_args: Any, **_kwargs: Any) -> None:
        raise error

    monkeypatch.setattr(slotted_ast.subprocess, "run", fail)
    with pytest.raises(type(error)):
        slotted_ast.slotted_ast_records([ast_case["file"]], ast_case["cache"], collect=True)
    assert not ast_case["cache"].exists()


@pytest.mark.parametrize("changed", ["source", "selection"])
def test_measurement_drift_does_not_publish_records(ast_case: dict[str, Any], changed: str) -> None:
    case = ast_case
    if changed == "source":
        case["measured"]["programs"]["source"] = "(sort Changed)"
    else:
        case["measured"]["file"] = "different.egg"
    with pytest.raises(ValueError, match="changed|different workload"):
        slotted_ast.slotted_ast_records([case["file"]], case["cache"], collect=True, compiler=case["compiler"])
    assert not case["cache"].exists()


def test_explicit_collection_resolves_current_compiler_before_reusing_unsupported(
    ast_case: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    case = ast_case
    old = slotted_ast.slotted_ast_records([case["file"]], case["cache"], collect=True, compiler=case["compiler"])
    current = case["compiler"].with_name("current-compiler")
    current.write_text("new compiler with proof support")
    measured = dict(case["measured"])
    measured.update(
        compiler_binary=str(current),
        proof_congruence_ast_nodes=16,
        proof_congruence_error=None,
        proof_congruence_error_debug=None,
        proof_congruence_error_stage=None,
    )
    measured["programs"] = {**measured["programs"], "proof_congruence": "(sort Proof)"}
    lowered = []

    def run(args: list[str], **_kwargs: Any) -> Any:
        if args[0] == "cargo":
            return subprocess.CompletedProcess(
                args,
                0,
                json.dumps(
                    {"reason": "compiler-artifact", "target": {"name": "slotted_ast"}, "executable": str(current)}
                )
                + "\n",
            )
        lowered.append(args)
        return subprocess.CompletedProcess(args, 0, json.dumps(measured) + "\n")

    monkeypatch.setattr(slotted_ast.subprocess, "run", run)
    new = slotted_ast.slotted_ast_records([case["file"]], case["cache"], collect=True)
    assert new[0]["compiler_binary_sha256"] != old[0]["compiler_binary_sha256"]
    assert new[0]["row"]["proof_congruence_ast_nodes"] == 16
    assert slotted_ast.slotted_ast_records([case["file"]], case["cache"], collect=True) == new
    assert len(lowered) == 1 and len(case["cache"].read_text().splitlines()) == 2


def test_unicode_ast_cache_and_exports_use_utf8(
    ast_case: dict[str, Any], tmp_path: Path, non_utf8_text_defaults: None
) -> None:
    ast_case["measured"]["benchmark"] = "mmm_sum_1st-44rules"
    ast_case["measured"]["proof_congruence_error"] = "Σ has no proof translation"
    records = slotted_ast.slotted_ast_records(
        [ast_case["file"]], ast_case["cache"], collect=True, compiler=ast_case["compiler"]
    )
    assert "Σ" in ast_case["cache"].read_bytes().decode("utf-8")
    assert slotted_ast.slotted_ast_records([ast_case["file"]], ast_case["cache"]) == records
    outputs = slotted_ast.export_slotted_ast(records, tmp_path / "unicode")
    assert all(path.read_bytes().decode("utf-8") for path in outputs)
    assert "ΣMMM" in (tmp_path / "unicode/slotted-runtime.ast.csv").read_bytes().decode("utf-8")
    assert "Σ has no proof translation" in (tmp_path / "unicode/slotted-runtime.ast.md").read_bytes().decode("utf-8")
