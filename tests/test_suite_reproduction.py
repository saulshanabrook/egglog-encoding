"""The reproduction CLI resumes acquisition without touching timed observations."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from scripts import suite_reproduction as reproduction


@pytest.fixture
def coordinator(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[Path, list[str]]:
    (tmp_path / "benchmarks/reproduction").mkdir(parents=True)
    (tmp_path / "benchmarks/reproduction/population.json").write_text("{}")
    (tmp_path / "benchmarks/catalog.json").write_text("{}")
    cache = tmp_path / ".reports.jsonl"
    cache.write_text("untouched performance cache\n")
    storage = tmp_path / "evidence"
    storage.mkdir()
    (storage / "settings.json").write_text(json.dumps({"eggcc": {"paths": {}, "revision": "one"}}))
    cases = [
        {"id": name, "family": "eggcc", "scope": "required", "source": name, "configuration": {}}
        for name in ["one", "two"]
    ]
    monkeypatch.setattr(reproduction, "ROOT", tmp_path)
    monkeypatch.setattr(reproduction, "STORAGE", storage)
    monkeypatch.setattr(reproduction, "expected_cases", lambda *_: cases)
    monkeypatch.setattr(reproduction, "case_identity", lambda case, settings, **_: {"case": case, "settings": settings})
    launched: list[str] = []

    def capture(case: dict[str, Any], settings: dict[str, Any], output: Path) -> dict[str, Any]:
        launched.append(case["id"])
        output.mkdir()
        replay = output / "full.egg"
        replay.write_text("(check (= 1 1))")
        return {
            "status": "reproduced",
            "source_completion": {"status": "success"},
            "workloads": [str(replay)],
            "sessions": [{"replay": str(replay)}],
            "materialization": {"complete": True, "expected_sessions": 1, "materialized_sessions": 1},
        }

    monkeypatch.setattr(reproduction, "capture_case", capture)
    return storage, launched


def test_cached_and_changed_revision_selection(coordinator: tuple, tmp_path: Path) -> None:
    storage, launched = coordinator
    assert reproduction.main(["--family", "eggcc", "--family", "eggcc", "--stage", "capture"]) == 0
    assert launched == ["one", "two"]
    assert reproduction.main(["--family", "eggcc", "--stage", "capture"]) == 0
    assert launched == ["one", "two"]
    settings = storage / "settings.json"
    settings.write_text(json.dumps({"eggcc": {"paths": {}, "revision": "two"}}))
    assert reproduction.main(["--family", "eggcc", "--case", "one", "--stage", "capture"]) == 0
    assert launched == ["one", "two", "one"]
    assert (tmp_path / ".reports.jsonl").read_text() == "untouched performance cache\n"


def test_capture_only_success_is_pending_in_both_publications(coordinator: tuple) -> None:
    storage, launched = coordinator
    assert reproduction.main(["--family", "eggcc", "--stage", "capture"]) == 0
    assert launched == ["one", "two"]
    index = json.loads((storage / "index.json").read_text())
    assert {record["status"] for record in index.values()} == {"success"}
    report = json.loads((storage / "report.json").read_text())
    assert {row["outcome"]["status"] for row in report["cases"]} == {"pending"}
    assert "| eggcc | 2 | 0 | 2 | 0 |" in (storage / "REPORT.md").read_text()
    corpus = json.loads((storage / "corpus/manifest.json").read_text())
    assert {case["status"] for case in corpus["cases"]} == {"pending"}
    assert corpus["workloads"] == []
    assert reproduction.main(["--family", "eggcc", "--stage", "capture"]) == 0
    assert launched == ["one", "two"]


def test_amx_paper_cells_remain_separate_from_program_successes(coordinator: tuple, tmp_path: Path) -> None:
    storage, _ = coordinator
    cells = [
        {"schedule": "reference", "layout": "VNNI", "supported": True, "source_mapping": "unresolved"},
        {"schedule": "preload-B", "layout": "standard", "supported": False, "source_mapping": "unresolved"},
    ]
    (tmp_path / "benchmarks/reproduction/population.json").write_text(json.dumps({"hardboiled": {"amx_cells": cells}}))
    assert reproduction.main(["--stage", "report"]) == 0
    report = json.loads((storage / "report.json").read_text())
    assert [cell["status"] for cell in report["hardboiled_amx_paper_cells"]] == [
        "mapping-unresolved",
        "paper-unsupported",
    ]
    text = (storage / "REPORT.md").read_text()
    assert "| reference | VNNI | mapping-unresolved |" in text
    assert "| preload-B | standard | paper-unsupported |" in text
    assert len(report["cases"]) == 2


def test_nested_safety_stop_halts_and_remains_cached(coordinator: tuple, monkeypatch: pytest.MonkeyPatch) -> None:
    storage, launched = coordinator

    def capture(case: dict, settings: dict, output: Path) -> dict:
        launched.append(case["id"])
        return {"status": "blocked", "source_completion": {"status": "memory-limit"}, "workloads": []}

    monkeypatch.setattr(reproduction, "capture_case", capture)
    assert reproduction.main(["--family", "eggcc", "--stage", "capture"]) == 2
    assert launched == ["one"]
    assert reproduction.main(["--family", "eggcc", "--stage", "capture"]) == 2
    assert launched == ["one", "two"]
    assert reproduction.main(["--family", "eggcc", "--stage", "capture"]) == 1
    assert launched == ["one", "two"]
    report = json.loads((storage / "report.json").read_text())
    assert [case["outcome"]["status"] for case in report["cases"]] == ["memory-limit", "memory-limit"]


def test_full_family_requires_paper_mapping_even_when_all_parents_validate(
    coordinator: tuple, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    storage, launched = coordinator
    cases = [{**case, "family": "hardboiled"} for case in reproduction.expected_cases({}, {})]
    monkeypatch.setattr(reproduction, "expected_cases", lambda *_: cases)
    for name in reproduction.VALIDATION_SOURCES:
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("validator")
    engine = tmp_path / "engine"
    engine.write_text("engine")
    (storage / "settings.json").write_text(json.dumps({"hardboiled": {"paths": {"egglog": str(engine)}}}))
    (tmp_path / "benchmarks/reproduction/population.json").write_text(
        json.dumps(
            {
                "hardboiled": {
                    "amx_cells": [
                        {"schedule": "preload-A", "layout": "VNNI", "supported": True, "source_mapping": "unresolved"}
                    ]
                }
            }
        )
    )

    def validate(capture: dict, engine: Path, output: Path, **kwargs: Any) -> dict:
        output.mkdir()
        (output / "receipt.json").write_text("ordinary validation")
        return {
            "status": "success",
            "workloads": capture["workloads"],
            "validations": [
                {
                    "replay": path,
                    "replay_sha256": reproduction.sha256_file(Path(path)),
                    "status": "success",
                    "output_contract_passed": True,
                }
                for path in capture["workloads"]
            ],
        }

    monkeypatch.setattr(reproduction, "validate_capture", validate)
    assert reproduction.main(["--family", "hardboiled"]) == 1
    assert launched == ["one", "two"]
    assert "| hardboiled | 2 | 2 | 0 | 0 |" in (storage / "REPORT.md").read_text()
    assert reproduction.main(["--family", "hardboiled", "--case", "one"]) == 0
    assert launched == ["one", "two"]


@pytest.mark.parametrize("phase", ["capture", "replay"])
@pytest.mark.parametrize("status", ["timed-out", "memory-limit", "resource-stopped"])
def test_cached_stop_resumes_other_cases_but_changed_identity_and_retry_stop_again(
    coordinator: tuple, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, phase: str, status: str
) -> None:
    storage, launched = coordinator
    for name in reproduction.VALIDATION_SOURCES:
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("validator identity")
    engine = tmp_path / "engine"
    engine.write_text("ordinary executable")
    settings = {"eggcc": {"paths": {"egglog": str(engine)}, "revision": "one"}}
    settings_path = storage / "settings.json"
    settings_path.write_text(json.dumps(settings))
    validations: list[Path] = []

    if phase == "capture":

        def capture(case: dict, settings: dict, output: Path) -> dict:
            launched.append(case["id"])
            return {"status": status, "workloads": []}

        monkeypatch.setattr(reproduction, "capture_case", capture)
    else:

        def validate(capture: dict, engine: Path, output: Path, **kwargs: Any) -> dict:
            validations.append(output)
            output.mkdir()
            (output / "failure.log").write_text(status)
            return {"status": status, "workloads": []}

        monkeypatch.setattr(reproduction, "validate_capture", validate)

    args = ["--family", "eggcc", "--stage", "all"]
    assert reproduction.main(args) == 2
    assert launched == ["one"]
    original = json.loads((storage / "index.json").read_text())["one"]
    receipt = Path(original["attempt"]) / "stage.json"
    original_bytes = receipt.read_bytes()
    assert reproduction.main(args) == 2
    assert launched == ["one", "two"]
    assert reproduction.main(args) == 1
    assert launched == ["one", "two"]
    assert len(validations) == (2 if phase == "replay" else 0)
    assert {row["status"] for row in json.loads((storage / "index.json").read_text()).values()} == {status}

    settings["eggcc"]["revision"] = "changed source"
    settings_path.write_text(json.dumps(settings))
    assert reproduction.main([*args, "--case", "one"]) == 2
    assert launched == ["one", "two", "one"]
    assert reproduction.main([*args, "--case", "one", "--retry"]) == 2
    assert launched == ["one", "two", "one", "one"]
    assert len(validations) == (4 if phase == "replay" else 0)
    assert receipt.read_bytes() == original_bytes


def test_failed_parent_never_promotes_prefix(coordinator: tuple, monkeypatch: pytest.MonkeyPatch) -> None:
    storage, launched = coordinator

    def capture(case: dict, settings: dict, output: Path) -> dict:
        launched.append(case["id"])
        return {
            "status": "blocked",
            "source_completion": {"status": "failed"},
            "reason": "compiler failed after export",
        }

    monkeypatch.setattr(reproduction, "capture_case", capture)
    assert reproduction.main(["--family", "eggcc"]) == 1
    assert reproduction.main(["--family", "eggcc"]) == 1
    assert launched == ["one", "two"]
    assert "compiler failed after export" in (storage / "REPORT.md").read_text()


def test_changed_configuration_marks_old_failure_historical_without_rerunning(
    coordinator: tuple, monkeypatch: pytest.MonkeyPatch
) -> None:
    storage, launched = coordinator

    def capture(case: dict, *args: object) -> dict:
        launched.append(case["id"])
        return {"status": "blocked", "reason": "old source compiler failed"}

    monkeypatch.setattr(reproduction, "capture_case", capture)
    assert reproduction.main(["--family", "eggcc", "--stage", "capture"]) == 1
    assert reproduction.main(["--stage", "report"]) == 0
    assert json.loads((storage / "index.json").read_text())["one"]["status"] == "blocked"
    (storage / "settings.json").write_text(json.dumps({"eggcc": {"paths": {}, "revision": "repaired"}}))
    assert reproduction.main(["--stage", "report"]) == 0
    result = json.loads((storage / "index.json").read_text())["one"]
    assert result["status"] == "pending" and result["historical_status"] == "blocked"
    assert "Stale evidence" in result["reason"]
    assert launched == ["one", "two"]


def test_completed_parent_with_blocked_export_never_reaches_validation(
    coordinator: tuple, monkeypatch: pytest.MonkeyPatch
) -> None:
    storage, launched = coordinator

    def capture(case: dict, settings: dict, output: Path) -> dict:
        launched.append(case["id"])
        return {
            "status": "blocked",
            "source_completion": {"status": "success"},
            "sessions": [{"replay": "valid-prefix.egg"}],
            "materialization": {"complete": False, "expected_sessions": 2, "materialized_sessions": 1},
            "reason": "later session is not representable",
        }

    monkeypatch.setattr(reproduction, "capture_case", capture)
    monkeypatch.setattr(reproduction, "validate_capture", lambda *_a, **_k: pytest.fail("partial export admitted"))
    assert reproduction.main(["--family", "eggcc"]) == 1
    assert launched == ["one", "two"]
    assert all(row["status"] == "blocked" for row in json.loads((storage / "index.json").read_text()).values())


@pytest.mark.parametrize("changed", ["settings", "artifact"])
def test_report_refresh_marks_stale_success_pending_in_report_and_index(coordinator: tuple, changed: str) -> None:
    storage, launched = coordinator
    assert reproduction.main(["--family", "eggcc", "--stage", "capture"]) == 0
    index = json.loads((storage / "index.json").read_text())
    if changed == "settings":
        (storage / "settings.json").write_text(json.dumps({"eggcc": {"paths": {}, "revision": "changed"}}))
    else:
        next(Path(path) for path in index["one"]["artifacts"] if path.endswith("full.egg")).unlink()
    assert reproduction.main(["--stage", "report"]) == 0
    assert launched == ["one", "two"]
    index = json.loads((storage / "index.json").read_text())
    report = json.loads((storage / "report.json").read_text())
    assert index["one"]["status"] == "pending" and index["one"]["historical_status"] == "success"
    assert "Stale evidence" in index["one"]["reason"]
    assert report["cases"][0]["outcome"] == index["one"]
    assert report["cases"][1]["outcome"]["status"] == "pending"


@pytest.mark.parametrize("family", ["eggcc", "churchroad", "hardboiled", "dialegg", "speq"])
@pytest.mark.parametrize("helper", ["scripts/hardboiled_replay.py", "scripts/dialegg_speq_complete.py"])
def test_imported_validation_helpers_are_in_every_capture_identity(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, family: str, helper: str
) -> None:
    monkeypatch.setattr(reproduction, "ROOT", tmp_path)
    path = tmp_path / helper
    path.parent.mkdir(parents=True)
    path.write_text("old validation behavior")
    case = {"id": "case", "family": family, "source": "input", "configuration": {}}
    before = reproduction.case_identity(case, {"paths": {}})
    path.write_text("new validation behavior")
    after = reproduction.case_identity(case, {"paths": {}})
    assert before != after
    assert before["inputs"][str(path)] != after["inputs"][str(path)]


def test_changed_imported_validator_invalidates_validation_attempt(
    coordinator: tuple, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    storage, launched = coordinator
    for name in reproduction.VALIDATION_SOURCES:
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("initial helper")
    engine = tmp_path / "engine"
    engine.write_text("ordinary engine identity")
    (storage / "settings.json").write_text(json.dumps({"eggcc": {"paths": {"egglog": str(engine)}}}))
    validations = []

    def validate(capture: dict, engine: Path, output: Path, **kwargs: Any) -> dict:
        validations.append(output)
        output.mkdir()
        (output / "receipt.json").write_text("retained ordinary validation")
        return {
            "status": "success",
            "workloads": capture["workloads"],
            "validations": [
                {
                    "replay": path,
                    "replay_sha256": reproduction.sha256_file(Path(path)),
                    "status": "success",
                    "output_contract_passed": True,
                }
                for path in capture["workloads"]
            ],
        }

    monkeypatch.setattr(reproduction, "validate_capture", validate)
    argv = ["--family", "eggcc", "--case", "one"]
    assert reproduction.main(argv) == 0
    assert reproduction.main(argv) == 0
    assert len(validations) == 1 and launched == ["one"]
    (tmp_path / "scripts/hardboiled_replay.py").write_text("changed parser/check behavior")
    assert reproduction.main(argv) == 0
    assert len(validations) == 2 and launched == ["one"]


@pytest.fixture
def misaal_identity(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[dict, dict, Path]:
    monkeypatch.setattr(reproduction, "ROOT", tmp_path)
    checkout = tmp_path / "checkout"
    sources = [
        "lib/compiler/EggLogCompiler.py",
        "lib/compiler/HydrideCompiler.py",
        "generators/one/src/one_generator.cpp",
    ]
    source_hashes = {}
    for name in sources:
        path = checkout / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(name)
        source_hashes[name] = hashlib.sha256(path.read_bytes()).hexdigest()
    request: dict[str, Any] = {
        "case_id": "misaal-one",
        "source": "generators/one",
        "configuration": {"target": "paper"},
        "revision": "a" * 40,
        "checkout": str(checkout),
        "source_hashes": source_hashes,
        "expected_generator_outputs": [],
        "egglog_export": "egglog-only-v1",
    }
    from scripts import reproduction_misaal_export

    monkeypatch.setattr(reproduction_misaal_export, "verify_export_request", lambda _: None)
    for name in ["backend", "python", "generator"]:
        path = tmp_path / name
        path.write_text("identity fixture, never executed")
        path.chmod(0o755)
        request[name] = str(path)
        request[name + "_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
    request["generator_command"] = [request["generator"], "{output}"]
    requests = tmp_path / "requests"
    requests.mkdir()
    path = requests / "misaal-one.json"
    path.write_text(json.dumps(request))
    case = {
        "id": "misaal-one",
        "family": "misaal",
        "source": request["source"],
        "configuration": request["configuration"],
    }
    return case, {"egglog_export": "egglog-only-v1", "paths": {"requests": str(requests)}}, path


@pytest.mark.parametrize("field", ["case_id", "source", "configuration"])
def test_misaal_request_cannot_impersonate_selected_inventory_case(misaal_identity: tuple, field: str) -> None:
    case, settings, path = misaal_identity
    request = json.loads(path.read_text())
    request[field] = {"target": "other"} if field == "configuration" else "another-case"
    path.write_text(json.dumps(request))
    with pytest.raises(ValueError, match="differs from the inventory"):
        reproduction.case_identity(case, settings)


@pytest.mark.parametrize("kind", ["backend", "python", "generator", "source"])
def test_misaal_referenced_inputs_are_verified_before_cache_lookup(misaal_identity: tuple, kind: str) -> None:
    case, settings, path = misaal_identity
    request = json.loads(path.read_text())
    before = reproduction.case_identity(case, settings)
    changed = (
        Path(request[kind]) if kind != "source" else Path(request["checkout"]) / "generators/one/src/one_generator.cpp"
    )
    assert str(changed) in before["inputs"]
    changed.write_text("changed after request was prepared")
    with pytest.raises(ValueError, match="identity changed"):
        reproduction.case_identity(case, settings)


def test_misaal_selected_source_generator_requires_an_explicit_pin(misaal_identity: tuple) -> None:
    case, settings, path = misaal_identity
    request = json.loads(path.read_text())
    del request["source_hashes"]["generators/one/src/one_generator.cpp"]
    path.write_text(json.dumps(request))
    with pytest.raises(ValueError, match="pin the selected source generator"):
        reproduction.case_identity(case, settings)


def test_other_misaal_requests_do_not_invalidate_selected_capture(misaal_identity: tuple) -> None:
    case, settings, path = misaal_identity
    before = reproduction.case_identity(case, settings)
    path.with_name("another-request.json").write_text("unrelated request")
    assert reproduction.case_identity(case, settings) == before
    request = json.loads(path.read_text())
    request["environment"] = {"CHANGED_SOURCE_SETTING": "1"}
    path.write_text(json.dumps(request))
    assert reproduction.case_identity(case, settings) != before


def test_dependency_blocker_is_configuration_specific_and_does_not_launch(
    coordinator: tuple, monkeypatch: pytest.MonkeyPatch
) -> None:
    storage, launched = coordinator
    cases = [
        {"id": name, "family": "eggcc", "scope": "required", "source": "fact", "configuration": {"solver": name}}
        for name in ("gurobi", "statewalk")
    ]
    monkeypatch.setattr(reproduction, "expected_cases", lambda *_: cases)
    settings = {
        "eggcc": {
            "paths": {},
            "configuration_blockers": [
                {
                    "configuration": {"solver": "gurobi"},
                    "reason": "Original solver CLI and license access unavailable",
                    "evidence": ["retained-native-failure.json"],
                }
            ],
        }
    }
    (storage / "settings.json").write_text(json.dumps(settings))
    assert reproduction.main(["--family", "eggcc", "--stage", "capture"]) == 1
    assert launched == ["statewalk"]
    index = json.loads((storage / "index.json").read_text())
    assert index["gurobi"]["status"] == "preparation-blocked"
    assert index["gurobi"]["evidence"] == ["retained-native-failure.json"]
    assert index["statewalk"]["status"] == "success"
    assert reproduction.main(["--stage", "report"]) == 0
    assert "Original solver CLI" in (storage / "REPORT.md").read_text()


def test_generator_build_blocker_does_not_block_other_cases_on_same_target() -> None:
    settings = {
        "configuration_blockers": [
            {
                "case_ids": ["misaal-x86-failed"],
                "configuration": {"target": "x86"},
                "reason": "original generator compilation failed",
                "evidence": ["compile.result.json"],
            }
        ]
    }
    case = {"id": "misaal-x86-ready", "configuration": {"target": "x86"}}
    assert reproduction.preparation_blocker(case, settings) is None
    result = reproduction.preparation_blocker({**case, "id": "misaal-x86-failed"}, settings)
    assert result is not None and result["status"] == "preparation-blocked"


@pytest.fixture
def preparation_coordinator(coordinator: tuple, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple:
    storage, captures = coordinator
    for name in (
        "scripts/reproduction_preparation.py",
        "scripts/reproduction_inventory.py",
        "scripts/misaal_reproduction.py",
        "scripts/reproduction_prepare_eggcc.py",
        "benchmarks/reproduction/fixtures/eggcc-core-row-order.patch",
        "scripts/reproduction_prepare_misaal.py",
        "scripts/reproduction_misaal_export.py",
        "scripts/reproduction_prepare_misaal_cases.py",
        "scripts/reproduction_prepare_misaal_arm.py",
        "scripts/reproduction_prepare_misaal_hvx.py",
        "scripts/reproduction_prepare_misaal_racket.py",
        "scripts/reproduction_misaal_abi_gate.py",
        "scripts/reproduction_misaal_patterns.py",
        "scripts/reproduction_misaal_runtime.py",
        "benchmarks/reproduction/fixtures/misaal-parameter/ki4k2nlc.rkt",
        "scripts/reproduction_misaal_hvx_lowering.py",
        "scripts/reproduction_misaal_x86_literals.py",
        "scripts/reproduction_misaal_legalizer.py",
        "scripts/reproduction_prepare_hardboiled.py",
        "scripts/eggcc_churchroad_complete.py",
        "scripts/paper_benchmarks/record_speq.py",
        "scripts/paper_benchmarks/materialize.py",
        "scripts/reproduction_process.py",
        "benchmarking/pilot.py",
        "benchmarking/memory_guard.py",
    ):
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("preparation implementation fixture")
    preparations = []

    def prepare(family: str, attempt: Path, engine: Path, **_: Any) -> dict:
        preparations.append(family)
        path = attempt / "settings.json"
        path.write_text(json.dumps({family: {"paths": {}, "revision": "prepared"}}))
        return {"status": "success", "settings": str(path), "artifacts": [str(path)]}

    monkeypatch.setattr(reproduction, "prepare_family", prepare)
    return storage, captures, preparations


def test_explicit_preparation_caches_real_outputs_without_capturing(preparation_coordinator: tuple) -> None:
    storage, captures, preparations = preparation_coordinator
    args = ["--family", "eggcc", "--stage", "prepare"]
    assert reproduction.main(args) == 0
    assert reproduction.main(args) == 0
    assert preparations == ["eggcc"] and captures == []
    assert json.loads((storage / "settings.json").read_text())["eggcc"]["revision"] == "prepared"


def test_eggcc_upstream_patch_change_invalidates_preparation(preparation_coordinator: tuple, tmp_path: Path) -> None:
    _, captures, preparations = preparation_coordinator
    args = ["--family", "eggcc", "--stage", "prepare"]
    assert reproduction.main(args) == 0
    assert reproduction.main(args) == 0
    assert preparations == ["eggcc"]
    (tmp_path / "benchmarks/reproduction/fixtures/eggcc-core-row-order.patch").write_text("changed upstream repair")
    assert reproduction.main(args) == 0
    assert preparations == ["eggcc", "eggcc"] and captures == []


@pytest.mark.parametrize(
    "input_path",
    [
        "scripts/reproduction_inventory.py",
        "scripts/misaal_reproduction.py",
        "scripts/reproduction_misaal_export.py",
        "scripts/reproduction_prepare_misaal_cases.py",
        "benchmarks/catalog.json",
        "benchmarks/reproduction/population.json",
        "scripts/reproduction_misaal_patterns.py",
        "scripts/reproduction_misaal_runtime.py",
    ],
)
def test_target_recipe_or_population_change_invalidates_fresh_misaal_preparation(
    preparation_coordinator: tuple,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    input_path: str,
) -> None:
    storage, captures, preparations = preparation_coordinator
    monkeypatch.setattr(
        reproduction,
        "expected_cases",
        lambda *_: [
            {
                "id": "misaal-arm-blur3x3",
                "family": "misaal",
                "scope": "required",
                "source": "benchmarks/arm/halide/blur3x3",
                "configuration": {"target": "arm"},
            }
        ],
    )
    args = ["--family", "misaal", "--stage", "prepare"]
    assert reproduction.main(args) == 0
    old = {path: path.read_bytes() for path in (storage / "stages").rglob("stage.json")}
    assert reproduction.main(args) == 0
    assert preparations == ["misaal"]
    changed = tmp_path / input_path
    changed.write_text(
        json.dumps({"reviewed_population_update": True})
        if changed.suffix == ".json"
        else changed.read_text() + "\n# Changed reviewed target preparation\n"
    )
    assert reproduction.main(args) == 0
    assert preparations == ["misaal", "misaal"] and captures == []
    assert all(path.read_bytes() == content for path, content in old.items())


@pytest.mark.parametrize("stage,existing", [("prepare", True), ("all", False)])
def test_failed_preparation_is_preserved_and_never_launches_capture(
    preparation_coordinator: tuple, monkeypatch: pytest.MonkeyPatch, stage: str, existing: bool
) -> None:
    storage, captures, _ = preparation_coordinator
    if not existing:
        (storage / "settings.json").write_text("{}")
    before = (storage / "settings.json").read_text()
    monkeypatch.setattr(
        reproduction,
        "prepare_family",
        lambda *_: {"status": "preparation-blocked", "reason": "real dependency build failed", "artifacts": []},
    )
    assert reproduction.main(["--family", "eggcc", "--stage", stage]) == 1
    assert captures == []
    assert (storage / "settings.json").read_text() == before
    index = json.loads((storage / "index.json").read_text())
    assert all(row["status"] == "preparation-blocked" for row in index.values())
    assert "real dependency build failed" in (storage / "REPORT.md").read_text()


def test_successful_preparation_retry_clears_current_blocker_but_keeps_history(
    preparation_coordinator: tuple, monkeypatch: pytest.MonkeyPatch
) -> None:
    storage, captures, _ = preparation_coordinator
    successful = reproduction.prepare_family
    monkeypatch.setattr(
        reproduction,
        "prepare_family",
        lambda *_: {"status": "preparation-blocked", "reason": "dependency unavailable", "artifacts": []},
    )
    args = ["--family", "eggcc", "--stage", "prepare"]
    assert reproduction.main(args) == 1
    old = json.loads((storage / "index.json").read_text())["one"]
    monkeypatch.setattr(reproduction, "prepare_family", successful)
    assert reproduction.main([*args, "--retry"]) == 0
    assert captures == []
    current = json.loads((storage / "index.json").read_text())["one"]
    assert current["status"] == "pending" and current["preparation"]["status"] == "success"
    assert current["historical_outcome"]["attempt"] == old["attempt"]
    assert current["historical_outcome"]["reason"] == "dependency unavailable"
    assert reproduction.main(["--stage", "report"]) == 0
    assert "prerequisites prepared; complete source capture is required" in (storage / "REPORT.md").read_text()


def test_shared_preparation_receipts_do_not_expand_every_case(
    preparation_coordinator: tuple, monkeypatch: pytest.MonkeyPatch
) -> None:
    storage, captures, _ = preparation_coordinator
    cases = [
        {"id": f"case-{i}", "family": "eggcc", "scope": "required", "source": str(i), "configuration": {}}
        for i in range(102)
    ]
    monkeypatch.setattr(reproduction, "expected_cases", lambda *_: cases)
    successful = reproduction.prepare_family
    payload = "large retained family artifact inventory " * 1024
    monkeypatch.setattr(
        reproduction,
        "prepare_family",
        lambda *_: {
            "status": "preparation-blocked",
            "reason": "dependency unavailable",
            "artifacts": [],
            "retained_diagnostic": payload,
        },
    )
    args = ["--family", "eggcc", "--stage", "prepare"]
    assert reproduction.main(args) == 1
    failed = json.loads((storage / "index.json").read_text())["case-0"]
    failed_receipt = Path(failed["receipt"])
    failed_bytes = failed_receipt.read_bytes()
    assert payload in failed_receipt.read_text()
    assert failed["receipt_sha256"] == reproduction.sha256_file(failed_receipt)
    assert "retained_diagnostic" not in failed and "identity" not in failed

    def prepare(*args: Any) -> dict:
        return {**successful(*args), "retained_diagnostic": payload}

    monkeypatch.setattr(reproduction, "prepare_family", prepare)
    assert reproduction.main([*args, "--retry"]) == 0
    index = json.loads((storage / "index.json").read_text())
    current = index["case-0"]
    assert current["status"] == "pending"
    assert current["historical_outcome"]["receipt"] == str(failed_receipt)
    assert current["historical_outcome"]["status"] == "preparation-blocked"
    assert current["preparation"]["status"] == "success"
    successful_receipt = Path(current["preparation"]["receipt"])
    successful_bytes = successful_receipt.read_bytes()
    assert payload in successful_receipt.read_text()
    assert captures == []
    for name in ("index.json", "report.json"):
        assert (storage / name).stat().st_size < 400_000
        assert payload not in (storage / name).read_text()
    before = (storage / "index.json").read_bytes()
    for _ in range(3):
        assert reproduction.main(["--stage", "report"]) == 0
        assert (storage / "index.json").read_bytes() == before
    assert failed_receipt.read_bytes() == failed_bytes
    assert successful_receipt.read_bytes() == successful_bytes
    assert json.loads((storage / "corpus/manifest.json").read_text())["workloads"] == []


def test_projection_discards_nested_history_without_repinning_immutable_evidence(tmp_path: Path) -> None:
    attempt = tmp_path / "attempt"
    attempt.mkdir()
    receipt = attempt / "stage.json"
    receipt.write_text("original immutable receipt")
    previous = {
        "status": "blocked",
        "reason": "old failure",
        "attempt": str(attempt),
        "identity": {"huge": "payload" * 1000},
        "artifacts": {"also": "large"},
        "prior_outcome": {"prior_outcome": {"identity": "earlier huge history"}},
    }
    current = {"status": "pending", "preparation": previous, "historical_outcome": previous}
    projected = reproduction.compact_outcome(current)
    expected = {
        "status": "blocked",
        "reason": "old failure",
        "attempt": str(attempt),
        "receipt": str(receipt),
        "receipt_sha256": reproduction.sha256_file(receipt),
    }
    assert projected == {"status": "pending", "preparation": expected, "historical_outcome": expected}
    assert "identity" in previous and "prior_outcome" in previous
    receipt.write_text("changed after the reference was recorded")
    assert reproduction.compact_outcome(projected) == projected
    receipt.unlink()
    assert reproduction.compact_outcome(projected) == projected
    missing = reproduction.compact_outcome({"status": "pending", "prior_outcome": previous})
    assert missing["prior_outcome"]["receipt_sha256"] is None


def test_projection_preserves_current_capture_and_validation_contracts() -> None:
    capture = {"status": "success", "identity": {"inputs": "retained"}, "artifacts": {"source": "hash"}}
    validation = {
        "status": "success",
        "stage": "validate",
        "identity": {"capture_sha256": "hash"},
        "artifacts": {"validation": "hash"},
        "capture_stage": capture,
        "workloads": ["input.egg"],
        "validations": [{"output_contract_passed": True}],
    }
    assert reproduction.compact_outcome(capture) == capture
    assert reproduction.compact_outcome(validation) == validation


def test_index_interruption_preserves_previous_complete_file(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    path = tmp_path / "index.json"
    before = '{"previous": {"status": "pending"}}\n'
    path.write_text(before)

    def interrupt(value: Any, stream: Any, **kwargs: Any) -> None:
        stream.write('{"incomplete":')
        raise KeyboardInterrupt

    with monkeypatch.context() as patch:
        patch.setattr(reproduction.json, "dump", interrupt)
        with pytest.raises(KeyboardInterrupt):
            reproduction.write_index(path, {"next": {"status": "pending"}})
    assert path.read_text() == before
    reproduction.write_index(path, {"next": {"status": "pending"}})
    assert json.loads(path.read_text()) == {"next": {"status": "pending"}}


def test_repeated_blocker_report_retains_only_original_outcome_reference(coordinator: tuple) -> None:
    storage, _ = coordinator
    attempt = storage / "old-attempt"
    attempt.mkdir()
    receipt = attempt / "stage.json"
    receipt.write_text('{"status":"blocked","reason":"native failure"}')
    case = {"id": "one", "family": "eggcc", "scope": "required", "configuration": {"solver": "gurobi"}}
    settings = {"eggcc": {"configuration_blockers": [{"configuration": case["configuration"], "reason": "license"}]}}
    index: dict[str, Any] = {"one": {"status": "blocked", "attempt": str(attempt), "identity": {"large": "payload"}}}
    reproduction.write_report([case], index, {}, settings)
    expected = json.dumps(index, sort_keys=True)
    for _ in range(3):
        reproduction.write_report([case], index, {}, settings)
        assert json.dumps(index, sort_keys=True) == expected
    prior = index["one"]["prior_outcome"]
    assert prior["receipt"] == str(receipt) and "identity" not in prior


def test_preparation_safety_stop_prevents_later_family_launch(
    preparation_coordinator: tuple, monkeypatch: pytest.MonkeyPatch
) -> None:
    storage, captures, _ = preparation_coordinator
    (storage / "settings.json").write_text("{}")
    monkeypatch.setattr(
        reproduction,
        "expected_cases",
        lambda *_: [
            {"id": family, "family": family, "scope": "required", "source": "case", "configuration": {}}
            for family in ("eggcc", "hardboiled")
        ],
    )
    launched = []

    def prepare(family: str, *args: object) -> dict:
        launched.append(family)
        return {"status": "resource-stopped", "reason": "disk guard refused", "artifacts": []}

    monkeypatch.setattr(reproduction, "prepare_family", prepare)
    assert reproduction.main(["--stage", "all"]) == 2
    assert launched == ["eggcc"] and captures == []
    index = json.loads((storage / "index.json").read_text())
    assert index["eggcc"]["status"] == "resource-stopped"
    assert "hardboiled" not in index
    assert reproduction.main(["--stage", "all"]) == 2
    assert launched == ["eggcc", "hardboiled"] and captures == []
    assert reproduction.main(["--stage", "all"]) == 1
    assert launched == ["eggcc", "hardboiled"] and captures == []


def test_phi_repair_implementation_is_bound_only_when_selected(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(reproduction, "ROOT", tmp_path)
    repair = tmp_path / "scripts/speq_phi_diagnostic.py"
    repair.parent.mkdir()
    repair.write_text("original repair implementation")
    case = {"id": "case", "family": "speq", "source": "input", "configuration": {}}
    ordinary = reproduction.case_identity(case, {"paths": {}})
    repaired = reproduction.case_identity(case, {"paths": {}, "phi_polarity_repair": True})
    repair.write_text("changed repair implementation")
    assert reproduction.case_identity(case, {"paths": {}}) == ordinary
    assert reproduction.case_identity(case, {"paths": {}, "phi_polarity_repair": True}) != repaired


@pytest.mark.parametrize("family", ["eggcc", "churchroad"])
def test_custom_extractor_dispatch_defers_ordinary_validation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, family: str
) -> None:
    from scripts import reproduction_dispatch as dispatch
    from scripts import suite_capture_eggcc_churchroad as capture

    called = []

    def complete(*args: Any, **kwargs: Any) -> list[dict]:
        called.append((args, kwargs))
        return [{"status": "ordinary-validation-pending", "workloads": []}]

    monkeypatch.setattr(capture, "capture_complete", complete)
    case = {"id": "case", "family": family, "configuration": {"native_options": []}}
    settings = {"paths": {name: str(tmp_path / name) for name in ("checkout", "binary", "egglog")}}
    assert dispatch.capture_case(case, settings, tmp_path / "capture")["status"] == "ordinary-validation-pending"
    assert len(called) == 1 and called[0][1]["validate_ordinary"] is False


def test_later_churchroad_dispatch_separates_input_and_native_revisions(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts import reproduction_dispatch as dispatch
    from scripts import suite_capture_eggcc_churchroad as capture

    called = []

    def complete(*args: Any, **kwargs: Any) -> list[dict]:
        called.append((args, kwargs))
        return [{"status": "ordinary-validation-pending"}]

    monkeypatch.setattr(capture, "capture_complete", complete)
    case: dict[str, Any] = {
        "id": "churchroad-later-mul_0_stage_unsigned_8_8_8_bit",
        "family": "churchroad",
        "source": "benchmarks/mul/0_stage/mul_0_stage_unsigned_8_8_8_bit.sv",
        "repository": "https://github.com/gussmith23/churchroad-evaluation",
        "revision": "evaluation-revision",
        "configuration": {
            "repository": "https://github.com/gussmith23/churchroad-evaluation",
            "revision": "evaluation-revision",
            "top_module_name": "mul_0_stage_unsigned_8_8_8_bit",
            "architecture": "xilinx-ultrascale-plus",
        },
    }
    settings: dict[str, Any] = {
        "revision": "native-driver-revision",
        "paths": {name: str(tmp_path / name) for name in ("checkout", "binary", "egglog")},
    }
    before = json.dumps(case, sort_keys=True)
    assert dispatch.capture_case(case, settings, tmp_path / "capture")["status"] == "pending"
    assert called == []
    settings["paths"]["source_root"] = str(tmp_path / "evaluation")
    assert dispatch.capture_case(case, settings, tmp_path / "capture")["status"] == "ordinary-validation-pending"
    args, kwargs = called[0]
    source_case = args[1][0]
    assert source_case["source"] == str(tmp_path / "evaluation" / case["source"])
    assert source_case["revision"] == settings["revision"]
    assert source_case["configuration"] == case["configuration"]
    assert source_case["top_module_name"] == case["configuration"]["top_module_name"]
    assert source_case["architecture"] == case["configuration"]["architecture"]
    assert args[3] == tmp_path / "checkout"
    assert kwargs["validate_ordinary"] is False
    assert json.dumps(case, sort_keys=True) == before


def test_later_churchroad_source_root_preserves_original_canary_identities(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(reproduction, "ROOT", tmp_path)
    cases: list[dict[str, Any]] = [
        {"id": f"churchroad-{name}", "family": "churchroad", "configuration": {}} for name in ("simple_mul", "wide_mul")
    ]
    cases.append(
        {
            "id": "churchroad-later-mul",
            "family": "churchroad",
            "repository": "https://github.com/gussmith23/churchroad-evaluation",
            "configuration": {},
        }
    )
    source_root = tmp_path / "evaluation"
    source_root.mkdir()
    source = source_root / "input.sv"
    source.write_text("original input")
    base: dict[str, Any] = {"revision": "native-driver", "paths": {"checkout": str(tmp_path / "native")}}
    settings = {"churchroad": {**base, "paths": {**base["paths"], "source_root": str(source_root)}}}
    before = json.dumps(settings, sort_keys=True)
    resolved = reproduction.resolve_case_settings(cases, settings)
    old_ids = {case["id"]: reproduction.case_identity(case, resolved[case["id"]]) for case in cases}
    for case in cases[:2]:
        assert resolved[case["id"]] == base
        assert old_ids[case["id"]] == reproduction.case_identity(case, base)
    assert resolved[cases[-1]["id"]] == settings["churchroad"]
    source.write_text("changed later input")
    for case in cases:
        changed = reproduction.case_identity(case, resolved[case["id"]]) != old_ids[case["id"]]
        assert changed == case["id"].startswith("churchroad-later-")
    assert json.dumps(settings, sort_keys=True) == before


@pytest.mark.parametrize(
    "relative",
    [
        "scripts/speq_c99_diagnostic.py",
        "scripts/speq_c99_gates.py",
        "scripts/paper_benchmarks/speq_c99_fir.inc",
        "scripts/paper_benchmarks/speq_c99_harness.cpp",
        "scripts/paper_benchmarks/speq_c99_fixture.ll",
        "scripts/paper_benchmarks/speq_rev_plugin.cpp",
    ],
)
def test_c99_implementation_closure_participates_in_selected_identity(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, relative: str
) -> None:
    monkeypatch.setattr(reproduction, "ROOT", tmp_path)
    path = tmp_path / relative
    path.parent.mkdir(parents=True)
    path.write_text("reviewed C99 source")
    case = {"id": "speq-polybench_gemm", "family": "speq", "source": "input", "configuration": {}}
    settings = {"paths": {}, "phi_polarity_repair": True, "c99_frontend_repair": "polybench-gemm-address-v1"}
    before = reproduction.case_identity(case, settings)
    path.write_text("changed C99 source")
    assert reproduction.case_identity(case, settings) != before


def test_case_timeout_resolution_preserves_all_unaffected_identity_bytes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(reproduction, "ROOT", tmp_path)
    cases: list[dict[str, Any]] = [
        {"id": name, "family": "eggcc", "configuration": {}}
        for name in [*(f"completed-{i}" for i in range(96)), "eggcc-raytrace--statewalk"]
    ]
    base = {
        "revision": "pinned",
        "paths": {},
        "timeout_sec": 300,
        "configuration_blockers": [{"configuration": {"native_options": ["--tiger-ilp"]}, "reason": "license"}],
        "other_metadata": {"keep": "unchanged"},
    }
    family = {**base, "case_timeout_sec": {"eggcc-raytrace--statewalk": 900}}
    before = json.dumps(family, sort_keys=True)
    resolved = reproduction.resolve_case_settings(cases, {"eggcc": family})
    for case in cases:
        old = json.dumps(reproduction.case_identity(case, base), sort_keys=True)
        new = json.dumps(reproduction.case_identity(case, resolved[case["id"]]), sort_keys=True)
        if case["id"] == "eggcc-raytrace--statewalk":
            assert old != new
            assert resolved[case["id"]] == {**base, "timeout_sec": 900}
        else:
            assert old == new
    assert json.dumps(family, sort_keys=True) == before
    assert reproduction.resolve_case_settings(cases, {"eggcc": {"paths": {}}})[cases[0]["id"]] == {"paths": {}}
    assert reproduction.resolve_case_settings(cases, {"eggcc": {"paths": {}, "case_timeout_sec": {}}})[
        cases[0]["id"]
    ] == {"paths": {}}


@pytest.mark.parametrize(
    "timeout", [True, False, 0, -1, float("nan"), float("inf"), -float("inf"), "900", None, [], {}, 10**400]
)
def test_case_timeout_rejects_invalid_numeric_budget(timeout: Any) -> None:
    with pytest.raises(ValueError, match="positive finite"):
        reproduction.resolve_case_settings(
            [{"id": "one", "family": "eggcc"}], {"eggcc": {"case_timeout_sec": {"one": timeout}}}
        )


@pytest.mark.parametrize("overrides", [None, [], 900, {"unknown": 900}, {"one*": 900}, {"other-family": 900}])
def test_case_timeout_requires_known_exact_same_family_id(overrides: Any) -> None:
    with pytest.raises(ValueError, match="case timeout ID|exact case IDs"):
        reproduction.resolve_case_settings(
            [{"id": "one", "family": "eggcc"}, {"id": "other-family", "family": "speq"}],
            {"eggcc": {"case_timeout_sec": overrides}},
        )


def test_case_timeout_accepts_finite_fraction_without_changing_other_fields() -> None:
    assert reproduction.resolve_case_settings(
        [{"id": "one", "family": "eggcc"}], {"eggcc": {"case_timeout_sec": {"one": 0.25}, "revision": "pinned"}}
    ) == {"one": {"timeout_sec": 0.25, "revision": "pinned"}}


def test_case_timeout_changes_only_selected_capture_replay_and_report(
    coordinator: tuple, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    storage, launched = coordinator
    for name in reproduction.VALIDATION_SOURCES:
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("validator identity")
    engine = tmp_path / "engine"
    engine.write_text("ordinary executable")
    settings = {"eggcc": {"paths": {"egglog": str(engine)}, "revision": "one", "timeout_sec": 300}}
    settings_path = storage / "settings.json"
    settings_path.write_text(json.dumps(settings))
    original_capture = reproduction.capture_case
    captures: list[tuple[str, int]] = []
    replays: list[int] = []

    def capture(case: dict, config: dict, output: Path) -> dict:
        assert "case_timeout_sec" not in config
        captures.append((case["id"], config["timeout_sec"]))
        if case["id"] == "one" and config["timeout_sec"] == 300:
            launched.append(case["id"])
            return {"status": "timed-out", "workloads": []}
        return original_capture(case, config, output)

    def validate(captured: dict, _engine: Path, output: Path, *, timeout_sec: int) -> dict:
        replays.append(timeout_sec)
        output.mkdir()
        (output / "validation.log").write_text("mocked ordinary success")
        return {
            "status": "success",
            "workloads": captured["workloads"],
            "validations": [
                {
                    "replay": path,
                    "replay_sha256": reproduction.sha256_file(Path(path)),
                    "status": "success",
                    "output_contract_passed": True,
                }
                for path in captured["workloads"]
            ],
        }

    monkeypatch.setattr(reproduction, "capture_case", capture)
    monkeypatch.setattr(reproduction, "validate_capture", validate)
    assert reproduction.main(["--case", "two"]) == 0
    assert reproduction.main(["--case", "one"]) == 2
    index = json.loads((storage / "index.json").read_text())
    old_timeout = Path(index["one"]["attempt"]) / "stage.json"
    completed = Path(index["two"]["attempt"]) / "stage.json"
    old_bytes, completed_bytes = old_timeout.read_bytes(), completed.read_bytes()
    completed_identity = index["two"]["identity_sha256"]
    settings["eggcc"]["case_timeout_sec"] = {"one": 900}
    settings_path.write_text(json.dumps(settings))
    assert reproduction.main(["--stage", "report"]) == 0
    report = json.loads((storage / "report.json").read_text())
    assert [(row["id"], row["timeout_sec"], row["outcome"]["status"]) for row in report["cases"]] == [
        ("one", 900, "pending"),
        ("two", 300, "success"),
    ]
    assert report["cases"][0]["outcome"]["historical_status"] == "timed-out"
    assert reproduction.main(["--case", "one", "--stage", "validate"]) == 1
    assert captures == [("two", 300), ("one", 300)] and replays == [300]
    assert reproduction.main([]) == 0
    assert reproduction.main([]) == 0
    assert captures == [("two", 300), ("one", 300), ("one", 900)]
    assert replays == [300, 900]
    assert launched == ["two", "one", "one"]
    final = json.loads((storage / "index.json").read_text())
    assert final["two"]["identity_sha256"] == completed_identity
    assert final["one"]["identity"]["timeout_sec"] == 900
    assert final["one"]["capture_stage"]["identity"]["settings"]["timeout_sec"] == 900
    assert final["one"]["capture_stage"]["identity_sha256"] != index["one"]["identity_sha256"]
    assert old_timeout.read_bytes() == old_bytes
    assert completed.read_bytes() == completed_bytes
    assert "| one | required | 900 | success |" in (storage / "REPORT.md").read_text()
    assert "separately to each ordinary replay" in (storage / "REPORT.md").read_text()
    assert "Eggcc source parents use the same budget" in (storage / "REPORT.md").read_text()
    assert "MISAAL source budgets remain in its requests" in (storage / "REPORT.md").read_text()
    assert (tmp_path / ".reports.jsonl").read_text() == "untouched performance cache\n"


def test_unknown_case_timeout_refuses_before_preparation_or_capture(
    coordinator: tuple, monkeypatch: pytest.MonkeyPatch
) -> None:
    storage, launched = coordinator
    (storage / "settings.json").write_text(json.dumps({"eggcc": {"case_timeout_sec": {"missing": 900}}}))

    def unexpected_prepare(*args: Any, **kwargs: Any) -> Any:
        pytest.fail("invalid timeout metadata must be rejected before native preparation")

    monkeypatch.setattr(reproduction, "prepare_family", unexpected_prepare)
    for stage in ("prepare", "capture", "validate", "report", "all"):
        with pytest.raises(ValueError, match="unknown eggcc case timeout ID"):
            reproduction.main(["--stage", stage])
    assert launched == []
    assert not (storage / "index.json").exists()


def test_explicit_preparation_preserves_coordinator_case_timeout_policy(preparation_coordinator: tuple) -> None:
    storage, captures, preparations = preparation_coordinator
    settings = storage / "settings.json"
    settings.write_text(json.dumps({"eggcc": {"paths": {}, "case_timeout_sec": {"one": 900}}}))
    assert reproduction.main(["--family", "eggcc", "--stage", "prepare"]) == 0
    assert reproduction.main(["--family", "eggcc", "--stage", "prepare"]) == 0
    assert json.loads(settings.read_text())["eggcc"] == {
        "paths": {},
        "revision": "prepared",
        "case_timeout_sec": {"one": 900},
    }
    assert preparations == ["eggcc"] and captures == []
    assert {row["id"]: row["timeout_sec"] for row in json.loads((storage / "report.json").read_text())["cases"]} == {
        "one": 900,
        "two": 300,
    }


@pytest.mark.parametrize("family", ["misaal", "churchroad", "dialegg", "speq", "hardboiled"])
def test_case_timeout_rejects_other_family_overrides(family: str) -> None:
    with pytest.raises(ValueError, match="only for Eggcc"):
        reproduction.resolve_case_settings(
            [{"id": "known", "family": family}], {family: {"case_timeout_sec": {"known": 900}}}
        )


def test_raytrace_policy_changes_only_its_resolved_identity(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    cases: list[dict[str, Any]] = [
        {"id": "eggcc-raytrace--statewalk", "family": "eggcc", "source": "raytrace", "configuration": {}},
        *[
            {"id": family, "family": family, "source": family, "configuration": {}}
            for family in ("eggcc", "churchroad", "hardboiled", "dialegg", "speq", "misaal")
        ],
    ]
    settings = {family: {"paths": {}, "revision": "pinned"} for family in reproduction.FAMILIES}
    settings["misaal"]["paths"] = {"requests": str(tmp_path / "requests")}
    monkeypatch.setattr(reproduction, "ROOT", tmp_path)
    monkeypatch.setattr(
        reproduction,
        "misaal_request",
        lambda *_: {
            **{key: str(tmp_path / key) for key in ("backend", "llvm_as", "python", "generator", "checkout")},
            "source_hashes": {},
        },
    )
    adapter = tmp_path / "scripts/suite_capture_eggcc_churchroad.py"
    adapter.parent.mkdir()
    adapter.write_text("prior shared adapter")
    before = reproduction.resolve_case_settings(cases, settings)
    old_ids = {c["id"]: reproduction.case_identity(c, before[c["id"]]) for c in cases}
    settings["eggcc"]["raytrace_materialization_policy"] = "raytrace-384mib-v1"
    after = reproduction.resolve_case_settings(cases, settings)
    assert after["eggcc-raytrace--statewalk"] == {
        **before["eggcc-raytrace--statewalk"],
        "materialization_policy": "raytrace-384mib-v1",
    }
    assert all(after[c["id"]] == before[c["id"]] for c in cases if c["id"] != "eggcc-raytrace--statewalk")
    adapter.write_text("reviewed extracted shared adapter")
    new_ids = {c["id"]: reproduction.case_identity(c, after[c["id"]]) for c in cases}
    for case in cases:
        assert (new_ids[case["id"]] != old_ids[case["id"]]) == (case["family"] in {"eggcc", "churchroad"})


@pytest.mark.parametrize(
    "family,value",
    [("eggcc", "unknown"), ("eggcc", 384), ("misaal", "raytrace-384mib-v1"), ("churchroad", "raytrace-384mib-v1")],
)
def test_raytrace_policy_rejects_unknown_or_other_family(family: str, value: Any) -> None:
    with pytest.raises(ValueError, match="raytrace materialization policy"):
        reproduction.resolve_case_settings([], {family: {"raytrace_materialization_policy": value}})


def test_recovery_selection_refuses_before_any_stage(coordinator: tuple) -> None:
    storage, launched = coordinator
    with pytest.raises(ValueError, match="one selected raytrace"):
        reproduction.main(["--resume-eggcc-capture", str(storage / "unknown.json")])
    assert launched == [] and not (storage / "index.json").exists()


def test_explicit_preparation_preserves_raytrace_policy(preparation_coordinator: tuple) -> None:
    storage, captures, preparations = preparation_coordinator
    settings = storage / "settings.json"
    settings.write_text(json.dumps({"eggcc": {"paths": {}, "raytrace_materialization_policy": "raytrace-384mib-v1"}}))
    assert reproduction.main(["--family", "eggcc", "--stage", "prepare"]) == 0
    assert json.loads(settings.read_text())["eggcc"]["raytrace_materialization_policy"] == "raytrace-384mib-v1"
    assert preparations == ["eggcc"] and captures == []


def test_resumed_parent_and_fresh_policy_share_reuse_identity(
    coordinator: tuple, monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts import suite_capture_eggcc_churchroad as adapter

    storage, launched = coordinator
    case = {
        "id": adapter.RAYTRACE_CASE,
        "family": "eggcc",
        "scope": "required",
        "source": "raytrace.rs",
        "configuration": {},
    }
    monkeypatch.setattr(reproduction, "expected_cases", lambda *_: [case])
    settings = {
        "eggcc": {
            "paths": {"checkout": ".", "binary": "compiler", "egglog": "engine"},
            "raytrace_materialization_policy": adapter.RAYTRACE_POLICY,
        }
    }
    (storage / "settings.json").write_text(json.dumps(settings))
    received = []

    def materialize(family: str, cases: list[dict], output: Path, *paths: Path, **kwargs: Any) -> list[dict]:
        received.append(kwargs)
        output.mkdir(parents=True)
        (output / "origin.json").write_text(json.dumps({"origin": str(kwargs["resume_stage"])}))
        return [
            {
                "id": adapter.RAYTRACE_CASE,
                "status": "ordinary-validation-pending",
                "workloads": [],
                "source_completion": {"status": "success", "parent_completed": True},
                "sessions": [],
            }
        ]

    monkeypatch.setattr(adapter, "capture_complete", materialize)
    assert (
        reproduction.main(
            [
                "--case",
                adapter.RAYTRACE_CASE,
                "--stage",
                "capture",
                "--resume-eggcc-capture",
                str(storage / "old-stage.json"),
            ]
        )
        == 1
    )
    receipt = json.loads((storage / "index.json").read_text())[adapter.RAYTRACE_CASE]
    identity = receipt["identity_sha256"]
    assert reproduction.main(["--case", adapter.RAYTRACE_CASE, "--stage", "capture"]) == 1
    assert len(received) == 1 and launched == []
    assert received[0]["max_evidence_bytes"] == 384 * 1024**2 and received[0]["validate_ordinary"] is False
    assert json.loads((storage / "index.json").read_text())[adapter.RAYTRACE_CASE]["identity_sha256"] == identity
    assert "resume" not in json.dumps(receipt["identity"])


@pytest.mark.parametrize("stage", ["capture", "all"])
def test_native_misaal_settings_cannot_launch_after_export_policy(
    preparation_coordinator: tuple, monkeypatch: pytest.MonkeyPatch, stage: str
) -> None:
    storage, captures, preparations = preparation_coordinator
    case = {"id": "misaal-one", "family": "misaal", "scope": "required", "source": "one", "configuration": {}}
    monkeypatch.setattr(reproduction, "expected_cases", lambda *_: [case])
    (storage / "settings.json").write_text(json.dumps({"misaal": {"paths": {"requests": "old-native"}}}))

    # Exercise the public selection gate even when identity is mocked by the fixture.
    def identity(case: dict, settings: dict, **_: Any) -> dict:
        if settings.get("egglog_export") != "egglog-only-v1":
            raise ValueError("MISAAL native lowering is disabled")
        return {"case": case, "settings": settings}

    monkeypatch.setattr(reproduction, "case_identity", identity)
    assert reproduction.main(["--family", "misaal", "--stage", stage]) == 1
    assert not captures
    assert preparations == (["misaal"] if stage == "all" else [])


def test_misaal_dispatch_rejects_native_request_before_verification_or_launch(
    misaal_identity: tuple, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    from scripts import misaal_reproduction, reproduction_dispatch

    case, settings, path = misaal_identity
    request = json.loads(path.read_text())
    request.pop("egglog_export")
    path.write_text(json.dumps(request))
    monkeypatch.setattr(misaal_reproduction, "verified_request", lambda *_: pytest.fail("native template must not run"))
    monkeypatch.setattr(misaal_reproduction, "capture_misaal", lambda *_: pytest.fail("native template must not run"))
    with pytest.raises(ValueError, match="native lowering is disabled"):
        reproduction_dispatch.capture_case(case, settings, tmp_path / "capture")


def test_export_identity_omits_obsolete_llvm_tools_and_helpers(misaal_identity: tuple) -> None:
    case, settings, _ = misaal_identity
    identity = reproduction.case_identity(case, settings)
    assert not any(Path(path).name in {"llvm_as", "reproduction_misaal_legalizer.py"} for path in identity["inputs"])
    assert any(Path(path).name == "reproduction_misaal_export.py" for path in identity["inputs"])
    assert any(Path(path).name == "suite_capture_hardboiled_misaal.py" for path in identity["inputs"])


def test_all_replaces_native_settings_with_export_before_capture(
    preparation_coordinator: tuple, monkeypatch: pytest.MonkeyPatch
) -> None:
    storage, captures, preparations = preparation_coordinator
    case = {"id": "misaal-one", "family": "misaal", "scope": "required", "source": "one", "configuration": {}}
    monkeypatch.setattr(reproduction, "expected_cases", lambda *_: [case])
    original = {"paths": {"requests": "retained-templates"}, "revision": "original"}
    (storage / "settings.json").write_text(json.dumps({"misaal": original}))

    def prepare(family: str, attempt: Path, engine: Path, **options: Any) -> dict:
        assert options["settings"] == original
        preparations.append(family)
        path = attempt / "settings.json"
        path.write_text(json.dumps({family: {"egglog_export": "egglog-only-v1", "paths": {}, "revision": "original"}}))
        return {"status": "success", "settings": str(path), "artifacts": [str(path)]}

    def capture(case: dict, settings: dict, output: Path) -> dict:
        assert settings["egglog_export"] == "egglog-only-v1"
        captures.append(case["id"])
        return {"status": "blocked", "reason": "mocked export capture"}

    monkeypatch.setattr(reproduction, "prepare_family", prepare)
    monkeypatch.setattr(reproduction, "capture_case", capture)
    reproduction.main(["--family", "misaal", "--stage", "all"])
    assert preparations == ["misaal"] and captures == ["misaal-one"]
    assert json.loads((storage / "settings.json").read_text())["misaal"]["egglog_export"] == "egglog-only-v1"
