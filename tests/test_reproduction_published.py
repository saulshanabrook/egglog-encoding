"""Published sources use exact bytes and ordinary outputs without native-parent claims."""

from __future__ import annotations

import copy
import hashlib
import json
import shutil
from pathlib import Path
from typing import Any

import pytest

from benchmarking.pilot import PilotProcessResult
from scripts import reproduction_preparation as preparation
from scripts import reproduction_prepare_hardboiled as native
from scripts import reproduction_prepare_misaal_racket as acquisition
from scripts import reproduction_published as published
from scripts import reproduction_validation as validation
from scripts import suite_reproduction as coordinator
from scripts.hardboiled_replay import egglog_forms
from scripts.reproduction_dispatch import capture_case
from scripts.reproduction_inventory import expected_cases

ROOT = Path(__file__).resolve().parents[1]


@pytest.fixture
def sources(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    population = json.loads((ROOT / "benchmarks/reproduction/population.json").read_text())
    inputs = {}
    for entry in population["hardboiled"]["inputs"]:
        data = f"; {entry['file']}\n(datatype E (A))\n(let root (A))\n(extract root)\n".encode()
        inputs[entry["file"]] = data
        entry.update(
            sha256=hashlib.sha256(data).hexdigest(),
            size_bytes=len(data),
            extracts=1,
            git_blob=hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest(),
        )
    (tmp_path / "benchmarks/reproduction").mkdir(parents=True)
    (tmp_path / "benchmarks/reproduction/population.json").write_text(json.dumps(population))
    catalog = (ROOT / "benchmarks/catalog.json").read_bytes()
    (tmp_path / "benchmarks/catalog.json").write_bytes(catalog)
    (tmp_path / ".reports.jsonl").write_text("protected performance observations\n")
    engine = tmp_path / "engine"
    engine.write_text("ordinary replay engine identity")
    fetched, launches = [], []

    def fetch(url: str, limit: int) -> bytes:
        assert url.startswith(
            f"https://raw.githubusercontent.com/yihozhang/egglog-benchmarks/{published.REVISION}/benchmarks/hardboiled/"
        )
        fetched.append(url)
        data = inputs[url.rsplit("/", 1)[1]]
        assert len(data) == limit
        return data

    def run(command: list[str], cwd: Path, prefix: Path, timeout_sec: float) -> PilotProcessResult:
        launches.append(command)
        stdout, stderr = prefix.with_suffix(".stdout"), prefix.with_suffix(".stderr")
        stdout.write_text("(A)\n")
        stderr.write_text("")
        return PilotProcessResult("success", 0, 0.01, 1024, stdout, stderr, None)

    monkeypatch.setattr(published, "ROOT", tmp_path)
    monkeypatch.setattr(acquisition, "fetch_bytes", fetch)
    monkeypatch.setattr(validation, "run_complete_command", run)
    monkeypatch.setattr(native, "prepare", lambda *_: pytest.fail("published inputs must not prepare Halide"))
    return {
        "root": tmp_path,
        "population": population,
        "inputs": inputs,
        "engine": engine,
        "fetched": fetched,
        "launches": launches,
        "catalog": catalog,
    }


def test_selected_inventory_has_42_published_inputs_and_separate_native_history() -> None:
    catalog = json.loads((ROOT / "benchmarks/catalog.json").read_text())
    population = json.loads((ROOT / "benchmarks/reproduction/population.json").read_text())
    entries = published.published_entries(population["hardboiled"])
    cases = [case for case in expected_cases(catalog, population) if case["family"] == "hardboiled"]
    assert {case["id"] for case in cases} == set(entries)
    assert all(case["input_kind"] == published.INPUT_KIND and case["scope"] == "required" for case in cases)
    assert sum(entry["extracts"] for entry in entries.values()) == 2074
    selected = [case for case in catalog["cases"] if case["id"] in entries]
    native = [case for case in catalog["cases"] if case["family"] == "hardboiled" and case["id"] not in entries]
    assert len(selected) == 42 and len(native) == 35
    assert all(case["benchmark_selection"]["workloads"] for case in selected)
    assert all(case["benchmark_selection"]["workloads"] == [] for case in native)
    historical_catalog = {**catalog, "cases": [case for case in catalog["cases"] if case["id"] not in entries]}
    assert expected_cases(catalog, population) == expected_cases(historical_catalog, population)
    history = population["hardboiled"]["native_history"]
    assert (history["required_source_parents"], history["captured_sessions"]) == (34, 38)
    assert sum(cell["supported"] for cell in history["amx_cells"]) == 7


def test_fresh_acquisition_and_capture_preserve_exact_bytes(sources: dict[str, Any]) -> None:
    root = sources["root"]
    result = preparation.prepare_family("hardboiled", root, sources["engine"], input_kind=published.INPUT_KIND)
    assert result["status"] == "success" and len(sources["fetched"]) == 42
    settings = json.loads(Path(result["settings"]).read_text())["hardboiled"]
    case = next(
        c for c in expected_cases(json.loads(sources["catalog"]), sources["population"]) if c["family"] == "hardboiled"
    )
    capture = capture_case(case, settings, root / "capture")
    assert "source_completion" not in capture
    session = capture["sessions"][0]
    assert Path(session["replay"]).read_bytes() == sources["inputs"][capture["published_input"]["file"]]
    assert Path(capture["published_source"]).read_bytes() == Path(session["replay"]).read_bytes()
    assert session["adaptations"] == []
    checked = validation.validate_capture(capture, sources["engine"], root / "validated")
    assert checked["status"] == "success" and checked["proof_validation"] == "not-run"
    assert checked["validations"][0]["output_contract_passed"]
    assert len(sources["launches"]) == 1
    with pytest.raises(FileExistsError):
        published.prepare_published(root / "environment", sources["engine"])


@pytest.fixture
def higher_order_capture(sources: dict[str, Any]) -> dict[str, Any]:
    entry = sources["population"]["hardboiled"]["inputs"][0]
    data = b"""(datatype E (A) (B) (Identity E))
(ruleset canonicalize)
(ruleset typechecking)
(ruleset amx)
(sort Callback (UnstableFn (E) E))
(relation callback (Callback))
(rule ((= e (A))) ((callback (unstable-fn "Identity"))) :ruleset canonicalize)
(rule ((callback f) (= e (A))) ((union e (unstable-app f e))) :ruleset canonicalize)
(let root (A))
(run-schedule (repeat 20 (saturate (run typechecking)) (run) (run amx)))
(extract root)
"""
    sources["inputs"][entry["file"]] = data
    entry.update(
        sha256=hashlib.sha256(data).hexdigest(),
        size_bytes=len(data),
        git_blob=hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest(),
    )
    root = sources["root"]
    (root / "benchmarks/reproduction/population.json").write_text(json.dumps(sources["population"]))
    result = published.prepare_published(root / "prepared", sources["engine"])
    settings = json.loads(Path(result["settings"]).read_text())["hardboiled"]
    case = next(
        c for c in expected_cases(json.loads(sources["catalog"]), sources["population"]) if c["id"] == entry["id"]
    )
    return published.capture_published(case, settings, root / "capture")


def test_published_capture_omits_only_unscheduled_higher_order_rules(
    sources: dict[str, Any], higher_order_capture: dict[str, Any]
) -> None:
    original = sources["inputs"][higher_order_capture["published_input"]["file"]]
    assert Path(higher_order_capture["published_source"]).read_bytes() == original
    session = higher_order_capture["sessions"][0]
    replay = Path(session["replay"]).read_bytes()
    assert replay != original
    assert session["replay_sha256"] == "sha256:" + hashlib.sha256(replay).hexdigest()
    assert session["adaptations"] == ["omit-unexecuted-higher-order-rules"]
    assert higher_order_capture["published_input"]["sha256"] == hashlib.sha256(original).hexdigest()
    assert session["output_contract"] == {"kind": published.INPUT_KIND, "extracts": 1}
    assert [tokens for _, _, tokens in egglog_forms(replay.decode())] == [
        tokens
        for _, _, tokens in egglog_forms(original.decode())
        if not {"unstable-app", "unstable-fn"}.intersection(tokens)
    ]
    published.verify_published_capture(higher_order_capture)
    checked = validation.validate_capture(higher_order_capture, sources["engine"], sources["root"] / "validated")
    assert checked["status"] == "success" and checked["proof_validation"] == "not-run"
    assert checked["workloads"] == [session["replay"]]


@pytest.mark.parametrize("change", ["source", "schedule", "seed", "query", "raw-replay", "recipe", "hash"])
def test_published_adaptation_rejects_other_changes(higher_order_capture: dict[str, Any], change: str) -> None:
    session = higher_order_capture["sessions"][0]
    replay = Path(session["replay"])
    if change == "source":
        source = Path(higher_order_capture["published_source"])
        source.write_bytes(source.read_bytes() + b"; changed\n")
    elif change == "recipe":
        session["adaptations"] = []
    elif change == "hash":
        session["replay_sha256"] = "sha256:" + higher_order_capture["published_input"]["sha256"]
    else:
        if change == "raw-replay":
            data = Path(higher_order_capture["published_source"]).read_bytes()
        else:
            old, new = {
                "schedule": (b"(repeat 20", b"(repeat 19"),
                "seed": (b"(let root (A))", b"(let root (B))"),
                "query": (b"(extract root)", b"(extract (A))"),
            }[change]
            data = replay.read_bytes().replace(old, new)
        replay.write_bytes(data)
        session["replay_sha256"] = "sha256:" + hashlib.sha256(data).hexdigest()
    with pytest.raises(ValueError):
        published.verify_published_capture(higher_order_capture)


@pytest.mark.parametrize("change", ["bytes", "missing-query", "include"])
def test_changed_source_and_missing_original_queries_are_rejected(sources: dict[str, Any], change: str) -> None:
    entry = copy.deepcopy(next(iter(published.published_entries().values())))
    data = sources["inputs"][entry["file"]]
    if change == "bytes":
        data += b"; changed\n"
        message = "identity changed"
    else:
        data = data.replace(b"(extract root)", b"" if change == "missing-query" else b'(include "other.egg")')
        entry.update(
            sha256=hashlib.sha256(data).hexdigest(),
            size_bytes=len(data),
            git_blob=hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest(),
        )
        message = "original extraction queries" if change == "missing-query" else "self-contained"
    with pytest.raises(ValueError, match=message):
        published.verify_input(entry, data)
    assert not sources["launches"]


@pytest.mark.parametrize("change", ["native-failure", "provenance", "contract", "replay", "missing-output"])
def test_published_label_cannot_admit_failed_native_parent_or_changed_output(
    sources: dict[str, Any], change: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    root = sources["root"]
    result = published.prepare_published(root / "prepared", sources["engine"])
    settings = json.loads(Path(result["settings"]).read_text())["hardboiled"]
    case = next(
        c for c in expected_cases(json.loads(sources["catalog"]), sources["population"]) if c["family"] == "hardboiled"
    )
    capture = published.capture_published(case, settings, root / "capture")
    if change == "native-failure":
        capture["source_completion"] = {"status": "failed"}
    elif change == "provenance":
        capture["published_input"]["revision"] = "another revision"
    elif change == "contract":
        capture["sessions"][0]["output_contract"]["extracts"] = 0
    elif change == "replay":
        Path(capture["sessions"][0]["replay"]).write_text("(datatype E (A))")
    else:
        run = validation.run_complete_command

        def missing(*args: Any) -> PilotProcessResult:
            result = run(*args)
            result.stdout_path.write_text("")
            return result

        monkeypatch.setattr(validation, "run_complete_command", missing)
    checked = validation.validate_capture(capture, sources["engine"], root / "checked")
    assert checked["status"] == "blocked" and not checked["workloads"]
    assert len(sources["launches"]) == (1 if change == "missing-output" else 0)


def test_public_pipeline_replaces_legacy_settings_and_publishes_only_verified_inputs(
    sources: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    root = sources["root"]
    # These are identity inputs only. Python executes the imported mirror modules.
    for directory in ("scripts", "benchmarking"):
        shutil.copytree(ROOT / directory, root / directory, ignore=shutil.ignore_patterns("__pycache__"))
    storage = root / "reproduction"
    storage.mkdir()
    settings = storage / "settings.json"
    settings.write_text(
        json.dumps({"hardboiled": {"revision": "historical-native", "paths": {"checkout": "absent-native-checkout"}}})
    )
    monkeypatch.setattr(coordinator, "ROOT", root)
    monkeypatch.setattr(coordinator, "STORAGE", storage)
    arguments = ["--family", "hardboiled", "--settings", str(settings), "--engine", str(sources["engine"])]
    assert coordinator.main(arguments) == 0
    assert len(sources["fetched"]) == len(sources["launches"]) == 42
    manifest = json.loads((storage / "corpus/manifest.json").read_text())
    cases = [c for c in manifest["cases"] if c["family"] == "hardboiled"]
    assert len(cases) == len(manifest["workloads"]) == 42
    assert all(c["status"] == "success" and c["configuration"]["input_kind"] == published.INPUT_KIND for c in cases)
    assert all(c["configuration"]["revision"] == published.REVISION for c in cases)
    for row in manifest["workloads"]:
        replay = storage / "corpus" / row["file"]
        assert replay.read_bytes() in sources["inputs"].values()
    report = json.loads((storage / "report.json").read_text())
    assert len(report["hardboiled_amx_paper_cells"]) == 10
    assert (root / "benchmarks/catalog.json").read_bytes() == sources["catalog"]
    assert (root / ".reports.jsonl").read_text() == "protected performance observations\n"
    assert coordinator.main(arguments) == 0
    assert len(sources["fetched"]) == len(sources["launches"]) == 42
    current = json.loads(settings.read_text())["hardboiled"]
    source = Path(current["paths"]["inputs"]) / next(iter(sources["inputs"]))
    source.write_bytes(source.read_bytes() + b"; changed\n")
    assert coordinator.main([*arguments, "--stage", "validate"]) == 1
    assert len(sources["launches"]) == 42
