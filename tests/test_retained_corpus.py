"""Retained inputs require intact receipts, complete calls, and ordinary replay."""

import hashlib
import json
from pathlib import Path

import pytest

from benchmarking.pilot import PilotProcessResult
from benchmarking.suites import resolve_suite
from benchmarking.targets import sha256_file
from scripts import retained_corpus as retained
from scripts.hardboiled_replay import native_check_contract
from scripts.reproduction_corpus import write_corpus


def stage(directory: Path, case: str, name: str, identity: dict, **fields: object) -> dict:
    directory.mkdir(parents=True)
    record = {
        "case": case,
        "stage": name,
        "identity": identity,
        "identity_sha256": hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest(),
        "attempt": str(directory),
        "status": "success",
        "artifacts": {},
        **fields,
    }
    (directory / "stage.json").write_text(json.dumps(record))
    return record


def setup_retained(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict:
    storage = tmp_path / "benchmarks/local/reproduction"
    storage.mkdir(parents=True)
    (tmp_path / "benchmarks/reproduction").mkdir()
    (tmp_path / "benchmarks/reproduction/population.json").write_text("{}")
    case: dict = {
        "id": "eggcc-source--config",
        "catalog_id": "eggcc-source",
        "family": "eggcc",
        "source": "source.bril",
        "configuration": {"pass": "complete"},
    }
    monkeypatch.setattr(retained, "expected_cases", lambda catalog, population: [case])
    catalog = {
        "families": {"eggcc": {}},
        "cases": [
            {"id": "eggcc-source", "family": "eggcc", "source": "source.bril", "status": "captured", "workloads": []}
        ],
    }
    (tmp_path / "benchmarks/catalog.json").write_text(json.dumps(catalog))
    replay = tmp_path / "source.egg"
    replay.write_text("(check (= 1 1))\n")
    captured = tmp_path / "capture.json"
    captured.write_text("{}")
    capture = stage(
        tmp_path / "capture",
        case["id"],
        "complete",
        {"case": case},
        capture=str(captured),
        artifacts={str(captured): sha256_file(captured), str(replay): sha256_file(replay)},
    )
    stdout = tmp_path / "stdout"
    stdout.write_text("success")
    validation = stage(
        tmp_path / "validate",
        case["id"],
        "validate",
        {"capture_sha256": sha256_file(captured), "artifacts": capture["artifacts"]},
        artifacts={str(stdout): sha256_file(stdout)},
        workloads=[str(replay)],
        validations=[
            {
                "replay": str(replay),
                "replay_sha256": sha256_file(replay),
                "status": "success",
                "output_contract_passed": True,
            }
        ],
    )
    index = {case["id"]: {**validation, "capture_stage": capture, "status": "pending", "historical_status": "success"}}
    (storage / "index.json").write_text(json.dumps(index))
    return catalog


def test_recovers_original_receipt_without_current_acquisition_identity(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    setup_retained(tmp_path, monkeypatch)
    rows, jobs = retained.retained_rows(tmp_path)
    assert rows[0]["outcome"]["status"] == "success"
    assert rows[0]["configuration"] == {"pass": "complete"}
    assert not jobs
    assert len(write_corpus(rows, tmp_path / "corpus")["workloads"]) == 1


@pytest.mark.parametrize("changed", ["source.egg", "capture.json", "stdout", "validate/stage.json"])
def test_stale_metadata_cannot_promote_missing_or_changed_evidence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, changed: str
) -> None:
    setup_retained(tmp_path, monkeypatch)
    (tmp_path / changed).unlink()
    rows, _ = retained.retained_rows(tmp_path)
    assert rows[0]["outcome"]["status"] == "blocked"
    assert not write_corpus(rows, tmp_path / "corpus")["workloads"]


def test_validation_must_bind_correct_capture(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    setup_retained(tmp_path, monkeypatch)
    path = tmp_path / "validate/stage.json"
    record = json.loads(path.read_text())
    record["identity"]["capture_sha256"] = "different"
    path.write_text(json.dumps(record))
    rows, _ = retained.retained_rows(tmp_path)
    assert rows[0]["outcome"]["status"] == "blocked"


@pytest.mark.parametrize("field", ["status", "reason", "capture"])
def test_frozen_capture_receipt_is_hash_bound(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, field: str) -> None:
    setup_retained(tmp_path, monkeypatch)
    rows, jobs = retained.retained_rows(tmp_path)
    frozen = tmp_path / "candidates.json"
    frozen.write_text(json.dumps({"rows": rows, "jobs": jobs}))
    assert retained.read_candidates(frozen, tmp_path) == (rows, jobs)
    receipt = tmp_path / "capture/stage.json"
    capture = json.loads(receipt.read_text())
    capture[field] = "changed"
    receipt.write_text(json.dumps(capture))
    with pytest.raises(ValueError, match="retained evidence changed"):
        retained.read_candidates(frozen, tmp_path)


def test_complete_independent_call_survives_parent_failure_and_deduplicates(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    catalog = setup_retained(tmp_path, monkeypatch)
    replay = tmp_path / "call.egg"
    replay.write_text("(datatype E (A) (B))\n(let $x (A))\n(run 5)\n(extract $x)\n")
    stdout = tmp_path / "native.stdout"
    stdout.write_text("(A)\n")
    invocation = {
        "index": 0,
        "caller": "apply_rewrite",
        "backend_status": "success",
        "backend_returncode": 0,
        "raw": str(replay),
        "sha256": sha256_file(replay),
        "stdout": str(stdout),
        "stdout_sha256": sha256_file(stdout),
        "workload": str(replay),
        "replay_sha256": sha256_file(replay),
        "query_kind": "source-extraction",
        "extract_count": 1,
    }
    catalog["families"]["misaal"] = {}
    catalog["cases"].append(
        {
            "id": "misaal-case",
            "family": "misaal",
            "source": "program",
            "configuration": {},
            "status": "captured",
            "workloads": [str(replay)],
            "capture_complete": False,
            "reason": "parent looped",
            "invocations": [
                invocation,
                {**invocation, "index": 1},
                {**invocation, "index": 2, "backend_returncode": 1},
            ],
        }
    )
    native_call = {
        "index": 0,
        "raw": str(replay),
        "sha256": sha256_file(replay),
        "caller": "apply_rewrite",
        "status": "success",
        "returncode": 0,
    }
    # Each source alias has its own matching receipt, while the restored input
    # can still deduplicate to one validation job.
    native_capture = tmp_path / "native-capture.json"
    calls: list[dict] = []
    for index, item in enumerate(catalog["cases"][-1]["invocations"]):
        raw = tmp_path / f"raw-{index}.egg"
        raw.write_bytes(replay.read_bytes())
        out = raw.with_suffix(".stdout.log")
        out.write_bytes(stdout.read_bytes())
        item.update(raw=str(raw), stdout=str(out))
        call = {**native_call, "index": index, "raw": str(raw)}
        raw.with_suffix(".json").write_text(json.dumps(call))
        calls.append(call)
    native_capture.write_text(
        json.dumps(
            {"case_id": "misaal-case", "source_sha256": "source", "program_sha256": "program", "invocations": calls}
        )
    )
    catalog["cases"][-1].update(
        backend_capture_evidence=str(native_capture), source_sha256="source", generated_program_sha256="program"
    )
    (tmp_path / "benchmarks/catalog.json").write_text(json.dumps(catalog))
    rows, jobs = retained.retained_rows(tmp_path)
    assert len(jobs) == 1
    assert len(jobs[0]["aliases"]) == 2
    assert [row["outcome"]["status"] for row in rows[1:]] == ["pending", "pending", "blocked"]
    assert rows[1]["parent_outcome"]["reason"] == "parent looped"
    engine = tmp_path / "engine"
    engine.write_text("engine")

    def run(command: list[str], cwd: Path, prefix: Path, **policy: object) -> PilotProcessResult:
        assert policy["require_guard"] is True
        assert policy["allow_warning_pressure"] is False
        assert policy["disk_reserve_bytes"] == 10 * 1024**3
        out, err = prefix.with_suffix(".stdout"), prefix.with_suffix(".stderr")
        out.write_text("(B)\n")  # Current optimum may differ; all original roots must still return.
        err.write_text("")
        return PilotProcessResult("success", 0, 0.01, 1, out, err, None)

    monkeypatch.setattr(retained, "run_bounded_command", run)
    directory = tmp_path / "ordinary"
    record = retained.validate_job(jobs[0], engine, directory)
    assert record["status"] == "success"
    assert retained.validate_job(jobs[0], engine, directory) == record
    assert retained.validate_job({**jobs[0], "aliases": ["another-alias"]}, engine, directory) == record
    with pytest.raises(ValueError, match="identity changed"):
        retained.validate_job(jobs[0], engine, directory, timeout_sec=120)
    retained.apply_validations(rows, jobs, directory, tmp_path)
    manifest = write_corpus(rows, tmp_path / "corpus")
    assert len(manifest["workloads"]) == 2
    assert manifest["cases"][1]["parent_outcome"]["reason"] == "parent looped"
    assert len(manifest["workloads"][1]["aliases"]) == 2


def test_catalog_groups_configurations_preserves_history_and_supersedes_hardboiled(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    catalog = setup_retained(tmp_path, monkeypatch)
    catalog["families"]["hardboiled"] = {}
    catalog["cases"].append(
        {
            "id": "hardboiled-old",
            "family": "hardboiled",
            "source": "generator",
            "status": "captured",
            "workloads": ["old.egg"],
        }
    )
    rows, _ = retained.retained_rows(tmp_path)
    rows.append({**rows[0], "id": "eggcc-source--other", "configuration": {"pass": "other"}})
    rows.append(
        {**rows[0], "id": "hardboiled-published-one", "catalog_id": "hardboiled-published-one", "family": "hardboiled"}
    )
    rows.append(
        {
            "id": "churchroad-later-extra",
            "family": "churchroad",
            "source": "extra.sv",
            "outcome": {"status": "blocked", "reason": "not acquired"},
        }
    )
    directory = tmp_path / "corpus"
    manifest = write_corpus(rows, directory)
    receipt = directory / "manifest.json"
    projected = retained.project_catalog(catalog, manifest, receipt, tmp_path)
    assert len(projected["cases"]) == 3
    assert projected["cases"][1]["benchmark_selection"]["workloads"] == []
    (tmp_path / "benchmarks/catalog.json").write_text(json.dumps(projected))
    selection = resolve_suite(["eggcc", "hardboiled"], tmp_path)
    assert len(selection.files) == 1
    assert not selection.capture_errors
    assert projected["cases"][0]["complete_reproduction"]["scope"] == "standalone-workload"
    assert len(manifest["workloads"][0]["aliases"]) == 3


@pytest.mark.parametrize(
    "changed",
    [
        None,
        "id",
        "source",
        "repository",
        "revision",
        "top_module_name",
        "architecture",
        "scope",
        "catalog_id",
        "status",
        "receipt_sha256",
        "foreign_receipt",
        "validation_stage",
        "validation_status",
        "validation_case",
        "replay",
        "captured_source",
        "captured_revision",
        "captured_configuration",
    ],
)
def test_projection_admits_only_verified_inventoried_later_churchroad_cases(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, changed: str | None
) -> None:
    catalog = setup_retained(tmp_path, monkeypatch)
    catalog["families"]["churchroad"] = {}
    catalog["cases"].append(
        {"id": "churchroad-wide_mul", "family": "churchroad", "source": "wide_mul.v", "workloads": []}
    )
    evaluation = {
        "repository": "https://github.com/gussmith23/churchroad-evaluation",
        "revision": "a" * 40,
        "sources": ["benchmarks/mul/0_stage/mul_0_stage_unsigned_8_8_8_bit.sv"],
    }
    (tmp_path / "benchmarks/reproduction/population.json").write_text(
        json.dumps({"churchroad": {"later_evaluation": evaluation}})
    )
    rows, _ = retained.retained_rows(tmp_path)
    case_id = "churchroad-later-mul_0_stage_unsigned_8_8_8_bit"
    churchroad = {
        "id": case_id,
        "catalog_id": case_id,
        "family": "churchroad",
        "source": evaluation["sources"][0],
        "configuration": {
            "repository": evaluation["repository"],
            "revision": evaluation["revision"],
            "top_module_name": Path(evaluation["sources"][0]).stem,
            "architecture": "xilinx-ultrascale-plus",
        },
        "scope": "artifact-extra",
        "repository": evaluation["repository"],
        "revision": evaluation["revision"],
    }
    replay = tmp_path / "churchroad.egg"
    replay.write_text("(check (= 2 2))\n")
    capture_result = tmp_path / "churchroad-capture.json"
    capture_result.write_text(json.dumps({"id": case_id, "source_complete": True}))
    capture = stage(
        tmp_path / "churchroad-complete",
        case_id,
        "complete",
        {"case": churchroad},
        capture=str(capture_result),
        artifacts={str(capture_result): sha256_file(capture_result), str(replay): sha256_file(replay)},
    )
    stdout = tmp_path / "churchroad.stdout"
    stdout.write_text("success")
    validation = stage(
        tmp_path / "churchroad-validate",
        case_id,
        "validate",
        {"capture_sha256": sha256_file(capture_result), "artifacts": capture["artifacts"]},
        artifacts={str(stdout): sha256_file(stdout)},
        workloads=[str(replay)],
        validations=[
            {
                "replay": str(replay),
                "replay_sha256": sha256_file(replay),
                "status": "success",
                "output_contract_passed": True,
            }
        ],
    )
    index = tmp_path / "benchmarks/local/reproduction/index.json"
    index.write_text(json.dumps({case_id: {**validation, "capture_stage": capture}}))
    monkeypatch.setattr(retained, "expected_cases", lambda catalog, population: [churchroad])
    churchroad_rows, _ = retained.retained_rows(tmp_path)
    rows.extend(churchroad_rows)
    directory = tmp_path / "corpus"
    manifest = write_corpus(rows, directory)
    receipt = directory / "manifest.json"
    row = manifest["cases"][-1]
    if changed:
        if changed in {"repository", "revision", "top_module_name", "architecture"}:
            row["configuration"][changed] = "changed"
        elif changed == "id":
            row[changed] = "churchroad-later-uninventoried"
        elif changed == "catalog_id":
            row[changed] = "churchroad-wide_mul"
        elif changed == "foreign_receipt":
            row["receipt"] = manifest["cases"][0]["receipt"]
            row["receipt_sha256"] = manifest["cases"][0]["receipt_sha256"]
        elif changed == "replay":
            row["workloads"] = manifest["cases"][0]["workloads"]
        elif changed.startswith("validation_"):
            validation[changed.removeprefix("validation_")] = "changed"
            Path(row["receipt"]).write_text(json.dumps(validation))
            row["receipt_sha256"] = sha256_file(Path(row["receipt"]))
        elif changed.startswith("captured_"):
            capture["identity"]["case"][changed.removeprefix("captured_")] = "changed"
            capture["identity_sha256"] = hashlib.sha256(
                json.dumps(capture["identity"], sort_keys=True).encode()
            ).hexdigest()
            capture_receipt = Path(capture["attempt"]) / "stage.json"
            capture_receipt.write_text(json.dumps(capture))
            row["evidence"]["capture_stage"].update(
                identity_sha256=capture["identity_sha256"], receipt_sha256=sha256_file(capture_receipt)
            )
        else:
            row[changed] = "changed"
        with pytest.raises(ValueError, match="later Churchroad|retained evidence changed"):
            retained.project_catalog(catalog, manifest, receipt, tmp_path)
        return
    projected = retained.project_catalog(catalog, manifest, receipt, tmp_path)
    assert len(projected["cases"]) == 3
    published = projected["cases"][-1]
    assert published["id"] == case_id
    assert published["source"] == evaluation["sources"][0]
    assert published["scope"] == "artifact-extra"
    assert published["configuration"] == rows[-1]["configuration"]
    assert published["repository"] == evaluation["repository"]
    assert published["revision"] == evaluation["revision"]
    assert published["benchmark_selection"]["workloads"]
    assert not projected["cases"][1]["complete_reproduction"]["workloads"]
    assert retained.project_catalog(projected, manifest, receipt, tmp_path) == projected


def test_packaged_calls_use_original_receipts_and_retain_recursive_aliases(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    catalog = setup_retained(tmp_path, monkeypatch)
    catalog["cases"].append(
        {
            "id": "misaal-loop",
            "family": "misaal",
            "source": "source",
            "configuration": {},
            "status": "blocked",
            "workloads": [],
        }
    )
    (tmp_path / "benchmarks/catalog.json").write_text(json.dumps(catalog))
    source = "(datatype E (A))\n(let $x (A))\n(run 5)\n(extract $x)\n(check (= $x (A)))\n"
    replay = tmp_path / "packaged.egg"
    replay.write_text(source)
    selections = [{"root": "$x", "selected": "(A)", "check": "(check (= $x (A)))"}]
    calls: list[dict] = []
    for index in range(2):
        raw = tmp_path / f"invocation-{index}.egg"
        raw.write_text(source)
        stdout = raw.with_suffix(".stdout.log")
        stdout.write_text("(A)\n")
        call = {
            "index": index,
            "raw": str(raw),
            "sha256": sha256_file(raw),
            "status": "success",
            "returncode": 0,
            "caller": "apply_rewrite",
            "selected": "(A)",
            "stdout_sha256": sha256_file(stdout),
        }
        raw.with_suffix(".result.json").write_text(json.dumps(call))
        calls.append(call)
    child = tmp_path / "child.json"
    child.write_text(
        json.dumps(
            {"status": "failure", "source_capture_complete": False, "error": "parent loop", "invocations": calls}
        )
    )
    selected = tmp_path / "selected-calls.json"
    selected.write_text(json.dumps({"invocations": [calls[0]]}))
    package = tmp_path / "package.json"
    package.write_text(
        json.dumps(
            {
                "selected_calls_sha256": sha256_file(selected),
                "source_receipts": [{"case": "misaal-loop", "receipt": str(child), "sha256": sha256_file(child)}],
                "invocations": [
                    {
                        **calls[0],
                        "replay": str(replay),
                        "replay_sha256": sha256_file(replay),
                        "selections": selections,
                        "output_contract": native_check_contract(source, [(4, selections[0]["check"])], selections),
                    }
                ],
            }
        )
    )
    rows: list[dict] = []
    jobs: list[dict] = []
    retained.add_packaged_misaal(rows, jobs, package, tmp_path)
    assert len(rows) == 2 and len(jobs) == 1 and len(jobs[0]["aliases"]) == 2
    assert all(row["outcome"]["status"] == "pending" for row in rows)
    assert all(row["parent_outcome"]["status"] == "failure" for row in rows)
    frozen = tmp_path / "candidates.json"
    frozen.write_text(json.dumps({"rows": rows, "jobs": jobs}))
    assert retained.read_candidates(frozen, tmp_path) == (rows, jobs)
    Path(calls[1]["raw"]).with_suffix(".result.json").write_text("{}")
    with pytest.raises(ValueError, match="retained evidence changed"):
        retained.read_candidates(frozen, tmp_path)


def test_projection_preserves_matching_normal_only_proof_blocker(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    catalog = setup_retained(tmp_path, monkeypatch)
    catalog["cases"][0]["normal_workloads"] = [
        {"path": "source.egg", "proof_blocker": "Native output has no proof query"}
    ]
    rows, _ = retained.retained_rows(tmp_path)
    directory = tmp_path / "corpus"
    manifest = write_corpus(rows, directory)
    projected = retained.project_catalog(catalog, manifest, directory / "manifest.json", tmp_path)
    assert retained.project_catalog(projected, manifest, directory / "manifest.json", tmp_path) == projected
    (tmp_path / "benchmarks/catalog.json").write_text(json.dumps(projected))
    assert not resolve_suite("eggcc", tmp_path).files
    selection = resolve_suite("eggcc", tmp_path, include_normal_only=True)
    assert len(selection.files) == 1
    assert list(selection.proof_blockers.values()) == ["Native output has no proof query"]
