"""Gate named-label suite reuse before deciding whether collection is needed."""

from __future__ import annotations

import json
import shutil
from pathlib import Path
from typing import Any

import pytest

from benchmarking import admission, benchmark, collection, models, suites
from benchmarking.reports.store import CacheKey, ReportStore

from .report_fixtures import make_record, write_report


def test_relocated_corpus_survives_cargo_cleanup_and_reuses_content_identities(tmp_path: Path) -> None:
    old_path = "target/benchmark-suite/workloads/captured.egg"
    new_path = "benchmarks/local/workloads/captured.egg"
    original = tmp_path / old_path
    original.parent.mkdir(parents=True)
    original.write_text("(check (= 1 1))\n")
    catalog_path = tmp_path / "benchmarks/catalog.json"
    catalog_path.parent.mkdir()
    catalog: dict[str, Any] = {
        "families": {"eggcc": {}},
        "cases": [
            {"id": "captured", "family": "eggcc", "source": "source", "status": "captured", "workloads": [old_path]}
        ],
    }
    catalog_path.write_text(json.dumps(catalog))
    original_file = suites.resolve_suite("eggcc", tmp_path).files[0]
    hashes = {"egglog": "sha256:binary"}
    pilot_record = {
        "identity": admission.pilot_identity(original_file, "eggcc", hashes, admission.PilotPolicy(), tmp_path),
        "file_path": old_path,
        "status": "admitted",
        "reason": None,
    }
    old_evidence = tmp_path / "target/benchmark-suite/pilot.jsonl"
    old_evidence.write_text(json.dumps(pilot_record) + "\n")
    report = tmp_path / "report.jsonl"
    record = make_record(
        0,
        started_at="2026-09-22T00:00:00Z",
        binary_sha256=hashes["egglog"],
        file_sha256=original_file.sha256,
    )
    record["file_path"] = old_path
    write_report(report, record)
    original_cache = report.read_bytes()
    destination = tmp_path / new_path
    destination.parent.mkdir(parents=True)
    original.rename(destination)
    evidence = tmp_path / admission.PILOT_RELATIVE_PATH
    old_evidence.rename(evidence)
    catalog["cases"][0]["workloads"] = [new_path]
    catalog_path.write_text(json.dumps(catalog))
    shutil.rmtree(tmp_path / "target")

    relocated = suites.resolve_suite("eggcc", tmp_path)
    assert not relocated.capture_errors
    file = relocated.files[0]
    assert file.sha256 == original_file.sha256
    assert (
        admission.find_pilot_record(
            admission.load_pilot_records(evidence), file, "eggcc", hashes, admission.PilotPolicy(), tmp_path
        )
        == pilot_record
    )
    store = ReportStore(report)
    rows = store.latest_records(CacheKey(hashes["egglog"], file.sha256, "off", 120, ""), 1)
    assert len(rows) == 1 and rows[0].record["file_path"] == old_path
    assert report.read_bytes() == original_cache


@pytest.fixture
def captured_suite(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> suites.SuiteSelection:
    """Create distinct captures and forbid builds or measurements unless a test opts in."""

    (tmp_path / "benchmarks").mkdir()
    cases = []
    for name, value in (("admitted", 1), ("rejected", 2)):
        (tmp_path / f"{name}.egg").write_text(f"(check (= {value} {value}))\n")
        cases.append(
            {
                "id": name,
                "family": "eggcc",
                "source": name,
                "status": "captured",
                "workloads": [f"{name}.egg"],
            }
        )
    cases.extend(
        {
            "id": f"blocked-{index}",
            "family": "eggcc",
            "source": f"unavailable-{index}",
            "status": "blocked",
            "workloads": [],
            "reason": "shared exporter blocker",
        }
        for index in range(12)
    )
    (tmp_path / "benchmarks/catalog.json").write_text(json.dumps({"families": {"eggcc": {}}, "cases": cases}))
    monkeypatch.setattr(benchmark, "__file__", str(tmp_path / "benchmarking/benchmark.py"))
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _path: tmp_path)
    monkeypatch.setattr(
        collection, "materialize_git_ref", lambda *_args: pytest.fail("cached suite must not materialize a checkout")
    )
    monkeypatch.setattr(
        collection, "build_resolved_target", lambda *_args: pytest.fail("cached suite must not build a binary")
    )
    monkeypatch.setattr(collection, "run_process", lambda *_args: pytest.fail("cached suite must not measure"))
    return suites.resolve_suite("eggcc", tmp_path)


@pytest.mark.parametrize("dirty", [False, True])
@pytest.mark.parametrize("split_targets", [False, True])
@pytest.mark.parametrize("rejected_pilot", ["timed-out", "missing", "stale"])
def test_named_label_reuses_complete_samples_without_pilot_but_preserves_known_failures(
    captured_suite: suites.SuiteSelection,
    dirty: bool,
    split_targets: bool,
    rejected_pilot: str,
    capsys: Any,
) -> None:
    root = captured_suite.root
    report = root / "report.jsonl"
    treatments: tuple[models.Treatment, ...] = ("off", "proof-extraction")
    rows = [
        make_record(
            0,
            started_at="2026-09-21T00:00:00Z",
            file_sha256=file.sha256,
            target_label=label,
            binary_sha256=binary,
            treatment=treatment,
        )
        for label, binary in (
            (("figures", "sha256:bin"), ("baseline", "sha256:baseline"))
            if split_targets
            else (("figures", "sha256:bin"),)
        )
        for treatment in treatments
        for file in captured_suite.files
    ]
    for row in rows:
        row["target_is_dirty"] = dirty
    write_report(report, *rows)
    evidence = root / admission.PILOT_RELATIVE_PATH
    evidence.parent.mkdir(parents=True)
    pilots = [
        {
            "identity": admission.pilot_identity(
                file,
                "eggcc",
                {"egglog": "sha256:stale" if index == 1 and rejected_pilot == "stale" else "sha256:bin"},
                admission.PilotPolicy(),
                root,
            ),
            "status": "admitted" if index == 0 else "timed-out",
            "reason": None if index == 0 else "proof-testing exceeded 120s",
        }
        for index, file in enumerate(captured_suite.files)
        if index == 0 or rejected_pilot != "missing"
    ]
    if split_targets:
        pilots.extend(
            {
                "identity": admission.pilot_identity(
                    file, "eggcc", {"egglog": "sha256:baseline"}, admission.PilotPolicy(), root
                ),
                "status": "admitted" if index == 0 else "timed-out",
                "reason": None if index == 0 else "proof-testing exceeded 120s",
            }
            for index, file in enumerate(captured_suite.files)
        )
    evidence.write_text("".join(json.dumps(row) + "\n" for row in pilots))
    original_report = report.read_bytes()
    original_evidence = evidence.read_bytes()

    result = benchmark.main(
        [
            "--suite",
            "eggcc",
            "--timeout-sec",
            "120",
            "--target",
            "figures=",
            "--rounds",
            "1",
            "--treatment",
            "proof-extraction",
            "--report",
            str(report),
            "--format",
            "markdown",
            "--detail",
            "files",
            *(["--compare-target", "baseline="] if split_targets else []),
        ]
    )

    output = capsys.readouterr()
    assert result == 0
    assert "12 blocked source cases" in output.err
    assert "coverage.md" in output.err
    assert "shared exporter blocker" not in output.err
    assert "admitted.egg" in output.out and "rejected.egg" in output.out
    if rejected_pilot == "timed-out" or split_targets:
        assert "classified 1 captured workload outcome" in " ".join(output.err.split())
        assert "proof-testing exceeded 120s" in output.out
    else:
        assert "proof-testing exceeded 120s" not in output.out
    assert report.read_bytes() == original_report
    assert evidence.read_bytes() == original_evidence


def test_named_label_rebuild_discards_stale_validation_and_collects_new_binary(
    captured_suite: suites.SuiteSelection,
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
) -> None:
    root = captured_suite.root
    report = root / "report.jsonl"
    treatments: tuple[models.Treatment, ...] = ("off", "proof-extraction")
    write_report(
        report,
        *(
            make_record(
                0,
                started_at="2026-09-21T00:00:00Z",
                file_sha256=captured_suite.files[0].sha256,
                target_label="figures",
                treatment=treatment,
            )
            for treatment in treatments
        ),
    )
    evidence = root / admission.PILOT_RELATIVE_PATH
    evidence.parent.mkdir(parents=True)
    evidence.write_text(
        "".join(
            json.dumps(
                {
                    "identity": admission.pilot_identity(
                        file, "eggcc", {"egglog": "sha256:bin"}, admission.PilotPolicy(), root
                    ),
                    "status": "admitted" if index == 0 else "timed-out",
                    "reason": None if index == 0 else "proof-testing exceeded 120s",
                }
            )
            + "\n"
            for index, file in enumerate(captured_suite.files)
        )
    )
    builds = []

    def build(request: models.TargetRequest, row: models.TargetRow, *_args: object) -> models.ResolvedTarget:
        builds.append(request.label)
        return models.ResolvedTarget(request, row, "sha256:rebuilt", root / "egglog")

    monkeypatch.setattr(collection, "materialize_git_ref", lambda *_args: (root, "abc123"))
    monkeypatch.setattr(
        collection,
        "target_row_for_request",
        lambda request, *_args: models.TargetRow(".", str(root), "HEAD", "abc123", False, request.label),
    )
    monkeypatch.setattr(collection, "build_resolved_target", build)

    def preflight(plan: collection.CollectionPlan, _timeout: int) -> None:
        assert plan.target.binary_sha256 == "sha256:rebuilt"
        assert plan.total_missing_observations == 8
        assert {run.file for run in plan.runs} == set(captured_suite.files)
        raise ValueError("fresh measurement plan needs no pilot")

    monkeypatch.setattr(benchmark, "preflight_collection", preflight)
    original_report = report.read_bytes()

    result = benchmark.main(
        [
            "--suite",
            "eggcc",
            "--timeout-sec",
            "120",
            "--target",
            "figures=",
            "--rounds",
            "2",
            "--treatment",
            "proof-extraction",
            "--report",
            str(report),
        ]
    )

    assert result == 2
    assert builds == ["figures"]
    assert "fresh measurement plan needs no pilot" in capsys.readouterr().err
    assert report.read_bytes() == original_report


def test_rebuilt_label_expanding_admission_rechecks_other_cached_targets(
    captured_suite: suites.SuiteSelection,
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
) -> None:
    root = captured_suite.root
    report = root / "report.jsonl"
    write_report(
        report,
        *(
            make_record(
                0,
                started_at="2026-09-21T00:00:00Z",
                file_sha256=captured_suite.files[0].sha256,
                target_label=label,
                binary_sha256=f"sha256:{label}",
            )
            for label in ("baseline", "candidate")
        ),
    )
    builds = []

    def gate(
        selection: suites.SuiteSelection, resolved: tuple[models.ResolvedTarget, ...], **_kwargs: object
    ) -> tuple[tuple[models.FileSpec, ...], tuple[str, ...], tuple[tuple[models.FileSpec, str], ...]]:
        candidate = next(target for target in resolved if target.request.label == "candidate")
        files = selection.files if candidate.binary_sha256 == "sha256:rebuilt-candidate" else selection.files[:1]
        return files, (), ()

    def build(request: models.TargetRequest, row: models.TargetRow, *_args: object) -> models.ResolvedTarget:
        builds.append(request.label)
        return models.ResolvedTarget(request, row, f"sha256:rebuilt-{request.label}", root / str(request.label))

    def preflight(plan: collection.CollectionPlan, _timeout: int) -> None:
        assert builds == ["candidate", "baseline"]
        assert tuple(run.file for run in plan.runs) == captured_suite.files
        assert plan.target.binary_path is not None
        raise ValueError("stopped after resolving every required binary")

    monkeypatch.setattr(benchmark, "require_suite_admission", gate)
    monkeypatch.setattr(collection, "materialize_git_ref", lambda *_args: (root, "abc123"))
    monkeypatch.setattr(
        collection,
        "target_row_for_request",
        lambda request, *_args: models.TargetRow(".", str(root), "HEAD", "abc123", False, request.label),
    )
    monkeypatch.setattr(collection, "build_resolved_target", build)
    monkeypatch.setattr(benchmark, "preflight_collection", preflight)
    original_report = report.read_bytes()

    result = benchmark.main(
        [
            "--suite",
            "eggcc",
            "--timeout-sec",
            "120",
            "--target",
            "candidate=",
            "--compare-target",
            "baseline=",
            "--rounds",
            "1",
            "--treatment",
            "proof-extraction",
            "--report",
            str(report),
        ]
    )

    assert result == 2
    assert "stopped after resolving every required binary" in capsys.readouterr().err
    assert report.read_bytes() == original_report
