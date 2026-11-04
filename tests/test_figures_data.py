"""Check figure selection against the cache identities and missing-data contract."""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Literal, cast

import pytest

from benchmarking.engines import Treatment
from benchmarking.reports.store import ReportRecord, ReportStore
from benchmarking.targets import sha256_file
from benchmarking.workloads import DEFAULT_WORKLOADS, resolve_files
from figures.prepare import FigureData, prepare_figures

from .report_fixtures import make_record, write_report


@pytest.fixture
def figure_root(tmp_path: Path) -> Path:
    """Provide distinct real workload hashes and fake binaries without building."""

    for index, workload in enumerate(DEFAULT_WORKLOADS):
        path = tmp_path / workload.file
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"; workload {index}\n(check (= {index} {index}))\n")
        if workload.fact_directory is not None:
            facts = tmp_path / workload.fact_directory
            facts.mkdir(parents=True)
            (facts / "facts.tsv").write_text("input\n")
    release = tmp_path / "target" / "release"
    release.mkdir(parents=True)
    for name in ("egglog-experimental", "egg-math-benchmark"):
        (release / (name + (".exe" if os.name == "nt" else ""))).write_bytes(name.encode())
    return tmp_path


def test_projection_selects_current_identity_latest_rows_and_preserves_failures(figure_root: Path) -> None:
    files = resolve_files((), figure_root)
    pointer = files[2]
    binary_hash = sha256_file(
        figure_root / "target/release" / ("egglog-experimental.exe" if os.name == "nt" else "egglog-experimental")
    )
    records = [
        make_record(
            index,
            started_at="2026-09-21T00:00:00Z",
            status="failure" if index == 2 else "timed-out" if index == 3 else "success",
            binary_sha256=binary_hash,
            file_sha256=pointer.sha256,
            fact_directory_sha256=pointer.fact_directory_sha256,
            target_label="old-label" if index % 2 else None,
            wall_sec=float(index),
        )
        for index in range(32)
    ]
    records[2]["error_exit_code"] = 17
    records[2]["error_message"] = "proof extraction failed"
    records[2]["file_path"] = "original-pointer.egg"
    records[2]["fact_directory_path"] = "/original/facts"
    records[3]["error_signal"] = 0
    records.append({**records[0], "started_at": "2026-09-20T00:00:00Z"})
    # A newer figures label points to an obsolete binary. Other newer rows
    # deliberately differ in each remaining cache-key coordinate.
    unrelated: tuple[ReportRecord, ...] = (
        {**records[0], "binary_sha256": "sha256:stale", "target_label": "figures"},
        {**records[0], "file_sha256": "sha256:other-file"},
        {**records[0], "fact_directory_sha256": "sha256:other-facts"},
        {**records[0], "treatment": "proofs"},
        {**records[0], "timeout_sec": 121},
    )
    for record in unrelated:
        record["started_at"] = "2026-09-22T00:00:00Z"
        records.append(record)
    report = figure_root / ".reports.jsonl"
    write_report(report, *records)
    original = report.read_bytes()

    _engine_path, overhead_path = prepare_figures(figure_root)
    payload = cast(FigureData, json.loads(overhead_path.read_bytes()))
    selected = next(
        group
        for group in payload["groups"]
        if group["workload_id"] == pointer.display_path and group["treatment"] == "off"
    )
    observations = selected["observations"]
    assert len(observations) == 30
    assert [row["row_index"] for row in observations] == list(range(2, 32))
    assert {row["started_at"] for row in observations} == {"2026-09-21T00:00:00Z"}
    assert [row["status"] for row in observations[:2]] == ["failure", "timed-out"]
    assert observations[0]["wall_sec"] == 2.0
    assert observations[1]["wall_sec"] is None
    source = payload["sources"][observations[0]["source_index"]]
    assert source["target_label"] is None
    assert source["file_path"] == "original-pointer.egg"
    assert source["fact_directory_path"] == "/original/facts"
    assert observations[0]["error_exit_code"] == 17
    assert observations[0]["error_message"] == "proof extraction failed"
    assert "error_signal" not in observations[0]
    assert observations[1]["error_signal"] == 0
    assert payload["sources"][observations[1]["source_index"]]["target_label"] == "old-label"
    assert len(payload["sources"]) == 3
    for observation in observations:
        original_row = records[observation["row_index"]]
        assert payload["sources"][observation["source_index"]] == {
            key: value
            for key, value in original_row.items()
            if key.startswith("target_") or key in ("file_path", "fact_directory_path")
        }
    assert report.read_bytes() == original

    assert len(payload["groups"]) == 30
    assert sum(not group["observations"] for group in payload["groups"]) == 28
    assert [group["workload_order"] for group in payload["groups"][::3]] == list(range(10))
    assert payload["metadata"] == {"source_report": ".reports.jsonl", "rounds": 30, "timeout_sec": 120}


def test_math_observations_are_shared_and_outputs_change_only_when_content_changes(figure_root: Path) -> None:
    files = resolve_files((), figure_root)
    math = files[0]
    suffix = ".exe" if os.name == "nt" else ""
    egglog_hash = sha256_file(figure_root / "target/release" / f"egglog-experimental{suffix}")
    egg_hash = sha256_file(figure_root / "target/release" / f"egg-math-benchmark{suffix}")
    report = figure_root / ".reports.jsonl"
    treatments: tuple[Treatment, ...] = ("off", "proof-extraction", "egg", "egg-proof-extraction")
    records = [
        make_record(
            index,
            started_at="2026-09-21T00:00:00Z",
            binary_sha256=egg_hash if treatment.startswith("egg") else egglog_hash,
            file_sha256=math.sha256,
            treatment=treatment,
            target_label="another-compatible-label",
        )
        for index, treatment in enumerate(treatments)
    ]
    # A different original source makes the table indices differ between files.
    records[2]["target_label"] = "egg-original-label"
    write_report(report, *records)
    output_paths = prepare_figures(figure_root, output_dir=Path("outputs"))
    engine_data, overhead_data = [cast(FigureData, json.loads(path.read_bytes())) for path in output_paths]
    assert [(group["engine"], group["proof_mode"], group["treatment"]) for group in engine_data["groups"]] == [
        ("Egg", "Off", "egg"),
        ("Egg", "Record + extract", "egg-proof-extraction"),
        ("Egglog", "Off", "off"),
        ("Egglog", "Record + extract", "proof-extraction"),
    ]
    for index, treatment in enumerate(("off", "proof-extraction")):
        engine_group = next(group for group in engine_data["groups"] if group["treatment"] == treatment)
        overhead_group = next(group for group in overhead_data["groups"] if group["treatment"] == treatment)
        assert len(engine_group["observations"]) == len(overhead_group["observations"]) == 1
        engine_row, overhead_row = engine_group["observations"][0], overhead_group["observations"][0]
        assert engine_row["row_index"] == overhead_row["row_index"] == index
        assert {key: value for key, value in engine_row.items() if key != "source_index"} == {
            key: value for key, value in overhead_row.items() if key not in ("source_index", "max_rss_bytes")
        }
        assert overhead_row["max_rss_bytes"] == records[index]["max_rss_bytes"]
        assert (
            engine_data["sources"][engine_row["source_index"]] == overhead_data["sources"][overhead_row["source_index"]]
        )
    assert {group["workload"] for group in engine_data["groups"]} == {"Math"}
    assert [group["binary_sha256"] for group in engine_data["groups"]] == [egg_hash, egg_hash, egglog_hash, egglog_hash]

    sentinel_ns = 1_000_000_000_000
    for path in output_paths:
        os.utime(path, ns=(sentinel_ns, sentinel_ns))
    prepare_figures(figure_root, output_dir=Path("outputs"))
    assert [path.stat().st_mtime_ns for path in output_paths] == [sentinel_ns, sentinel_ns]

    # An unrelated workload changes only the overhead projection.
    ReportStore(report).append(
        make_record(
            4,
            started_at="2026-09-21T00:00:01Z",
            binary_sha256=egglog_hash,
            file_sha256=files[3].sha256,
        )
    )
    prepare_figures(figure_root, output_dir=Path("outputs"))
    assert output_paths[0].stat().st_mtime_ns == sentinel_ns
    assert output_paths[1].stat().st_mtime_ns != sentinel_ns


def test_missing_cache_does_not_create_empty_report_or_outputs(figure_root: Path) -> None:
    with pytest.raises(FileNotFoundError, match="run the figure benchmarks first"):
        prepare_figures(figure_root)
    assert not (figure_root / ".reports.jsonl").exists()
    assert not (figure_root / "figures").exists()


@pytest.mark.parametrize("mutation", ("egg", "egglog", "workload", "facts"))
def test_changed_current_bytes_invalidate_only_matching_figure_groups(
    figure_root: Path, mutation: Literal["egg", "egglog", "workload", "facts"]
) -> None:
    files = resolve_files((), figure_root)
    suffix = ".exe" if os.name == "nt" else ""
    egglog_binary = figure_root / "target/release" / f"egglog-experimental{suffix}"
    egg_binary = figure_root / "target/release" / f"egg-math-benchmark{suffix}"
    treatments: tuple[Treatment, ...] = ("off", "proofs", "proof-extraction")
    records = [
        make_record(
            0,
            started_at="2026-09-21T00:00:00Z",
            binary_sha256=sha256_file(egglog_binary),
            file_sha256=file.sha256,
            fact_directory_sha256=file.fact_directory_sha256,
            treatment=treatment,
            target_label="figures",
        )
        for file in files
        for treatment in treatments
    ]
    egg_treatments: tuple[Treatment, ...] = ("egg", "egg-proof-extraction")
    records.extend(
        make_record(
            0,
            started_at="2026-09-21T00:00:00Z",
            binary_sha256=sha256_file(egg_binary),
            file_sha256=files[0].sha256,
            treatment=treatment,
            target_label="figures",
        )
        for treatment in egg_treatments
    )
    report = figure_root / ".reports.jsonl"
    write_report(report, *records)
    before = [cast(FigureData, json.loads(path.read_bytes())) for path in prepare_figures(figure_root)]
    assert all(len(group["observations"]) == 1 for payload in before for group in payload["groups"])

    pointer_facts = files[2].fact_directory
    assert pointer_facts is not None
    changed_path = {
        "egg": egg_binary,
        "egglog": egglog_binary,
        "workload": files[0].absolute_path,
        "facts": pointer_facts / "facts.tsv",
    }[mutation]
    changed_path.write_bytes(changed_path.read_bytes() + b"\n; changed\n")
    current_files = {file.display_path: file for file in resolve_files((), figure_root)}

    after = [cast(FigureData, json.loads(path.read_bytes())) for path in prepare_figures(figure_root)]
    affected_groups = 0
    for payload in after:
        for row in payload["groups"]:
            affected = {
                "egg": row["engine"] == "Egg",
                "egglog": row["engine"] == "Egglog",
                "workload": row["workload_id"] == files[0].display_path,
                "facts": row["workload_id"] == files[2].display_path,
            }[mutation]
            assert len(row["observations"]) == (0 if affected else 1)
            affected_groups += affected
            current_file = current_files[row["workload_id"]]
            assert row["file_sha256"] == current_file.sha256
            assert row["fact_directory_sha256"] == current_file.fact_directory_sha256
            assert row["binary_sha256"] == sha256_file(egg_binary if row["engine"] == "Egg" else egglog_binary)
    assert affected_groups == {"egg": 2, "egglog": 32, "workload": 7, "facts": 3}[mutation]
