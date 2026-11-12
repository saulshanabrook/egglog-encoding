"""Portable figure data preserves recorded identities and never measures implicitly."""

from __future__ import annotations

import gzip
import io
import json
import subprocess
from copy import deepcopy
from pathlib import Path
from typing import Any, cast

import pytest
from rich.console import Console

from benchmarking import collection, figures, slotted_ast, targets
from benchmarking.engines import Treatment
from benchmarking.figure_results import figure_results
from benchmarking.figure_reuse import FigureData, grouped_figure, import_figure, merge_observations, reuse_figure
from benchmarking.figures import renderer_metadata
from benchmarking.reports.store import ReportStore

from .report_fixtures import make_record


@pytest.fixture
def saved(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    monkeypatch.setattr(figures, "renderer_metadata", lambda: {"git_sha": "renderer", "is_dirty": False})
    name = "retired-export"
    inputs = []
    rows: list[dict[str, Any]] = []
    for offset, treatment in enumerate(("off", "term")):
        indices = []
        for run in range(2):
            row = dict(
                make_record(
                    run,
                    started_at=f"2026-01-01T00:00:0{run}Z",
                    treatment=cast(Treatment, treatment),
                    target_label="historical",
                    max_rss_bytes=1048576,
                    wall_sec=offset + 1.0,
                    timeout_sec=17,
                )
            )
            row["target_path"] = "/absent/old-checkout"
            row["file_path"] = "/absent/input.egg"
            row["row_index"] = len(rows)
            indices.append(len(rows))
            rows.append(row)
        inputs.append(
            {
                "logical_id": "sha256:file",
                "label": "gone.egg",
                "family": "test",
                "file_sha256": "sha256:file",
                "treatment": treatment,
                "threads": 1,
                "requested_threads": 1,
                "binary_sha256": "sha256:bin",
                "memory_limit_bytes": 17179869184,
                "selected_row_indices": indices,
                "validation_failures": {},
                "validation_issue": "",
                "exclusion": None,
            }
        )
    spec = {
        "$schema": "https://vega.github.io/schema/vega-lite/v6.json",
        "data": {"url": "/absent/cache.json"},
        "params": [
            {"name": key, "value": value}
            for key, value in {
                "selected_inputs": inputs,
                "target_label": "historical",
                "rounds": 2,
                "timeout_sec": 17,
                "t_critical": 12.706204736432095,
                "source_blockers": [],
            }.items()
        ],
        "mark": "point",
    }
    data = FigureData(name, spec, grouped_figure(rows, "historical"), {"target": {"git_sha": "measured"}})
    directory = tmp_path / "saved"
    figures.render_figure_data([data], directory, Console(file=io.StringIO()), images=False)
    return directory


def test_complete_directory_replay_uses_no_current_catalog_inputs_or_collectors(
    saved: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    def forbidden(*_args: Any, **_kwargs: Any) -> Any:
        pytest.fail("complete replay attempted live input/target/measurement work")

    monkeypatch.setattr(figures, "DEFAULT_CONFIG", tmp_path / "absent-catalog.json")
    monkeypatch.setattr(figures, "resolve_figures", forbidden)
    monkeypatch.setattr(collection, "resolve_requests", forbidden)
    monkeypatch.setattr(collection, "collect", forbidden)
    monkeypatch.setattr(slotted_ast, "slotted_ast_records", forbidden)
    monkeypatch.setattr(ReportStore, "__init__", forbidden)
    captured = []
    monkeypatch.setattr(figures, "render_figure_data", lambda data, *_args, **_kw: captured.extend(data))
    for name in ([], ["retired-export"]):
        assert figures.main([*name, "--reuse-from", str(saved), "--no-runs"]) == 0
    assert len(captured) == 2
    parameters = {p["name"]: p["value"] for p in captured[0].spec["params"]}
    assert (parameters["rounds"], parameters["timeout_sec"]) == (2, 17)
    assert captured[0].provenance["target"]["git_sha"] == "measured"


def test_compact_roundtrip_preserves_raw_samples_and_portable_plot_data(saved: Path, tmp_path: Path) -> None:
    first = json.loads((saved / "retired-export.results.json").read_text())
    data = import_figure("retired-export", saved)
    figures.render_figure_data([data], tmp_path / "again", Console(file=io.StringIO()), images=False)
    second = json.loads((tmp_path / "again/retired-export.results.json").read_text())
    assert first["comparisons"] == second["comparisons"]
    assert [row["sample_n"] for row in second["conditions"]] == [2, 2]
    assert all("timing_summary" not in row for c in second["conditions"] for row in c["observations"])
    spec = json.loads((tmp_path / "again/retired-export.bound.vl.json").read_text())
    assert "url" not in spec["data"]
    assert all("target_path" not in row for group in spec["data"]["values"][0]["groups"] for row in group["samples"])
    assert second["renderer"]["git_sha"] == "renderer" != second["provenance"]["target"]["git_sha"]


def test_overlapping_caches_keep_distinct_identical_samples() -> None:
    one = {**make_record(0, started_at="2026-01-01T00:00:00Z"), "row_index": 0}
    two = {**one, "row_index": 1}
    different = {**one, "wall_sec": 2}
    rows: list[dict[str, Any]] = []
    merge_observations(rows, [one, two])
    merge_observations(rows, [one, two, different])
    assert len(rows) == 3
    assert [row["row_index"] for row in rows] == [0, 1, 2]
    assert [row["source_row_index"] for row in rows] == [0, 1, 0]


def test_colliding_imported_indices_preserve_distinct_conditions(saved: Path) -> None:
    path = saved / "retired-export.results.json"
    result = json.loads(path.read_text())
    for row in result["conditions"][1]["observations"]:
        row["row_index"] -= 2
    result["conditions"][1]["selected_row_indices"] = [0, 1]
    path.write_text(json.dumps(result))
    path = saved / "retired-export.bound.vl.json"
    spec = json.loads(path.read_text())
    selected = next(p["value"] for p in spec["params"] if p["name"] == "selected_inputs")
    selected[1]["selected_row_indices"] = [0, 1]
    path.write_text(json.dumps(spec))
    data = import_figure("retired-export", saved)
    assert len(data.grouped.records) == 4
    assert [cast(Any, row)["row_index"] for row in data.grouped.records] == [0, 1, 2, 3]


def test_only_explicit_settings_override_and_missing_no_runs_is_read_only(saved: Path, tmp_path: Path) -> None:
    data = import_figure("retired-export", saved)
    cache = tmp_path / "unused-cache.jsonl"
    reuse_figure(data, cache, True, {"rounds": 1}, Console(file=io.StringIO()))
    parameters = {p["name"]: p["value"] for p in data.spec["params"]}
    assert parameters["rounds"] == 1 and parameters["timeout_sec"] == 17
    assert all(len(item["selected_row_indices"]) == 1 for item in parameters["selected_inputs"])
    with pytest.raises(ValueError, match="missing 1 observations.*no-runs"):
        reuse_figure(import_figure("retired-export", saved), cache, True, {"rounds": 3}, Console(file=io.StringIO()))
    assert not cache.exists()


def test_explicit_config_restyles_without_resolving_workload_globs(
    saved: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    style = tmp_path / "style.json"
    style.write_text(json.dumps({"title": "Edited", "data": {"url": "unused"}, "params": []}))
    config = tmp_path / "catalog.json"
    config.write_text(
        json.dumps(
            {
                "rounds": 99,
                "figures": {
                    "retired-export": {"spec": "style.json", "files": ["/absent/*.egg"], "treatments": ["off"]}
                },
            }
        )
    )
    monkeypatch.setattr(figures, "resolve_figures", lambda *_: pytest.fail("restyling resolved workloads"))
    captured = []
    monkeypatch.setattr(figures, "render_figure_data", lambda data, *_args, **_kw: captured.extend(data))
    assert figures.main(["--reuse-from", str(saved), "--no-runs", "--config", str(config)]) == 0
    assert captured[0].spec["title"] == "Edited"
    assert next(p["value"] for p in captured[0].spec["params"] if p["name"] == "rounds") == 2


def test_gzip_import_and_identity_validation(saved: Path) -> None:
    path = saved / "retired-export.results.json"
    result = json.loads(path.read_text())
    with gzip.open(path.with_suffix(".json.gz"), "wt") as handle:
        json.dump(result, handle)
    path.unlink()
    bound = saved / "retired-export.bound.vl.json"
    with gzip.open(Path(str(bound) + ".gz"), "wb") as handle:
        handle.write(bound.read_bytes())
    bound.unlink()
    assert len(import_figure("retired-export", saved).grouped.records) == 4
    result["conditions"][0]["observations"][0]["binary_sha256"] = "wrong"
    with gzip.open(path.with_suffix(".json.gz"), "wt") as handle:
        json.dump(result, handle)
    with pytest.raises(ValueError, match="recorded input/engine"):
        import_figure("retired-export", saved)


def test_missing_original_endpoint_blocks_before_any_collector(
    saved: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(collection, "collect", lambda *_a, **_k: pytest.fail("mismatched endpoint was launched"))
    with pytest.raises(ValueError, match="unavailable or changed"):
        reuse_figure(
            import_figure("retired-export", saved),
            tmp_path / "none.jsonl",
            False,
            {"rounds": 3},
            Console(file=io.StringIO()),
        )


def test_missing_samples_reuse_local_overlap_without_collection(
    saved: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    data = import_figure("retired-export", saved)
    path = tmp_path / "local.jsonl"
    store = ReportStore(path)
    original = json.loads((saved / "retired-export.results.json").read_text())
    for condition in original["conditions"]:
        for observed in condition["observations"]:
            row = dict(observed)
            row.pop("row_index", None)
            row.pop("source_row_index", None)
            # Figure exports omit profiling; the real local cache retains full profiling.
            row["timing_summary"] = make_record(0, started_at=row["started_at"])["timing_summary"]
            store.append(cast(Any, row))
        extra = dict(row)
        extra["started_at"] = "2026-01-01T00:00:02Z"
        store.append(cast(Any, extra))
    before = path.read_bytes()
    monkeypatch.setattr(collection, "collect", lambda *_a, **_k: pytest.fail("matching local rows were remeasured"))
    reuse_figure(data, path, True, {"rounds": 3}, Console(file=io.StringIO()))
    assert len(data.grouped.records) == 6
    assert path.read_bytes() == before
    assert all(
        len(item["selected_row_indices"]) == 3
        for item in next(p["value"] for p in data.spec["params"] if p["name"] == "selected_inputs")
    )


def test_exact_missing_fill_collects_only_deficit_and_rejects_changed_input(
    saved: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.delenv("CARGO_TARGET_DIR", raising=False)
    checkout = tmp_path / "historical=source"
    binary = checkout / "target/release/egglog-experimental"
    binary.parent.mkdir(parents=True)
    binary.write_text("frozen executable")
    source = checkout / "input.egg"
    source.write_text("frozen source")
    data = import_figure("retired-export", saved)
    parameters = {p["name"]: p["value"] for p in data.spec["params"]}
    parameters["selected_inputs"][:] = parameters["selected_inputs"][:1]
    next(p for p in data.spec["params"] if p["name"] == "target_label")["value"] = "figures"
    item = parameters["selected_inputs"][0]
    item["binary_sha256"], item["file_sha256"] = targets.sha256_file(binary), targets.sha256_file(source)
    rows = [dict(row) for row in data.grouped.records if row["treatment"] == "off"]
    for row in rows:
        row.update(
            binary_sha256=item["binary_sha256"],
            file_sha256=item["file_sha256"],
            target_path=str(checkout),
            file_path=str(source),
        )
    data.grouped = grouped_figure(rows, "historical")
    calls = []

    def collect(store: ReportStore, plans: Any, *_args: Any, **_kwargs: Any) -> None:
        run = plans[0].runs[0]
        calls.append(run)
        assert run.missing_observations == 1
        assert run.cached_statuses == ("success", "success")
        assert plans[0].target.binary_path_for("off") == binary
        row = make_record(
            2,
            started_at="2026-01-01T00:00:02Z",
            binary_sha256=item["binary_sha256"],
            file_sha256=item["file_sha256"],
            max_rss_bytes=1048576,
            target_label=plans[0].target.row.label,
        )
        assert _args[0][0].endpoint.target.label is None
        assert not collection.current_label_bindings(_args[0], _args[1])
        store.append(row)

    monkeypatch.setattr(collection, "collect", collect)
    path = tmp_path / "new.jsonl"
    store = ReportStore(path)
    store.append(make_record(0, started_at="2026-01-01T00:00:00Z", target_label="figures", binary_sha256="sha256:live"))
    pointer = store.find_label_pointer("figures", "egglog-experimental")
    reuse_figure(data, path, False, {"rounds": 3}, Console(file=io.StringIO()))
    assert len(calls) == 1 and ReportStore(path).row_count == 2
    assert ReportStore(path).find_label_pointer("figures", "egglog-experimental") == pointer
    assert all(group["labels"] == ["figures"] for group in data.grouped.data["groups"])
    assert len(data.grouped.records) == 3
    source.write_text("changed bytes")
    with pytest.raises(ValueError, match="original input.*unavailable or changed"):
        reuse_figure(data, path, False, {"rounds": 4}, Console(file=io.StringIO()))
    assert len(calls) == 1


def test_failures_and_exclusions_remain_recorded_outcomes(saved: Path, tmp_path: Path) -> None:
    result = json.loads((saved / "retired-export.results.json").read_text())
    result["conditions"][0]["observations"][0]["status"] = "failure"
    (saved / "retired-export.results.json").write_text(json.dumps(result))
    data = import_figure("retired-export", saved)
    inputs = next(p["value"] for p in data.spec["params"] if p["name"] == "selected_inputs")
    inputs[1]["exclusion"] = {"kind": "unsupported", "reason": "known", "evidence": "source"}
    inputs[1]["selected_row_indices"] = []
    reuse_figure(data, tmp_path / "unused.jsonl", True, {}, Console(file=io.StringIO()))
    with pytest.raises(ValueError, match="failed observations"):
        figures.render_figure_data([data], tmp_path / "out", Console(file=io.StringIO()), images=False)
    parameters = {p["name"]: p["value"] for p in data.spec["params"]}
    exported = figure_results(data.name, inputs, data.grouped, parameters["rounds"], parameters["t_critical"])
    assert not list((tmp_path / "out").iterdir())
    assert exported["conditions"][0]["failed_n"] == 1
    assert exported["conditions"][1]["exclusion"]["reason"] == "known"
    assert exported["conditions"][1]["sample_n"] == 0


def test_empty_cohort_and_imported_ast_unsupported_snapshot_need_no_compiler(
    saved: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    result = json.loads((saved / "retired-export.results.json").read_text())
    spec = json.loads((saved / "retired-export.bound.vl.json").read_text())
    result["figure"] = "slotted-runtime"
    (saved / "slotted-runtime.results.json").write_text(json.dumps(result))
    (saved / "slotted-runtime.bound.vl.json").write_text(json.dumps(spec))
    ast = {
        "source_checkout": "/absent/source",
        "source_revision": "ast-compiler-revision",
        "compiler_binary_sha256": "sha256:ast-compiler",
        "compiler_binary": "/absent/compiler",
        "rows": [
            {
                "benchmark": "batax_1st-44rules",
                "file": "original.egg",
                "reference_file": "original.ref",
                "source_ast_nodes": 4,
                "slotted_ast_nodes": 8,
                "proof_congruence_ast_nodes": None,
                "proof_congruence_error": "uses subst, which has no proof translation",
            }
        ],
    }
    (saved / "slotted-runtime.ast.json").write_text(json.dumps(ast))
    monkeypatch.setattr(slotted_ast, "slotted_ast_records", lambda *_a, **_k: pytest.fail("snapshot recompiled AST"))
    data = import_figure("slotted-runtime", saved)
    figures.render_figure_data([data], tmp_path / "out", Console(file=io.StringIO()), images=False)
    exported = json.loads((tmp_path / "out/slotted-runtime.ast.json").read_text())
    assert exported["source_revision"] == "ast-compiler-revision"
    assert exported["rows"][0]["proof_congruence_ast_nodes"] is None
    assert "Unsupported" in (tmp_path / "out/slotted-runtime.ast.tex").read_text()
    result.update(figure="corpus-empty", conditions=[])
    next(p for p in spec["params"] if p["name"] == "selected_inputs")["value"] = []
    (saved / "corpus-empty.results.json").write_text(json.dumps(result))
    (saved / "corpus-empty.bound.vl.json").write_text(json.dumps(spec))
    empty = import_figure("corpus-empty", saved)
    reuse_figure(empty, tmp_path / "absent-cache.jsonl", True, {}, Console(file=io.StringIO()))
    figures.render_figure_data([empty], tmp_path / "out", Console(file=io.StringIO()), images=False)
    exported = json.loads((tmp_path / "out/corpus-empty.results.json").read_text())
    assert exported["coverage"]["runtime"]["cohort_n"] == 0


def test_different_recorded_versions_remain_per_figure(saved: Path) -> None:
    original = import_figure("retired-export", saved)
    result = json.loads((saved / "retired-export.results.json").read_text())
    result["figure"] = "other-version"
    result["provenance"]["target"]["git_sha"] = "other-measured-revision"
    for condition in result["conditions"]:
        for row in condition["observations"]:
            row["target_git_sha"] = "other-measured-revision"
    (saved / "other-version.results.json").write_text(json.dumps(result))
    (saved / "other-version.bound.vl.json").write_bytes((saved / "retired-export.bound.vl.json").read_bytes())
    other = import_figure("other-version", saved)
    assert original.provenance["target"]["git_sha"] == "measured"
    assert other.provenance["target"]["git_sha"] == "other-measured-revision"
    assert len(original.grouped.records) == len(other.grouped.records) == 4
    assert all(row["target_git_sha"] == "other-measured-revision" for row in other.grouped.records)


def test_explicit_target_uses_new_identity_path_and_reuses_matching_imports(
    saved: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from dataclasses import replace

    from .report_fixtures import make_target

    source = tmp_path / "current.egg"
    source.write_text("(check (= 1 1))")
    sha = targets.sha256_file(source)
    result_path = saved / "retired-export.results.json"
    result = json.loads(result_path.read_text())
    bound_path = saved / "retired-export.bound.vl.json"
    spec = json.loads(bound_path.read_text())
    for condition in result["conditions"]:
        condition.update(logical_id=sha, file_sha256=sha)
        for row in condition["observations"]:
            row["file_sha256"] = sha
    for item in next(p["value"] for p in spec["params"] if p["name"] == "selected_inputs"):
        item.update(logical_id=sha, file_sha256=sha)
    result_path.write_text(json.dumps(result))
    bound_path.write_text(json.dumps(spec))
    authored = tmp_path / "style.json"
    authored.write_text(json.dumps(spec))
    config = tmp_path / "catalog.json"
    config.write_text(
        json.dumps(
            {
                "rounds": 2,
                "timeout_sec": 17,
                "figures": {
                    "retired-export": {"spec": "style.json", "files": ["current.egg"], "treatments": ["off", "term"]}
                },
            }
        )
    )
    resolutions = []

    def resolve(requests: Any, *_args: Any) -> Any:
        resolutions.append(requests)
        request = requests[0].endpoint.target
        return {request: replace(make_target(target_label="current"), request=request)}

    monkeypatch.setattr(collection, "resolve_requests", resolve)
    plans = []

    def collect(_store: Any, prepared: Any, *_args: Any, **_kwargs: Any) -> Any:
        plans.extend(prepared)
        return _store.grouped_report()

    monkeypatch.setattr(collection, "collect", collect)
    monkeypatch.setattr(figures, "render_figures", lambda *_args: ())
    assert (
        figures.main(
            [
                "--reuse-from",
                str(saved),
                "--target",
                "current=.",
                "--config",
                str(config),
                "--report",
                str(tmp_path / "local.jsonl"),
            ]
        )
        == 0
    )
    assert len(resolutions) == 1
    assert sum(plan.total_missing_observations for plan in plans) == 0


def test_missing_fill_preserves_pinned_valid_observations(saved: Path, tmp_path: Path) -> None:
    path = saved / "retired-export.results.json"
    result = json.loads(path.read_text())
    result["conditions"][0]["observations"] = result["conditions"][0]["observations"][:1]
    path.write_text(json.dumps(result))
    path = saved / "retired-export.bound.vl.json"
    spec = json.loads(path.read_text())
    next(p["value"] for p in spec["params"] if p["name"] == "selected_inputs")[0]["selected_row_indices"] = [0]
    path.write_text(json.dumps(spec))
    data = import_figure("retired-export", saved)
    cache = tmp_path / "local.jsonl"
    store = ReportStore(cache)
    for index in range(3):
        store.append(
            make_record(
                index,
                started_at=f"2026-01-02T00:00:0{index}Z",
                treatment="off",
                target_label="historical",
                max_rss_bytes=1048576,
                wall_sec=100.0 + index,
                timeout_sec=17,
            )
        )
    reuse_figure(data, cache, True, {}, Console(file=io.StringIO()))
    inputs = next(p["value"] for p in data.spec["params"] if p["name"] == "selected_inputs")
    rows = {row["row_index"]: row for group in data.grouped.data["groups"] for row in group["samples"]}
    assert [rows[index]["wall_sec"] for index in inputs[0]["selected_row_indices"]] == [1.0, 102.0]


@pytest.mark.parametrize("version", [None, 1, 4])
def test_incompatible_export_version_is_rejected_before_reading_bindings(saved: Path, version: int | None) -> None:
    path = saved / "retired-export.results.json"
    result = json.loads(path.read_text())
    if version is None:
        result.pop("figure_data_version")
    else:
        result["figure_data_version"] = version
    path.write_text(json.dumps(result))
    (saved / "retired-export.bound.vl.json").unlink()
    with pytest.raises(ValueError, match="unsupported figure data.*regenerate exports"):
        import_figure("retired-export", saved)


def test_portable_replay_outside_git_records_unknown_renderer(
    saved: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(figures, "ROOT", tmp_path)
    monkeypatch.setattr(figures, "renderer_metadata", renderer_metadata)
    run = subprocess.run
    git_failures = []

    def render(command: list[str], **kwargs: Any) -> Any:
        if command[0] == "git":
            try:
                return run(command, **kwargs)
            except subprocess.CalledProcessError as error:
                git_failures.append(error)
                raise
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")
        return None

    monkeypatch.setattr(figures.subprocess, "run", render)
    output = tmp_path / "outside-git"
    assert figures.main(["--reuse-from", str(saved), "--no-runs", "--output-dir", str(output)]) == 0
    assert git_failures
    result = json.loads((output / "retired-export.results.json").read_text(encoding="utf-8"))
    assert result["renderer"] == {"git_sha": None, "is_dirty": None}


@pytest.mark.parametrize("issue", ["failed", "excluded", "validation", "missing", "runtime", "memory"])
@pytest.mark.parametrize("images", [False, True])
def test_replay_publication_rejects_invalid_late_figure_atomically(
    saved: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, issue: str, images: bool
) -> None:
    valid = import_figure("retired-export", saved)
    invalid = deepcopy(valid)
    invalid.name = "invalid"
    item = next(p["value"] for p in invalid.spec["params"] if p["name"] == "selected_inputs")[0]
    row = invalid.grouped.data["groups"][0]["samples"][0]
    if issue == "failed":
        row["status"] = "failure"
    elif issue == "excluded":
        item["exclusion"] = {"kind": "unsupported", "reason": "known", "evidence": "source"}
    elif issue == "validation":
        item["validation_issue"] = "strict check failed"
    elif issue == "missing":
        item["selected_row_indices"].pop()
    else:
        row["wall_sec" if issue == "runtime" else "max_rss_bytes"] = None
    destination = tmp_path / "existing"
    destination.mkdir()
    for name in (valid.name, invalid.name):
        for suffix in ("pdf", "svg", "png", "results.json", "bound.vl.json", "numbers.tex", "table.tex"):
            (destination / f"{name}.{suffix}").write_bytes(b"previous bundle")
    before = {path.name: path.read_bytes() for path in destination.iterdir()}

    monkeypatch.setattr(
        figures.subprocess, "run", lambda *_args, **_kwargs: pytest.fail("invalid bundle started image rendering")
    )
    with pytest.raises(ValueError, match="invalid:.*no figure outputs replaced"):
        figures.render_figure_data([valid, invalid], destination, Console(file=io.StringIO()), images=images)
    assert {path.name: path.read_bytes() for path in destination.iterdir()} == before
    # Rejected outcomes remain inspectable without publishing figures or tables.
    parameters = {p["name"]: p["value"] for p in invalid.spec["params"]}
    result = figure_results(
        invalid.name, parameters["selected_inputs"], invalid.grouped, parameters["rounds"], parameters["t_critical"]
    )
    condition = result["conditions"][0]
    if issue == "failed":
        assert condition["failed_n"] == 1
    elif issue == "excluded":
        assert condition["exclusion"]["reason"] == "known"
    elif issue == "validation":
        assert condition["validation_issue"] == "strict check failed"
    elif issue == "missing":
        assert condition["sample_n"] == 1
    else:
        assert condition["metrics"][issue]["valid_n"] == 1


@pytest.mark.parametrize("compressed", [False, True])
def test_portable_unicode_roundtrip_with_non_utf8_defaults(
    saved: Path, tmp_path: Path, compressed: bool, non_utf8_text_defaults: None
) -> None:
    data = import_figure("retired-export", saved)
    name = data.name = "Σ-export"
    data.spec["title"] = "Σ workload"
    next(p["value"] for p in data.spec["params"] if p["name"] == "selected_inputs")[0]["label"] = "Σ workload"
    source = tmp_path / "unicode"
    figures.render_figure_data([data], source, Console(file=io.StringIO()), images=False)
    if compressed:
        for suffix in ("results.json", "bound.vl.json"):
            path = source / f"{name}.{suffix}"
            Path(str(path) + ".gz").write_bytes(gzip.compress(path.read_bytes()))
            path.unlink()
    imported = import_figure(name, source)
    style = tmp_path / "style.json"
    style.write_text(
        json.dumps({"title": "Σ restyled", "data": {"url": "unused"}}, ensure_ascii=False), encoding="utf-8"
    )
    config = tmp_path / "catalog.json"
    config.write_text(
        json.dumps(
            {"rounds": 2, "figures": {"Σ": {"spec": "style.json", "files": ["absent"], "treatments": ["off"]}}},
            ensure_ascii=False,
        ),
        encoding="utf-8",
    )
    (styled,) = figures.load_config(config).figures
    from benchmarking.figure_reuse import restyle_figure

    restyle_figure(imported, styled.spec)
    destination = tmp_path / "unicode-again"
    figures.render_figure_data([imported], destination, Console(file=io.StringIO()), images=False)
    for suffix in ("results.json", "bound.vl.json", "numbers.tex", "table.tex"):
        text = (destination / f"{name}.{suffix}").read_bytes().decode("utf-8")
        assert "Σ" in text


def test_portable_replay_rejects_silent_worker_count_overrides(saved: Path, capsys: pytest.CaptureFixture[str]) -> None:
    assert figures.main(["--reuse-from", str(saved), "--no-runs", "--threads", "4"]) == 2
    assert "retains recorded worker counts" in capsys.readouterr().err
