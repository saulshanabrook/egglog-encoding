"""Exercise the public flat figure catalog and inspectable render bindings."""

from __future__ import annotations

import io
import json
from dataclasses import replace
from pathlib import Path
from typing import Any

import pytest
from rich.console import Console

import bench
from benchmarking import figures
from benchmarking.models import EngineBinary, FileSpec
from benchmarking.reports.grouped import grouped_report_path, write_grouped_report
from benchmarking.reports.store import ReportStore

from .report_fixtures import make_record, make_target, make_timing_summary, write_report


def catalog_fixture(directory: Path, **settings: Any) -> Path:
    spec = directory / "chart.vl.json"
    spec.write_text(
        json.dumps(
            {
                "data": {"url": "old-grouped.json"},
                "params": [
                    {"name": name, "value": None}
                    for name in ("selected_inputs", "target_label", "rounds", "t_critical")
                ],
            }
        )
    )
    path = directory / "catalog.json"
    path.write_text(
        json.dumps(
            {
                "rounds": 2,
                "timeout_sec": 120,
                "figures": {
                    "runtime": {"spec": "chart.vl.json", "files": ["*.egg"], "treatments": ["off"]},
                    "memory": {"spec": "chart.vl.json", "files": ["*.egg"], "treatments": ["off"]},
                },
                **settings,
            }
        )
    )
    return path


def test_public_dispatch_is_lazy(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(figures, "main", lambda argv: 7 if argv == ("--help",) else 9)
    assert bench.main(("figures", "--help")) == 7


def test_config_help_does_not_expand_files(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    path = catalog_fixture(tmp_path)
    with pytest.raises(SystemExit) as error:
        figures.parse_args(["--config", str(path), "--help"])
    assert error.value.code == 0
    text = capsys.readouterr().out
    assert "runtime:" in text and "memory:" in text
    assert "--cached" not in text


@pytest.mark.parametrize("rounds", ["0", "-1", "no"])
def test_invalid_round_override(tmp_path: Path, rounds: str) -> None:
    with pytest.raises(SystemExit):
        figures.parse_args(["--config", str(catalog_fixture(tmp_path)), "--rounds", rounds])


@pytest.mark.parametrize("rounds", [1, 3])
def test_round_override_collects_shared_runs_and_binds_effective_samples(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, rounds: int
) -> None:
    from benchmarking import collection, processes

    path = catalog_fixture(tmp_path)
    (tmp_path / "one.egg").write_text("(check (= 1 1))")
    report = tmp_path / "report.jsonl"
    target = make_target(target_label="figures", binary_path=tmp_path / "engine")
    launched: list[Any] = []
    resolved_rounds: list[int] = []
    bound_specs: list[dict[str, Any]] = []

    def resolve(requests: Any, _store: Any, rounds: int, *_args: Any) -> Any:
        resolved_rounds.append(rounds)
        return {request.endpoint.target: target for request in requests}

    def observe(*args: Any) -> Any:
        launched.append(args)
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=1), None), make_timing_summary()
        )

    def render(command: list[str], **_kwargs: Any) -> None:
        bound_specs.append(json.loads(Path(command[command.index("--base") - 2]).read_bytes()))
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(collection, "resolve_requests", resolve)
    monkeypatch.setattr(collection, "preflight_collection", lambda *_args: None)
    monkeypatch.setattr(collection, "run_process", observe)
    monkeypatch.setattr(figures.subprocess, "run", render)
    args = ["--config", str(path), "--report", str(report), "--rounds", str(rounds)]
    assert figures.main(args) == 0
    assert len(launched) == rounds  # Both figure views share one collection request.
    assert figures.load_config(path).rounds == 2
    assert figures.load_config(figures.DEFAULT_CONFIG).rounds == 10
    for bound in bound_specs:
        params = {p["name"]: p["value"] for p in bound["params"]}
        assert params["rounds"] == rounds
        assert params["t_critical"] == (None if rounds == 1 else pytest.approx(4.302652729696142))
        assert params["selected_inputs"][0]["selected_row_indices"] == list(range(rounds))
    assert figures.main(args) == 0
    assert len(launched) == rounds
    assert len(bound_specs) == 12  # Every image is rendered again; observations are reused.
    assert resolved_rounds == [rounds, rounds]


@pytest.mark.parametrize("settings", [{"rounds": 0}, {"rounds": True}, {"timeout_sec": -1}, {"experiments": {}}])
def test_invalid_global_settings(tmp_path: Path, settings: dict[str, Any]) -> None:
    with pytest.raises(ValueError):
        figures.load_config(catalog_fixture(tmp_path, **settings))


def test_duplicate_keys_and_treatments_are_rejected(tmp_path: Path) -> None:
    path = tmp_path / "bad.json"
    path.write_text('{"rounds":1,"rounds":2}')
    with pytest.raises(ValueError, match="duplicate"):
        figures.load_config(path)
    path = catalog_fixture(tmp_path)
    data = json.loads(path.read_text())
    data["figures"]["runtime"]["treatments"] = ["off", "off"]
    path.write_text(json.dumps(data))
    with pytest.raises(ValueError, match="duplicate treatment"):
        figures.load_config(path)


def test_names_require_config_option_and_no_new_cache_flag(tmp_path: Path) -> None:
    path = catalog_fixture(tmp_path)
    for args in ([str(path)], ["runtime", "runtime"], ["--cached"]):
        with pytest.raises(SystemExit):
            figures.parse_args(["--config", str(path), *args])


def test_globs_are_relative_sorted_and_overlaps_do_not_duplicate(tmp_path: Path) -> None:
    path = catalog_fixture(tmp_path)
    (tmp_path / "z.egg").write_text("(check (= 1 1))")
    (tmp_path / "a.egg").write_text("(check (= 2 2))")
    data = json.loads(path.read_text())
    data["figures"]["runtime"]["files"] = ["*.egg", "a.egg"]
    path.write_text(json.dumps(data))
    result = figures.resolve_figures(figures.load_config(path), ["runtime"], tmp_path.parent)
    assert [f.absolute_path.name for f in result[0].files] == ["a.egg", "z.egg"]
    assert all(f.display_path.startswith(tmp_path.name + "/") for f in result[0].files)
    (tmp_path / "copy.egg").write_bytes((tmp_path / "a.egg").read_bytes())
    with pytest.raises(ValueError, match="identical"):
        figures.resolve_figures(figures.load_config(path), ["runtime"], tmp_path)


def test_unmatched_files_and_unknown_treatments_fail_before_build(tmp_path: Path) -> None:
    path = catalog_fixture(tmp_path)
    with pytest.raises(ValueError, match="matched nothing"):
        figures.resolve_figures(figures.load_config(path), ["runtime"], tmp_path)
    data = json.loads(path.read_text())
    data["figures"]["runtime"]["treatments"] = ["not-a-treatment"]
    path.write_text(json.dumps(data))
    with pytest.raises(ValueError, match="unknown treatment"):
        figures.load_config(path)


def test_shared_specs_and_inputs_are_read_once(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    from benchmarking import workloads

    config = figures.load_config(catalog_fixture(tmp_path))
    (tmp_path / "one.egg").write_text("(check (= 1 1))")
    reads: list[Path] = []
    hashes: list[Path] = []
    validations: list[Path] = []
    read_bytes = Path.read_bytes
    sha256_file = workloads.sha256_file
    contains_prove = workloads.file_contains_executable_prove_command

    def read(path: Path) -> bytes:
        reads.append(path)
        return read_bytes(path)

    def hash_file(path: Path) -> str:
        hashes.append(path)
        return sha256_file(path)

    def validate(path: Path) -> bool:
        validations.append(path)
        return contains_prove(path)

    monkeypatch.setattr(Path, "read_bytes", read)
    monkeypatch.setattr(workloads, "sha256_file", hash_file)
    monkeypatch.setattr(workloads, "file_contains_executable_prove_command", validate)
    resolved = figures.resolve_figures(config, [], tmp_path)
    assert reads == [tmp_path / "chart.vl.json"]
    assert hashes == validations == [tmp_path / "one.egg"]
    assert resolved[0].files[0] is resolved[1].files[0]


@pytest.mark.parametrize("raise_error", [False, True])
def test_temporary_bindings_render_every_time_and_preserve_images_on_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, raise_error: bool
) -> None:
    path = catalog_fixture(tmp_path)
    config = figures.load_config(path)
    file = FileSpec("example.egg", tmp_path / "example.egg", "sha256:file")
    resolved = [figures.ResolvedFigure(f, (file,), json.loads(f.spec.read_bytes())) for f in config.figures]
    report = tmp_path / "cache.jsonl"
    write_report(
        report, *[make_record(i, started_at=f"2026-10-01T00:00:0{i}Z", target_label="figures") for i in range(3)]
    )
    grouped = ReportStore(report).grouped_report()
    write_grouped_report(grouped, grouped_report_path(report))
    target = make_target(target_label="figures")
    calls = []
    bindings = []
    fail_png = False

    def render(command: list[str], **_kwargs: Any) -> None:
        calls.append(command)
        bound = Path(command[command.index("--base") - 2])
        bindings.append(json.loads(bound.read_bytes()))
        generated = Path(command[command.index("--base") - 1])
        generated.write_bytes(b"" if fail_png and generated.suffix == ".png" else b"rendered")
        if fail_png and generated.suffix == ".png" and raise_error:
            raise figures.subprocess.CalledProcessError(1, command)

    monkeypatch.setattr(figures.subprocess, "run", render)
    stream = io.StringIO()
    console = Console(file=stream, width=20)
    original = (tmp_path / "chart.vl.json").read_bytes()
    inventory: figures.FigureInventory = {"workloads": [], "unavailable_cases": []}
    outputs = figures.render_figures(resolved, config, grouped, report, target, tmp_path / "out", console, inventory)
    assert len(outputs) == 6 and len(calls) == 6
    assert all(str(output) in stream.getvalue().splitlines() for output in outputs)
    assert bindings[0] == bindings[3]
    params = {p["name"]: p["value"] for p in bindings[0]["params"]}
    assert params["target_label"] == "figures"
    assert params["selected_inputs"][0]["file_sha256"] == "sha256:file"
    assert params["selected_inputs"][0]["selected_row_indices"] == [1, 2]
    assert bindings[0]["data"]["url"] == grouped_report_path(report).as_uri()
    assert (tmp_path / "chart.vl.json").read_bytes() == original
    assert set((tmp_path / "out").iterdir()) == set(outputs)
    assert all(
        command[-2:] == ["--base", str(tmp_path)] or command[-4:-2] == ["--base", str(tmp_path)] for command in calls
    )
    figures.render_figures(resolved, config, grouped, report, target, tmp_path / "out", console, inventory)
    assert len(calls) == 12

    # A failing renderer preserves every previous image, including a corrupt
    # member. A later successful invocation replaces the complete set.
    outputs[2].write_bytes(b"corrupt")
    fail_png = True
    with pytest.raises(figures.subprocess.CalledProcessError if raise_error else ValueError):
        figures.render_figures(resolved, config, grouped, report, target, tmp_path / "out", console, inventory)
    assert outputs[0].read_bytes() == b"rendered"
    assert outputs[2].read_bytes() == b"corrupt"
    assert set((tmp_path / "out").iterdir()) == set(outputs)
    fail_png = False
    figures.render_figures(resolved, config, grouped, report, target, tmp_path / "out", console, inventory)
    assert outputs[2].read_bytes() == b"rendered"
    assert len(calls) == 21


def test_bindings_select_exact_binaries_physical_inputs_and_resource_bounds(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    config = figures.load_config(catalog_fixture(tmp_path))
    figure = replace(config.figures[0], treatments=("off", "egg-de", "term"))
    native = FileSpec("example.in", tmp_path / "example.in", "native")
    logical = FileSpec("example.egg", tmp_path / "example.egg", "logical", engine_inputs=(("egg-de", native),))
    target = replace(make_target(target_label="figures"), engine_binaries=(EngineBinary("egg-de", "native-bin", None),))
    report = tmp_path / "report.jsonl"
    records = [make_record(i, started_at=f"2026-10-01T00:00:0{i}Z", file_sha256="logical") for i in range(2)] + [
        make_record(
            i,
            started_at=f"2026-10-01T00:00:0{i}Z",
            file_sha256="native",
            treatment="egg-de",
            binary_sha256="native-bin",
        )
        for i in range(2, 4)
    ]
    records += [
        make_record(4, started_at="2026-10-01T00:00:04Z", file_sha256="logical", binary_sha256="old"),
        make_record(5, started_at="2026-10-01T00:00:05Z", file_sha256="logical", timeout_sec=121, wall_sec=122),
        make_record(
            6, started_at="2026-10-01T00:00:06Z", file_sha256="logical", treatment="egg-de", binary_sha256="native-bin"
        ),
    ]
    write_report(report, *records)
    grouped = ReportStore(report).grouped_report()
    bound = []

    def render(command: list[str], **_kwargs: Any) -> None:
        bound.append(json.loads(Path(command[command.index("--base") - 2]).read_bytes()))
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(figures.subprocess, "run", render)
    stream = io.StringIO()
    figures.render_figures(
        [figures.ResolvedFigure(figure, (logical,), json.loads(figure.spec.read_bytes()))],
        config,
        grouped,
        report,
        target,
        tmp_path / "out",
        Console(file=stream),
        {"workloads": [], "unavailable_cases": []},
    )
    inputs = next(p["value"] for p in bound[0]["params"] if p["name"] == "selected_inputs")
    assert [item["file_sha256"] for item in inputs] == ["logical", "native", "logical"]
    assert [item["selected_row_indices"] for item in inputs] == [[0, 1], [2, 3], []]
    assert "1/3 incomplete or unsuccessful conditions" in stream.getvalue()


def test_bound_ids_share_resource_selection_without_rewriting_rows(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = catalog_fixture(tmp_path)
    config = figures.load_config(path)
    file = FileSpec("example.egg", tmp_path / "example.egg", "sha256:file")
    resolved = [figures.ResolvedFigure(f, (file,), json.loads(f.spec.read_bytes())) for f in config.figures]
    report = tmp_path / "cache.jsonl"
    rows = [
        make_record(0, started_at="2026-10-01T00:00:00Z", timeout_sec=120, wall_sec=120.01),
        make_record(1, started_at="2026-10-01T00:00:01Z", timeout_sec=300, wall_sec=100),
        make_record(2, started_at="2026-10-01T00:00:02Z", timeout_sec=300, wall_sec=180),
        make_record(3, started_at="2026-10-01T00:00:03Z", timeout_sec=60, status="timed-out"),
        make_record(4, started_at="2026-10-01T00:00:04Z", status="failure"),
        make_record(5, started_at="2026-10-01T00:00:05Z", status="failure"),
    ]
    for row, cap in zip(rows[-2:], (8, 16), strict=True):
        row["error_exit_code"] = 86
        row["error_memory_limit_bytes"] = cap * 1024**3
    for row in rows:
        row["target_label"] = "figures"
    write_report(report, *rows)
    original = report.read_bytes()
    grouped = ReportStore(report).grouped_report()
    write_grouped_report(grouped, grouped_report_path(report))
    assert len(grouped.data["groups"]) == 1
    assert len(grouped.data["groups"][0]["samples"]) == 6

    bindings = []

    def render(command: list[str], **_kwargs: Any) -> None:
        bindings.append(json.loads(Path(command[command.index("--base") - 2]).read_bytes()))
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(figures.subprocess, "run", render)
    for cap, expected in ((16, [1, 5]), (32, [0, 1])):
        monkeypatch.setattr(figures, "NATIVE_LIMIT_BYTES", cap * 1024**3)
        bindings.clear()
        figures.render_figures(
            resolved,
            config,
            grouped,
            report,
            make_target(target_label="figures"),
            tmp_path,
            Console(file=io.StringIO()),
            {"workloads": [], "unavailable_cases": []},
        )
        assert len(bindings) == 6
        for bound in bindings:
            params = {p["name"]: p["value"] for p in bound["params"]}
            assert params["selected_inputs"][0]["selected_row_indices"] == expected
        assert report.read_bytes() == original


def test_render_keeps_a_label_bound_to_another_executable_missing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    config = figures.load_config(catalog_fixture(tmp_path))
    file = FileSpec("example.egg", tmp_path / "example.egg", "sha256:file")
    report = tmp_path / "cache.jsonl"
    write_report(report, make_record(0, started_at="2026-10-01T00:00:00Z", target_label="figures", binary_sha256="old"))
    bindings = []

    def render(command: list[str], **_kwargs: Any) -> None:
        bindings.append(json.loads(Path(command[command.index("--base") - 2]).read_bytes()))
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(figures.subprocess, "run", render)
    figures.render_figures(
        [figures.ResolvedFigure(config.figures[0], (file,), json.loads(config.figures[0].spec.read_bytes()))],
        config,
        ReportStore(report).grouped_report(),
        report,
        make_target(target_label="figures"),
        tmp_path,
        Console(file=io.StringIO()),
        {"workloads": [], "unavailable_cases": []},
    )
    params = {p["name"]: p["value"] for p in bindings[0]["params"]}
    assert params["selected_inputs"][0]["selected_row_indices"] == []


@pytest.fixture
def main_environment(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    from benchmarking import collection

    (tmp_path / "one.egg").write_text("(check (= 1 1))")
    config = catalog_fixture(tmp_path)
    report = tmp_path / "observations.jsonl"
    rendered: list[Any] = []
    monkeypatch.setattr(
        collection,
        "resolve_requests",
        lambda requests, *_args: {request.endpoint.target: make_target(target_label="figures") for request in requests},
    )
    monkeypatch.setattr(collection, "plan_collection", lambda *_args: ())
    monkeypatch.setattr(figures, "render_figures", lambda *args: rendered.append(args[2]))
    return {"args": ["--config", str(config), "--report", str(report)], "report": report, "rendered": rendered}


def test_main_rewrites_fresh_partial_snapshot_before_rendering(
    main_environment: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking import collection
    from benchmarking.reports.store import parse_grouped_report

    report = main_environment["report"]
    write_report(report, make_record(0, started_at="2026-10-01T00:00:00Z", binary_sha256="old", target_label="figures"))
    write_grouped_report(ReportStore(report).grouped_report(), grouped_report_path(report))

    def interrupted_write(store: ReportStore, _plans: Any, requests: Any, *_args: Any) -> Any:
        store.append(
            make_record(
                1,
                started_at="2026-10-01T00:00:01Z",
                target_label="figures",
                status="failure",
                file_sha256=requests[0].files[0].sha256,
            )
        )
        raise OSError("initial grouped write failed after partial collection")

    monkeypatch.setattr(collection, "collect", interrupted_write)
    assert figures.main(main_environment["args"]) == 2
    assert len(main_environment["rendered"]) == 1
    fresh = parse_grouped_report(grouped_report_path(report).read_bytes(), str(report))
    assert [(g["key"]["binary_sha256"], g["labels"]) for g in fresh.data["groups"]] == [
        ("old", []),
        ("sha256:bin", ["figures"]),
    ]
    assert main_environment["rendered"][0].data == fresh.data


def test_main_skips_render_when_partial_snapshot_cannot_be_refreshed(
    main_environment: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking import collection

    def fail_collection(*_args: Any) -> Any:
        raise OSError("collection snapshot failure")

    def fail_snapshot(*_args: Any) -> Any:
        raise OSError("snapshot remains unwritable")

    monkeypatch.setattr(collection, "collect", fail_collection)
    monkeypatch.setattr(figures, "write_grouped_report", fail_snapshot)
    assert figures.main(main_environment["args"]) == 2
    assert main_environment["rendered"] == []


def test_main_ctrl_c_preserves_collector_snapshot_without_rendering(
    main_environment: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking import collection

    def interrupted(store: ReportStore, _plans: Any, requests: Any, targets: Any, *_args: Any) -> Any:
        store.append(
            make_record(
                0, started_at="2026-10-01T00:00:00Z", target_label="figures", file_sha256=requests[0].files[0].sha256
            )
        )
        write_grouped_report(
            store.grouped_report(collection.current_label_bindings(requests, targets)), grouped_report_path(store.path)
        )
        raise KeyboardInterrupt

    monkeypatch.setattr(collection, "collect", interrupted)
    assert figures.main(main_environment["args"]) == 130
    assert main_environment["rendered"] == []
    assert ReportStore(main_environment["report"]).row_count == 1
    assert grouped_report_path(main_environment["report"]).is_file()


def test_main_rejects_label_only_target_before_resolution(
    main_environment: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking import collection

    monkeypatch.setattr(collection, "resolve_requests", lambda *_args: pytest.fail("label lookup must not resolve"))
    assert figures.main([*main_environment["args"], "--target", "figures="]) == 2
    assert main_environment["rendered"] == []
