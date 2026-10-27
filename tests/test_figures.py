"""Exercise the public flat figure catalog and inspectable render bindings."""

from __future__ import annotations

import io
import json
from pathlib import Path
from typing import Any

import pytest
from rich.console import Console

import bench
from benchmarking import figures
from benchmarking.models import FileSpec
from benchmarking.reports.grouped import grouped_report_path, write_grouped_report
from benchmarking.reports.store import ReportStore

from .report_fixtures import make_record, make_target, write_report


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


def test_bound_copy_receipt_and_incremental_rendering(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    path = catalog_fixture(tmp_path)
    config = figures.load_config(path)
    file = FileSpec("example.egg", tmp_path / "example.egg", "sha256:file")
    resolved = [figures.ResolvedFigure(f, (file,)) for f in config.figures]
    report = tmp_path / "cache.jsonl"
    write_report(
        report, *[make_record(i, started_at=f"2026-10-01T00:00:0{i}Z", target_label="figures") for i in range(3)]
    )
    grouped = ReportStore(report).grouped_report()
    write_grouped_report(grouped, grouped_report_path(report))
    target = make_target(target_label="figures")
    calls = []
    fail_png = False

    def render(command: list[str], **_kwargs: Any) -> None:
        calls.append(command)
        generated = Path(command[command.index("--base") - 1])
        generated.write_bytes(b"" if fail_png and generated.suffix == ".png" else b"rendered")
        if fail_png and generated.suffix == ".png":
            raise figures.subprocess.CalledProcessError(1, command)

    monkeypatch.setattr(figures.subprocess, "run", render)
    stream = io.StringIO()
    console = Console(file=stream, width=20)
    original = (tmp_path / "chart.vl.json").read_bytes()
    outputs = figures.render_figures(resolved, config, grouped, report, target, tmp_path / "out", [], console)
    assert len(outputs) == 6 and len(calls) == 6
    assert all(str(output) in stream.getvalue().splitlines() for output in outputs)
    receipt = json.loads((tmp_path / "out/runtime.receipt.json").read_bytes())
    other = json.loads((tmp_path / "out/memory.receipt.json").read_bytes())
    assert receipt["selection_sha256"] == other["selection_sha256"]
    assert [row["row_index"] for row in receipt["selected_observations"][0]["rows"]] == [1, 2]
    bound = json.loads((tmp_path / "out/runtime.bound.vl.json").read_bytes())
    params = {p["name"]: p["value"] for p in bound["params"]}
    assert params["target_label"] == "figures"
    assert params["selected_inputs"][0]["file_sha256"] == "sha256:file"
    assert "binary_sha256" not in params["selected_inputs"][0]
    assert bound["data"]["url"] == grouped_report_path(report).as_uri()
    assert (tmp_path / "chart.vl.json").read_bytes() == original
    assert all(
        command[-2:] == ["--base", str(tmp_path)] or command[-4:-2] == ["--base", str(tmp_path)] for command in calls
    )
    figures.render_figures(resolved, config, grouped, report, target, tmp_path / "out", [], console)
    assert len(calls) == 6

    # Corrupt output cannot become a successful cache hit. A failing retry
    # preserves the prior complete image members and provenance receipt.
    receipt_path = tmp_path / "out/runtime.receipt.json"
    previous_receipt = receipt_path.read_bytes()
    outputs[2].write_bytes(b"corrupt")
    fail_png = True
    with pytest.raises(figures.subprocess.CalledProcessError):
        figures.render_figures(resolved, config, grouped, report, target, tmp_path / "out", [], console)
    assert receipt_path.read_bytes() == previous_receipt
    assert outputs[0].read_bytes() == b"rendered"
    fail_png = False
    figures.render_figures(resolved, config, grouped, report, target, tmp_path / "out", [], console)
    assert outputs[2].read_bytes() == b"rendered"
    assert len(calls) == 12


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
