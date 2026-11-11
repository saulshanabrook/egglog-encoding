"""Exercise the public flat figure catalog and inspectable render bindings."""

from __future__ import annotations

import io
import json
import subprocess
import sys
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

import pytest
from rich.console import Console

import bench
from benchmarking import figures
from benchmarking.engines import Treatment
from benchmarking.models import BuiltBinary, Exclusion, FileSpec, Status
from benchmarking.reports.grouped import grouped_report_path, write_grouped_report
from benchmarking.reports.store import ReportStore

from .report_fixtures import make_record, make_target, make_timing_summary, write_report


@pytest.fixture(autouse=True)
def renderer_version(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(figures, "renderer_metadata", lambda: {"git_sha": "renderer", "is_dirty": False})


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


def test_complete_multipattern_catalog_selects_original_sdql_pairs_without_resource_failures() -> None:
    args, config = figures.parse_args(["slotted-multipattern-runtime", "--rounds", "3"])
    assert args.names == ["slotted-multipattern-runtime"] and config.rounds == 3
    assert len(config.figures) == 7
    nested, complete = figures.resolve_figures(
        config, ["slotted-runtime", "slotted-multipattern-runtime"], figures.ROOT
    )
    assert nested.figure.treatments == ("slotted-ref-nested", "slotted-no-aliasing")
    assert nested.figure.checks == ("slotted", "slotted-ref-multi", "slotted-ref-nested-snapshot")
    assert len(nested.files) == 10
    assert complete.figure.treatments == ("slotted-ref-multi", "slotted")
    assert complete.figure.spec == nested.figure.spec and complete.spec is nested.spec
    assert complete.figure.patterns == (
        nested.figure.patterns[0],
        "!../benchmarks/slotted/inputs/sdql/batax_2nd-44rules.egg",
        "!../benchmarks/slotted/inputs/sdql/mttkrp_2nd-44rules.egg",
    )
    assert len(complete.files) == 8
    assert complete.files == tuple(
        file
        for file in nested.files
        if file.absolute_path.name not in ("batax_2nd-44rules.egg", "mttkrp_2nd-44rules.egg")
    )
    for file in complete.files:
        native = file.for_binary("slotted-reference")
        assert file.absolute_path.parent.name == "sdql"
        assert native.absolute_path == file.absolute_path.with_suffix(".ref")
        assert all(
            file.exclusion_for(cast(Treatment, treatment), memory_limit_bytes=None) is None
            for treatment in complete.figure.treatments
        )


def test_config_help_does_not_expand_files(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    path = catalog_fixture(tmp_path)
    with pytest.raises(SystemExit) as error:
        figures.parse_args(["--config", str(path), "--help"])
    assert error.value.code == 0
    text = capsys.readouterr().out
    assert "runtime:" in text and "memory:" in text
    assert "--no-runs" in text


def test_default_output_is_checkout_relative_and_explicit_override_is_preserved(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    config = catalog_fixture(tmp_path)
    elsewhere = tmp_path / "elsewhere"
    elsewhere.mkdir()
    monkeypatch.chdir(elsewhere)
    args, _ = figures.parse_args(["--config", str(config)])
    assert args.output_dir == figures.ROOT / "figures/output/eval"
    overridden, _ = figures.parse_args(["--config", str(config), "--output-dir", "relative-output"])
    assert overridden.output_dir == Path("relative-output")


def test_lmfao_catalog_selection_and_overrides(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    from benchmarking.lmfao import cli, data

    assert figures.load_config(figures.DEFAULT_CONFIG).lmfao is not None
    config = catalog_fixture(tmp_path, lmfao={"data": "data", "backend": "backend/build/multifaq"})
    checked = []
    monkeypatch.setattr(cli, "verify_backend", lambda path: checked.append(path))
    monkeypatch.setattr(data, "validate_inputs", lambda path: checked.append(path))
    monkeypatch.chdir(tmp_path)
    args, settings = figures.parse_args(
        [
            "--config",
            str(config),
            "lmfao",
            "--rounds",
            "3",
            "--timeout-sec",
            "71",
            "--memory-limit-gib",
            "2",
            "--lmfao-data",
            "alternate-data",
            "--output-dir",
            "out",
            "--lmfao-backend",
            "alternate-backend",
            "--lmfao-cxxflags=-O2 -I/boost",
            "--report",
            "cache.jsonl",
        ]
    )
    selected = figures.prepare_lmfao(args, settings)
    assert selected is not None
    assert (selected.samples, selected.timeout, selected.memory_limit_bytes) == (3, 71, 2 * 1024**3)
    assert selected.output_dir == tmp_path / "out/lmfao"
    assert selected.report == tmp_path / "cache.jsonl" and selected.cxxflags == "-O2 -I/boost"
    assert checked == [tmp_path / "alternate-backend", tmp_path / "alternate-data"]
    args.names = ["runtime"]
    assert figures.prepare_lmfao(args, settings) is None
    assert len(checked) == 2


@pytest.mark.parametrize("selection", [[], ["lmfao"]])
def test_lmfao_missing_setup_fails_before_collection(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, selection: list[str], capsys: pytest.CaptureFixture[str]
) -> None:
    from benchmarking import collection

    config = catalog_fixture(tmp_path, lmfao={"data": "missing", "backend": "missing/build/multifaq"})
    monkeypatch.setattr(collection, "resolve_requests", lambda *_: pytest.fail("must preflight before building"))
    report = tmp_path / "cache.jsonl"
    assert figures.main(["--config", str(config), "--report", str(report), *selection]) == 2
    assert not report.exists()
    assert "missing LMFAO provenance" in capsys.readouterr().err


def test_lmfao_joins_the_paper_collection_and_reuses_its_store(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    from benchmarking import collection, processes
    from benchmarking.lmfao import cli, data, optimizer
    from benchmarking.lmfao import report as lmfao_report
    from benchmarking.reports import store as report_store
    from benchmarking.workloads import resolve_files

    config = catalog_fixture(tmp_path, lmfao={"data": "data", "backend": "backend/build/multifaq"})
    (tmp_path / "one.egg").write_text("(check (= 1 1))")
    path = tmp_path / "cache.jsonl"
    loads, launched, evaluated, snapshots = [], [], [], []

    class CountStore(ReportStore):
        def __init__(self, path: Path) -> None:
            loads.append(path)
            super().__init__(path)

    def inputs(output: Path, rounds: int) -> dict[str, FileSpec]:
        output.mkdir(parents=True, exist_ok=True)
        files = {}
        for i, mode in enumerate(optimizer.MODES, 2):
            source = output / f"{mode}.egg"
            source.write_text(f"(check (= {i} {i}))")
            files[mode] = resolve_files([str(source)], figures.ROOT)[0]
        return files

    def observe(*args: Any) -> Any:
        launched.append(args)
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=1, max_rss_bytes=1048576), None),
            make_timing_summary(),
        )

    def summarize(output: Path, store: ReportStore, *args: Any) -> Any:
        snapshots.append(store)
        assert store.row_count == 6  # Two repetitions of one figure input and both LMFAO encodings.
        return optimizer.OptimizerCollection(
            {"slotted": {"treatment": "slotted"}}, {"optimizer": {"slotted": {"failures": []}}}, store, args[0]
        )

    def evaluate(args: Any, *, collected: Any) -> dict[str, Any]:
        evaluated.append(args)
        assert collected.successful == {"slotted": {"treatment": "slotted"}}
        assert (args.samples, args.timeout, args.report) == (2, 120, path)
        return {"checked": True}

    monkeypatch.setattr(report_store, "ReportStore", CountStore)
    monkeypatch.setattr(cli, "verify_backend", lambda _: None)
    monkeypatch.setattr(data, "validate_inputs", lambda _: None)
    monkeypatch.setattr(optimizer, "optimizer_inputs", inputs)
    monkeypatch.setattr(optimizer, "optimizer_report", summarize)
    monkeypatch.setattr(cli, "run", evaluate)
    monkeypatch.setattr(cli, "collect_optimizers", lambda *_: pytest.fail("must use the shared collection"))
    monkeypatch.setattr(lmfao_report, "paper_results", lambda *_: {"lmfao.table.tex": "table"})
    monkeypatch.setattr(collection, "preflight_collection", lambda *_: None)
    monkeypatch.setattr(collection, "run_process", observe)
    monkeypatch.setattr(
        collection,
        "resolve_requests",
        lambda requests, *_: {
            request.endpoint.target: make_target(target_label="figures", binary_path=tmp_path / "engine")
            for request in requests
        },
    )
    published = []
    monkeypatch.setattr(figures, "render_figures", lambda *_, **kwargs: published.append(kwargs))
    args = ["--config", str(config), "--report", str(path), "--output-dir", str(tmp_path / "out")]
    assert bench.main(["figures", *args]) == 0
    assert len(launched) == 6 and loads == [path] and len(evaluated) == 1
    assert published[0] == {"extra_outputs": {"lmfao.table.tex": "table"}}
    assert isinstance(snapshots[0], CountStore)
    # Selecting only LMFAO reuses its observations without collecting the other figures.
    assert bench.main(["figures", *args, "lmfao"]) == 0
    assert len(launched) == 6 and loads == [path, path] and len(evaluated) == 2
    assert bench.main(["figures", *args, "runtime"]) == 0
    assert len(launched) == 6 and len(evaluated) == 2
    cached = {
        "binary_sha256": {"slotted": "sha256:bin"},
        "optimizer_memory_limit_bytes": figures.DEFAULT_MEMORY_LIMIT_BYTES,
        "optimizer_timeout_seconds": 120,
        "optimizer": {
            mode: {"requested_samples": 2, "input_sha256": file.sha256}
            for mode, file in inputs(tmp_path / "out/lmfao", 192).items()
        },
    }
    (tmp_path / "out/lmfao.results.json").write_text(json.dumps(cached))
    assert bench.main(["figures", *args, "lmfao", "--no-runs"]) == 0
    assert len(launched) == 6 and len(evaluated) == 2
    assert bench.main(["figures", *args, "lmfao", "--no-runs", "--rounds", "3"]) == 2
    monkeypatch.setattr(
        optimizer,
        "optimizer_report",
        lambda *_: optimizer.OptimizerCollection(
            {"slotted": {}},
            {"optimizer": {"debruijn": {"failures": [{"status": "failure"}]}}},
            snapshots[0],
            make_target(),
        ),
    )
    assert bench.main(["figures", *args, "lmfao"]) == 2
    assert len(evaluated) == 2


def test_lmfao_table_export_replays_without_running_or_preparing_backends(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking.lmfao import cli, report

    exported = tmp_path / "exported"
    exported.mkdir()
    source = exported / "lmfao.results.json"
    source.write_text('{"measured": true}')
    monkeypatch.setattr(cli, "verify_backend", lambda *_: pytest.fail("replay prepared a backend"))
    monkeypatch.setattr(cli, "run", lambda *_args, **_kw: pytest.fail("replay collected measurements"))
    monkeypatch.setattr(report, "paper_results", lambda value: {"lmfao.table.tex": str(value["measured"])})
    args = [
        "figures",
        "lmfao",
        "--reuse-from",
        str(exported),
        "--no-runs",
        "--output-dir",
        str(tmp_path / "out"),
        "--report",
        str(tmp_path / "cache.jsonl"),
    ]
    assert bench.main(args) == 0
    assert (tmp_path / "out/lmfao.table.tex").read_text() == "True"
    assert not (tmp_path / "cache.jsonl").exists()
    assert source.read_text() == '{"measured": true}'
    assert bench.main([*args, "--rounds", "3"]) == 2


def test_importing_figures_does_not_import_scipy() -> None:
    result = subprocess.run(
        [sys.executable, "-c", "import sys; import benchmarking.figures; assert 'scipy' not in sys.modules"],
        cwd=figures.ROOT,
        capture_output=True,
        text=True,
        timeout=15,
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout == result.stderr == ""


@pytest.mark.parametrize("args, code", [(["--help"], 0), (["--rounds", "0"], 2)])
def test_help_and_argument_errors_have_no_phase_status(
    args: list[str], code: int, capsys: pytest.CaptureFixture[str]
) -> None:
    with pytest.raises(SystemExit) as error:
        figures.main(args)
    assert error.value.code == code
    captured = capsys.readouterr()
    assert not any(label in captured.out + captured.err for label in ("Resolving inputs", "Loading cache", "Rendering"))
    if code == 0:
        assert captured.err == ""
    else:
        assert captured.out == ""


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
            processes.TimingResult("success", processes.TimingRow(wall_sec=1, max_rss_bytes=1048576), None),
            make_timing_summary(),
        )

    def render(command: list[str], **_kwargs: Any) -> None:
        bound_specs.append(json.loads(Path(command[command.index("--base") - 2]).read_bytes()))
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(collection, "resolve_requests", resolve)
    monkeypatch.setattr(collection, "preflight_collection", lambda *_args: None)
    monkeypatch.setattr(collection, "run_process", observe)
    monkeypatch.setattr(figures.subprocess, "run", render)
    output_dir = tmp_path / "output/eval"
    monkeypatch.setattr(figures, "DEFAULT_OUTPUT_DIR", output_dir)
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
    assert len(list(output_dir.iterdir())) == 14
    assert not list(tmp_path.glob("*.pdf"))
    for name in ("runtime", "memory"):
        for suffix in ("pdf", "svg", "png", "bound.vl.json", "results.json", "numbers.tex", "table.tex"):
            assert (output_dir / f"{name}.{suffix}").is_file()


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


def test_names_require_config_option(tmp_path: Path) -> None:
    path = catalog_fixture(tmp_path)
    for args in ([str(path)], ["runtime", "runtime"]):
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


@pytest.mark.parametrize(
    "patterns, expected",
    [
        (["*.egg", "!b.egg"], ["a.egg", "z.egg"]),
        (["!b.egg", "*.egg"], ["a.egg", "b.egg", "z.egg"]),
        (["*.egg", "!b.egg", "b.egg"], ["a.egg", "z.egg", "b.egg"]),
        (["*.egg", "!*.egg", "z.egg"], ["z.egg"]),
    ],
)
def test_negative_globs_remove_current_matches_and_allow_ordered_readdition(
    tmp_path: Path, patterns: list[str], expected: list[str]
) -> None:
    path = catalog_fixture(tmp_path)
    for number, name in enumerate(("z.egg", "a.egg", "b.egg")):
        (tmp_path / name).write_text(f"(check (= {number} {number}))")
    data = json.loads(path.read_text())
    data["figures"]["runtime"]["files"] = patterns
    path.write_text(json.dumps(data))
    (resolved,) = figures.resolve_figures(figures.load_config(path), ["runtime"], tmp_path.parent)
    assert [file.absolute_path.name for file in resolved.files] == expected
    assert all(file.display_path.startswith(tmp_path.name + "/") for file in resolved.files)


def test_negative_globs_skip_validation_of_removed_inputs_until_readded(tmp_path: Path) -> None:
    path = catalog_fixture(tmp_path)
    (tmp_path / "valid.egg").write_text("(check (= 1 1))")
    (tmp_path / "invalid.egg").write_text('(include "missing.egg")')
    data = json.loads(path.read_text())
    patterns = ["*.egg", "!invalid.egg"]
    data["figures"]["runtime"]["files"] = patterns
    path.write_text(json.dumps(data))
    (resolved,) = figures.resolve_figures(figures.load_config(path), ["runtime"], tmp_path)
    assert [file.absolute_path.name for file in resolved.files] == ["valid.egg"]
    patterns.append("invalid.egg")
    path.write_text(json.dumps(data))
    with pytest.raises(ValueError, match="self-contained"):
        figures.resolve_figures(figures.load_config(path), ["runtime"], tmp_path)


@pytest.mark.parametrize(
    "patterns, message",
    [
        (["a.egg", "!"], "empty file pattern"),
        (["a.egg", "!missing.egg"], "matched nothing"),
        (["a.egg", "!directory"], "not a workload file"),
        (["a.egg", "!a.egg"], "selected no workloads"),
        (["!a.egg"], "selected no workloads"),
    ],
)
def test_negative_globs_reject_invalid_matches_and_empty_selections(
    tmp_path: Path, patterns: list[str], message: str
) -> None:
    path = catalog_fixture(tmp_path)
    (tmp_path / "a.egg").write_text("(check (= 1 1))")
    (tmp_path / "directory").mkdir()
    data = json.loads(path.read_text())
    data["figures"]["runtime"]["files"] = patterns
    path.write_text(json.dumps(data))
    with pytest.raises(ValueError, match=message):
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
    read_bytes = Path.read_bytes
    sha256_file = workloads.sha256_file

    def read(path: Path) -> bytes:
        reads.append(path)
        return read_bytes(path)

    def hash_file(path: Path) -> str:
        hashes.append(path)
        return sha256_file(path)

    monkeypatch.setattr(Path, "read_bytes", read)
    monkeypatch.setattr(workloads, "sha256_file", hash_file)
    resolved = figures.resolve_figures(config, [], tmp_path)
    assert reads == [tmp_path / "chart.vl.json"]
    assert hashes == [tmp_path / "one.egg"]
    assert resolved[0].files[0] is resolved[1].files[0]


@pytest.mark.parametrize("raise_error", [False, True])
@pytest.mark.parametrize("default_output", [False, True])
def test_temporary_bindings_render_every_time_and_preserve_images_on_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, raise_error: bool, default_output: bool
) -> None:
    path = catalog_fixture(tmp_path)
    config = figures.load_config(path)
    file = FileSpec("example.egg", tmp_path / "example.egg", "sha256:file")
    resolved = [figures.ResolvedFigure(f, (file,), json.loads(f.spec.read_bytes())) for f in config.figures]
    report = tmp_path / "cache.jsonl"
    write_report(
        report,
        *[
            make_record(
                i,
                memory_limit_bytes=None,
                started_at=f"2026-10-01T00:00:0{i}Z",
                target_label="figures",
                max_rss_bytes=1048576,
            )
            for i in range(3)
        ],
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
        assert f"Rendering {generated.stem}" in stream.getvalue()
        generated.write_bytes(b"" if fail_png and generated.name == "memory.png" else b"rendered")
        if fail_png and generated.name == "memory.png" and raise_error:
            raise figures.subprocess.CalledProcessError(1, command)

    monkeypatch.setattr(figures.subprocess, "run", render)
    stream = io.StringIO()
    console = Console(file=stream, width=20)
    output_dir = tmp_path / "out[red]"
    monkeypatch.setattr(figures, "DEFAULT_OUTPUT_DIR", output_dir)
    output_argument = None if default_output else output_dir
    original = (tmp_path / "chart.vl.json").read_bytes()
    inventory: figures.FigureInventory = {"workloads": [], "unavailable_cases": []}
    extra = {"lmfao.table.tex": "original table"}
    outputs = figures.render_figures(
        resolved, config, grouped, report, target, output_argument, console, inventory, extra_outputs=extra
    )
    assert len(outputs) == 15 and len(calls) == 6
    assert all(str(output) in stream.getvalue().splitlines() for output in outputs)
    assert bindings[0] == bindings[3]
    params = {p["name"]: p["value"] for p in bindings[0]["params"]}
    assert params["target_label"] == "figures"
    assert params["selected_inputs"][0]["file_sha256"] == "sha256:file"
    assert params["selected_inputs"][0]["selected_row_indices"] == [1, 2]
    assert "url" not in bindings[0]["data"]
    assert bindings[0]["data"]["values"][0]["groups"][0]["samples"][0]["row_index"] == 1
    assert json.loads((output_dir / "runtime.bound.vl.json").read_bytes()) == bindings[0]
    assert json.loads((output_dir / "memory.bound.vl.json").read_bytes()) == bindings[3]
    assert (tmp_path / "chart.vl.json").read_bytes() == original
    assert set((output_dir).iterdir()) == set(outputs)
    assert all(Path(command[command.index("--base") + 1]).parent == output_dir for command in calls)
    figures.render_figures(resolved, config, grouped, report, target, output_argument, console, inventory)
    assert len(calls) == 12

    # A failing renderer preserves every previous image, including a corrupt
    # member. A later successful invocation replaces the complete set.
    outputs[2].write_bytes(b"corrupt")
    previous_bundle = {output: output.read_bytes() for output in outputs}
    previous_binding = (output_dir / "runtime.bound.vl.json").read_bytes()
    fail_png = True
    with pytest.raises(figures.subprocess.CalledProcessError if raise_error else ValueError):
        figures.render_figures(
            resolved,
            config,
            grouped,
            report,
            target,
            output_argument,
            console,
            inventory,
            extra_outputs={"lmfao.table.tex": "new table"},
        )
    assert {output: output.read_bytes() for output in outputs} == previous_bundle
    assert outputs[0].read_bytes() == b"rendered"
    assert outputs[2].read_bytes() == b"corrupt"
    assert (output_dir / "runtime.bound.vl.json").read_bytes() == previous_binding
    assert set((output_dir).iterdir()) == set(outputs)
    fail_png = False
    figures.render_figures(
        resolved,
        config,
        grouped,
        report,
        target,
        output_argument,
        console,
        inventory,
        extra_outputs={"lmfao.table.tex": "new table"},
    )
    assert outputs[2].read_bytes() == b"rendered"
    assert (output_dir / "lmfao.table.tex").read_text() == "new table"
    assert len(calls) == 24


@pytest.mark.parametrize(
    "problem",
    ["missing", "failure", "timed-out", "memory-limited", "runtime", "memory", "resource", "unsupported", "validation"],
)
def test_incomplete_later_figure_preserves_entire_previous_bundle(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, problem: str
) -> None:
    config = replace(figures.load_config(catalog_fixture(tmp_path)), rounds=1)
    first = FileSpec("first.egg", tmp_path / "first.egg", "first")
    second = FileSpec("second.egg", tmp_path / "second.egg", "second")
    treatment: Treatment = "proofs" if problem == "validation" else "off"
    if problem in ("resource", "unsupported"):
        second = replace(
            second,
            exclusions=(
                Exclusion("resource" if problem == "resource" else "unsupported", "restricted", "issue", ("off",)),
            ),
        )
    resolved = [
        figures.ResolvedFigure(config.figures[0], (first,), json.loads(config.figures[0].spec.read_bytes())),
        figures.ResolvedFigure(
            replace(config.figures[1], treatments=(treatment,)),
            (second,),
            json.loads(config.figures[1].spec.read_bytes()),
        ),
    ]
    rows = [make_record(0, started_at="2026-10-01T00:00:00Z", file_sha256="first", max_rss_bytes=1048576)]
    if problem != "missing":
        row = make_record(1, started_at="2026-10-01T00:00:01Z", file_sha256="second", max_rss_bytes=1048576)
        row["treatment"] = treatment
        if problem in ("failure", "timed-out", "memory-limited"):
            row["status"] = cast(Status, problem)
            row["timing_summary"] = None
        elif problem == "runtime":
            row["wall_sec"] = None
        elif problem == "memory":
            row["max_rss_bytes"] = 0
        rows.append(row)
    report = tmp_path / "report.jsonl"
    write_report(report, *rows)
    destination = tmp_path / "out"
    destination.mkdir()
    previous = {}
    for figure in config.figures:
        for suffix in ("pdf", "svg", "png", "bound.vl.json", "results.json", "numbers.tex", "table.tex"):
            path = destination / f"{figure.name}.{suffix}"
            path.write_bytes(b"previous")
            previous[path] = path.read_bytes()
    calls = []

    def render(command: list[str], **_kwargs: Any) -> None:
        calls.append(command)
        Path(command[command.index("--base") - 1]).write_bytes(b"new")

    monkeypatch.setattr(figures.subprocess, "run", render)
    inventory: figures.FigureInventory = {"workloads": [], "unavailable_cases": []}
    if problem == "validation":
        inventory["workloads"] = [
            {
                "label": "second",
                "family": "eggcc",
                "file_sha256": "second",
                "validation_failures": {"sha256:bin": "Strict proof failure"},
            }
        ]
    with pytest.raises(ValueError, match="no figure outputs replaced"):
        figures.render_figures(
            resolved,
            config,
            ReportStore(report).grouped_report(),
            report,
            make_target(target_label="figures"),
            destination,
            Console(file=io.StringIO()),
            inventory,
        )
    assert not calls  # Validate all figure selections before starting rendering.
    assert set(destination.iterdir()) == set(previous)
    assert {path: path.read_bytes() for path in previous} == previous


@pytest.mark.parametrize("exclude_term", [False, True])
@pytest.mark.parametrize("requested_cap", [None, 10737418240])
def test_bindings_select_exact_binaries_physical_inputs_and_resource_bounds(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, exclude_term: bool, requested_cap: int | None
) -> None:
    config = replace(figures.load_config(catalog_fixture(tmp_path)), memory_limit_bytes=requested_cap)
    figure = replace(config.figures[0], treatments=("off", "egg-de", "term"))
    native = FileSpec("example.in", tmp_path / "example.in", "native")
    logical = FileSpec(
        "example.egg",
        tmp_path / "example.egg",
        "logical",
        binary_inputs=(("egg-de", native),),
        exclusions=(
            # This original driver is always uncapped, even in a capped figure.
            Exclusion("resource", "cap-only native limit", "probe", ("egg-de",), memory_limit_bytes=10737418240),
            *((Exclusion("resource", "recorded limit", "probe", ("term",)),) if exclude_term else ()),
        ),
    )
    target = replace(make_target(target_label="figures"), binaries=(BuiltBinary("egg-de", "native-bin", None),))
    report = tmp_path / "report.jsonl"
    records = [
        make_record(
            i,
            memory_limit_bytes=requested_cap,
            started_at=f"2026-10-01T00:00:0{i}Z",
            file_sha256="logical",
            max_rss_bytes=1048576,
        )
        for i in range(2)
    ] + [
        make_record(
            i,
            memory_limit_bytes=None,
            started_at=f"2026-10-01T00:00:0{i}Z",
            file_sha256="native",
            treatment="egg-de",
            binary_sha256="native-bin",
            max_rss_bytes=1048576,
        )
        for i in range(2, 4)
    ]
    records += [
        make_record(
            4,
            memory_limit_bytes=requested_cap,
            started_at="2026-10-01T00:00:04Z",
            file_sha256="logical",
            binary_sha256="old",
            max_rss_bytes=1048576,
        ),
        make_record(
            5,
            memory_limit_bytes=requested_cap,
            started_at="2026-10-01T00:00:05Z",
            file_sha256="logical",
            timeout_sec=121,
            wall_sec=122,
            max_rss_bytes=1048576,
        ),
        make_record(
            6,
            memory_limit_bytes=None,
            started_at="2026-10-01T00:00:06Z",
            file_sha256="logical",
            treatment="egg-de",
            binary_sha256="native-bin",
            max_rss_bytes=1048576,
        ),
    ]
    records += [
        make_record(
            i, started_at=f"2026-10-01T00:00:0{i}Z", file_sha256="logical", treatment="term", max_rss_bytes=1048576
        )
        for i in range(7, 9)
    ]
    write_report(report, *records)
    grouped = ReportStore(report).grouped_report()
    bound = []

    def render(command: list[str], **_kwargs: Any) -> None:
        bound.append(json.loads(Path(command[command.index("--base") - 2]).read_bytes()))
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(figures.subprocess, "run", render)
    stream = io.StringIO()
    if exclude_term:
        with pytest.raises(ValueError, match="excluded.*resource"):
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
        assert not bound and not list((tmp_path / "out").iterdir())
        return
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
    assert [item["selected_row_indices"] for item in inputs] == [[1, 5], [2, 3], [7, 8]]


def test_figure_timings_include_expected_failure_without_changing_shared_policy(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    config = figures.load_config(catalog_fixture(tmp_path))
    figure = replace(config.figures[0], treatments=("term",))
    file = FileSpec(
        "case.egg",
        tmp_path / "case.egg",
        "sha256:file",
        exclusions=(Exclusion("expected-failure", "known bug", "issue", ("term",)),),
    )
    native = replace(file, display_path="case.ref", absolute_path=tmp_path / "case.ref", sha256="native")
    file = replace(file, binary_inputs=(("slotted-reference", native),))
    file.absolute_path.write_text("(check true)\n")
    monkeypatch.setattr(figures, "resolve_files", lambda *_args: (file,))
    timed = figures.resolve_figures(config, [], tmp_path)[0].files[0]
    assert file.exclusion_for("term", memory_limit_bytes=None) is not None
    assert timed.exclusions == ()
    assert native.exclusions and timed.for_binary("slotted-reference").exclusions == ()
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        *[
            make_record(
                i,
                started_at=f"2026-10-01T00:00:0{i}Z",
                treatment="term",
                memory_limit_bytes=None,
                max_rss_bytes=1048576,
            )
            for i in range(2)
        ],
    )
    before = report.read_bytes()
    bindings = []

    def render(command: list[str], **_kwargs: Any) -> None:
        bindings.append(json.loads(Path(command[command.index("--base") - 2]).read_bytes()))
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(figures.subprocess, "run", render)
    figures.render_figures(
        [figures.ResolvedFigure(figure, (timed,), json.loads(figure.spec.read_bytes()))],
        config,
        ReportStore(report).grouped_report(),
        report,
        make_target(target_label="figures"),
        tmp_path / "out",
        Console(file=io.StringIO()),
        {"workloads": [], "unavailable_cases": []},
    )
    selected = next(p["value"] for p in bindings[0]["params"] if p["name"] == "selected_inputs")[0]
    assert selected["selected_row_indices"] == [0, 1]
    assert selected["exclusion"] is None
    assert report.read_bytes() == before


def test_bound_ids_share_resource_selection_without_rewriting_rows(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = catalog_fixture(tmp_path)
    config = figures.load_config(path)
    file = FileSpec("example.egg", tmp_path / "example.egg", "sha256:file")
    resolved = [figures.ResolvedFigure(f, (file,), json.loads(f.spec.read_bytes())) for f in config.figures]
    report = tmp_path / "cache.jsonl"
    rows = [
        make_record(
            0,
            memory_limit_bytes=None,
            started_at="2026-10-01T00:00:00Z",
            timeout_sec=120,
            wall_sec=120.01,
            max_rss_bytes=1048576,
        ),
        make_record(
            1,
            memory_limit_bytes=None,
            started_at="2026-10-01T00:00:01Z",
            timeout_sec=300,
            wall_sec=100,
            max_rss_bytes=1048576,
        ),
        make_record(
            2,
            memory_limit_bytes=None,
            started_at="2026-10-01T00:00:02Z",
            timeout_sec=300,
            wall_sec=180,
            max_rss_bytes=1048576,
        ),
        make_record(
            3,
            memory_limit_bytes=None,
            started_at="2026-10-01T00:00:03Z",
            timeout_sec=60,
            status="timed-out",
            max_rss_bytes=1048576,
        ),
        make_record(
            4, memory_limit_bytes=None, started_at="2026-10-01T00:00:04Z", status="failure", max_rss_bytes=1048576
        ),
        make_record(
            5, memory_limit_bytes=None, started_at="2026-10-01T00:00:05Z", status="failure", max_rss_bytes=1048576
        ),
    ]
    for row, cap in zip(rows[-2:], (8, 16), strict=True):
        row["status"] = "memory-limited"
        row["memory_limit_bytes"] = cap * 1024**3
    for row in rows:
        row["target_label"] = "figures"
    write_report(report, *rows)
    original = report.read_bytes()
    grouped = ReportStore(report).grouped_report()
    write_grouped_report(grouped, grouped_report_path(report))
    assert len(grouped.data["groups"]) == 1
    assert sum(len(g["samples"]) for g in grouped.data["groups"]) == 6

    bindings = []

    def render(command: list[str], **_kwargs: Any) -> None:
        bindings.append(json.loads(Path(command[command.index("--base") - 2]).read_bytes()))
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(figures.subprocess, "run", render)
    for requested_cap, expected in ((None, [1, 2]), (16 * 1024**3, [2, 5]), (32 * 1024**3, [1, 2])):
        config = figures.replace(config, memory_limit_bytes=requested_cap)
        bindings.clear()
        if requested_cap == 16 * 1024**3:
            with pytest.raises(ValueError, match="failed observations"):
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
            assert not bindings and report.read_bytes() == original
            continue
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
    write_report(
        report,
        make_record(
            0,
            memory_limit_bytes=None,
            started_at="2026-10-01T00:00:00Z",
            target_label="figures",
            binary_sha256="old",
            max_rss_bytes=1048576,
        ),
    )
    bindings = []

    def render(command: list[str], **_kwargs: Any) -> None:
        bindings.append(json.loads(Path(command[command.index("--base") - 2]).read_bytes()))
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(figures.subprocess, "run", render)
    with pytest.raises(ValueError, match="0/2 observations"):
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
    assert not bindings


@pytest.mark.parametrize("verbose", [False, True])
def test_main_announces_preparation_and_fallback_before_each_operation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, verbose: bool
) -> None:
    from benchmarking import collection
    from benchmarking.reports import store as store_module

    config = catalog_fixture(tmp_path)
    (tmp_path / "one.egg").write_text("(check (= 1 1))")
    report = tmp_path / "observations[1].jsonl"
    stream = io.StringIO()
    console = Console(file=stream, width=200, color_system=None)
    events = []
    ticks = iter((10, 11, 20, 22, 30, 33, 40, 44, 50, 55))
    monkeypatch.setattr(figures, "perf_counter", lambda: next(ticks))

    def make_console(**kwargs: Any) -> Console:
        assert kwargs["stderr"] is True
        return console

    def inputs(*args: Any) -> Any:
        assert "Resolving inputs for 2 paper outputs" in stream.getvalue()
        events.append("inputs")
        return original_inputs(*args)

    def metadata(*args: Any) -> Any:
        assert "Loading corpus metadata" in stream.getvalue()
        events.append("metadata")
        return original_metadata(*args)

    class Store(ReportStore):
        def __init__(self, path: Path) -> None:
            assert f"Loading cache {report}" in stream.getvalue()
            events.append("cache")
            super().__init__(path)

        def grouped_report(self, *args: Any, **kwargs: Any) -> Any:
            assert f"Writing {grouped_report_path(report)}" in stream.getvalue()
            events.append("snapshot")
            return super().grouped_report(*args, **kwargs)

    def targets(requests: Any, *_args: Any) -> Any:
        assert "Resolving targets" in stream.getvalue()
        events.append("targets")
        return {request.endpoint.target: make_target(target_label="figures") for request in requests}

    def collect(*_args: Any, **kwargs: Any) -> Any:
        assert kwargs["verbose"] is verbose
        events.append("collect")
        raise OSError("collection interrupted")

    def snapshot(*args: Any) -> None:
        assert f"Writing {grouped_report_path(report)}" in stream.getvalue()
        events.append("write")
        original_snapshot(*args)

    original_inputs, original_metadata = figures.resolve_figures, figures._figure_inventory
    original_snapshot = figures.write_grouped_report
    monkeypatch.setattr(figures, "Console", make_console)
    monkeypatch.setattr(figures, "resolve_figures", inputs)
    monkeypatch.setattr(figures, "_figure_inventory", metadata)
    monkeypatch.setattr(store_module, "ReportStore", Store)
    monkeypatch.setattr(collection, "resolve_requests", targets)
    monkeypatch.setattr(collection, "plan_collection", lambda *_args: ())
    monkeypatch.setattr(collection, "collect", collect)
    monkeypatch.setattr(figures, "write_grouped_report", snapshot)
    monkeypatch.setattr(figures, "render_figures", lambda *_args: ())
    args = ["--config", str(config), "--report", str(report), *(["-v"] if verbose else [])]
    assert figures.main(args) == 2
    assert events == ["inputs", "metadata", "cache", "targets", "collect", "snapshot", "write"]
    text = stream.getvalue()
    if verbose:
        assert "1 unique input" in text and "1.0s" in text
        assert "0 metadata" in text and "2.0s" in text
        assert "0 observations" in text and "3.0s" in text
        assert "1 target" in text and "4.0s" in text
        assert "5.0s" in text
    else:
        assert not any(marker in text for marker in ("  resolved", "  loaded", "  wrote"))


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
    write_report(
        report,
        make_record(
            0,
            memory_limit_bytes=None,
            started_at="2026-10-01T00:00:00Z",
            binary_sha256="old",
            target_label="figures",
            max_rss_bytes=1048576,
        ),
    )
    write_grouped_report(ReportStore(report).grouped_report(), grouped_report_path(report))

    def interrupted_write(store: ReportStore, _plans: Any, requests: Any, *_args: Any, **_kwargs: Any) -> Any:
        store.append(
            make_record(
                1,
                memory_limit_bytes=None,
                started_at="2026-10-01T00:00:01Z",
                target_label="figures",
                status="failure",
                file_sha256=requests[0].files[0].sha256,
                max_rss_bytes=1048576,
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

    def fail_collection(*_args: Any, **_kwargs: Any) -> Any:
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

    def interrupted(store: ReportStore, _plans: Any, requests: Any, targets: Any, *_args: Any, **_kwargs: Any) -> Any:
        store.append(
            make_record(
                0,
                memory_limit_bytes=None,
                started_at="2026-10-01T00:00:00Z",
                target_label="figures",
                file_sha256=requests[0].files[0].sha256,
                max_rss_bytes=1048576,
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


def test_cache_defaults_and_explicit_paths(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    from benchmarking.benchmark import parse_benchmark_args, resolve_report_path

    monkeypatch.chdir(tmp_path)
    pair = parse_benchmark_args([])
    args, _ = figures.parse_args([])
    default = tmp_path / "data-cache/reports.jsonl"
    assert resolve_report_path(pair.report, tmp_path) == default
    assert args.report.resolve() == default
    assert grouped_report_path(default) == tmp_path / "data-cache/reports-grouped.json"
    explicit = "custom[1].jsonl"
    pair = parse_benchmark_args(["--report", explicit])
    args, _ = figures.parse_args(["--report", explicit])
    assert resolve_report_path(pair.report, tmp_path) == args.report.resolve() == tmp_path / explicit


def test_no_runs_main_never_resolves_or_collects_targets(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    from benchmarking import collection
    from benchmarking.targets import sha256_file

    config = catalog_fixture(tmp_path)
    file = tmp_path / "one.egg"
    file.write_text("(check (= 1 1))")
    report = tmp_path / "observations.jsonl"
    write_report(
        report,
        *[
            make_record(
                i,
                started_at=f"2026-10-01T00:00:0{i}Z",
                target_label="figures",
                file_sha256=sha256_file(file),
                max_rss_bytes=1048576,
            )
            for i in range(2)
        ],
    )
    write_grouped_report(ReportStore(report).grouped_report(), grouped_report_path(report))
    before = {path: path.read_bytes() for path in (report, grouped_report_path(report))}
    monkeypatch.setattr(collection, "resolve_requests", lambda *_args: pytest.fail("cached render resolved targets"))
    monkeypatch.setattr(collection, "collect", lambda *_args, **_kw: pytest.fail("cached render collected timings"))
    snapshots = []
    monkeypatch.setattr(figures, "render_figures", lambda *args: snapshots.append(args[4]))
    assert figures.main(["--config", str(config), "--report", str(report), "--no-runs"]) == 0
    assert len(snapshots) == 1 and snapshots[0].binary_path is None
    assert all(path.read_bytes() == content for path, content in before.items())
