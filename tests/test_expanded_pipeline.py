"""Exercise the real expanded Make rules with isolated, inert executables."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

from benchmarking.benchmark import parse_benchmark_args
from benchmarking.collection import build_collection_plan
from benchmarking.engines import Engine, Treatment
from benchmarking.models import BenchmarkEndpoint, EngineBinary, ResolvedTarget, TargetRequest, TargetRow
from benchmarking.pilot import require_suite_admission
from benchmarking.reports.store import ReportStore
from benchmarking.suites import resolve_suite
from benchmarking.targets import sha256_file, workload_command

from .report_fixtures import make_record

ROOT = Path(__file__).resolve().parents[1]


EXPANDED_FIGURES = ("math-cutoff-11", "proof-overhead-cdf")
EXPANDED_IMAGES = tuple(f"figures/expanded/{name}.{ext}" for name in EXPANDED_FIGURES for ext in ("svg", "png"))


@pytest.fixture
def pipeline_env(tmp_path: Path) -> dict[str, str]:
    """Run the real Make graph, isolating every external executable and artifact."""
    shutil.copyfile(ROOT / "Makefile", tmp_path / "Makefile")
    for relative in ("bin", "figures/expanded", "benchmarks/local"):
        (tmp_path / relative).mkdir(parents=True, exist_ok=True)
    for name in (*EXPANDED_FIGURES, "unselected"):
        (tmp_path / f"figures/expanded/{name}.vl.json").write_text("{}\n")
    (tmp_path / ".reports.jsonl").write_text("retained observations\n")
    (tmp_path / "inventory-source.json").write_text("{}\n")
    stub = tmp_path / "stage.py"
    stub.write_text(
        f"#!{sys.executable}\n"
        + textwrap.dedent(
            r"""
            import json, os, pathlib, sys, tempfile, time
            root = pathlib.Path(os.environ['PIPELINE_TEST_ROOT'])
            name, args = pathlib.Path(sys.argv[0]).name, sys.argv[1:]
            lock = root / 'collecting'
            if name == 'bench.py':
                assert args[0] != 'export'
                stage = 'pilot' if '--baseline-only' in args else 'collect'
                assert os.environ['EGGLOG_BENCH_MEMORY_GUARD'] == '1'
            elif name == 'uv' and 'benchmarking.figure_inventory' in args:
                stage = 'inventory'
                assert {'run', '--locked', 'python', '-m'} <= set(args)
            elif name == 'npx':
                stage = 'render'
                assert not lock.exists()
                assert (root / '.reports-grouped.json').exists()
                assert (root / 'benchmarks/local/figure-inventory.json').exists()
            else:
                raise AssertionError(('Unexpected build or collection command', name, args))

            def record(event):
                with (root / 'events.jsonl').open('a') as output:
                    output.write(json.dumps([event, *args]) + '\n')

            def write_changed(path, content):
                if path.exists() and path.read_text() == content:
                    return
                with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, delete=False) as output:
                    output.write(content)
                os.replace(output.name, path)

            if stage == 'collect':
                if os.environ.get('PIPELINE_TEST_EXPLICIT_PILOT') == '1':
                    assert (root / 'pilot-finished').exists()
                lock.mkdir()  # Fail concurrent collectors; do not serialize them in this stub.
                record('collect-start')
            else:
                assert not lock.exists(), stage
                record(stage)
            if os.environ.get('PIPELINE_TEST_FAILURE') == stage:
                raise SystemExit(7)
            if stage == 'collect':
                time.sleep(0.05)
                with (root / '.reports.jsonl').open('a') as output:
                    output.write(json.dumps(args) + '\n')
                write_changed(root / '.reports-grouped.json', (root / '.reports.jsonl').read_text())
                record('collect-end')
                lock.rmdir()
            elif stage == 'pilot':
                time.sleep(0.05)
                (root / 'pilot-finished').touch()
                raise SystemExit(int(os.environ.get('PIPELINE_TEST_PILOT_EXIT', '0')))
            elif stage == 'inventory':
                inventory = json.loads((root / 'inventory-source.json').read_text())
                inventory['timeout_sec'] = int(args[args.index('--timeout-sec') + 1])
                write_changed(root / 'benchmarks/local/figure-inventory.json', json.dumps(inventory))
            elif stage == 'render':
                command = 'vl2svg' if 'vl2svg' in args else 'vl2png'
                index = args.index(command)
                assert pathlib.Path(args[index + 1]).exists()
                pathlib.Path(args[index + 2]).write_text('rendered\n')
            """
        )
    )
    stub.chmod(0o755)
    for name in ("uv", "npx", "cargo", "npm"):
        (tmp_path / "bin" / name).symlink_to(stub)
    (tmp_path / "bench.py").symlink_to(stub)
    return {
        **os.environ,
        "PATH": f"{tmp_path / 'bin'}{os.pathsep}{os.environ['PATH']}",
        "MAKEFLAGS": "",
        "PIPELINE_TEST_ROOT": str(tmp_path),
    }


@pytest.mark.parametrize("timeout_sec", [300, 480])
def test_inventory_then_direct_images_render_existing_snapshot_without_collection(
    tmp_path: Path, pipeline_env: dict[str, str], timeout_sec: int
) -> None:
    cache = tmp_path / ".reports.jsonl"
    cache_mtime = cache.stat().st_mtime_ns
    snapshot = tmp_path / ".reports-grouped.json"
    snapshot.write_text("existing grouped snapshot\n")
    # A newer JSONL must not trigger a snapshot refresh during direct rendering.
    os.utime(snapshot, (1_600_000_000, 1_600_000_000))
    result = subprocess.run(
        ["make", "figure-inventory", f"EXPANDED_TIMEOUT_SEC={timeout_sec}"],
        cwd=tmp_path,
        env=pipeline_env,
        capture_output=True,
        text=True,
        timeout=15,
    )
    assert result.returncode == 0, result.stderr
    result = subprocess.run(
        ["make", "-j8", *EXPANDED_IMAGES],
        cwd=tmp_path,
        env=pipeline_env,
        capture_output=True,
        text=True,
        timeout=15,
    )
    assert result.returncode == 0, result.stderr
    events = [json.loads(line) for line in (tmp_path / "events.jsonl").read_text().splitlines()]
    assert [event[0] for event in events] == ["inventory", *(["render"] * 4)]
    assert json.loads((tmp_path / "benchmarks/local/figure-inventory.json").read_text())["timeout_sec"] == timeout_sec
    rendered = set()
    for _stage, *args in events[1:]:
        assert "--yes" in args
        assert {arg for arg in args if arg.startswith("--package=")} == {
            "--package=vega@6.4.0",
            "--package=vega-lite@6.4.3",
            "--package=vega-cli@6.4.0",
            "--package=canvas@3.2.3",
        }
        command = "vl2svg" if "vl2svg" in args else "vl2png"
        index = args.index(command)
        spec, image = args[index + 1 : index + 3]
        assert spec.removesuffix(".vl.json") == Path(image).stem
        assert Path(image).suffix == (".svg" if command == "vl2svg" else ".png")
        if command == "vl2png":
            assert args[args.index("-s") + 1] == "3"
        rendered.add(image)
    assert rendered == {f"{name}.{extension}" for name in EXPANDED_FIGURES for extension in ("svg", "png")}
    assert cache.read_text() == "retained observations\n"
    assert cache.stat().st_mtime_ns == cache_mtime
    assert snapshot.read_text() == "existing grouped snapshot\n"
    assert snapshot.stat().st_mtime == 1_600_000_000


@pytest.mark.parametrize("pilot_exit", [0, 1, 2])
@pytest.mark.parametrize("timeout_override", [None, 480])
@pytest.mark.parametrize("explicit_pilot", [False, True])
@pytest.mark.parametrize("recording_only", [False, True])
def test_parallel_expanded_pipeline_orders_baselines_proofs_and_figures(
    tmp_path: Path,
    pipeline_env: dict[str, str],
    pilot_exit: int,
    timeout_override: int | None,
    explicit_pilot: bool,
    recording_only: bool,
) -> None:
    result = subprocess.run(
        [
            "make",
            "-j8",
            *([f"EXPANDED_TIMEOUT_SEC={timeout_override}"] if timeout_override is not None else []),
            *(
                []
                if recording_only
                else ["figures-expanded", "figures-data", "figures-expanded-data", "expanded-bench"]
            ),
            "expanded-bench-recording",
            *(["expanded-pilot"] if explicit_pilot else []),
        ],
        cwd=tmp_path,
        env={
            **pipeline_env,
            "PIPELINE_TEST_PILOT_EXIT": str(pilot_exit),
            "PIPELINE_TEST_EXPLICIT_PILOT": str(int(explicit_pilot)),
        },
        capture_output=True,
        text=True,
        timeout=15,
    )
    events = [json.loads(line) for line in (tmp_path / "events.jsonl").read_text().splitlines()]
    if explicit_pilot:
        assert events[0][0] == "pilot"
        args = parse_benchmark_args(events[0][1:])
        assert args.baseline_only and args.baseline_window
        assert args.suite == ["expanded"] and args.treatment == "proof-extraction" and args.compare_treatment == "off"
        assert args.target == "figures=." and args.rounds == 10 and args.timeout_sec == (timeout_override or 300)
        if pilot_exit != 0:
            assert result.returncode != 0
            assert len(events) == 1
            return
        events = events[1:]
    assert result.returncode == 0, result.stderr
    comparisons = [("expanded", "proofs", "off")]
    if not recording_only:
        comparisons += [
            ("expanded", "proof-extraction", "off"),
            ("math-11", "proof-extraction", "off"),
            ("math-11", "egg-proof-extraction", "egg"),
        ]
    for index, (suite, candidate, baseline) in enumerate(comparisons):
        start, end = events[2 * index : 2 * index + 2]
        assert start[0] == "collect-start" and end[0] == "collect-end" and start[1:] == end[1:]
        args = parse_benchmark_args(start[1:])
        assert args.suite == [suite] and args.treatment == candidate and args.compare_treatment == baseline
        assert args.baseline_window == (suite == "expanded") and not args.baseline_only
        assert args.target == "figures=." and args.rounds == 10 and args.timeout_sec == (timeout_override or 300)
    remaining = events[2 * len(comparisons) :]
    assert (tmp_path / ".reports-grouped.json").read_text() == (tmp_path / ".reports.jsonl").read_text()
    if recording_only:
        assert not remaining
        return
    assert [event[0] for event in remaining] == ["inventory", *(["render"] * 4)]
    inventory = json.loads((tmp_path / "benchmarks/local/figure-inventory.json").read_text())
    assert inventory["timeout_sec"] == (timeout_override or 300)


@pytest.mark.parametrize("failure", ["collect", "inventory"])
def test_failed_pipeline_stage_blocks_downstream_work(
    tmp_path: Path, pipeline_env: dict[str, str], failure: str
) -> None:
    result = subprocess.run(
        ["make", "-j8", "figures-expanded"],
        cwd=tmp_path,
        env={**pipeline_env, "PIPELINE_TEST_FAILURE": failure},
        capture_output=True,
        text=True,
        timeout=15,
    )
    assert result.returncode != 0
    events = [json.loads(line) for line in (tmp_path / "events.jsonl").read_text().splitlines()]
    assert [event[0] for event in events] == {
        "collect": ["collect-start"],
        "inventory": [*(["collect-start", "collect-end"] * 4), "inventory"],
    }[failure]
    assert not list((tmp_path / "figures/expanded").glob("*.svg"))
    assert not list((tmp_path / "figures/expanded").glob("*.png"))


@pytest.mark.parametrize("target", ["figures-data", "figures-expanded-data"])
def test_data_targets_collect_then_refresh_inventory_without_rendering(
    tmp_path: Path, pipeline_env: dict[str, str], target: str
) -> None:
    result = subprocess.run(
        ["make", "-j8", target], cwd=tmp_path, env=pipeline_env, capture_output=True, text=True, timeout=15
    )
    assert result.returncode == 0, result.stderr
    events = [json.loads(line) for line in (tmp_path / "events.jsonl").read_text().splitlines()]
    assert [event[0] for event in events] == [*(["collect-start", "collect-end"] * 4), "inventory"]
    assert (tmp_path / ".reports-grouped.json").read_text() == (tmp_path / ".reports.jsonl").read_text()
    assert not list((tmp_path / "figures/expanded").glob("*.svg"))
    assert not list((tmp_path / "figures/expanded").glob("*.png"))


@pytest.mark.parametrize("missing", [".reports-grouped.json", "benchmarks/local/figure-inventory.json"])
def test_direct_images_require_existing_snapshot_and_inventory(
    tmp_path: Path, pipeline_env: dict[str, str], missing: str
) -> None:
    for relative in (".reports-grouped.json", "benchmarks/local/figure-inventory.json"):
        if relative != missing:
            (tmp_path / relative).write_text("{}\n")
    result = subprocess.run(
        ["make", "-j8", *EXPANDED_IMAGES], cwd=tmp_path, env=pipeline_env, capture_output=True, text=True, timeout=15
    )
    assert result.returncode != 0
    assert not (tmp_path / "events.jsonl").exists()
    assert not list((tmp_path / "figures/expanded").glob("*.svg"))
    assert not list((tmp_path / "figures/expanded").glob("*.png"))


@pytest.mark.parametrize(("suite_name", "file_count"), [("math-growth", 11), ("math-11", 1)])
def test_math_suite_admits_and_plans_all_four_endpoints_at_requested_timeout(
    tmp_path: Path, suite_name: str, file_count: int
) -> None:
    catalog = json.loads((ROOT / "benchmarks/catalog.json").read_text())
    catalog["cases"] = [
        case for case in catalog["cases"] if case["family"] == "math-growth" and case["status"] != "deferred"
    ]
    for case in catalog["cases"]:
        for workload in case["workloads"]:
            path = tmp_path / workload
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / workload, path)
    (tmp_path / "benchmarks/catalog.json").write_text(json.dumps(catalog))
    release = tmp_path / "target/release"
    release.mkdir(parents=True)
    for name in ("egglog-experimental", "egg-math-benchmark"):
        (release / name).write_text(name)
    hashes = {
        "egglog": sha256_file(release / "egglog-experimental"),
        "egg": sha256_file(release / "egg-math-benchmark"),
    }
    selection = resolve_suite(suite_name, tmp_path)
    assert len(selection.files) == file_count
    evidence = tmp_path / "pilot.jsonl"
    store = ReportStore(tmp_path / "reports.jsonl")
    for file in selection.files:
        for treatment in ("off", "proof-extraction"):
            store.append(
                make_record(
                    0,
                    started_at="2026-09-24T00:00:00Z",
                    treatment=treatment,
                    binary_sha256=hashes["egglog"],
                    file_sha256=file.sha256,
                    timeout_sec=300,
                    wall_sec=0.01,  # Fast cutoffs still belong in the dedicated Math charts.
                )
            )
    assert not evidence.exists()  # Neither screening nor correctness evidence is needed.
    conditions: tuple[tuple[Engine, str, Treatment, Treatment], ...] = (
        ("egglog", "egglog-experimental", "proof-extraction", "off"),
        ("egg", "egg-math-benchmark", "egg-proof-extraction", "egg"),
    )
    for engine, name, candidate, baseline in conditions:
        args = parse_benchmark_args(
            [
                "--suite",
                suite_name,
                "--treatment",
                candidate,
                "--compare-treatment",
                baseline,
                "--timeout-sec",
                "300",
            ]
        )
        assert not args.baseline_window and args.rounds == 10
        target = ResolvedTarget(
            TargetRequest("figures=.", ".", "figures"),
            TargetRow(".", str(tmp_path), "HEAD", "fixture", False, "figures"),
            hashes[engine],
            release / name,
            (EngineBinary(engine, hashes[engine], release / name),),
            engine,
        )
        files, _diagnostics, issues = require_suite_admission(
            selection, (target,), evidence, store=store, timeout_sec=args.timeout_sec
        )
        assert files == selection.files and not issues
        endpoints = (BenchmarkEndpoint(target, args.compare_treatment), BenchmarkEndpoint(target, args.treatment))
        plan = build_collection_plan(store, target, endpoints, files, args.rounds, args.timeout_sec, False, True)
        assert plan.total_missing_observations == file_count * 2 * (9 if engine == "egglog" else 10)
        for run in plan.runs:
            command = workload_command(release / name, run.file, run.treatment)
            assert command[0] == str(release / name)
            if engine == "egg":
                assert command[1:3] == ["--proof-mode", "off" if run.treatment == "egg" else "extract"]


@pytest.mark.parametrize(
    ("changed", "expected_figures"),
    [
        (None, ()),
        ("figures/expanded/math-cutoff-11.vl.json", ("math-cutoff-11",)),
        ("figures/expanded/proof-overhead-cdf.vl.json", ("proof-overhead-cdf",)),
        ("figures/expanded/unselected.vl.json", ()),
        (".reports-grouped.json", EXPANDED_FIGURES),
        (".reports.jsonl", ()),
        ("inventory-source.json", EXPANDED_FIGURES),
        ("Makefile", EXPANDED_FIGURES),
    ],
)
def test_cached_figures_rebuild_only_changed_dependencies(
    tmp_path: Path,
    pipeline_env: dict[str, str],
    changed: str | None,
    expected_figures: tuple[str, ...],
) -> None:
    (tmp_path / ".reports-grouped.json").write_text("existing grouped snapshot\n")
    refresh_inventory = ["make", "figure-inventory"]
    result = subprocess.run(
        refresh_inventory, cwd=tmp_path, env=pipeline_env, capture_output=True, text=True, timeout=15
    )
    assert result.returncode == 0, result.stderr
    command = ["make", "-j8", *EXPANDED_IMAGES]
    initial = subprocess.run(command, cwd=tmp_path, env=pipeline_env, capture_output=True, text=True, timeout=15)
    assert initial.returncode == 0, initial.stderr
    images = [tmp_path / image for image in EXPANDED_IMAGES]
    # Establish deterministic dependency ordering without filesystem-resolution sleeps.
    for path in tmp_path.rglob("*"):
        if path.is_file():
            timestamp = 1_600_000_002 if path in images else 1_600_000_000
            if path.name in (".reports-grouped.json", "figure-inventory.json"):
                timestamp = 1_600_000_001
            os.utime(path, (timestamp, timestamp))
    if changed is not None:
        path = tmp_path / changed
        if changed == "inventory-source.json":
            path.write_text('{"revision": 2}\n')
        elif changed == ".reports.jsonl":
            path.write_text("retained observations\nnew observation\n")
        os.utime(path, (1_600_000_003, 1_600_000_003))
    (tmp_path / "events.jsonl").write_text("")
    result = subprocess.run(
        refresh_inventory, cwd=tmp_path, env=pipeline_env, capture_output=True, text=True, timeout=15
    )
    assert result.returncode == 0, result.stderr
    result = subprocess.run(command, cwd=tmp_path, env=pipeline_env, capture_output=True, text=True, timeout=15)
    assert result.returncode == 0, result.stderr
    events = [json.loads(line) for line in (tmp_path / "events.jsonl").read_text().splitlines()]
    assert [event[0] for event in events] == ["inventory", *(["render"] * (2 * len(expected_figures)))]
    rendered = set()
    for stage, *args in events:
        if stage == "render":
            command_name = "vl2svg" if "vl2svg" in args else "vl2png"
            rendered.add(args[args.index(command_name) + 2])
    assert rendered == {f"{name}.{extension}" for name in expected_figures for extension in ("svg", "png")}
    for path in images:
        assert (path.stat().st_mtime == 1_600_000_002) == (path.stem not in expected_figures)
    assert ((tmp_path / "benchmarks/local/figure-inventory.json").stat().st_mtime == 1_600_000_001) == (
        changed != "inventory-source.json"
    )
