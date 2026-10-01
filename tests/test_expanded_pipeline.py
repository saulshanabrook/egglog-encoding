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


@pytest.mark.parametrize("timeout_sec", [300, 480])
def test_cached_figures_project_then_render_without_collection(tmp_path: Path, timeout_sec: int) -> None:
    shutil.copyfile(ROOT / "Makefile", tmp_path / "Makefile")
    (tmp_path / "bin").mkdir()
    (tmp_path / "figures").mkdir()
    cache = tmp_path / ".reports.jsonl"
    cache.write_text("retained observations\n")
    stub = tmp_path / "stage.py"
    stub.write_text(
        f"#!{sys.executable}\n"
        + textwrap.dedent(
            """\
            import json, os, pathlib, sys
            root = pathlib.Path(os.environ['PIPELINE_TEST_ROOT'])
            name, args = pathlib.Path(sys.argv[0]).name, sys.argv[1:]
            assert name in ('uv', 'render'), 'Unexpected build or collection'
            if name == 'uv':
                assert args[:5] == ['run', '--locked', 'python', '-m', 'figures.prepare_expanded']
            with (root / 'events.jsonl').open('a') as output:
                output.write(json.dumps([name, *args]) + '\\n')
            """
        )
    )
    stub.chmod(0o755)
    for name in ("uv", "render", "cargo"):
        (tmp_path / "bin" / name).symlink_to(stub)
    (tmp_path / "bench.py").symlink_to(stub)
    (tmp_path / "figures/Makefile").write_text(".PHONY: expanded\nexpanded:\n\t../bin/render\n")
    result = subprocess.run(
        ["make", "-j8", "figures-expanded-cached", f"EXPANDED_TIMEOUT_SEC={timeout_sec}"],
        cwd=tmp_path,
        env={
            **os.environ,
            "PATH": f"{tmp_path / 'bin'}{os.pathsep}{os.environ['PATH']}",
            "MAKEFLAGS": "",
            "PIPELINE_TEST_ROOT": str(tmp_path),
        },
        capture_output=True,
        text=True,
        timeout=15,
    )
    assert result.returncode == 0, result.stderr
    assert [json.loads(line) for line in (tmp_path / "events.jsonl").read_text().splitlines()] == [
        ["uv", "run", "--locked", "python", "-m", "figures.prepare_expanded", "--timeout-sec", str(timeout_sec)],
        ["render"],
    ]
    assert cache.read_text() == "retained observations\n"


@pytest.mark.parametrize("pilot_exit", [0, 1, 2])
@pytest.mark.parametrize("timeout_override", [None, 480])
@pytest.mark.parametrize("explicit_pilot", [False, True])
@pytest.mark.parametrize("recording_only", [False, True])
def test_parallel_expanded_pipeline_orders_baselines_proofs_and_figures(
    tmp_path: Path, pilot_exit: int, timeout_override: int | None, explicit_pilot: bool, recording_only: bool
) -> None:
    timeout_sec = str(timeout_override or 300)
    shutil.copyfile(ROOT / "Makefile", tmp_path / "Makefile")
    (tmp_path / "bin").mkdir()
    (tmp_path / "figures").mkdir()
    stub = tmp_path / "stage.py"
    stub.write_text(
        f"#!{sys.executable}\n"
        + textwrap.dedent(
            """\
            import json, os, pathlib, sys, time
            root = pathlib.Path(os.environ['PIPELINE_TEST_ROOT'])
            name, args = pathlib.Path(sys.argv[0]).name, sys.argv[1:]
            lock = root / 'collecting'
            if name == 'cargo':
                stage = 'build'
            elif name == 'bench.py':
                stage = 'pilot' if '--baseline-only' in args else 'collect'
                suite = args[args.index('--suite') + 1]
                assert ('--baseline-window' in args) == (suite == 'expanded')
                assert suite in ('expanded', 'math-11')
                assert os.environ['EGGLOG_BENCH_MEMORY_GUARD'] == '1'
            elif name == 'render':
                stage = 'render'
            elif name == 'uv' and 'figures.prepare_expanded' in args:
                stage = 'project'
            elif name == 'uv' and 'benchmarking.pilot' in args:
                assert '--coverage-only' in args  # No correctness/screening runs during benchmarking.
                stage = 'coverage'
            else:
                raise AssertionError((name, args))
            def record(event):
                with (root / 'events.jsonl').open('a') as output:
                    output.write(json.dumps([event, *args]) + '\\n')
            if stage == 'pilot':
                assert '--baseline-only' in args
            if stage == 'collect':
                if os.environ['PIPELINE_TEST_EXPLICIT_PILOT'] == '1':
                    assert (root / 'pilot-finished').exists()
                lock.mkdir()  # Concurrent collectors must fail, rather than serialize in the stub.
                record('collect-start')
                time.sleep(0.1)
                record('collect-end')
                lock.rmdir()
            else:
                assert not lock.exists(), stage
                record(stage)
            if stage == 'build':
                time.sleep(0.05)
                (root / 'built').touch()
            if stage == 'pilot':
                time.sleep(0.05)
                (root / 'pilot-finished').touch()
                raise SystemExit(int(os.environ['PIPELINE_TEST_PILOT_EXIT']))
            """
        )
    )
    stub.chmod(0o755)
    for name in ("cargo", "uv", "render"):
        (tmp_path / "bin" / name).symlink_to(stub)
    (tmp_path / "bench.py").symlink_to(stub)
    (tmp_path / "figures/Makefile").write_text(".PHONY: expanded\nexpanded:\n\t../bin/render\n")
    result = subprocess.run(
        [
            "make",
            "-j8",
            *([f"EXPANDED_TIMEOUT_SEC={timeout_override}"] if timeout_override is not None else []),
            *([] if recording_only else ["figures-expanded", "figures-expanded-data", "expanded-bench"]),
            "expanded-bench-recording",
            *(["expanded-pilot"] if explicit_pilot else []),
        ],
        cwd=tmp_path,
        env={
            **os.environ,
            "PATH": f"{tmp_path / 'bin'}{os.pathsep}{os.environ['PATH']}",
            "MAKEFLAGS": "",
            "PIPELINE_TEST_ROOT": str(tmp_path),
            "PIPELINE_TEST_PILOT_EXIT": str(pilot_exit),
            "PIPELINE_TEST_EXPLICIT_PILOT": str(int(explicit_pilot)),
        },
        capture_output=True,
        text=True,
        timeout=15,
    )
    events = [json.loads(line) for line in (tmp_path / "events.jsonl").read_text().splitlines()]
    baseline_event = [
        "pilot",
        "--suite",
        "expanded",
        "--baseline-window",
        "--baseline-only",
        "--target",
        "figures=.",
        "--treatment",
        "proof-extraction",
        "--compare-treatment",
        "off",
        "--rounds",
        "10",
        "--timeout-sec",
        timeout_sec,
    ]
    if explicit_pilot:
        assert events[0] == baseline_event
        if pilot_exit != 0:
            assert result.returncode != 0
            assert len(events) == 1
            return
        events = events[1:]
    treatments = ("proofs",) if recording_only else ("proofs", "proof-extraction")
    for index, treatment in enumerate(treatments):
        arguments = [
            "--suite",
            "expanded",
            "--baseline-window",
            "--target",
            "figures=.",
            "--treatment",
            treatment,
            "--compare-treatment",
            "off",
            "--rounds",
            "10",
            "--timeout-sec",
            timeout_sec,
        ]
        assert events[2 * index] == ["collect-start", *arguments]
        assert events[1 + 2 * index] == ["collect-end", *arguments]
    assert result.returncode == 0, result.stderr
    if recording_only:
        assert len(events) == 2
        return
    for index, (candidate, baseline) in enumerate((("proof-extraction", "off"), ("egg-proof-extraction", "egg"))):
        arguments = [
            "--suite",
            "math-11",
            "--target",
            "figures=.",
            "--treatment",
            candidate,
            "--compare-treatment",
            baseline,
            "--rounds",
            "10",
            "--timeout-sec",
            timeout_sec,
        ]
        assert events[4 + 2 * index] == ["collect-start", *arguments]
        assert events[5 + 2 * index] == ["collect-end", *arguments]
    assert events[8:] == [
        ["project", *["run", "--locked", "python", "-m", "figures.prepare_expanded", "--timeout-sec", timeout_sec]],
        [
            "coverage",
            *[
                "run",
                "--locked",
                "python",
                "-m",
                "benchmarking.pilot",
                "--suite",
                "expanded",
                "--coverage-only",
                "--report",
                ".reports.jsonl",
                "--coverage-output",
                "benchmarks/local/coverage.json",
                "--timeout-sec",
                timeout_sec,
            ],
        ],
        ["render"],
    ]


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


def test_figure_make_discovers_specs_and_rebuilds_only_affected_images(tmp_path: Path) -> None:
    shutil.copyfile(ROOT / "figures/Makefile", tmp_path / "Makefile")
    specs = (
        "egg-vs-egglog.vl.json",
        "proof-overhead.vl.json",
        "proof-context.vl.json",
        "extra.vl.json",
        "alternatives/egg-vs-egglog-ecdf.vl.json",
        "alternatives/egg-vs-egglog-boxplot.vl.json",
        "alternatives/proof-overhead-suite-order.vl.json",
        "alternatives/math-growth-overlay.vl.json",
        "alternatives/math-growth-ratios.vl.json",
        "alternatives/math-memory-overlay.vl.json",
        "alternatives/math-memory-ratios.vl.json",
        "expanded/math-growth.vl.json",
        "expanded/math-memory.vl.json",
        "expanded/math-comparison.vl.json",
        "expanded/math-cutoff-11.vl.json",
        "expanded/proof-overhead-cdf.vl.json",
    )
    families = ("eggcc", "luminal")
    atlas_pages = ("eggcc", "other")
    inputs = [
        *specs,
        "package.json",
        "package-lock.json",
        "egg-vs-egglog.data.json",
        "proof-overhead.data.json",
        "expanded/math-growth.data.json",
        "expanded/overview.data.json",
        "expanded/proof-overhead-atlas.vl.json",
        *(f"expanded/atlas/{page}/atlas.data.json" for page in atlas_pages),
        *(f"expanded/{family}/proof-overhead.data.json" for family in families),
        "unrelated.data.json",
        "metadata.json",
        "alternatives/not-a-spec.data.json",
        "expanded/not-a-spec.data.json",
    ]
    for relative in inputs:
        path = tmp_path / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("{}\n")
    (tmp_path / "bin").mkdir()
    renderers = tmp_path / "node_modules/.bin"
    renderers.mkdir(parents=True)
    stub = tmp_path / "tool.py"
    stub.write_text(
        f"#!{sys.executable}\n"
        + textwrap.dedent(
            """\
            import json, os, pathlib, sys
            root = pathlib.Path(os.environ['FIGURE_TEST_ROOT'])
            name, args = pathlib.Path(sys.argv[0]).name, sys.argv[1:]
            if name == 'npm':
                assert args == ['ci', '--no-audit', '--no-fund']
                event = ['install']
            else:
                assert name in ('vl2svg', 'vl2png')
                assert (root / 'node_modules/.installed').exists()
                if name == 'vl2png':
                    assert args[-2:] == ['-s', '3']
                source, output = pathlib.Path(args[0]), pathlib.Path(args[1])
                assert source.name.endswith('.vl.json'), source
                assert source.is_file()
                assert output.suffix == ('.svg' if name == 'vl2svg' else '.png')
                output.write_text('rendered ' + source.name)
                event = [
                    'render', str(output.resolve().relative_to(root)),
                    str(source.resolve().relative_to(root)), args,
                ]
            with (root / 'events.jsonl').open('a') as output:
                output.write(json.dumps(event) + '\\n')
            """
        )
    )
    stub.chmod(0o755)
    (tmp_path / "bin/npm").symlink_to(stub)
    for name in ("vl2svg", "vl2png"):
        (renderers / name).symlink_to(stub)
    environment = {
        **os.environ,
        "PATH": f"{tmp_path / 'bin'}{os.pathsep}{os.environ['PATH']}",
        "MAKEFLAGS": "",
        "FIGURE_TEST_ROOT": str(tmp_path),
    }
    command = ["make", "-j8", "all", "alternatives", "expanded-details"]
    # Default rendering builds only the final Math and combined overhead charts.
    subprocess.run(
        ["make", "-j8", "expanded"],
        cwd=tmp_path,
        env=environment,
        check=True,
        capture_output=True,
        text=True,
        timeout=15,
    )
    assert {
        str(path.relative_to(tmp_path)) for extension in ("svg", "png") for path in tmp_path.rglob(f"*.{extension}")
    } == {
        f"expanded/{chart}.{extension}"
        for chart in ("math-cutoff-11", "proof-overhead-cdf")
        for extension in ("svg", "png")
    }
    expected = (
        {f"{name.removesuffix('.vl.json')}.{extension}" for name in specs for extension in ("png", "svg")}
        | {
            f"expanded/{family}/{chart}.{extension}"
            for family in families
            for chart in ("proof-overhead", "proof-context")
            for extension in ("png", "svg")
        }
        | {f"expanded/atlas/{page}/proof-overhead.{extension}" for page in atlas_pages for extension in ("png", "svg")}
    )
    subprocess.run(command, cwd=tmp_path, env=environment, check=True, capture_output=True, text=True, timeout=15)
    log = tmp_path / "events.jsonl"
    events = [json.loads(line) for line in log.read_text().splitlines()]
    assert sum(event[0] == "install" for event in events) == 1
    assert len(events) == len(expected) + 1
    assert {event[1] for event in events if event[0] == "render"} == expected
    assert {
        str(path.relative_to(tmp_path)) for extension in ("svg", "png") for path in tmp_path.rglob(f"*.{extension}")
    } == expected
    for event in events:
        if event[0] == "render" and event[1].startswith(tuple(f"expanded/{family}/" for family in families)):
            assert event[2] == Path(event[1]).stem + ".vl.json"
            assert event[3][2:4] == ["-b", str(Path(event[1]).parent) + "/"]
        if event[0] == "render" and event[1].startswith("expanded/atlas/"):
            assert event[2] == "expanded/proof-overhead-atlas.vl.json"
            assert event[3][2:4] == ["-b", str(Path(event[1]).parent) + "/"]

    # An unchanged invocation must neither reinstall dependencies nor render.
    unchanged_log = log.read_bytes()
    unchanged_mtimes = {name: (tmp_path / name).stat().st_mtime_ns for name in expected}
    subprocess.run(command, cwd=tmp_path, env=environment, check=True, capture_output=True, text=True, timeout=15)
    assert log.read_bytes() == unchanged_log
    assert {name: (tmp_path / name).stat().st_mtime_ns for name in expected} == unchanged_mtimes

    for changed, rebuilt, installs in (
        (
            "expanded/luminal/proof-overhead.data.json",
            {
                f"expanded/luminal/{chart}.{ext}"
                for chart in ("proof-overhead", "proof-context")
                for ext in ("png", "svg")
            },
            0,
        ),
        ("expanded/math-growth.vl.json", {f"expanded/math-growth.{ext}" for ext in ("png", "svg")}, 0),
        (
            "expanded/math-growth.data.json",
            {name for name in expected if name.startswith(("expanded/math-", "alternatives/math-"))},
            0,
        ),
        (
            "expanded/overview.data.json",
            {f"expanded/proof-overhead-cdf.{ext}" for ext in ("png", "svg")},
            0,
        ),
        (
            "expanded/atlas/eggcc/atlas.data.json",
            {f"expanded/atlas/eggcc/proof-overhead.{ext}" for ext in ("png", "svg")},
            0,
        ),
        (
            "expanded/proof-overhead-atlas.vl.json",
            {name for name in expected if name.startswith("expanded/atlas/")},
            0,
        ),
        (
            "proof-overhead.vl.json",
            {
                name
                for name in expected
                if name.startswith(tuple(f"expanded/{family}/proof-overhead." for family in families))
            }
            | {"proof-overhead.png", "proof-overhead.svg"},
            0,
        ),
        (
            "proof-context.vl.json",
            {
                name
                for name in expected
                if name.startswith(tuple(f"expanded/{family}/proof-context." for family in families))
            }
            | {"proof-context.png", "proof-context.svg"},
            0,
        ),
        ("package-lock.json", expected, 1),
    ):
        # Deterministic, past timestamps avoid sleeps and coarse-clock races:
        # inputs < installed dependencies < images < the one touched input.
        base = 1_600_000_000
        for name in inputs:
            os.utime(tmp_path / name, (base, base))
        os.utime(tmp_path / "node_modules/.installed", (base + 1, base + 1))
        for name in expected:
            os.utime(tmp_path / name, (base + 2, base + 2))
        os.utime(tmp_path / changed, (base + 3, base + 3))
        log.write_text("")
        subprocess.run(command, cwd=tmp_path, env=environment, check=True, capture_output=True, text=True, timeout=15)
        events = [json.loads(line) for line in log.read_text().splitlines()]
        assert sum(event[0] == "install" for event in events) == installs, changed
        assert len(events) == len(rebuilt) + installs, changed
        assert {event[1] for event in events if event[0] == "render"} == rebuilt, changed
