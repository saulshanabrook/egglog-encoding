"""Paper orchestration reuses the ordinary runner and never prepares source inputs."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

from benchmarks import paper

ROOT = Path(__file__).resolve().parents[1]


def corpus_fixture(root: Path) -> paper.Corpus:
    directory = root / "benchmarks/corpus"
    corpus: paper.Corpus = {"cases": [], "workloads": []}
    sources = [
        ("math", (ROOT / "egglog-experimental/tests/math-microbenchmark-rational.egg").read_bytes()),
        ("eggcc", b"(datatype Expr (A))\n(let root (A))\n(extract root)\n"),
        ("hardboiled", b"(datatype Expr (B))\n(let root (B))\n(extract root)\n"),
    ]
    for family, source in sources:
        file = f"{family}/{family}-call-01.egg"
        path = directory / file
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(source)
        corpus["workloads"].append(
            {
                "file": file,
                "sha256": "sha256:" + hashlib.sha256(source).hexdigest(),
                "facts_sha256": "",
                "aliases": [{"case": family, "order": 0}],
            }
        )
        corpus["cases"].append(
            {
                "id": family,
                "family": family,
                "status": "ready",
                "workloads": [file],
                "reason": None,
            }
        )
    corpus["cases"].append(
        {
            "id": "missing-source",
            "family": "misaal",
            "status": "blocked",
            "workloads": [],
            "reason": "Source dependency is unavailable",
        }
    )
    (directory / "manifest.json").write_text(json.dumps(corpus))
    return corpus


def test_collection_uses_three_comparisons_and_shared_defaults(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    corpus_fixture(tmp_path)
    calls: list[list[str]] = []

    def collect(argv: list[str]) -> int:
        calls.append(argv)
        return 0

    monkeypatch.setattr(paper, "ROOT", tmp_path)
    monkeypatch.setattr(paper.benchmark, "main", collect)
    assert paper.main(["collect"]) == 0
    parsed = [paper.benchmark.parse_benchmark_args(call) for call in calls]
    assert [(args.treatment, args.compare_treatment) for args in parsed] == [
        ("proofs", "off"),
        ("proof-testing", "off"),
        ("egg-proof-testing", "egg"),
    ]
    assert [len(args.files) for args in parsed] == [3, 3, 1]
    assert all(args.rounds == 5 and args.timeout_sec == 300 for args in parsed)
    assert parsed[0].files == parsed[1].files
    assert all(Path(args.report) == tmp_path / ".reports.jsonl" and not args.force_run for args in parsed)

    calls.clear()
    assert paper.main(["collect", "--comparison", "checked", "--rounds", "8", "--timeout-sec", "90"]) == 0
    assert len(calls) == 1
    args = paper.benchmark.parse_benchmark_args(calls[0])
    assert (args.treatment, args.rounds, args.timeout_sec) == ("proof-testing", 8, 90)


def test_setup_failure_prevents_later_comparisons(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    corpus_fixture(tmp_path)
    calls: list[list[str]] = []

    def fail(argv: list[str]) -> int:
        calls.append(argv)
        return 2

    monkeypatch.setattr(paper.benchmark, "main", fail)
    assert paper.collect(tmp_path, "all", 5, 300, tmp_path / "report.jsonl") == 2
    assert len(calls) == 1


def test_changed_or_duplicate_inputs_cannot_address_the_corpus(tmp_path: Path) -> None:
    corpus = corpus_fixture(tmp_path)
    first = corpus["workloads"][0]
    (tmp_path / "benchmarks/corpus" / first["file"]).write_text("(run 10)")
    with pytest.raises(ValueError, match="corpus input changed"):
        paper.load_corpus(tmp_path)
    corpus = corpus_fixture(tmp_path)
    corpus["workloads"].append(corpus["workloads"][0])
    (tmp_path / "benchmarks/corpus/manifest.json").write_text(json.dumps(corpus))
    with pytest.raises(ValueError, match="duplicate corpus identity"):
        paper.load_corpus(tmp_path)


def test_inventory_is_projection_only_and_preserves_mtime(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    corpus = corpus_fixture(tmp_path)
    monkeypatch.setattr(paper, "ROOT", tmp_path)
    monkeypatch.setattr(paper.benchmark, "main", lambda *_args: pytest.fail("inventory must not collect"))
    destination = tmp_path / "benchmarks/local/figure-inventory.json"
    assert paper.main(["inventory"]) == 0
    before = destination.stat().st_mtime_ns
    assert paper.main(["inventory"]) == 0
    assert destination.stat().st_mtime_ns == before
    inventory = json.loads(destination.read_text())
    assert len(inventory["workloads"]) == 4
    assert inventory["workloads"][-1]["unavailable_reason"] == "Source dependency is unavailable"
    assert inventory["workloads"][0]["iteration"] == 11
    assert not (tmp_path / ".reports.jsonl").exists()
    corpus["cases"][-1]["reason"] = "New source evidence"
    (tmp_path / "benchmarks/corpus/manifest.json").write_text(json.dumps(corpus))
    assert paper.main(["inventory"]) == 0
    assert destination.stat().st_mtime_ns != before
    assert "New source evidence" in destination.read_text()


def test_strict_metadata_is_identity_bound_and_can_be_cleared(tmp_path: Path) -> None:
    corpus = corpus_fixture(tmp_path)
    item = corpus["workloads"][0]
    outcome = {
        "file_sha256": item["sha256"],
        "fact_directory_sha256": "",
        "binary_sha256": "sha256:engine",
        "timeout_sec": 300,
        "disequality_encoding": "nee",
        "kind": "validation",
        "policy": "proof-testing-v1",
        "status": "failure",
        "reason": "Strict replay failed",
    }
    path = tmp_path / "benchmarks/corpus/.local/outcomes.json"
    path.parent.mkdir()
    path.write_text(json.dumps([outcome]))
    assert paper.figure_inventory(tmp_path, 300)["workloads"][0]["validation_failures"] == {
        "sha256:engine/300/nee": "Strict replay failed",
    }
    assert paper.figure_inventory(tmp_path, 120)["workloads"][0]["validation_failures"] == {}
    path.write_text(json.dumps([outcome, {**outcome, "status": "success"}]))
    assert paper.figure_inventory(tmp_path, 300)["workloads"][0]["validation_failures"] == {}


def test_parallel_make_orders_collectors_and_cached_render_rebuilds_only_changes(tmp_path: Path) -> None:
    shutil.copyfile(ROOT / "Makefile", tmp_path / "Makefile")
    figures = tmp_path / "figures/expanded"
    figures.mkdir(parents=True)
    for name in ("math-cutoff-11", "proof-overhead-cdf"):
        (figures / f"{name}.vl.json").write_text("{}\n")
    tools = tmp_path / "tools"
    tools.mkdir()
    script = """#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
root = Path(os.environ['PAPER_TEST_ROOT'])
args = sys.argv[1:]
with (root/'commands.jsonl').open('a') as f: f.write(json.dumps(args)+'\\n')
if 'benchmarks.paper' in args:
    if 'collect' in args:
        path = root/'.reports-grouped.json'
    else:
        path = root/'benchmarks/local/figure-inventory.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists(): path.write_text('{}')
else:
    command = 'vl2svg' if 'vl2svg' in args else 'vl2png'
    Path(args[args.index(command)+2]).write_text('rendered')
"""
    for name in ("uv", "npx"):
        path = tools / name
        path.write_text(script)
        path.chmod(0o755)
    env = {**os.environ, "PATH": str(tools) + os.pathsep + os.environ["PATH"], "PAPER_TEST_ROOT": str(tmp_path)}
    subprocess.run(["make", "-j8", "figures-all"], cwd=tmp_path, env=env, check=True, capture_output=True)
    commands = [json.loads(line) for line in (tmp_path / "commands.jsonl").read_text().splitlines()]
    collect = [args[args.index("--comparison") + 1] for args in commands if "collect" in args]
    assert collect == ["recording", "checked", "math"]
    assert len([args for args in commands if "vl2svg" in args or "vl2png" in args]) == 4
    (tmp_path / "commands.jsonl").write_text("")
    subprocess.run(["make", "-j8", "figures-all-cached"], cwd=tmp_path, env=env, check=True, capture_output=True)
    commands = [json.loads(line) for line in (tmp_path / "commands.jsonl").read_text().splitlines()]
    assert len(commands) == 1 and "inventory" in commands[0]
    (tmp_path / "commands.jsonl").write_text("")
    # macOS Make may compare only whole seconds; use a deterministic older
    # checkpoint rather than sleeping or depending on subsecond filesystem time.
    dependencies = [
        tmp_path / "Makefile",
        tmp_path / ".reports-grouped.json",
        tmp_path / "benchmarks/local/figure-inventory.json",
        *figures.iterdir(),
    ]
    for path in dependencies:
        os.utime(path, (1_700_000_000, 1_700_000_000))
    (figures / "math-cutoff-11.vl.json").write_text("{}\n\n")
    subprocess.run(["make", "-j8", "figures-all-cached"], cwd=tmp_path, env=env, check=True, capture_output=True)
    commands = [json.loads(line) for line in (tmp_path / "commands.jsonl").read_text().splitlines()]
    rendered = [args for args in commands if "vl2svg" in args or "vl2png" in args]
    assert len(rendered) == 2
    assert all("math-cutoff-11.vl.json" in args for args in rendered)
    (tmp_path / "commands.jsonl").write_text("")
    for path in dependencies:
        os.utime(path, (1_700_000_000, 1_700_000_000))
    (tmp_path / ".reports-grouped.json").write_text("{}\n")
    subprocess.run(["make", "-j8", "figures-all-cached"], cwd=tmp_path, env=env, check=True, capture_output=True)
    commands = [json.loads(line) for line in (tmp_path / "commands.jsonl").read_text().splitlines()]
    assert len([args for args in commands if "vl2svg" in args or "vl2png" in args]) == 4
