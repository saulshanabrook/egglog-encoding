"""Scoped rewrites must derive executable views and preserve natural-join bags."""

from __future__ import annotations

import json
import os
import random
import subprocess
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

import pytest

from benchmarking.lmfao import model, program
from benchmarking.native_memory import native_memory_command
from benchmarking.tests.test_lmfao import QUERIES, evaluate, join
from benchmarking.tests.test_lmfao import extractor_binary as extractor_binary


@pytest.mark.parametrize("mode", ["slotted", "debruijn"])
def test_scoped_plans_preserve_bags(mode: str, extractor_binary: Path, tmp_path: Path) -> None:
    source, destination = tmp_path / "input.egg", tmp_path / "plan.json"
    source.write_text(program.program(mode, queries=QUERIES))
    command, env = native_memory_command(
        [str(extractor_binary), "slotted" if mode == "slotted" else "off", str(source), str(destination), "10"],
        os.environ,
    )
    subprocess.run(command, env=env, check=True, timeout=180)
    plan = json.loads(destination.read_text())
    assert len(plan["outputs"]) == len(QUERIES)
    assert json.loads((tmp_path / "extraction.json").read_text())["solver"]["optimal"]
    rng = random.Random(804)
    for trial in range(20):
        data = {}
        for table, fields in model.WORKLOAD.relations.items():
            rows = [
                {
                    k: Fraction(rng.randrange(-3, 4), 2)
                    if k in {"unit_sales", "oilprize", "transactions"}
                    else rng.randrange(2)
                    for k in fields
                }
                for _ in range(trial % 4 + 1)
            ]
            data[table] = rows + [rows[0]]
        if trial == 19:
            data["Oil"] = []
        expected = []
        for query in QUERIES:
            answer: dict[tuple[int | Fraction, ...], Fraction] = defaultdict(Fraction)
            for row in join(list(data.values())):
                weight = Fraction(1)
                for factor in query.factors:
                    weight *= row[factor]
                answer[tuple(row[k] for k in query.groups)] += weight
            expected.append(answer)
        assert evaluate(plan, data) == expected


def test_hoisting_is_required_for_executable_lowering(extractor_binary: Path, tmp_path: Path) -> None:
    source = tmp_path / "input.egg"
    source.write_text(program.program(queries=QUERIES, hoist=False))
    command, env = native_memory_command(
        [str(extractor_binary), "slotted", str(source), str(tmp_path / "plan.json"), "5"], os.environ
    )
    result = subprocess.run(command, env=env, capture_output=True, text=True, timeout=180)
    assert result.returncode != 0
    assert "no executable alternative" in result.stderr


@pytest.mark.parametrize("mode", ["slotted", "debruijn"])
def test_fusion_derives_a_cheaper_shared_producer(mode: str, extractor_binary: Path, tmp_path: Path) -> None:
    costs = []
    # Compatible outputs are separated by an incompatible grouping. Their Oil
    # child also has two different kernels, so sharing must reach below roots.
    queries = [model.Query(), model.Query(("family",)), model.Query((), ("oilprize",))]
    for fusion in (False, True):
        directory = tmp_path / str(fusion)
        directory.mkdir()
        source, destination = directory / "input.egg", directory / "plan.json"
        source_text = program.program(mode, queries=queries, roots=["Sales"], fusion=fusion)
        if not fusion:
            # No rule may bypass tuple fusion to introduce a shared producer,
            # even if extraction would not select it.
            source_text += """
(constructor NoSharing () U)
(constructor FoundSharing () U)
(let observation (NoSharing))
(rewrite observation (FoundSharing) :when ((= view (SharedView region keys))))
(run 1)
(fail (check (= observation (FoundSharing))))
"""
        source.write_text(source_text)
        command, env = native_memory_command(
            [str(extractor_binary), "slotted" if mode == "slotted" else "off", str(source), str(destination), "10"],
            os.environ,
        )
        subprocess.run(command, env=env, check=True, timeout=120)
        plan = json.loads(destination.read_text())
        assert any(len(v["aggregates"]) > 1 for v in plan["views"]) == fusion
        if fusion:
            outputs = plan["outputs"]
            assert outputs[0]["view"] == outputs[2]["view"] != outputs[1]["view"]
            oil = list(model.WORKLOAD.relations).index("Oil")
            assert any(v["origin"] == oil and len(v["aggregates"]) == 2 for v in plan["views"])
        costs.append(json.loads((directory / "extraction.json").read_text())["estimated_cost"])
    assert costs[1] < costs[0]


def test_plan_replay_checks_actual_query_equalities(extractor_binary: Path, tmp_path: Path) -> None:
    queries = [model.Query(), model.Query((), ("oilprize",))]
    source, destination = tmp_path / "input.egg", tmp_path / "plan.json"
    original = program.program(queries=queries)
    source.write_text(original)
    command, env = native_memory_command(
        [str(extractor_binary), "slotted", str(source), str(destination), "10"], os.environ
    )
    subprocess.run(command, env=env, check=True, timeout=120)
    plan = model.read_plan(destination)
    claims = program.plan_checks(plan, queries)
    assert claims.count("(check (= input selected_batch))") == 1
    assert '(Symbol "q0")' in claims and '(Symbol "q1")' in claims
    assert "(union " not in claims
    source.write_text(original + claims)
    subprocess.run(command, env=env, check=True, timeout=120)
    # A different kernel must not pass merely because witness terms are inserted.
    source.write_text(
        original + "(constructor InvalidView (U U U U U) U)\n" + claims.replace("(ComputeView", "(InvalidView")
    )
    result = subprocess.run(command, env=env, text=True, capture_output=True, timeout=120)
    assert result.returncode != 0
