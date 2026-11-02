"""Parity, grounding, and failure reporting for the independent DSP evaluator."""

import copy
import importlib
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

mapping = importlib.import_module("slotted.churchroad.eval_mapping")
evaluation = importlib.import_module("slotted.churchroad.evaluation")
import_egg = importlib.import_module("slotted.churchroad.importer").import_egg
ir = importlib.import_module("slotted.churchroad.ir")
ROOT = Path(__file__).resolve().parents[1]


def multiply_graph(*, alias: bool = False, width: int = 8, prefix: str = "") -> Any:
    graph = mapping.ConcreteGraph()
    a, b, out = (prefix + x for x in ("a", "b", "out"))
    graph.nodes[a].add(mapping.Node("Input", ("a",)))
    graph.nodes[b].add(mapping.Node("Input", ("b",)))
    graph.nodes[out].add(mapping.Node("Mul", (), (a, a if alias else b)))
    graph.widths.update({a: width, b: width, out: width})
    graph.outputs["out"] = out
    return graph


def test_signatures_ignore_internal_ids_but_preserve_widths_and_aliases() -> None:
    expected = multiply_graph().signature()
    assert expected == multiply_graph(prefix="renumbered").signature()
    assert expected != multiply_graph(alias=True).signature()
    assert expected != multiply_graph(width=16).signature()


def test_signatures_compare_candidate_membership_not_just_counts() -> None:
    first, second = multiply_graph(), multiply_graph()
    first.nodes["out"].add(mapping.Node("DSP2", (), ("a", "b")))
    second.nodes["out"].add(mapping.Node("DSP2", (), ("b", "a")))
    assert len(first.signature()["proposals"]) == len(second.signature()["proposals"]) == 1
    assert first.signature() != second.signature()


def test_parity_rejects_a_dropped_dead_proposal() -> None:
    graph = multiply_graph()
    graph.nodes["dead"].add(mapping.Node("DSP2", (), ("a", "b")))
    with pytest.raises(ValueError, match="outside the output cone"):
        graph.signature()


def test_slot_grounding_uses_edge_maps_and_bound_port_order() -> None:
    # The two operands share the same alpha-equivalent input e-class. Only
    # their edge renamings distinguish a*b from a*a.
    document = json.loads((ROOT / "tests/fixtures/churchroad-slotted-mul.json").read_text())
    grounded = mapping.specialized_graph(document, ["a", "b"])
    assert grounded.signature() == multiply_graph().signature()
    alias = copy.deepcopy(document)
    alias["slotted"]["nodes"]["E/n4"]["arguments"][1] = alias["slotted"]["nodes"]["E/n4"]["arguments"][0]
    assert mapping.specialized_graph(alias, ["a", "b"]).signature() == multiply_graph(alias=True).signature()
    assert mapping.specialized_graph(document, ["b", "a"]).signature() != grounded.signature()


def test_bridge_preserves_behavior_without_wire_placeholders() -> None:
    graph = multiply_graph()
    source = graph.bridge_program()
    # Native EnsureExtractSpecExtractor tracks node IDs and excludes Wire.
    assert "(Wire " not in source
    circuit = import_egg(source)
    for a, b in [(0, 255), (1, 1), (255, 255), (17, 23)]:
        assert ir.evaluate(circuit.outputs["out"], {"a": a, "b": b}) == a * b % 256


def test_specialization_preserves_native_global_lookup_and_closes_inputs() -> None:
    circuit = import_egg((ROOT / "slotted/churchroad/fixtures/wide-mul.egg").read_text())
    named = mapping.specialized(circuit, False)
    slots = mapping.specialized(circuit, True)
    assert '(V "a")' in named[1]
    assert "(Bind 0 $p0 (Bind 1 $p1" in slots[1]
    assert "(Mul $port_0 $port_1)" in named[2]
    assert "(Mul port_0 port_1)" in slots[2]
    assert " :when ((= m " in slots[2]  # DSP3's multipattern joins an equivalent multiply.


def test_downstream_failure_does_not_erase_mapping_parity_or_phase_data() -> None:
    rows = [
        {
            "treatment": treatment,
            "status": "error",
            "signature_sha256": "same-complete-graph",
            "pipeline_wall_sec": 9.0,
            "phases_sec": {"eqsat": 0.003},
            "rosette_phases_sec": {"solve": 2.5},
            "tool_phases_sec": {"racket": 8.5},
        }
        for treatment in ["native", "slotted"]
    ]
    assert evaluation.mapping_parity(rows) == "passed"
    summary = evaluation.summarize(rows)["native"]
    assert summary["successful"] == 0
    assert summary["pipeline_completed"] == 1
    assert summary["eqsat_median_sec"] == 0.003
    assert summary["solver_query_median_sec"] == 2.5
    partial = {**rows[0], "rosette_phases_sec": {"solve": 0.01}, "tool_phases_sec": {"racket": 0.02}}
    del partial["pipeline_wall_sec"]
    summary = evaluation.summarize([rows[0], partial])["native"]
    assert summary["attempted"] == 2
    assert summary["pipeline_completed"] == 1
    assert summary["solver_query_median_sec"] == 2.5  # No mixing partial and complete synthesis totals.
    rows[1]["signature_sha256"] = "different"
    assert evaluation.mapping_parity(rows) == "failed"
    del rows[1]["signature_sha256"]
    assert evaluation.mapping_parity(rows) == "not-established"


@pytest.mark.parametrize("extra", [["--samples", "0"], ["--timeout", "nan"], ["--top", "x;bad"]])
def test_cli_rejects_invalid_requests_before_toolchain_work(tmp_path: Path, extra: list[str]) -> None:
    result = subprocess.run(
        [sys.executable, str(ROOT / "churchroad-eval.py"), "--output-dir", str(tmp_path / "report"), *extra],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 2
    assert not result.stdout
    assert "Churchroad evaluation:" in result.stderr
    assert not (tmp_path / "report").exists()


def test_cli_help_needs_no_hardware_dependencies() -> None:
    result = subprocess.run(
        [sys.executable, str(ROOT / "churchroad-eval.py"), "--help"],
        capture_output=True,
        text=True,
        check=True,
    )
    assert "--mapping-only" in result.stdout
    assert "typed-named" in result.stdout


@pytest.mark.skipif(sys.platform != "linux", reason="Linux child subreaper")
def test_supervision_reaps_orphaned_solver_children(tmp_path: Path) -> None:
    process = importlib.import_module("benchmarks.reproduction.reproduction_process")
    pid_file = tmp_path / "child.pid"
    source = (
        "import os,time,pathlib\n"
        "child=os.fork()\n"
        "if child == 0: time.sleep(30)\n"
        f"else: pathlib.Path({str(pid_file)!r}).write_text(str(child))\n"
    )
    with evaluation.reap_descendants():
        result = process.run_bounded_command([sys.executable, "-c", source], ROOT, tmp_path / "process", timeout_sec=5)
    assert result.status == "success"
    child = int(pid_file.read_text())
    with pytest.raises(ChildProcessError):
        os.waitpid(child, os.WNOHANG)
    assert not Path(f"/proc/{child}").exists()
