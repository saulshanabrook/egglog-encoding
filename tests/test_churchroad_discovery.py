"""Discovery semantics and strict reporting; live engines run in make slotted-test."""

import importlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

discovery = importlib.import_module("slotted.churchroad.discovery")
evaluation = importlib.import_module("slotted.churchroad.discovery_eval")
ir = importlib.import_module("slotted.churchroad.ir")
ROOT = Path(__file__).resolve().parents[1]


def test_generated_ripple_preserves_arithmetic_and_independent_copies() -> None:
    circuit = evaluation.generated_ripple(3, 2)
    for a in range(8):
        for b in range(8):
            inputs = {"a0": a, "b0": b, "a1": 7 - a, "b1": 7 - b}
            for i in range(2):
                total = inputs[f"a{i}"] + inputs[f"b{i}"]
                assert ir.evaluate(circuit.outputs[f"sum{i}"], inputs) == total % 8
                assert ir.evaluate(circuit.outputs[f"carry{i}"], inputs) == total // 8


def test_reference_preserves_native_shared_underscore_restriction() -> None:
    a, b = [ir.operation("Input", data=(name, 1)) for name in "ab"]
    left = ir.operation("Not", [a])
    right = ir.operation("And", [a, b])
    out = ir.operation("Or", [left, right])
    nodes = discovery.source_nodes(ir.Circuit({"a": a, "b": b}, {"out": out}))
    rows = discovery.reference(nodes, 4)
    templates = {json.loads(row[1])[0] for row in rows}
    assert "(Or)" in templates
    # Incorporating both children requires equal interface vectors: [0] != [0,1].
    target = discovery.canonical(("(Or)", (("(Not)", (("Hole", 0),)), ("(And)", (("Hole", 0), ("Hole", 2))))))[0]
    assert target not in {r[1] for r in rows}
    assert len(discovery.reference(nodes, 1)) < len(rows)


def test_signatures_preserve_argument_aliases_order_and_root_membership() -> None:
    separate = discovery.canonical(("(And)", (("Hole", 3), ("Hole", 8))))
    renamed = discovery.canonical(("(And)", (("Hole", 9), ("Hole", 2))))
    repeated = discovery.canonical(("(And)", (("Hole", 3), ("Hole", 3))))
    assert separate[0] == renamed[0]
    assert separate[1] != renamed[1]
    assert separate[0] != repeated[0]


def test_cached_slotted_templates_keep_each_instances_boundary_and_reject_collapsing_maps() -> None:
    document = {
        "nodes": {
            "v": {"op": "var", "eclass": "variable", "children": []},
            "m": {"op": '(Node2 "(And)")', "eclass": "module", "children": ["v", "v"]},
        },
        "slotted": {
            "classes": {"variable": {"slots": ["0"]}, "module": {"slots": ["0", "1"]}},
            "nodes": {
                "m": {
                    "arguments": [
                        {"kind": "child", "renaming": [["0", "0"]]},
                        {"kind": "child", "renaming": [["0", "1"]]},
                    ]
                }
            },
        },
    }
    rows = [{"root": i, "class": "module", "bindings": [[0, 10 * i], [1, 10 * i + 1]]} for i in [1, 2]]
    result = discovery.signature(document, rows)
    assert result[0][1] == result[1][1]
    assert [r[2] for r in result] == [(10, 11), (20, 21)]
    rows[1]["bindings"] = [[0, 20], [1, 20]]
    with pytest.raises(ValueError, match="bijectively"):
        discovery.signature(document, rows)


def test_parity_and_summary_do_not_accept_partial_or_missing_runs() -> None:
    rows: list[dict[str, Any]] = [
        dict(treatment=t, sample=s, status="success", signature_sha256="same")
        for t in ["native", "slotted"]
        for s in range(2)
    ]
    assert evaluation.parity(rows, ["native", "slotted"], 2) == "passed"
    assert evaluation.parity(rows[:-1], ["native", "slotted"], 2) == "not-established"
    rows[0]["signature_sha256"] = "different"
    assert evaluation.parity(rows, ["native", "slotted"], 2) == "failed"
    rows[0]["status"] = "error"
    assert evaluation.parity(rows, ["native", "slotted"], 2) == "not-established"
    summary = evaluation.summarize([dict(treatment="slotted", status="error", discovery_sec=0.001)])
    assert summary["slotted"]["discovery_sec_median"] is None


@pytest.mark.parametrize(
    "extra", [["--samples", "0"], ["--rounds", "0"], ["--timeout", "nan"], ["--treatments", "native", "native"]]
)
def test_discovery_cli_rejects_bad_limits_before_loading_toolchain(tmp_path: Path, extra: list[str]) -> None:
    result = subprocess.run(
        [
            sys.executable,
            str(ROOT / "churchroad-eval.py"),
            "discovery",
            "--output-dir",
            str(tmp_path / "out"),
            "--toolchain",
            str(tmp_path / "absent"),
            *extra,
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 2
    assert "positive" in result.stderr or "duplicate" in result.stderr
    assert not (tmp_path / "out").exists()


def test_discovery_help_has_no_hardware_dependency() -> None:
    result = subprocess.run(
        [sys.executable, str(ROOT / "churchroad-eval.py"), "discovery", "--help"],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0
    assert "--rounds" in result.stdout and "--treatments" in result.stdout
