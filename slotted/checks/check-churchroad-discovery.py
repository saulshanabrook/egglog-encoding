#!/usr/bin/env python3
"""Check live vector/slotted discovery against independent bounded tree search."""

import json
import random
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from slotted.churchroad.discovery import encoding, reference, signature, source_nodes  # noqa: E402
from slotted.churchroad.discovery_eval import bound_templates, generated_ripple  # noqa: E402
from slotted.churchroad.evaluation import execute  # noqa: E402
from slotted.churchroad.ir import Circuit, operation  # noqa: E402


def cases():
    a, b, c = [operation("Input", data=(name, 1)) for name in "abc"]
    const = operation("BV", data=(0, 1))
    x = operation("And", [a, b])
    y = operation("And", [a, a])
    yield Circuit({"a": a, "b": b}, {"out": operation("Or", [operation("Not", [a]), x])})
    yield Circuit({"a": a, "b": b, "c": c}, {"out": operation("Mux", [c, x, y]), "constant": const})
    yield generated_ripple(2, 2)
    for seed in range(5):
        rng = random.Random(seed)
        terms = [a, b, c, const]
        for _ in range(4):
            op = rng.choice(["Not", "Xor", "And", "Or", "Mux"])
            n = 1 if op == "Not" else 3 if op == "Mux" else 2
            terms.append(operation(op, [rng.choice(terms) for _ in range(n)]))
        yield Circuit({"a": a, "b": b, "c": c}, {"out": terms[-1], "other": terms[-2]})


def main():
    worker = ROOT / "target/debug/examples/churchroad_discovery"
    count = 0
    with tempfile.TemporaryDirectory(prefix="churchroad-discovery-check-") as temp:
        for case, circuit in enumerate(cases()):
            nodes = source_nodes(circuit)
            for rounds in [1, 2, 4]:
                expected = reference(nodes, rounds)
                for treatment in ["vector", "slotted-eager", "slotted"]:
                    directory = Path(temp) / f"{case}-{rounds}-{treatment}"
                    directory.mkdir()
                    request = dict(
                        **encoding(nodes, treatment != "vector"),
                        directory=str(directory),
                        rounds=rounds,
                        eager_maintenance=treatment == "slotted-eager",
                    )
                    (directory / "request.json").write_text(json.dumps(request))
                    execute(
                        [str(worker), str(directory / "request.json")],
                        directory,
                        "worker",
                        30,
                        {"RAYON_NUM_THREADS": "1"},
                    )
                    actual = signature(
                        json.loads((directory / "graph.json").read_text()),
                        json.loads((directory / "candidates.json").read_text()),
                    )
                    assert actual == expected, (case, rounds, treatment, len(actual), len(expected))
                    count += 1
                if case < 2:
                    # The reusable exported interfaces must really bind every
                    # input, including repeated arguments and zero-input modules.
                    program = bound_templates(expected)
                    for i, _ in enumerate(sorted({r[1] for r in expected})):
                        program += f"(check (free-names-are module_{i}))\n"
                    (directory / "templates.egg").write_text(program)
                    execute(
                        [str(ROOT / "target/debug/egglog-experimental"), "--slotted", str(directory / "templates.egg")],
                        directory,
                        "interfaces",
                        30,
                        {"RAYON_NUM_THREADS": "1"},
                    )
    print(f"OK: {count}/{count} live discovery searches matched the independent oracle; exported binders are closed.")


if __name__ == "__main__":
    main()
