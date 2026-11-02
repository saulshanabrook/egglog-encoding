"""Enumerate bounded circuit cuts and turn their interfaces into BindInput terms."""

from dataclasses import dataclass
from itertools import chain, combinations
from pathlib import Path

from slotted.reference import render

from .ir import operation

LANGUAGE_PATH = Path(__file__).resolve().parents[2] / "egglog-experimental/tests/slotted/languages/churchroad.egg"
LANGUAGE = LANGUAGE_PATH.read_text()


def term(expr, boundary):
    if expr in boundary:
        return boundary[expr]
    if expr.op == "Input":
        raise ValueError(f"unbound circuit input {expr.data[0]}")
    data = expr.data
    if expr.op in {"ZeroExtend", "SignExtend"}:
        data = ()  # The result-width payload already carries the target width.
    if expr.op == "BV":
        value = data[0]
        if value >= 2**63:
            value -= 1 << expr.width
        if not -(2**63) <= value < 2**63:
            raise ValueError("Churchroad BV payload is outside Egglog's i64 range")
        data = (value,)
    return [expr.op, str(expr.width), *map(str, data), *(term(a, boundary) for a in expr.args)]


def bundle(roots, boundary):
    result = ["NoOutputs"]
    for root in reversed(roots):
        result = ["OutputCons", str(root.width), term(root, boundary), result]
    return result


@dataclass(frozen=True)
class Candidate:
    roots: tuple
    inputs: tuple
    depth: int

    def body(self, index):
        # Deliberately give occurrences different names. Deduplication is done
        # by the slotted engine, not by pre-canonicalizing these source terms.
        names = {expr: f"$m{index}_{i}" for i, expr in enumerate(self.inputs)}
        result = bundle(self.roots, names)
        for expr in reversed(self.inputs):
            result = ["BindInput", str(expr.width), names[expr], result]
        return result

    def legacy_key(self):
        """Independent Graph/Hole + occurrence-index-vector reference identity."""
        positions = {expr: i for i, expr in enumerate(self.inputs)}
        indices = []

        def graph(expr):
            if expr in positions:
                indices.append(positions[expr])
                return ("Hole", expr.width)
            return (expr.op, expr.width, expr.data, tuple(graph(a) for a in expr.args))

        graphs = tuple(graph(root) for root in self.roots)
        return tuple(e.width for e in self.inputs), graphs, tuple(indices)


def enumerate_modules(circuit, *, max_depth=2, max_inputs=4, max_candidates=256):
    if min(max_depth, max_inputs, max_candidates) <= 0:
        raise ValueError("module enumeration limits must be positive")
    nodes = [n for n in circuit.nodes() if n.args]
    # Equal-height roots keep module contraction acyclic. Shared-child pairs
    # include the adder's sum/carry and slices of one word, without all subsets.
    pairs = (
        pair
        for pair in combinations(nodes, 2)
        if pair[0].height == pair[1].height and set(pair[0].args) & set(pair[1].args)
    )
    groups = chain(pairs, ((n,) for n in nodes))
    found, seen = [], set()
    for roots in groups:
        for depth in range(1, max_depth + 1):
            boundary = {}

            def cut(expr, remaining, boundary=boundary):
                if expr.op == "BV":
                    return
                if remaining == 0 or expr.op == "Input":
                    boundary.setdefault(expr, None)
                    return
                for child in expr.args:
                    cut(child, remaining - 1)

            for root in roots:
                cut(root, depth)
            if len(boundary) > max_inputs:
                continue
            candidate = Candidate(tuple(roots), tuple(boundary), depth)
            key = candidate.roots, candidate.inputs
            if key in seen:
                continue
            seen.add(key)
            if len(found) == max_candidates:
                return found, True
            found.append(candidate)
    return found, False


def program(circuit, candidates):
    inputs = {expr: f"$port_{i}" for i, expr in enumerate(circuit.inputs.values())}
    lines = [LANGUAGE]
    for i, candidate in enumerate(candidates):
        body = candidate.body(i)
        lines.append(f"(let module_{i} {render(body)})")
        applied = f"module_{i}"
        for arg in candidate.inputs:
            applied = ["Apply", applied, term(arg, inputs)]
        lines.append(f"(let instance_{i} {render(applied)})")
        lines.append(f"(let expected_{i} {render(bundle(candidate.roots, inputs))})")
    rounds = max((len(c.inputs) for c in candidates), default=0) + 2
    lines.append(f"(run {rounds})")
    for i in range(len(candidates)):
        lines.append(f"(check (= instance_{i} expected_{i}))")
    lines += [f"(extract module_{i})" for i in range(len(candidates))]
    return "\n".join(lines) + "\n"


def decode_module(form):
    """Type-check the engine's extracted module before exporting hardware."""
    inputs = {}
    while isinstance(form, list) and form[0] == "BindInput":
        _, width, name, form = form
        if name in inputs:
            raise ValueError("extracted module shadows an input slot")
        inputs[name] = operation("Input", data=(f"in{len(inputs)}", int(width)))

    def expr(tree):
        if isinstance(tree, str):
            if tree not in inputs:
                raise ValueError(f"free slot in extracted module: {tree}")
            return inputs[tree]
        op, width, *args = tree
        width = int(width)
        if op == "BV":
            result = operation(op, data=(int(args[0]), width))
        elif op == "Extract":
            high, low, child = args
            result = operation(op, [expr(child)], (int(high), int(low)))
        elif op in {"ZeroExtend", "SignExtend"}:
            result = operation(op, [expr(args[0])], (width,))
        else:
            result = operation(op, [expr(a) for a in args])
        if result.width != width:
            raise ValueError(f"extracted {op} declares {width} bits, computes {result.width}")
        return result

    kind = form[0]
    if kind == "HalfAdder":
        _, order, a, b = form
        a, b = expr(a), expr(b)
        if (a.width, b.width) != (1, 1) or order not in {"0", "1"}:
            raise ValueError("invalid extracted half-adder interface")
        roots = [operation("Xor", [a, b]), operation("And", [a, b])]
        if order == "1":
            roots.reverse()
    elif kind == "SlicePair":
        _, w0, w1, h0, l0, h1, l1, value = form
        value = expr(value)
        roots = [operation("Extract", [value], (int(high), int(low))) for high, low in [(h0, l0), (h1, l1)]]
        if [r.width for r in roots] != [int(w0), int(w1)]:
            raise ValueError("invalid extracted slice-pair widths")
    else:
        roots = []
        while form != ["NoOutputs"]:
            if len(form) != 4 or form[0] != "OutputCons":
                raise ValueError(f"invalid extracted output bundle {form}")
            _, width, value, form = form
            value = expr(value)
            if value.width != int(width):
                raise ValueError("extracted output width disagrees with its expression")
            roots.append(value)
    return tuple(inputs.values()), tuple(roots), kind
