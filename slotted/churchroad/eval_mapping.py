"""Matched mapping encodings and complete concrete-graph comparison.

The specialization removes width guards, not matches: every possible width in the
supported source and the mapping rules' generated terms is enumerated. The named
specialization is a separate control so its effects are not attributed to slots.
"""

import json
from collections import defaultdict
from dataclasses import dataclass, field
from itertools import product

from slotted.reference import parse, render

DSP = {"DSP2", "DSP3"}
OPERATORS = {"Mul": 2, "Add": 2, "Shl": 2, "Shr": 2, "Concat": 2, "ZeroExtend": 1, "Extract": 1, "BV": 0}


def w(width, body):
    return ["W", str(width), body]


def encode(expr, slots):
    if expr.op == "Input":
        body = ["V", slots[expr.data[0]]]
    else:
        if expr.op not in OPERATORS:
            raise ValueError(f"mapping evaluation does not support {expr.op}")
        data = expr.data if expr.op == "Extract" else expr.data[:1] if expr.op == "BV" else ()
        body = [expr.op, *map(str, data), *(encode(child, slots) for child in expr.args)]
    return w(expr.width, body)


def specialized(circuit, slotted):
    names = {name: f"$p{i}" if slotted else json.dumps(name) for i, name in enumerate(circuit.inputs)}
    variable_type = "E" if slotted else "String"
    binder = "(Bind i64 E E :binder 0)" if slotted else ""
    declarations = f"""(datatype E (W i64 E) (V {variable_type}) (BV i64) (Extract i64 i64 E)
      (ZeroExtend E) (Mul E E) (Add E E) (Shl E E) (Shr E E) (Concat E E)
      (DSP2 E E) (DSP3 E E E) (Root String E) {binder})
    """
    prefix = "" if slotted else "$"
    inputs = [f"(let {prefix}port_{i} {render(encode(expr, names))})" for i, expr in enumerate(circuit.inputs.values())]
    for ordinal, (name, expr) in enumerate(circuit.outputs.items()):
        body = encode(expr, names)
        if slotted:
            for i, port in reversed(list(enumerate(circuit.inputs))):
                body = ["Bind", str(i), names[port], body]
        inputs.append(render(["let", f"{prefix}result_{ordinal}", ["Root", json.dumps(name), body]]))
    widths = {expr.width for expr in circuit.nodes()}
    # Only the transform rule creates new widths, through its two Extracts.
    widths |= {n // 2 for n in widths if n <= 32 and n % 2 == 0}
    rules = []

    def rewrite(left, right, guards=()):
        condition = " :when (" + " ".join(render(g) for g in guards) + ")" if guards else ""
        rules.append(f"(rewrite {render(left)} {render(right)}{condition})")

    # Preserve native declaration-time global lookup (a/b may be input globals).
    globals_ = {name: f"{prefix}port_{i}" for i, name in enumerate(circuit.inputs)}
    a, b = globals_.get("a", "a"), globals_.get("b", "b")
    for n in sorted(widths):
        if n < 18:
            rewrite(w(n, ["Mul", a, b]), w(n, ["DSP2", a, b]))
        if n < 36:
            for aw, bw in product(sorted(widths), repeat=2):
                if max(aw, bw) > 16:
                    continue
                x, y = w(aw, "x"), w(bw, "y")
                mul = w(n, ["Mul", w(n, ["ZeroExtend", x]), w(n, ["ZeroExtend", y])])
                rewrite(mul, w(n, ["DSP2", x, y]))
                for cw in sorted(widths):
                    if cw <= 48:
                        z = w(cw, "z")
                        rewrite(w(n, ["Add", "m", z]), w(n, ["DSP3", x, y, z]), [["=", "m", mul]])
        if n <= 32 and n % 2 == 0:
            for aw in sorted(widths):
                if aw > 16:
                    continue
                # Mul's typing requires both operands and the result to have width n.
                guards = [["=", a, w(aw, "av")], ["=", b, w(n, "bv")]]
                lo = w(n // 2, ["Extract", str(n // 2 - 1), "0", b])
                hi = w(n // 2, ["Extract", str(n - 1), str(n // 2), b])
                za = w(n, ["ZeroExtend", a])
                low = w(n, ["Mul", za, w(n, ["ZeroExtend", lo])])
                high = w(n, ["Mul", za, w(n, ["ZeroExtend", hi])])
                rhs = w(n, ["Add", low, w(n, ["Shl", high, w(n, ["BV", str(n // 2)])])])
                rewrite(w(n, ["Mul", za, b]), rhs, guards)
    return declarations, "\n".join(inputs), "\n".join(rules)


@dataclass(frozen=True, order=True)
class Node:
    op: str
    data: tuple = ()
    children: tuple = ()


@dataclass
class ConcreteGraph:
    nodes: dict = field(default_factory=lambda: defaultdict(set))
    widths: dict = field(default_factory=dict)
    outputs: dict = field(default_factory=dict)

    def reachable(self):
        pending, seen = list(self.outputs.values()), set()
        while pending:
            cid = pending.pop()
            if cid in seen:
                continue
            seen.add(cid)
            for node in self.nodes[cid]:
                pending.extend(node.children)
        return seen

    def representatives(self):
        best = {}
        reachable = self.reachable()
        while True:
            updated = False
            for cid in reachable:
                for node in self.nodes[cid]:
                    if node.op in DSP or any(c not in best for c in node.children):
                        continue
                    term = (node.op, self.widths[cid], node.data, tuple(best[c][1] for c in node.children))
                    choice = (1 + sum(best[c][0] for c in node.children), repr(term))
                    if cid not in best or choice < best[cid]:
                        best[cid] = choice
                        updated = True
            if not updated:
                break
        if set(best) != reachable:
            raise ValueError("mapped graph has no finite behavioral representative for every reachable class")
        return {cid: value[1] for cid, value in best.items()}

    def signature(self):
        if not self.outputs:
            raise ValueError("mapped graph has no outputs")
        reachable = self.reachable()
        if any(node.op in DSP for cid, nodes in self.nodes.items() if cid not in reachable for node in nodes):
            raise ValueError("DSP proposals outside the output cone are not supported by this evaluation")
        reps = self.representatives()
        rows = set()
        proposals = set()
        for cid in self.reachable():
            for node in self.nodes[cid]:
                row = (reps[cid], node.op, self.widths[cid], node.data, tuple(reps[c] for c in node.children))
                rows.add(row)
                if node.op in DSP:
                    proposals.add(row)
        return {
            "nodes": sorted(rows),
            "proposals": sorted(proposals),
            "outputs": {n: reps[c] for n, c in self.outputs.items()},
        }

    def bridge_program(self):
        """Reconstitute the mapped state for the unchanged native synthesis bridge."""
        reps = self.representatives()
        classes = sorted(reps, key=lambda c: reps[c])
        names = {cid: f"evalc{i}" for i, cid in enumerate(classes)}
        lines = []

        def expression(cid, node):
            children = [names[c] for c in node.children]
            if node.op == "Input":
                return ["Var", json.dumps(node.data[0]), str(self.widths[cid])]
            if node.op in DSP:
                return ["PrimitiveInterfaceDSP" + ("3" if node.op == "DSP3" else ""), *children]
            data = node.data
            if node.op in {"ZeroExtend", "SignExtend"}:
                data = (self.widths[cid],)
            if node.op == "BV":
                data = (*data, self.widths[cid])
            return [f"Op{len(children)}", [node.op, *map(str, data)], *children]

        # Use finite behavioral representatives as the initial nodes. Wire
        # placeholders break the native spec extractor: it tracks node IDs and
        # refuses to select Wire nodes, including those used by DSP interfaces.
        declared = set()

        def declare(cid):
            if cid in declared:
                return
            node = next(
                n
                for n in self.nodes[cid]
                if n.op not in DSP
                and repr((n.op, self.widths[cid], n.data, tuple(reps[c] for c in n.children))) == reps[cid]
            )
            for child in node.children:
                declare(child)
            lines.append(render(["let", names[cid], expression(cid, node)]))
            declared.add(cid)

        for cid in classes:
            declare(cid)
        for cid in classes:
            for node in sorted(self.nodes[cid], key=lambda n: (n.op, repr(n.data), tuple(reps[c] for c in n.children))):
                lines.append(render(["union", names[cid], expression(cid, node)]))
                if node.op == "Input":
                    lines.append(f'(IsPort "" {json.dumps(node.data[0])} (Input) {names[cid]})')
        lines += [f'(IsPort "" {json.dumps(n)} (Output) {names[c]})' for n, c in self.outputs.items()]
        lines.append("(run-schedule (saturate (seq typing misc)))")
        return "\n".join(lines)


def native_graph(document):
    graph = ConcreteGraph()
    nodes = document["nodes"]

    def literal(nid):
        return json.loads(nodes[nid]["op"])

    for node in nodes.values():
        op, args = node["op"], node["children"]
        cid = node["eclass"]
        if op == "HasType":
            typ = nodes[args[1]]
            if typ["op"] == "Bitvector":
                graph.widths[nodes[args[0]]["eclass"]] = literal(typ["children"][0])
        elif op == "IsPort" and nodes[args[2]]["op"] == "Output":
            graph.outputs[literal(args[1])] = nodes[args[3]]["eclass"]
        elif op == "Var":
            graph.nodes[cid].add(Node("Input", (literal(args[0]),)))
        elif op in {"Op0", "Op1", "Op2", "Op3"}:
            operator = nodes[args[0]]
            data = tuple(literal(a) for a in operator["children"])
            if operator["op"] in {"ZeroExtend", "SignExtend"}:
                data = ()
            if operator["op"] == "BV":
                data = data[:1]
            graph.nodes[cid].add(Node(operator["op"], data, tuple(nodes[a]["eclass"] for a in args[1:])))
        elif op in {"PrimitiveInterfaceDSP", "PrimitiveInterfaceDSP3"}:
            graph.nodes[cid].add(
                Node("DSP3" if op.endswith("3") else "DSP2", (), tuple(nodes[a]["eclass"] for a in args))
            )
    return graph


def specialized_graph(document, input_names):
    """Instantiate logical slot maps from closed, input-bound output roots."""
    graph = ConcreteGraph()
    nodes = document["nodes"]
    classes = defaultdict(list)
    for nid, node in nodes.items():
        classes[node["eclass"]].append(nid)
    slots = document.get("slotted")
    payloads = {"W": 1, "V": 0 if slots else 1, "BV": 1, "Extract": 2, "Root": 1, "Bind": 1}

    def parts(nid, env):
        node = nodes[nid]
        if slots:
            label = parse(node["op"])[0]
            op, data = (label[0], tuple(json.loads(s) for s in label[1:])) if isinstance(label, list) else (label, ())
            annotations = slots["nodes"][nid]["arguments"]
            bound = [a["slot"] for a in annotations if a["kind"] == "slot"]
            local = dict(env)
            if op == "Bind":
                local[bound[0]] = input_names[data[0]]
            child_maps = [
                dict((a, local[b]) for a, b in arg["renaming"]) for arg in annotations if arg["kind"] == "child"
            ]
            children = [(nodes[c]["eclass"], mapping) for c, mapping in zip(node["children"], child_maps, strict=True)]
            if op == "var":
                data = (local[bound[0]],)
        else:
            op = node["op"]
            n = payloads.get(op, 0)
            data = tuple(json.loads(nodes[c]["op"]) for c in node["children"][:n])
            children = [(nodes[c]["eclass"], {}) for c in node["children"][n:]]
        return op, data, children

    def variable(cid, env):
        values = {parts(n, env)[1][0] for n in classes[cid] if parts(n, env)[0] == "var"}
        if len(values) != 1:
            raise ValueError("an input slot did not identify exactly one original input")
        return values.pop()

    def visit(cid, env):
        key = repr((cid, sorted(env.items())))
        if key in graph.widths:
            return key
        for nid in classes[cid]:
            op, data, children = parts(nid, env)
            if op == "Bind":
                return visit(*children[0])
            if op != "W":
                raise ValueError(f"expected typed expression, found {op}")
            width = data[0]
            if key in graph.widths and graph.widths[key] != width:
                raise ValueError("equality merged different widths")
            graph.widths[key] = width
            inner, mapping = children[0]
            for body in classes[inner]:
                operator, payload, args = parts(body, mapping)
                if operator == "V":
                    name = variable(*args[0]) if slots else payload[0]
                    graph.nodes[key].add(Node("Input", (name,)))
                else:
                    graph.nodes[key].add(Node(operator, payload, tuple(visit(*arg) for arg in args)))
        return key

    for nid, node in nodes.items():
        if node["op"] == "Root" or node["op"].startswith("(Root "):
            _, data, children = parts(nid, {})
            graph.outputs[data[0]] = visit(*children[0])
    if not graph.outputs:
        raise ValueError("export contains no output roots")
    return graph
