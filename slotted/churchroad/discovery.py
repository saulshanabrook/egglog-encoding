"""Churchroad's single-output module enumeration, with matched bounded searches.

The Python code lowers the input DAG and checks results; it does not enumerate
candidates for either timed engine. Discovery runs as joins in Egglog. Slotted
construction uses the existing lowered encoding and its node-shape primitive.
"""

import json
from collections import defaultdict
from functools import cache
from itertools import product

from slotted.reference import parse, render


def source_nodes(circuit):
    expressions = circuit.nodes()
    ids = {expr: i for i, expr in enumerate(expressions)}
    nodes = []
    for expr in expressions:
        data = expr.data
        if expr.op == "Input":
            data = (*data, expr.width)
        elif expr.op == "BV":
            value = data[0]
            if value >= 2**63:
                value -= 1 << expr.width
            if not -(2**63) <= value < 2**63:
                raise ValueError("BV literal exceeds Churchroad's i64 payload")
            data = (value, expr.width)
        nodes.append(dict(id=ids[expr], op=expr.op, data=data, children=[ids[a] for a in expr.args], width=expr.width))
    return nodes


def operator(node):
    return render([node["op"], *map(str, node["data"])])


def native_input(nodes):
    lines = ["(function DiscoverySource (Expr) i64 :merge (min old new))"]
    for node in nodes:
        i, children = node["id"], node["children"]
        if node["op"] == "Input":
            name, width = node["data"]
            value = f"(Var {json.dumps(name)} {width})"
            # Var_ is deliberately distinct from Var in the upstream experiment.
            lines.append(f"(set (DiscoverySource (Var_ {json.dumps(name)} {width})) {len(nodes) + i})")
        else:
            value = f"(Op{len(children)} {operator(node)} {' '.join(f'disc{c}' for c in children)})"
        lines += [f"(let disc{i} {value})", f"(set (DiscoverySource disc{i}) {i})"]
    return "\n".join(lines)


def encoding(nodes, slots):
    declarations = "(datatype M " + " ".join(f"(Node{n} String {' '.join(['M'] * n)})" for n in range(4)) + ")"
    if not slots:
        declarations += "\n(constructor Hole () M)\n(sort IVec (Vec i64))\n(datatype Module (MakeModule M IVec))"
    carrier, environment = ("M", "Renaming") if slots else ("Module", "IVec")
    inputs = [f"(function Candidate (i64 {carrier} {environment}) Unit :no-merge)", "(ruleset enumerate)"]
    inputs += [f"(relation Source{n} (i64 String {' '.join(['i64'] * n)}))" for n in range(4)]
    inputs.append("(relation SourceVar (i64 i64))")
    if slots:
        inputs += [
            "(function Interface (M) IVec :no-merge)",
            "(ruleset interfaces)",
            "(set (Interface (SlottedVar_0 0)) (vec-of 0))",
        ]
    for node in nodes:
        i = node["id"]
        if node["op"] == "Input":
            inputs.append(f"(SourceVar {i} {len(nodes) + i})")
        else:
            inputs.append(
                f"(Source{len(node['children'])} {i} {json.dumps(operator(node))} "
                f"{' '.join(map(str, node['children']))})"
            )
    hole = "(SlottedVar_0 0)" if slots else "(Hole)"
    variable = f"{hole} (map-of 0 leaf)" if slots else "(MakeModule (Hole) (vec-of 0)) (vec-of leaf)"
    rules = [f"(rule ((SourceVar root leaf)) ((set (Candidate root {variable}) ())) :ruleset enumerate)"]
    for n in range(4):
        for incorporate in product([False, True], repeat=n):
            premises = [f"(Source{n} root op {' '.join(f'c{i}' for i in range(n))})"]
            children, edges = [], []
            for i, expand in enumerate(incorporate):
                if expand:
                    # `_` is one shared variable in the pinned native engine,
                    # not a fresh wildcard for each child. Preserve that join.
                    module = f"t{i}" if slots else f"(MakeModule t{i} indices)"
                    premises.append(f"(Candidate c{i} {module} a{i})")
                    if slots:
                        premises.append(f"(= indices (Interface t{i}))")
                    children.append(f"t{i}")
                    edges.append(f"a{i}")
                else:
                    children.append(hole)
                    edges.append(f"(map-of 0 c{i})" if slots else f"(vec-of c{i})")
            actions = []
            if slots and n:
                # Building directly in canonical frames avoids materializing an
                # extra template for every concrete boundary naming. This is
                # the existing slotted runtime, not a Churchroad name primitive.
                groups = [f"g{i}" for i in range(n)]
                premises += [f"(= {g} (EclassGroup_0 {child}))" for g, child in zip(groups, children, strict=True)]
                actions.append(f"(let sh (node-shape (vec-of {' '.join(edges)}) (vec-of {' '.join(groups)})))")
                body = f"(Node{n} op {' '.join(f'(vec-get sh {i}) {child}' for i, child in enumerate(children))})"
                args = f"(vec-get sh {n})"
            elif slots:
                body, args = "(Node0 op)", "(map-empty)"
            else:
                body = f"(Node{n} op {' '.join(children)})"
                args = "(vec-empty)" if not n else f"(vec-append (vec-empty) {' '.join(edges)})"
                actions.append(f"(let args {args})")
                body, args = f"(MakeModule {body} (debruijnify args))", "args"
            actions.append(f"(set (Candidate root {body} {args}) ())")
            rules.append(f"(rule ({' '.join(premises)}) ({' '.join(actions)}) :ruleset enumerate)")
        if slots:
            operands = " ".join(f"m{i} t{i}" for i in range(n))
            guards = " ".join(f"(= xs{i} (Interface t{i}))" for i in range(n))
            traces = " ".join(f"(interface-rename xs{i} m{i})" for i in range(n))
            trace = f"(vec-append (vec-empty) {traces})" if n else "(vec-empty)"
            public = "(map-empty)"
            for i in range(n):
                public = f"(map-union {public} (map-image m{i}))"
            # Canonical ordered templates never union or acquire symmetries.
            # Initialize metadata once per template, not once per application.
            # This also prepares child metadata before the next discovery round.
            rules.append(
                f"(rule ((= t (Node{n} op {operands})) {guards}) "
                f"((set (Interface t) {trace}) (let public {public}) "
                "(set (FreeVars_0 t) public) (set (EclassGroup_0 t) (set-of public)) "
                "(RenamesToLeader_0 t public t)) :ruleset interfaces)"
            )
    return dict(declarations=declarations, input="\n".join(inputs), rules="\n".join(rules), slotted=slots)


def canonical(body):
    """Return a template and ordered boundary occurrences, preserving aliases."""
    names, arguments = {}, []

    def visit(term):
        if term[0] == "Hole":
            arg = term[1]
            arguments.append(arg)
            return ("Hole", names.setdefault(arg, len(names)))
        return (term[0], tuple(visit(child) for child in term[1]))

    template = visit(body)
    return json.dumps(template, separators=(",", ":")), tuple(arguments)


def signature(document, candidates=None):
    """Compare every (source root, module, boundary occurrence vector), not counts."""
    nodes = document["nodes"]
    classes = defaultdict(list)
    for nid, node in nodes.items():
        classes[node["eclass"]].append(nid)
    slotted = document.get("slotted")
    result = set()

    def unique(cid, allowed=None):
        choices = [nid for nid in classes[cid] if allowed is None or nodes[nid]["op"] in allowed]
        if len(choices) != 1:
            raise ValueError(f"expected exactly one template node in {cid}: {choices}")
        return choices[0]

    def literal(nid):
        return json.loads(nodes[nid]["op"])

    def vector(nid):
        node = nodes[nid]
        if node["op"] not in {"vec-of", "vec-empty", "ExprVec", "IVec"}:
            raise ValueError(f"expected vector: {node}")
        return node["children"]

    if slotted:

        def tree(cid, env):
            nid = unique(cid)
            node = nodes[nid]
            if node["op"] == "var":
                (slot,) = slotted["classes"][cid]["slots"]
                return ("Hole", env[slot])
            label = parse(node["op"])[0]
            op = json.loads(label[1])
            children = []
            for child, edge in zip(node["children"], slotted["nodes"][nid]["arguments"], strict=True):
                mapping = edge["renaming"]
                # Logical exports spell each edge as a list of [child, parent].
                local = {a: env[b] for a, b in mapping}
                children.append(tree(nodes[child]["eclass"], local))
            return (op, tuple(children))

        @cache
        def module(cid):
            slots = slotted["classes"][cid]["slots"]
            return canonical(tree(cid, {slot: slot for slot in slots}))

        for row in candidates:
            template, occurrences = module(row["class"])
            env = {str(k): v for k, v in row["bindings"]}
            if set(env) != set(occurrences) or len(set(env.values())) != len(env):
                raise ValueError("candidate slot map must bijectively name the template's live inputs")
            args = tuple(env[slot] for slot in occurrences)
            result.add((row["root"], template, args))
    else:
        source_ids = {}
        if candidates is None:
            # Read the primitive output via its class, not the opaque value ID.
            for node in nodes.values():
                if node["op"] == "DiscoverySource":
                    value = next(literal(nid) for nid in classes[node["eclass"]] if not nodes[nid]["children"])
                    source_ids[nodes[node["children"][0]]["eclass"]] = value
            candidates = []
            for node in nodes.values():
                if node["op"] != "apply":
                    continue
                if node["eclass"] not in source_ids:
                    # Upstream constructs empty vectors by popping Var unused/0.
                    # That implementation sentinel itself gets an identity module.
                    sentinel = [nodes[n] for n in classes[node["eclass"]] if nodes[n]["op"] == "Var"]
                    if not any([literal(a) for a in n["children"]] == ["unused", 0] for n in sentinel):
                        raise ValueError("native discovery produced a candidate outside the frozen source graph")
                    continue
                candidates.append(
                    {
                        "root": source_ids[node["eclass"]],
                        "class": nodes[node["children"][0]]["eclass"],
                        "arguments": [source_ids[nodes[a]["eclass"]] for a in vector(node["children"][1])],
                    }
                )

        def tree(nid, args):
            node = nodes[nid]
            if node["op"] == "Hole":
                return ("Hole", next(args))
            children = node["children"]
            if node["op"].startswith("Node"):
                op = literal(children[0])
            else:
                operator_node = nodes[children[0]]
                op = render([operator_node["op"], *(nodes[c]["op"] for c in operator_node["children"])])
            return (op, tuple(tree(c, args) for c in children[1:]))

        @cache
        def module(cid):
            graph, vector_id = nodes[unique(cid, {"MakeModule"})]["children"]
            indices = tuple(literal(a) for a in vector(vector_id))
            remaining = iter(indices)
            try:
                body = tree(graph, remaining)
            except StopIteration as error:
                raise ValueError("module has more holes than index entries") from error
            if next(remaining, None) is not None:
                raise ValueError("module has fewer holes than index entries")
            return canonical(body)[0], indices

        for row in candidates:
            template, indices = module(row["class"])
            actuals = tuple(row["arguments"])
            expected, seen = [], {}
            for a in actuals:
                expected.append(seen.setdefault(a, len(seen)))
            if tuple(expected) != indices:
                raise ValueError("native module index vector disagrees with its argument aliases")
            result.add((row["root"], template, actuals))
    return sorted(result)


def reference(nodes, rounds):
    """Small independent oracle for tests: explicit trees, no e-graph machinery."""
    found = {n["id"]: set() for n in nodes}
    for _ in range(rounds):
        following = {i: set(terms) for i, terms in found.items()}
        for node in nodes:
            i = node["id"]
            if node["op"] == "Input":
                following[i].add(("Hole", len(nodes) + i))
            else:
                choices = [[(("Hole", c), False), *((t, True) for t in found[c])] for c in node["children"]]
                for choice in product(*choices):
                    interfaces = []
                    for body, expand in choice:
                        if expand:
                            _, args = canonical(body)
                            seen = {}
                            interfaces.append(tuple(seen.setdefault(a, len(seen)) for a in args))
                    if len(set(interfaces)) <= 1:
                        following[i].add((operator(node), tuple(t for t, _ in choice)))
        found = following
    return sorted((i, *canonical(body)) for i, bodies in found.items() for body in bodies)
