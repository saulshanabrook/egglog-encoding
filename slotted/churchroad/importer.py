"""Read circuit-building commands emitted by Churchroad's Yosys plugin.

This imports the frontend's wiring, not arbitrary Egglog programs. Typing/misc
schedules and extraction requests are accepted; executable optimization rules
or other schedules are rejected instead of silently discarded.
"""

import json
from functools import lru_cache

from slotted.reference import parse, render

from .ir import Circuit, operation


def import_egg(source, outputs=()):
    parents, nodes, names, interned, ports = [], [], {}, {}, []

    def find(i):
        while parents[i] != i:
            parents[i] = parents[parents[i]]
            i = parents[i]
        return i

    def term(form):
        if isinstance(form, str):
            if form not in names:
                raise ValueError(f"unknown Churchroad binding {form!r}")
            return names[form]
        head, *args = form
        if head in {"Var", "Wire"}:
            name, width = args
            node = (head, (json.loads(name), int(width)), ())
        elif head in {"Op0", "Op1", "Op2", "Op3"}:
            operator, *children = args
            if len(children) != int(head[-1]):
                raise ValueError(f"malformed Churchroad application: {render(form)}")
            op, *data = operator
            node = (op, tuple(map(int, data)), tuple(term(c) for c in children))
        else:
            raise ValueError(f"unsupported Churchroad expression: {render(form)}")
        if node not in interned:
            interned[node] = len(nodes)
            parents.append(len(nodes))
            nodes.append(node)
        return interned[node]

    def typing_schedule(form):
        if isinstance(form, str):
            return form in {"typing", "misc"} or form.isdecimal()
        return (
            bool(form)
            and form[0] in {"run-schedule", "seq", "saturate", "repeat", "run"}
            and all(typing_schedule(a) for a in form[1:])
        )

    try:
        forms = parse(source)
    except (IndexError, RecursionError) as error:
        raise ValueError("malformed Churchroad s-expression") from error
    for form in forms:
        match form:
            case ["let", name, value]:
                if name in names:
                    raise ValueError(f"duplicate Churchroad binding {name}")
                names[name] = term(value)
            case ["union", a, b]:
                left, right = find(term(a)), find(term(b))
                parents[right] = left
            case ["IsPort", module, name, [direction], value]:
                if direction not in {"Input", "Output"}:
                    raise ValueError(f"unsupported port direction {direction}")
                ports.append((json.loads(module), json.loads(name), direction, term(value)))
            case ["delete", ["Wire", *_]]:
                pass  # Wires are resolved through their equivalence class below.
            case ["run-schedule", *_] if typing_schedule(form):
                pass  # Width checks are performed by operation().
            case ["extract", _] | ["query-extract", ["HasType", *_]]:
                pass
            case _:
                raise ValueError(f"unsupported Churchroad frontend command: {render(form)}")

    members = {}
    for i, node in enumerate(nodes):
        members.setdefault(find(i), []).append(node)
    if len({module for module, _, _, _ in ports}) > 1:
        raise ValueError("multiple Churchroad modules; select one top module before importing")
    input_ports, input_names = {}, {}
    for _, name, direction, i in ports:
        if direction == "Input":
            root = find(i)
            if root in input_ports and input_ports[root] != name:
                raise ValueError("aliased input ports need an explicit interface adaptation")
            if name in input_names and input_names[name] != root:
                raise ValueError(f"input port {name!r} names distinct wires")
            input_ports[root] = name
            input_names[name] = root
    active = set()

    @lru_cache(None)
    def resolve(root):
        if root in active:
            raise ValueError("cyclic Churchroad circuit has no finite combinational representation")
        active.add(root)
        try:
            entries = members[root]
            declared = {data[1] for op, data, _ in entries if op in {"Var", "Wire"}}
            if len(declared) > 1:
                raise ValueError(f"inconsistent wire widths: {sorted(declared)}")
            variables = {data for op, data, _ in entries if op == "Var"}
            if len(variables) > 1:
                raise ValueError("distinct primary inputs were unioned")
            if root in input_ports or variables:
                if any(op not in {"Var", "Wire"} for op, _, _ in entries):
                    raise ValueError("a primary input has a circuit definition")
                name = input_ports.get(root, next(iter(variables))[0] if variables else "")
                return operation("Input", data=(name, next(iter(declared))))
            choices = []
            for op, data, children in entries:
                if op == "Reg":
                    raise ValueError("sequential Reg is unsupported; select an explicitly combinational root")
                if op != "Wire":
                    choices.append(operation(op, [resolve(find(c)) for c in children], data))
            if not choices:
                raise ValueError(f"unconnected Churchroad wire: {entries}")
            if declared and any(e.width not in declared for e in choices):
                raise ValueError("wire width disagrees with its circuit definition")
            # Raw frontend aliases should identify the same syntactic circuit.
            if len(set(choices)) != 1:
                raise ValueError("multiple circuit definitions require Egglog evaluation before import")
            return choices[0]
        finally:
            active.remove(root)

    selected = {}
    if outputs:
        for name in outputs:
            if name not in names:
                raise ValueError(f"unknown requested output binding {name!r}")
            selected[name] = resolve(find(names[name]))
    else:
        for module, name, direction, i in ports:
            if direction == "Output":
                if name in selected:
                    raise ValueError(f"duplicate output port {module}.{name}")
                selected[name] = resolve(find(i))
    if not selected:
        raise ValueError("no output ports; specify the frontend's output bindings with --outputs")
    inputs = {}
    for root in members:
        if root in input_ports or any(op == "Var" for op, _, _ in members[root]):
            expr = resolve(root)
            name = expr.data[0]
            if name in inputs and inputs[name] != expr:
                raise ValueError(f"input name {name!r} has inconsistent widths")
            inputs[name] = expr
    return Circuit(inputs, selected)
