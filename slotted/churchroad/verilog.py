"""Export original circuits and extracted module instances as synthesizable Verilog."""

import re
from collections import Counter

from .ir import Circuit
from .modules import decode_module


def identifier(name):
    if not name or any(c.isspace() for c in name):
        raise ValueError(f"cannot export Verilog identifier {name!r}")
    return name if re.fullmatch(r"[a-zA-Z_][a-zA-Z_0-9$]*", name) else f"\\{name} "


def expression(expr, args):
    op, width = expr.op, expr.width
    if op == "BV":
        return f"{width}'d{expr.data[0]}"
    binary = {
        "And": "&",
        "Or": "|",
        "Xor": "^",
        "Add": "+",
        "Sub": "-",
        "Mul": "*",
        "Eq": "==",
        "Ne": "!=",
        "Shl": "<<",
        "Shr": ">>",
        "LogicAnd": "&&",
        "LogicOr": "||",
    }
    unary = {"Not": "~", "ReduceOr": "|", "ReduceAnd": "&", "ReduceXor": "^", "LogicNot": "!"}
    if op in binary:
        return f"({args[0]} {binary[op]} {args[1]})"
    if op in unary:
        return f"({unary[op]}{args[0]})"
    if op == "Concat":
        return "{" + ", ".join(args) + "}"
    if op == "Mux":
        return f"({args[0]} ? {args[2]} : {args[1]})"
    if op == "Extract":
        return f"{args[0]}[{expr.data[0]}:{expr.data[1]}]"
    if op == "ZeroExtend":
        extra = width - expr.args[0].width
        return args[0] if not extra else f"{{{{{extra}{{1'b0}}}}, {args[0]}}}"
    if op == "SignExtend":
        return f"$signed({args[0]})"
    raise ValueError(f"cannot export {op} to Verilog")


def select_instances(candidates, identities, kinds):
    counts = Counter(identities)
    choices = sorted(
        range(len(candidates)),
        key=lambda i: (kinds[i] not in {"HalfAdder", "SlicePair"}, -len(candidates[i].roots), -candidates[i].depth, i),
    )
    selected = {}
    for i in choices:
        candidate = candidates[i]
        if counts[identities[i]] < 2 and kinds[i] not in {"HalfAdder", "SlicePair"}:
            continue
        if any(root in selected for root in candidate.roots):
            continue
        for output, root in enumerate(candidate.roots):
            selected[root] = (i, output)
    return selected


def emit_circuit(circuit, name, *, candidates=(), identities=(), selected=None):
    if set(circuit.inputs) & set(circuit.outputs):
        raise ValueError("an input and output cannot have the same Verilog port name")
    selected = selected or {}
    cache = {expr: identifier(port) for port, expr in circuit.inputs.items()}
    declarations, statements, used, active = [], [], set(), set()
    serial = 0

    def wire(width):
        nonlocal serial
        while f"cr_wire_{serial}" in circuit.inputs or f"cr_wire_{serial}" in circuit.outputs:
            serial += 1
        result = f"cr_wire_{serial}"
        serial += 1
        declarations.append(f"  wire [{width - 1}:0] {result};")
        return result

    def emit(expr):
        if expr in cache:
            return cache[expr]
        if expr in active:
            raise ValueError("module selection introduced a circuit cycle")
        active.add(expr)
        if expr in selected:
            i, _ = selected[expr]
            candidate = candidates[i]
            inputs = [emit(a) for a in candidate.inputs]
            outputs = [wire(root.width) for root in candidate.roots]
            cache.update(zip(candidate.roots, outputs, strict=True))
            connections = [f".in{j}({a})" for j, a in enumerate(inputs)]
            connections += [f".out{j}({a})" for j, a in enumerate(outputs)]
            instance_name = f"cr_instance_{i}"
            while instance_name in circuit.inputs or instance_name in circuit.outputs:
                instance_name += "_"
            statements.append(f"  cr_module_{identities[i]} {instance_name} ({', '.join(connections)});")
            used.add(i)
        else:
            children = [emit(a) for a in expr.args]
            cache[expr] = wire(expr.width)
            statements.append(f"  assign {cache[expr]} = {expression(expr, children)};")
        active.remove(expr)
        return cache[expr]

    for port, expr in circuit.outputs.items():
        value = emit(expr)
        statements.append(f"  assign {identifier(port)} = {value};")
    ports = [f"input wire [{expr.width - 1}:0] {identifier(port)}" for port, expr in circuit.inputs.items()]
    ports += [f"output wire [{expr.width - 1}:0] {identifier(port)}" for port, expr in circuit.outputs.items()]
    source = f"module {identifier(name)} (\n  " + ",\n  ".join(ports) + ");\n"
    return source + "\n".join(declarations + statements) + "\nendmodule\n", used


def export(circuit, candidates, extracted):
    modules, identities, kinds = {}, [], []
    for candidate, form in zip(candidates, extracted, strict=True):
        inputs, outputs, kind = decode_module(form)
        if tuple(e.width for e in inputs) != tuple(e.width for e in candidate.inputs):
            raise ValueError("extraction changed the module's ordered input signature")
        if tuple(e.width for e in outputs) != tuple(e.width for e in candidate.roots):
            raise ValueError("extraction changed the module's ordered output signature")
        key = inputs, outputs
        if key not in modules:
            modules[key] = len(modules)
        identities.append(modules[key])
        kinds.append(kind)
    selected = select_instances(candidates, identities, kinds)
    mapped, used = emit_circuit(circuit, "mapped", candidates=candidates, identities=identities, selected=selected)
    used_modules = {identities[i] for i in used}
    definitions = []
    for (inputs, outputs), i in modules.items():
        if i in used_modules:
            module = Circuit({e.data[0]: e for e in inputs}, {f"out{j}": e for j, e in enumerate(outputs)})
            definitions.append(emit_circuit(module, f"cr_module_{i}")[0])
    original = emit_circuit(circuit, "reference")[0]
    legacy_to_slotted, slotted_to_legacy = {}, {}
    for candidate, identity in zip(candidates, identities, strict=True):
        legacy = candidate.legacy_key()
        legacy_to_slotted.setdefault(legacy, set()).add(identity)
        slotted_to_legacy.setdefault(identity, set()).add(legacy)
    if any(len(v) != 1 for v in [*legacy_to_slotted.values(), *slotted_to_legacy.values()]):
        raise ValueError("slotted module identities disagree with the Graph/Hole reference partition")
    stats = {
        "candidate_occurrences": len(candidates),
        "legacy_unique_templates": len(legacy_to_slotted),
        "slotted_unique_templates": len(modules),
        "legacy_partition_matches": True,
        "recognized_candidates": dict(Counter(k for k in kinds if k in {"HalfAdder", "SlicePair"})),
        "emitted_instances": len(used),
        "emitted_module_definitions": len(used_modules),
        "emitted_recognized_instances": dict(Counter(kinds[i] for i in used if kinds[i] in {"HalfAdder", "SlicePair"})),
    }
    return original, "\n".join(definitions + [mapped]), stats
