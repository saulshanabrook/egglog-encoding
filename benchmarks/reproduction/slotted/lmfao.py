"""Freeze original aggregate queries and query-independent join-tree metadata."""

import argparse
import json
from pathlib import Path

from benchmarking.lmfao import model

from . import ROOT, reference, sdql
from .workloads import Workload, ctor_lines

RULES = ROOT / "benchmarks/lmfao/logical.egg"


def symbol(name):
    return ["Symbol", json.dumps(name)]


def balanced(op, terms):
    assert terms
    while len(terms) > 1:
        terms = [[op, *terms[i : i + 2]] if i + 1 < len(terms) else terms[i] for i in range(0, len(terms), 2)]
    return terms[0]


def tree(op, leaves):
    if not leaves or len(leaves) & (len(leaves) - 1):
        raise ValueError("balanced vector needs a nonempty power-of-two length")
    return balanced(op, leaves)


def mask(indices, width):
    return tree("Mask", [["B1" if i in indices else "B0"] for i in range(width)])


def linked(values):
    result = ["Nil"]
    for value in reversed(values):
        result = ["Cons", value, result]
    return result


def source():
    src = reference.Source(RULES)
    base = sdql.reference_language()
    for name, op in src.lang.ops.items():
        op.ref = base.ops[name].ref if name in base.ops else name
        op.ref_prefix = base.ops[name].ref_prefix if name in base.ops else None
    return src


def input_terms(qs=None, roots=None, definition=model.WORKLOAD):
    attrs, relations, edges = definition.attributes, definition.relations, definition.edges
    names, tables = [a for a, _ in attrs], list(relations)
    functions = definition.functions
    owner = {a: next(t for t in tables if a in relations[t]) for a in names}
    aw, fw = 1 << (len(names) - 1).bit_length(), 1 << (len(functions) - 1).bit_length()
    neighbors = {t: [] for t in tables}
    for a, b in edges:
        neighbors[a].append(b)
        neighbors[b].append(a)

    def region(node, parent):
        children, members = [], {node}
        for child in neighbors[node]:
            if child != parent:
                subtree, child_members = region(child, node)
                members |= child_members
                separator = {names.index(a) for a in set(relations[node]) & set(relations[child])}
                children.append(["Neighbor", subtree, mask(separator, aw)])
        columns = {names.index(a) for t in members for a in relations[t]}
        subtree_functions = {i for i, (a, _) in enumerate(functions) if owner[a] in members}
        local_functions = {i for i, (a, _) in enumerate(functions) if owner[a] == node}
        return [
            "Region",
            symbol(node),
            symbol(parent),
            mask(columns, aw),
            mask(subtree_functions, fw),
            mask(local_functions, fw),
            linked(children),
        ], members

    domain = symbol("favorita")
    orientations = [["TreeRoot", domain, region(root, root)[0]] for root in (tables if roots is None else roots)]
    outputs = []
    for i, q in enumerate(definition.queries if qs is None else qs):
        requested = (
            [(q.factors[0], 2)] if len(q.factors) == 2 and q.factors[0] == q.factors[1] else [(a, 1) for a in q.factors]
        )
        weights = []
        for j in range(fw):
            if j >= len(functions) or functions[j] not in requested:
                weights.append(["WeightOne"])
                continue
            name, power = functions[j]
            row = f"$q{i}_function{j}"
            value = ["Get", row, symbol(name)]
            if power == 2:
                value = ["Mult", value, value]
            weights.append(["Scalar", symbol(owner[name]), ["Lambda", row, value]])
        query = ["AggregateQuery", domain, mask({names.index(k) for k in q.groups}, aw), tree("Weights", weights)]
        outputs.append(["Output", symbol(f"q{i}"), query])
    return ["Program", balanced("Pair", outputs)], orientations


def workload(mode="shared", *, rounds=64, qs=None, roots=None, definition=model.WORKLOAD):
    if mode not in ("single-root", "roots", "shared"):
        raise ValueError(mode)
    src = source()
    if roots is None and mode == "single-root":
        roots = [definition.root]
    inp, facts = input_terms(qs, roots, definition)
    rules = [
        f
        for f, _ in src.body
        if f[0] == "rewrite"
        and (mode != "roots" or f[f.index(":name") + 1] not in ('"logical-merge-views"', '"logical-distinct-columns"'))
    ]
    forms = [["sort", "U"], *src._ctors, *rules, ["let", "input", inp]]
    forms += [["let", f"schema{i}", fact] for i, fact in enumerate(facts)]
    forms.append(["run", str(rounds)])
    program = (
        ";;; Generated from benchmarks/lmfao/logical.egg; edit rules there.\n"
        ";;; Regenerate: uv run --locked python -m benchmarks.reproduction.slotted.lmfao\n"
        + "\n".join(reference.render(f) for f in forms)
        + "\n"
    )
    spec = [f"rounds {rounds}", *ctor_lines(src.lang)]
    spec += ["term " + src.lang.sexpr(src.term(term, ground=True)) for term in [inp, *facts]]
    spec += [line for rule in rules for line in reference.rule_lines(src, src.lang, rule)]
    return Workload(
        study="lmfao-logical",
        case=mode,
        rounds=rounds,
        rules=len(rules),
        program=program,
        graph_program=program,
        multi="\n".join(spec) + "\n",
        nested=None,
        unsupported_reason="root, pushdown and view-merging rules require multipatterns",
    )


def frozen(qs=None, modes=("single-root", "roots", "shared"), *, definition=model.WORKLOAD):
    files, variants = {}, []
    for mode in modes:
        w = workload(mode, qs=qs, definition=definition)
        files[f"{mode}.egg"] = w.program
        files[f"{mode}.ref"] = (
            json.dumps({"multi": w.multi, "nested": None, "unsupported_reason": w.unsupported_reason}, indent=2) + "\n"
        )
        variants.append({"name": mode, "file": f"{mode}.egg", "rewrite_round_budget": w.rounds})
    names = []
    for op in source().lang.ops.values():
        fields = [json.dumps(op.ref or ("=payload" if op.pays else op.ctor))]
        if op.ref_prefix:
            fields.append(json.dumps(op.ref_prefix))
        names.append(f"({op.ctor} {' '.join(fields)})")
    files["manifest.json"] = json.dumps({"variants": variants, "export_names": " ".join(names)}, indent=2) + "\n"
    return files


def ordinary(program, *, canonical):
    """Represent closed kernel binders as ordinary symbols, optionally alpha-normalized."""

    def term(value):
        if isinstance(value, list):
            return [term(v) for v in value]
        if value.startswith("$q"):
            return symbol("$row" if canonical else value)
        return value

    forms = reference.parse(program)
    for form in forms:
        if form[0] == "constructor" and ":binder" in form:
            del form[form.index(":binder") :]
    return (
        ";;; Generated ordinary representation of closed LMFAO kernels.\n"
        + "\n".join(reference.render(term(form)) for form in forms)
        + "\n"
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "benchmarks/lmfao/inputs")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--queries", type=int)
    parser.add_argument("--fixtures", action="store_true")
    args = parser.parse_args()
    qs = model.WORKLOAD.queries[: args.queries] if args.queries else None
    if args.fixtures:
        qs = [
            model.Query(),
            model.Query((), ("unit_sales",)),
            model.Query((), ("unit_sales", "oilprize")),
            model.Query(("family",)),
            model.Query(("family",), ("unit_sales",)),
            model.Query(("city",), ("oilprize", "oilprize")),
        ]
        args.output = ROOT / "benchmarks/lmfao/correctness"
    for name, contents in frozen(qs).items():
        path = args.output / name
        if args.check:
            if path.read_text() != contents:
                raise SystemExit(f"Frozen input differs: {path}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(contents)


if __name__ == "__main__":
    main()
