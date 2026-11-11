"""Translate LMFAO queries into egglog inputs and generate selected-plan equality checks."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from benchmarks.reproduction.slotted import reference

from . import model

RULES = model.FIXTURES / "logical.egg"
DEFAULT_ROUNDS = 192
INPUTS = model.FIXTURES / "inputs"
SOURCE_FIELDS = {
    "Reduce": [0, 1],
    "Scan": [],
    "Lookup": [2],
    "Product": [0, 1],
    "One": [],
    "GroupKey": [0],
    "FunctionValue": [0],
    "ViewLookup": [2],
    "Tuple": [0, 1],
    "First": [0],
    "Second": [0],
    "FusionCandidate": [1, 2],
    # Lowering admits bodies whose only free variable is the row it binds.
    # Root nodes and view kernels are therefore closed; child nodes expose
    # only their parent row. Reindexing must handle these lowered terms too.
    "AggregateQuery": [],
    "ComputeView": [],
    "SharedView": [],
    "ViewColumn": [],
    "BuildRoot": [],
    "FinishRoot": [],
    "ShareRoot": [],
    "BuildChild": [2],
    "FinishChild": [2],
    "ShareChild": [2],
}
BINDERS = {"Reduce": 2, "Lambda": 1, "BuildRoot": 2, "BuildChild": 4}


def symbol(name: str) -> list[str]:
    return ["Symbol", json.dumps(name)]


def balanced(op: str, terms: list[Any]) -> Any:
    assert terms
    while len(terms) > 1:
        terms = [[op, *terms[i : i + 2]] if i + 1 < len(terms) else terms[i] for i in range(0, len(terms), 2)]
    return terms[0]


def tree(op: str, leaves: list[Any]) -> Any:
    if not leaves or len(leaves) & (len(leaves) - 1):
        raise ValueError("balanced vector needs a nonempty power-of-two length")
    return balanced(op, leaves)


def mask(indices: set[int], width: int) -> Any:
    return tree("Mask", [["B1" if i in indices else "B0"] for i in range(width)])


def linked(values: list[Any]) -> Any:
    result: Any = ["Nil"]
    for value in reversed(values):
        result = ["Cons", value, result]
    return result


def input_terms(
    qs: list[model.Query] | None = None,
    roots: list[str] | None = None,
    definition: model.Workload = model.WORKLOAD,
) -> tuple[Any, list[Any]]:
    attrs, relations, edges = definition.attributes, definition.relations, definition.edges
    names, tables = [a for a, _ in attrs], list(relations)
    functions = definition.functions
    owner = {a: next(t for t in tables if a in relations[t]) for a in names}
    aw, fw = 1 << (len(names) - 1).bit_length(), 1 << (len(functions) - 1).bit_length()
    neighbors: dict[str, list[str]] = {t: [] for t in tables}
    for a, b in edges:
        neighbors[a].append(b)
        neighbors[b].append(a)

    def region(node: str, parent: str) -> tuple[Any, set[str]]:
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
        weights: list[Any] = []
        for j in range(fw):
            if j >= len(functions) or functions[j] not in requested:
                weights.append(["WeightOne"])
                continue
            name, power = functions[j]
            row = f"$q{i}_function{j}"
            value: Any = ["Get", ["V", row], symbol(name)]
            if power == 2:
                value = ["Mult", value, value]
            weights.append(["Scalar", symbol(owner[name]), ["Lambda", row, value]])
        query = ["AggregateQuery", domain, mask({names.index(k) for k in q.groups}, aw), tree("Weights", weights)]
        outputs.append(["Output", symbol(f"q{i}"), query])
    return ["Program", balanced("Pair", outputs)], orientations


def debruijn(term: Any, scope: tuple[str, ...] = ()) -> Any:
    if isinstance(term, str):
        return term
    if term[0] == "V":
        return ["Var", str(scope[::-1].index(term[1]))]
    if term[0] in ("Reduce", "Lambda"):
        index = 2 if term[0] == "Reduce" else 1
        return [term[0], *[debruijn(v, scope) for v in term[1:index]], debruijn(term[-1], (*scope, term[index]))]
    return [debruijn(v, scope) for v in term]


def name(form: Any) -> str | None:
    return json.loads(form[form.index(":name") + 1]) if ":name" in form else None


def ordinary_rules(forms: list[Any]) -> list[Any]:
    """Use explicit shifts/swaps for source terms; backend metadata is closed."""
    result = []
    for form in forms:
        if form[0] == "constructor":
            if form[1] == "V":
                continue
            if ":binder" in form:
                if form[1] in BINDERS:
                    form = form.copy()
                    form[2] = form[2].copy()
                    del form[2][BINDERS[form[1]] - 1]
                form = form[: form.index(":binder")]
            result.append(form)
        elif name(form) not in {
            "scoped-hoist-left",
            "scoped-hoist-right",
            "scoped-hoist-constant",
            "scoped-interchange",
        }:

            def erase(t: Any) -> Any:
                if isinstance(t, str):
                    return t
                if t and t[0] == "V":
                    assert t[1] == "$row"
                    return ["Var", "0"]
                if t and t[0] == "free-names-are":
                    return ["=", ["Within", erase(t[1]), "1" if len(t) == 3 else "0"], "true"]
                if t and isinstance(t[0], str) and t[0] in BINDERS:
                    index = BINDERS[t[0]]
                    return [erase(v) for i, v in enumerate(t) if i != index]
                return [erase(x) for x in t]

            result.append(erase(form))
    result += reference.parse("""
(constructor Var (i64) U :cost 0)
(constructor Shift (U i64 i64) U :cost 100000)
(constructor Swap (U i64) U :cost 100000)
(relation NeedAbsent (U i64))
(function Absent (U i64) bool :merge (or old new))
(relation NeedWithin (U i64))
(function Within (U i64) bool :merge (or old new))
(rule ((NeedWithin e k)) ((set (Within e k) false)))
(rule ((NeedWithin e k) (= e (Var i)) (< i k)) ((set (Within e k) true)))
(rule ((Reduce rows body)) ((NeedWithin body 0) (NeedWithin body 1)))
(rule ((NeedAbsent e k)) ((set (Absent e k) false)))
(rule ((NeedAbsent e k) (= e (Var i)) (!= i k)) ((set (Absent e k) true)))
(rule ((Reduce rows body)) ((NeedAbsent body 0)))
(rule ((Reduce rows body) (= body (Product a b))) ((NeedAbsent a 0) (NeedAbsent b 0)))
(rule ((Reduce rows body) (= body (Reduce s x))) ((NeedAbsent s 0)))
(rewrite (Shift x 0 k) x)
(rewrite (Shift (Var i) d k) (Var i) :when ((< i k)))
(rewrite (Shift (Var i) d k) (Var (+ i d)) :when ((>= i k)))
(rewrite (Swap (Var i) k) (Var (+ k 1)) :when ((= i k)))
(rewrite (Swap (Var i) k) (Var k) :when ((= i (+ k 1))))
(rewrite (Swap (Var i) k) (Var i) :when ((!= i k) (!= i (+ k 1))))
(rewrite total (Product (Shift factor -1 0) (Reduce rows rest)) :name "scoped-hoist-left"
 :when ((= total (Reduce rows body)) (= body (Product factor rest)) (= (Absent factor 0) true)))
(rewrite total (Product (Reduce rows rest) (Shift factor -1 0)) :name "scoped-hoist-right"
 :when ((= total (Reduce rows body)) (= body (Product rest factor)) (= (Absent factor 0) true)))
(rewrite total (Product (Shift body -1 0) (Reduce rows (One))) :name "scoped-hoist-constant"
 :when ((= total (Reduce rows body)) (= (Absent body 0) true)))
(rewrite total (Reduce (Shift s -1 0) (Reduce (Shift r 1 0) (Swap body 0)))
 :name "scoped-interchange"
 :when ((= total (Reduce r inner)) (= inner (Reduce s body)) (= (Absent s 0) true)))
""")
    constructors = {f[1]: len(f[2]) for f in result if f[0] == "constructor"}
    for op, children in SOURCE_FIELDS.items():
        args = [f"a{i}" for i in range(constructors[op])]
        term = f"({op} {' '.join(args)})"

        def level(i: int, operator: str = op) -> str:
            return "(+ k 1)" if operator == "Reduce" and i == 1 else "k"

        for helper, params in [("Shift", "d k"), ("Swap", "k")]:
            mapped = [
                f"({helper} {a} {'d ' if helper == 'Shift' else ''}{level(i)})" if i in children else a
                for i, a in enumerate(args)
            ]
            result += reference.parse(f"(rewrite ({helper} {term} {params}) ({op} {' '.join(mapped)}))")
        needs = " ".join(f"(NeedAbsent {args[i]} {level(i)})" for i in children)
        if needs:
            result += reference.parse(f"(rule ((NeedAbsent e k) (= e {term})) ({needs}))")
        guards = " ".join(f"(= (Absent {args[i]} {level(i)}) true)" for i in children)
        result += reference.parse(f"(rule ((NeedAbsent e k) (= e {term}) {guards}) ((set (Absent e k) true)))")
        needs = " ".join(f"(NeedWithin {args[i]} {level(i)})" for i in children)
        if needs:
            result += reference.parse(f"(rule ((NeedWithin e k) (= e {term})) ({needs}))")
        guards = " ".join(f"(= (Within {args[i]} {level(i)}) true)" for i in children)
        result += reference.parse(f"(rule ((NeedWithin e k) (= e {term}) {guards}) ((set (Within e k) true)))")
    return [f for f in result if f[0] not in ("rewrite", "rule")] + [f for f in result if f[0] in ("rewrite", "rule")]


def program(
    mode: str = "slotted",
    *,
    queries: list[model.Query] | None = None,
    roots: list[str] | None = None,
    rounds: int = DEFAULT_ROUNDS,
    hoist: bool = True,
    interchange: bool = True,
    fusion: bool = True,
    definition: model.Workload = model.WORKLOAD,
) -> str:
    queries = definition.queries if queries is None else queries
    names = [a for a, _ in definition.attributes]
    tables = list(definition.relations)
    owner = {a: next(t for t in tables if a in definition.relations[t]) for a in names}
    aw = 1 << (len(names) - 1).bit_length()
    fw = 1 << (len(definition.functions) - 1).bit_length()
    rw = 1 << (len(tables) - 1).bit_length()
    inp, orientations = input_terms(queries, roots, definition)
    outputs = []
    regions: dict[str, str] = {}
    declarations: list[Any] = []

    def region_global(term: Any) -> str:
        key = reference.render(term)
        if key not in regions:

            def nested(value: Any) -> Any:
                if isinstance(value, list):
                    return region_global(value) if value[0] == "Region" else [nested(v) for v in value]
                return value

            value = [term[0], *[nested(v) for v in term[1:]]]
            regions[key] = f"region{len(regions)}"
            declarations.append(["let", regions[key], value])
        return regions[key]

    def collect(t: Any) -> None:
        if t[0] == "Pair":
            collect(t[1])
            collect(t[2])
        else:
            outputs.append(t[2])

    collect(inp[1])
    empty_weights = tree("Weights", [["WeightOne"] for _ in range(fw)])
    empty_kids = tree("Kids", [["NoChild"] for _ in range(rw)])
    facts = [["EmptyParts", ["Parts", mask(set(), aw), empty_weights, empty_weights, empty_kids]]]
    for i, table in enumerate(tables):
        path: Any = ["Here"]
        for bit in range(rw.bit_length() - 1):
            path = ["Right" if i & (1 << bit) else "Left", path]
        facts.append(["RelationPosition", symbol(table), mask({i}, rw), path])
        facts.extend(
            ["AttributeInfo", symbol(table), symbol(attr), mask({names.index(attr)}, aw)]
            for attr in definition.relations[table]
        )
    for i, (attr, power) in enumerate(definition.functions):
        row = "$kernel"
        body: Any = ["Get", ["V", row], symbol(attr)]
        if power == 2:
            body = ["Mult", body, body]
        weights = [
            ["Scalar", symbol(owner[attr]), ["Lambda", row, body]] if j == i else ["WeightOne"] for j in range(fw)
        ]
        facts.append(["FunctionInfo", symbol(owner[attr]), symbol(f"f{i}"), tree("Weights", weights)])

    def children(region: Any) -> list[tuple[Any, Any]]:
        result = []
        items = region[-1]
        while items[0] == "Cons":
            result.append((items[1][1], items[1][2]))
            items = items[2]
        return result

    for qi, (query, qterm) in enumerate(zip(queries, outputs, strict=True)):
        requested = (
            [(query.factors[0], 2)]
            if len(query.factors) == 2 and query.factors[0] == query.factors[1]
            else [(a, 1) for a in query.factors]
        )
        for orientation in orientations:
            traversal: list[Any] = []
            variables = {t: f"$q{qi}_{t}" for t in tables}

            def visit(
                region: Any,
                parent: str | None = None,
                separator: Any = None,
                variables: Any = variables,
                traversal: Any = traversal,
            ) -> None:
                table = json.loads(region[1][1])
                row = variables[table]
                domain = (
                    ["Scan", region_global(region)]
                    if parent is None
                    else ["Lookup", region_global(region), separator, ["V", variables[parent]]]
                )
                traversal.append((domain, row))
                for child, sep in children(region):
                    visit(child, table, sep)

            visit(orientation[2])
            factors = [["GroupKey", ["V", variables[owner[a]]], symbol(a)] for a in query.groups]
            factors += [
                ["FunctionValue", ["V", variables[owner[a]]], symbol(f"f{i}")]
                for i, (a, p) in enumerate(definition.functions)
                if (a, p) in requested
            ]
            body = balanced("Product", factors) if factors else ["One"]
            for domain, row in reversed(traversal):
                body = ["Reduce", domain, row, body]
            facts.append(["Lowering", qterm, body])
    forms = reference.parse(RULES.read_text())
    if not hoist:
        forms = [f for f in forms if not (name(f) or "").startswith("scoped-hoist")]
    if not interchange:
        forms = [f for f in forms if name(f) != "scoped-interchange"]
    if not fusion:
        forms = [f for f in forms if name(f) != "scoped-fuse"]
    if mode == "debruijn":
        forms = ordinary_rules(forms)
        inp = debruijn(inp)
        facts = [debruijn(f) for f in facts]
        if not hoist:
            forms = [f for f in forms if not (name(f) or "").startswith("scoped-hoist")]
        if not interchange:
            forms = [f for f in forms if name(f) != "scoped-interchange"]
    forms = [f for f in forms if f[0] not in ("rewrite", "rule")] + [f for f in forms if f[0] in ("rewrite", "rule")]
    forms += declarations
    forms += [["let", "input", inp]]
    forms += [["let", "batch", balanced("Tuple", [debruijn(q) if mode == "debruijn" else q for q in outputs])]]
    forms += [["let", f"metadata{i}", fact] for i, fact in enumerate(facts)]
    forms += [["run", str(rounds)]]
    return "\n".join(reference.render(f) for f in forms) + "\n"


def plan_checks(plan: dict[str, Any], queries: list[model.Query] | None = None) -> str:
    """One ground batch equality for the selected aggregate computations.

    Append after rewriting. These declarations construct terms, never assert
    equalities. The proof checker must justify the query-to-view connections.
    Backend code generation and physical sharing are outside these claims.
    """
    definition = model.WORKLOAD
    queries = definition.queries if queries is None else queries
    _, orientations = input_terms(queries)
    tables, attrs = list(definition.relations), [a for a, _ in definition.attributes]
    aw, fw = 1 << (len(attrs) - 1).bit_length(), 1 << (len(definition.functions) - 1).bit_length()
    regions: dict[tuple[str, str], Any] = {}

    def visit(region: Any) -> None:
        regions[json.loads(region[1][1]), json.loads(region[2][1])] = region
        children = region[-1]
        while children[0] == "Cons":
            visit(children[1][1])
            children = children[2]

    for orientation in orientations:
        visit(orientation[2])

    def vector(indices: set[int]) -> Any:
        values: list[Any] = [["WeightOne"] for _ in range(fw)]
        for i in indices:
            attr, power = definition.functions[i]
            owner = next(t for t in tables if attr in definition.relations[t])
            value: Any = ["Get", ["V", "$row"], symbol(attr)]
            if power == 2:
                value = ["Mult", value, value]
            values[i] = ["Scalar", symbol(owner), ["Lambda", "$row", value]]
        return tree("Weights", values)

    weights: dict[tuple[int, int], set[int]] = {}
    forms = []
    for i, view in enumerate(plan["views"]):
        region = regions[tables[view["origin"]], tables[view["destination"]]]
        for j, aggregate in enumerate(view["aggregates"]):
            local = set(aggregate["functions"])
            requested = local.union(*(weights[x, y] for x, y in aggregate["incoming"]))
            weights[i, j] = requested
            term = [
                "ComputeView",
                region,
                mask(set(view["keys"]), aw),
                vector(requested),
                vector(local),
                linked([f"witness_{x}_{y}" for x, y in aggregate["incoming"]]),
            ]
            forms.append(["let", f"witness_{i}_{j}", term])
    outputs = [
        ["Output", symbol(f"q{i}"), f"witness_{output['view']}_{output['aggregate']}"]
        for i, (_, output) in enumerate(zip(queries, plan["outputs"], strict=True))
    ]
    forms.append(["let", "selected_batch", ["Program", balanced("Pair", outputs)]])
    forms.append(["check", ["=", "input", "selected_batch"]])
    return "\n".join(reference.render(f) for f in forms) + "\n"


def benchmark_input(mode: str, directory: Path, rounds: int = DEFAULT_ROUNDS) -> Path:
    """Return the checked-in input at the default budget; write a generated input otherwise."""
    if rounds == DEFAULT_ROUNDS:
        return INPUTS / f"{mode}.egg"
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f"{mode}.egg"
    path.write_text(program(mode, rounds=rounds))
    return path


def main() -> None:
    parser = argparse.ArgumentParser(description="Regenerate the frozen LMFAO benchmark inputs")
    parser.add_argument("--check", action="store_true", help="fail if checked-in inputs need regeneration")
    parser.add_argument(
        "--proof-plan", type=Path, help="emit a slotted replay with equality checks for this selected plan"
    )
    parser.add_argument("--output", type=Path, help="destination for --proof-plan")
    args = parser.parse_args()
    if args.proof_plan is not None:
        if args.output is None or args.check:
            parser.error("--proof-plan requires --output and cannot be combined with --check")
        args.output.write_text((INPUTS / "slotted.egg").read_text() + plan_checks(model.read_plan(args.proof_plan)))
        return
    if args.output is not None:
        parser.error("--output requires --proof-plan")
    for mode in ("slotted", "debruijn"):
        path = INPUTS / f"{mode}.egg"
        source = ";;; GENERATED: python -m benchmarking.lmfao.program\n" + program(mode)
        if args.check:
            if path.read_text() != source:
                raise SystemExit(f"stale generated input: {path}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)


if __name__ == "__main__":
    main()
