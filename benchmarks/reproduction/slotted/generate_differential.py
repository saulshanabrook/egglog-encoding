"""Explicitly freeze the retired Python differential case tables as Rust inputs.

Run python -m benchmarks.reproduction.slotted.generate_differential [--check].
No executable is built or run. Expected partitions remain native-reference
observations at test time; named known limitations retain both original answers.
"""

import argparse
import json
from pathlib import Path

from . import ROOT, cases_array, cases_nested, cases_sdql, cases_toy, reference, workloads
from . import differential_source as source

INPUTS = ROOT / "benchmarks/slotted/correctness"


def frozen_inputs():
    result = {}

    def expand(text):
        forms = []
        for form in reference.parse(text):
            if form[0] == "include":
                forms.extend(expand((ROOT / json.loads(form[1])).read_text()))
            else:
                forms.append(reference.render(form))
        return forms

    def add(family, name, program, multi, probes=(), **expect):
        path = Path(family) / name
        result[path.with_suffix(".egg")] = (
            "; Frozen differential input; see generate_differential.py.\n" + "\n".join(expand(program)) + "\n"
        )
        result[path.with_suffix(".ref")] = (
            json.dumps(
                {"multi": multi, "nested": expect.pop("nested", None), "probes": list(probes), "expect": expect},
                indent=2,
                ensure_ascii=False,
            )
            + "\n"
        )

    def case(family, item, **expect):
        probes = [source.term(item.lang, term) if term[0] == "var" else f"_p{i}" for i, term in enumerate(item.probes)]
        if hasattr(item, "want"):
            expect.update(
                encoding_partition=item.want, reference_partition=item.ref_want or item.want, limitation=item.why
            )
        add(family, item.name, item.egg_program(mult=1), item.spec(), probes, **expect)

    for item in cases_toy.curated():
        case("toy", item)
    for item in cases_array.per_rule_cases() + cases_array.unbound_cases():
        case("array", item)
        if item.name.endswith("blocked") and any(rule.conds for rule in item.rules):
            unguarded = cases_array.Case(
                item.name + "-unguarded",
                item.terms,
                [rule.without_guards() for rule in item.rules],
                item.probes,
                item.rounds,
                item.unions,
            )
            case("array", unguarded, differs_from=item.name)
    for item in cases_sdql.cases() + cases_sdql.known_encoding_limitations():
        case("sdql", item)
    for name, unions, start, lhs, rhs, differs in cases_nested.CASES:
        program = (
            '(include "egglog-experimental/tests/slotted/languages/toy.egg")\n'
            + f"(let _variable_seed (V $0))\n{unions}\n(let start {start})\n(rewrite {lhs} {rhs})\n(run 1)\n"
        )
        parsed = reference.Source(Path("nested.egg"), text=program)
        lang = cases_toy.LANG
        head = [
            "rounds 1",
            *workloads.ctor_lines(lang),
            f"term {lang.sexpr(parsed.term(reference.parse(start)[0], ground=True))}",
            "term (var $0)",
        ]
        head += [
            "union " + " ".join(lang.sexpr(parsed.term(value, ground=True)) for value in form[1:])
            for form in reference.parse(unions)
        ]
        forms = [form for form in reference.parse(program) if form[0] == "rewrite"]
        multi = "\n".join(head + [line for form in forms for line in reference.rule_lines(parsed, lang, form)]) + "\n"
        nested = (
            "\n".join(head + [line for form in forms for line in reference.rule_lines(parsed, lang, form, nested=True)])
            + "\n"
        )
        add("nested", name, program, multi, nested=nested, full_nodes_exceed_compat=differs)
    for name, rounds in (("subst-refresh", 2), ("coset-direction", 1)):
        path = ROOT / "egglog-experimental/tests/slotted" / f"{name}.egg"
        program = path.read_text().replace("(let start", "(let _variable_seed (V $0))\n(let start", 1)
        parsed = reference.Source(path)
        lang = workloads.pf.reference_language()
        forms = reference.parse(program)
        start = next(form[2] for form in forms if form[:2] == ["let", "start"])
        target = next(form[1][2] for form in forms if form[0] == "check")
        spec = [
            f"rounds {rounds}",
            *workloads.ctor_lines(lang),
            f"term {lang.sexpr(parsed.term(start, ground=True))}",
            "term (var $0)",
        ]
        spec += [
            "union " + " ".join(lang.sexpr(parsed.term(value, ground=True)) for value in form[1:])
            for form in forms
            if form[0] == "union"
        ]
        spec += workloads.rule_lines(lang, path, None, False) + [f"goal {lang.sexpr(parsed.term(target, ground=True))}"]
        add("eval", name, program, "\n".join(spec) + "\n", expected_counts=[5, 8] if name == "subst-refresh" else None)
    lang = cases_toy.LANG
    atoms = [("root", "Null", [])] + [(f"p{i}", "F", [("pv", f"a{i}"), ("pv", f"a{i}")]) for i in range(6)]
    rhs = ("pv", "a5")
    for i in reversed(range(5)):
        rhs = ("G", ("pv", f"a{i}"), rhs)
    program = '(include "egglog-experimental/tests/slotted/languages/toy.egg")\n'
    program += (
        source.rewrite(lang, atoms, "root", rhs, name="all-refinements")
        + "\n(let n (Null))\n(let f (F (V $0) (V $0)))\n(run 1)\n"
    )
    root, lines = reference.atom_lines(lang, "root", atoms)
    spec = [
        "rounds 1",
        *workloads.ctor_lines(lang),
        "term (var $0)",
        "term (null)",
        "term (f (var $0) (var $0))",
        "rule",
        *lines,
        f"rhs {root} {reference.pat_sexpr(lang, rhs)}",
    ]
    add("eval", "all-refinements", program, "\n".join(spec) + "\n", expected_counts=[77, 280])
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    generated = frozen_inputs()
    if args.check:
        existing = {path.relative_to(INPUTS) for path in INPUTS.rglob("*") if path.suffix in (".egg", ".ref")}
        if existing != set(generated) or any((INPUTS / path).read_text() != text for path, text in generated.items()):
            raise SystemExit("frozen differential files differ from the explicit generator")
        print(f"{len(generated) // 2} frozen differential pairs match")
        return
    for path, text in generated.items():
        destination = INPUTS / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text)
    print(f"froze {len(generated) // 2} differential pairs")


if __name__ == "__main__":
    main()
