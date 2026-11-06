"""Prepare the same slotted workloads for benchmarking and correctness tests.

Each workload has a source program with a goal check, an input-only program for
graph export, and reference specs for the two matchers. These are plain data so
serial and spawned-worker evaluation consume exactly the same inputs.
"""

import json
from dataclasses import dataclass

from . import ROOT
from . import array as array_bench
from . import reference as syntax
from . import sdql as pf

BATAX_SUBSET = ROOT / "egglog-experimental" / "tests" / "slotted" / "sdql-paper-batax.egg"
LOGIC_FIXTURES = ROOT / "egglog-experimental/benches/slotted/logic"


@dataclass(frozen=True)
class Workload:
    study: str
    case: str
    rounds: int
    rules: int | None
    program: str
    graph_program: str
    multi: str
    nested: str | None
    unsupported_reason: str = ""


def prepare(task, *, rounds=None, rules=44):
    study, case = task
    if study == "array":
        return array_workload(case, rounds=6 if rounds is None else rounds)
    if study == "logic":
        return logic_workload(LOGIC_FIXTURES / f"{case}.egg", rounds=rounds)
    return sdql_workload(*case, rules=rules, rounds=rounds)


def logic_source(path, *, text=None):
    src = syntax.Source(path, text=text)
    if len(src.sorts) != 1:
        raise ValueError(f"{path.name}: reference case studies require one equality sort")
    # These constructors have identical names and column order in xmulti's L.
    for op in src.lang.ops.values():
        op.ref = "var" if op.sig == [syntax.SLOT] else op.ctor
    return src


def logic_workload(path, *, rounds=None):
    """Derive the logic rules, initial equations, round budget and goal from .egg.

    Accept one initialization phase, one run, and one final equality check.
    Unsupported command sequences fail instead of silently dropping actions.
    """
    program = path.read_text()
    src = logic_source(path, text=program)
    rules, unions, goal, budget = [], [], None, None
    for form, _ in src.body:
        match form:
            case ["sort", _] if budget is None:
                pass
            case ["rewrite", *_] if budget is None:
                rules.append(form)
            case ["union", a, b] if budget is None:
                unions.append((a, b))
            case ["run", n] if budget is None:
                budget = int(n)
            case ["check", ["=", a, b]] if budget is not None and goal is None:
                goal = a, b
            case _:
                raise ValueError(f"{path.name}: unsupported reference fixture command: {syntax.render(form)}")
    if budget is None or goal is None or not rules:
        raise ValueError(f"{path.name}: expected rewrites, one run, and one final equality check")
    # The oracle compares to its first seed. It must already be an input term;
    # adding the goal before rewriting would change the experiment.
    if not any(goal[0] == term for pair in unions for term in pair):
        raise ValueError(f"{path.name}: the goal's left side must be an initial union term")
    budget = budget if rounds is None else rounds

    def term(form):
        return src.lang.sexpr(src.term(form, ground=True))

    # Seed the same variable node explicitly in both engines, including closed inputs.
    head = [f"rounds {budget}", *ctor_lines(src.lang), f"term {term(goal[0])}"]
    variable = src.carriers[src.sorts[0]].var
    if variable is not None:
        head.append("term (var $0)")
    head += [f"union {term(a)} {term(b)}" for a, b in unions]
    tail = [f"goal {term(goal[1])}"]
    multi = [line for rule in rules for line in syntax.rule_lines(src, src.lang, rule)]
    unsupported = ""
    try:
        nested = [line for rule in rules for line in syntax.rule_lines(src, src.lang, rule, nested=True)]
        nested_spec = "\n".join(head + nested + tail) + "\n"
    except syntax.NestedPatternUnsupported as exc:
        nested_spec = None
        unsupported = str(exc)
    forms = syntax.parse(program)
    forms = [["run", str(budget)] if f[0] == "run" else f for f in forms]
    first_action = next(i for i, form in enumerate(forms) if form[0] in ("union", "run"))
    if variable is not None:
        forms.insert(first_action, ["let", "_variable_seed", [variable, "$0"]])
    return Workload(
        study="logic",
        case=path.stem,
        rounds=budget,
        rules=len(rules),
        program="\n".join(syntax.render(f) for f in forms) + "\n",
        graph_program="\n".join(syntax.render(f) for f in forms if f[0] != "check") + "\n",
        multi="\n".join(head + multi + tail) + "\n",
        nested=nested_spec,
        unsupported_reason=unsupported,
    )


def ctor_lines(lang):
    """`ctor <tag> <Name>` lines: what the encoding calls each of the oracle's constructors,
    so the oracle's substitution snapshot breaks ties by the same spelling."""
    out = []
    for op in lang.ops.values():
        if op.ref:
            out.append(f"ctor {op.ref} {op.ctor}")
        else:
            out.append(f"ctor {'symbol' if 'String' in op.sig else 'number'} {op.ctor}")
    return sorted(out)


def rule_lines(lang, rules_path, selected, nested):
    """A rule file's rules as oracle spec lines, flattened or nested."""
    src = syntax.Source(rules_path)
    out = []
    for form in syntax.parse(rules_path.read_text()):
        if not (isinstance(form, list) and form and form[0] == "rewrite"):
            continue
        r = syntax.rewrite_parts(src, form)
        if selected is not None and r["name"] not in selected:
            continue
        out += syntax.rule_lines(src, lang, form, nested=nested)
    return out


def array_program(start, target, rounds, *, with_target):
    """Source terms and the shared eight-rule library; Rust performs the encoding."""

    def term(t):
        if t[0] == "var":
            return f"({array_bench.LANG.symbols_for(array_bench.LANG.default_sort).var} ${t[1]})"
        op = array_bench.LANG.ops[t[0]]
        args = []
        for kind, arg in zip(op.arg_kinds(), t[1:], strict=True):
            if kind is syntax.CHILD:
                args.append(term(arg))
            elif kind is syntax.BINDER:
                args.append(f"${array_bench.LANG.slot(arg)}")
            else:
                args.append(json.dumps(arg))
        return "(" + " ".join([op.ctor, *args]) + ")"

    lines = ['(include "egglog-experimental/tests/slotted/languages/array-rules.egg")']
    lines.append(f"(let input0 {term(start)})")
    lines.append(f"(run {rounds})")
    if with_target:
        lines.append(f"(check (= input0 {term(target)}))")
    return "\n".join(lines) + "\n"


def array_workload(n, *, rounds=6):
    start, target = array_bench.goal(n)
    head = [f"rounds {rounds}", *ctor_lines(array_bench.LANG), f"term {array_bench.LANG.sexpr(start)}"]
    goal = [f"goal {array_bench.LANG.sexpr(target)}"]
    multi = rule_lines(array_bench.LANG, array_bench.RULES, None, nested=False)
    nested = rule_lines(array_bench.LANG, array_bench.RULES, None, nested=True)
    return Workload(
        study="array",
        case=f"goal-2d-4f-N{n}",
        rounds=rounds,
        rules=None,
        program=array_program(start, target, rounds, with_target=True),
        graph_program=array_program(start, target, rounds, with_target=False),
        multi="\n".join(head + multi + goal) + "\n",
        nested="\n".join(head + nested + goal) + "\n",
    )


def sdql_program(kernel, phase, rules, rounds, with_target):
    """One workload as a slotted source: the full library by include, or BATAX's own 12."""
    if rules == 12:
        # the goal-directed test, its own rules and schedule; only its terms are reused
        forms = syntax.parse(BATAX_SUBSET.read_text())
        forms = [["run", str(rounds)] if f[:1] == ["run"] and f[1] != "0" else f for f in forms]
    else:
        forms = pf.test_forms(kernel, phase, rounds)
    if not with_target:
        # the saturated input alone, for counting: no target, no check
        forms = [f for f in forms if f[0] != "check" and f[:2] != ["let", "paper-target"]]
    return "\n".join(syntax.render(f) for f in forms) + "\n"


def sdql_workload(kernel, phase, *, rules=44, rounds=None):
    lang = pf.reference_language()
    start, target = pf.workload_text(kernel, phase, syntax.Source(pf.RULES), lang)
    budget = pf.iteration_limit(kernel, phase) if rounds is None else rounds
    selected = None
    if rules == 12:
        subset = syntax.Source(BATAX_SUBSET)
        selected = {syntax.rule_name(subset, f) for f in syntax.parse(BATAX_SUBSET.read_text()) if f[:1] == ["rewrite"]}
    head = [f"rounds {budget}", *ctor_lines(lang), f"term {start}"]
    goal = [f"goal {target}"]
    multi = rule_lines(lang, pf.RULES, selected, nested=False)
    nested = rule_lines(lang, pf.RULES, selected, nested=True)
    return Workload(
        study="sdql",
        case=f"{kernel}_{phase}-{rules}rules",
        rounds=budget,
        rules=rules,
        program=sdql_program(kernel, phase, rules, budget, True),
        graph_program=sdql_program(kernel, phase, rules, budget, False),
        multi="\n".join(head + multi + goal) + "\n",
        nested="\n".join(head + nested + goal) + "\n",
    )
