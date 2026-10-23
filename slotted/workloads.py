"""Prepare the same slotted workloads for benchmarking and correctness tests.

Each workload has a source program with a goal check, an input-only program for
graph export, and reference specs for the two matchers. These are plain data so
serial and spawned-worker evaluation consume exactly the same inputs.
"""

import json
import re
from dataclasses import dataclass, field
from pathlib import Path

from slotted import reference as syntax
from slotted.benchmarks import array as array_bench
from slotted.benchmarks import sdql as pf
from slotted.treatments import TREATMENTS

ROOT = Path(__file__).resolve().parents[1]
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
    unsupported: dict[str, str] = field(default_factory=dict)

    @property
    def lang(self):
        # Language descriptors contain identity-based sentinels; reconstruct them
        # in each worker rather than pickling them with the generated programs.
        if self.study == "logic":
            return logic_source(Path(self.case), text=self.program).lang
        return array_bench.LANG if self.study == "array" else pf.reference_language()

    def reference(self, side):
        if side in self.unsupported:
            raise ValueError(f"{self.case} / {side}: {self.unsupported[side]}")
        treatment = TREATMENTS[side]
        if treatment.engine != "reference":
            raise ValueError(f"{side} is not a reference treatment")
        return self.multi if treatment.matcher == "multi" else self.nested

    def supported_sides(self, sides):
        return tuple(side for side in sides if side not in self.unsupported)


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
        op.ref = op.ctor
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

    # Rust initializes one variable class even for a closed program.
    head = [f"rounds {budget}", *ctor_lines(src.lang), f"term {term(goal[0])}", "term (var $0)"]
    head += [f"union {term(a)} {term(b)}" for a, b in unions]
    tail = [f"goal {term(goal[1])}"]
    multi = [line for rule in rules for line in syntax.rule_lines(src, src.lang, rule)]
    unsupported = {}
    try:
        nested = [line for rule in rules for line in syntax.rule_lines(src, src.lang, rule, nested=True)]
        nested_spec = "\n".join(head + nested + tail) + "\n"
    except syntax.NestedPatternUnsupported as exc:
        nested_spec = None
        unsupported = {name: str(exc) for name, t in TREATMENTS.items() if t.matcher == "nested"}
    forms = syntax.parse(program)
    forms = [["run", str(budget)] if f[0] == "run" else f for f in forms]
    return Workload(
        study="logic",
        case=path.stem,
        rounds=budget,
        rules=len(rules),
        program="\n".join(syntax.render(f) for f in forms) + "\n",
        graph_program="\n".join(syntax.render(f) for f in forms if f[0] != "check") + "\n",
        multi="\n".join(head + multi + tail) + "\n",
        nested=nested_spec,
        unsupported=unsupported,
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
            return f"${t[1]}"
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
        lines.append(f"(check (= {term(start)} {term(target)}))")
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


def workload_label(study, case, rules):
    if study == "logic":
        return case
    if study == "array" and (match := re.fullmatch(r"goal-2d-4f-N(\d+)", case)):
        return "Array N=" + match[1]
    if study == "sdql" and (
        match := re.fullmatch(r"(mmm_sum|mttkrp|mmm|ttm|batax)_(1st|2nd)-" + str(rules) + "rules", case)
    ):
        kernel, phase = match.groups()
        name = "ΣMMM" if kernel == "mmm_sum" else kernel.upper()
        suffix = f", {rules} rules" if rules != 44 else ""
        return f"{name} ({phase}{suffix})"
    return f"{study}: {case}"


def add_arguments(parser):
    """Workload selectors have identical meanings in the benchmark and checker."""
    parser.add_argument("study", nargs="?", default="all", choices=("all", "array", "sdql", "logic"))
    parser.add_argument("--case", nargs="+", help="logic fixture names without .egg; default all")
    parser.add_argument("--rounds", type=int, help="rewrite iterations; default paper/fixture budget, not samples")
    parser.add_argument("--kernel", nargs="+", default=list(pf.KERNELS), choices=pf.KERNELS)
    parser.add_argument("--phase", nargs="+", default=list(pf.PHASES), choices=pf.PHASES)
    parser.add_argument("--rules", type=int, default=44, choices=(12, 44), help="SDQL rules; 12 requires BATAX 2nd")


def select(args):
    if args.rounds is not None and args.rounds < 0:
        raise ValueError("--rounds must be nonnegative")
    if args.case and args.study not in ("all", "logic"):
        raise ValueError("--case selects logic fixtures; use study logic or all")
    tasks = []
    if args.study in ("all", "array"):
        # Figure 8: four functions over a 2D array, with 0–10 extra parameters.
        tasks += [("array", n) for n in range(11)]
    if args.study in ("all", "sdql"):
        selected = [w for w in pf.WORKLOADS if w[0] in args.kernel and w[1] in args.phase]
        if args.rules == 12 and selected != [("batax", "2nd")]:
            raise ValueError("--rules 12 requires --kernel batax --phase 2nd")
        tasks += [("sdql", w) for w in selected]
    if args.study in ("all", "logic"):
        names = [p.stem for p in sorted(LOGIC_FIXTURES.glob("first-order-logic*.egg"))]
        if args.case and (unknown := set(args.case) - set(names)):
            raise ValueError(f"unknown logic cases: {', '.join(sorted(unknown))}; choose from {', '.join(names)}")
        tasks += [("logic", name) for name in names if not args.case or name in args.case]
    if not tasks:
        raise ValueError("no workloads selected")
    if len(set(tasks)) != len(tasks):
        raise ValueError("duplicate workloads selected")
    return [prepare(task, rounds=args.rounds, rules=args.rules) for task in tasks]
