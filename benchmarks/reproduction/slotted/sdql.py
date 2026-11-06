#!/usr/bin/env python3
"""Pure SDQL artifact translation and workload metadata for explicit reproduction.

The vendored inputs/targets come from artifact revision 83f2e5b. The common
freeze command is python -m benchmarks.reproduction.slotted.generate; routine
Rust tests and figures consume the saved 44-rule inputs without generation.
"""

import re

from . import ROOT
from . import reference as syntax

FIXTURES = ROOT / "benchmarks/reproduction/slotted/fixtures/sdql"
RULES = ROOT / "egglog-experimental" / "tests" / "slotted" / "languages" / "sdql-rules.egg"
ARTIFACT_COMMIT = "83f2e5bee2b3aa45bf97ef1e3a8abe953790c735"

KERNELS = ("mmm_sum", "mttkrp", "mmm", "ttm", "batax")  # Table 1's order: ΣMMM, MTTKRP, MMM, TTM, BATAX
PHASES = ("1st", "2nd")
WORKLOADS = tuple((kernel, phase) for phase in PHASES for kernel in KERNELS)  # Table 1's row order

#: Table 1's `slotted` rows: iterations, nodes, classes, saturated. The two BATAX
#: workloads ran out of memory before saturating, at 1.7 GB and 1.6 GB.
TABLE1 = {
    ("mmm_sum", "1st"): (5, 30, 15, True),
    ("mttkrp", "1st"): (8, 466, 59, True),
    ("mmm", "1st"): (9, 130, 27, True),
    ("ttm", "1st"): (9, 280, 47, True),
    ("batax", "1st"): (13, 97_238, 16_767, False),
    ("mmm_sum", "2nd"): (15, 314, 75, True),
    ("mttkrp", "2nd"): (25, 4_891, 307, True),
    ("mmm", "2nd"): (18, 1_308, 128, True),
    ("ttm", "2nd"): (25, 2_044, 196, True),
    ("batax", "2nd"): (12, 71_643, 10_435, False),
}

# Small full-rule workloads for the regression suite. Larger workloads run through
# eval.py/check.py; tests/sdql-paper-{batax,mmm}.egg also exercise rule subsets.


def iteration_limit(kernel, phase):
    """The artifact runner's `iter_limit` for one workload."""
    if kernel == "batax":
        return 13 if phase == "1st" else 12
    return 30


def fixture_names(kernel, phase):
    """The vendored input and target of one workload."""
    return f"{kernel}_{phase}.sexp", f"{kernel}_{phase}_esat.sexp"


OP = {
    "sing": "Sing",
    "+": "Add",
    "*": "Mult",
    "-": "Sub",
    "eq": "Equality",
    "get": "Get",
    "range": "Range",
    "apply": "App",
    "ifthen": "IfThen",
    "binop": "Binop",
    "subarray": "SubArray",
    "unique": "Unique",
}


class Names:
    """One file's variable numbering: `var_NN` keeps NN, any other name is numbered from 1000."""

    def __init__(self):
        self.named = {}

    def slot(self, atom):
        atom = atom.lstrip("$")
        match = re.fullmatch(r"var_0*([1-9][0-9]*)", atom)
        if match:
            return "$" + match.group(1)
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", atom):
            raise ValueError(f"unexpected artifact variable {atom!r}")
        return "$" + str(self.named.setdefault(atom, 1000 + len(self.named)))


def translate(term, names=None):
    """The artifact's constructor order to `languages/sdql.egg`'s, as a parsed form."""
    names = Names() if names is None else names
    if not isinstance(term, list):
        if re.fullmatch(r"-?[0-9]+", term):
            return ["Num", term]
        if term.startswith("$") or term.startswith("var_"):
            return ["V", names.slot(term)]
        return ["Symbol", f'"{term}"']
    op, *args = term
    if op == "var":
        return ["V", names.slot(args[0])]
    if op == "lambda":
        return ["Lambda", names.slot(args[0]), translate(args[1], names)]
    if op == "let":
        # Artifact: binder, value, body.  Local: value, binder, body.
        return ["Let", translate(args[1], names), names.slot(args[0]), translate(args[2], names)]
    if op == "sum":
        # Artifact: binders, range, body.  Local: range, binders, body.
        return ["Sum", translate(args[2], names), names.slot(args[0]), names.slot(args[1]), translate(args[3], names)]
    if op == "merge":
        return [
            "Merge",
            translate(args[3], names),
            translate(args[4], names),
            names.slot(args[0]),
            names.slot(args[1]),
            names.slot(args[2]),
            translate(args[5], names),
        ]
    if op not in OP:
        raise ValueError(f"unexpected artifact operator {op!r}")
    return [OP[op], *(translate(arg, names) for arg in args)]


def workload(kernel, phase):
    """`(input, target)` of one workload as parsed forms in the language of `sdql-rules.egg`."""
    src_name, tgt_name = fixture_names(kernel, phase)
    src = syntax.parse((FIXTURES / src_name).read_text())[0]
    tgt = syntax.parse((FIXTURES / tgt_name).read_text())[0]
    return translate(src), translate(tgt)


def reference_language():
    """The SDQL language with the oracle's spelling of each constructor."""
    decls = RULES.with_name("sdql.egg")
    return syntax.language(decls, decls.with_suffix(".ref"))


def workload_text(kernel, phase, source=None, lang=None):
    """The same two terms spelled for the oracle."""
    source = source or syntax.Source(RULES)
    lang = lang or reference_language()
    inp, tgt = workload(kernel, phase)
    return lang.sexpr(source.term(inp, ground=True)), lang.sexpr(source.term(tgt, ground=True))


# ---------------------------------------------------------------------- the tests
def pretty(form, indent=0, width=100):
    """A parsed form, one child per line once it stops fitting; the head keeps its leading atoms."""
    flat = syntax.render(form)
    if not isinstance(form, list) or indent + len(flat) <= width:
        return flat
    lead = 1
    while lead < len(form) and not isinstance(form[lead], list):
        lead += 1
    pad = " " * (indent + 2)
    first = "(" + " ".join(form[:lead])
    rest = [pad + pretty(c, indent + 2, width) for c in form[lead:]]
    return "\n".join([first, *rest]) + ")"


def test_forms(kernel, phase, rounds=None):
    """The forms a workload's test consists of, in order.

    The target is declared only after the bounded user-rule phase: declared before it,
    the graph would be seeded with the answer and the test would show joinability rather
    than the artifact's reachability. `(run 0)` installs the target's nodes with the
    machinery alone.
    """
    inp, tgt = workload(kernel, phase)
    rounds = iteration_limit(kernel, phase) if rounds is None else rounds
    return [
        ["include", '"egglog-experimental/tests/slotted/languages/sdql-rules.egg"'],
        ["let", "paper-input", inp],
        ["run", str(rounds)],
        ["let", "paper-target", tgt],
        ["run", "0"],
        ["check", ["=", "paper-input", "paper-target"]],
    ]
