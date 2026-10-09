#!/usr/bin/env python3
"""The paper's SDQL case study, S4.2: its ten workloads, their published targets, and the
tests written from them.

The fixtures under `slotted/tests/artifact/sdql/` are copied from commit 83f2e5b of
`memoryleak47/slotted-egraphs-artifact`: `sdql/slotted/progs/<kernel>_<phase>.sexp` is
what the artifact's slotted runner read, and `sdql/baseline/progs/<kernel>_<phase>_esat.sexp`
is the program its egg baseline extracted after saturating. Table 1 compares extraction
costs, and "finds the best program" there means reaching that cost; the tests here ask
for more, that the input's class comes to contain the target itself.
`slotted/checks/check-paper-sdql.py` pins the fixtures' hashes and checks that each test
under `slotted/tests/sdql-paper/` is what `test_text` writes for it; `slotted/eval.py` runs
every workload from the same forms, so the eight that never became files are one command away.

The artifact spells a variable `$name`, `name`, or `$var_NN`; its targets are alpha-numbered
`var_NN`. Every term is closed, so a translation only has to be consistent within one
file: `var_NN` keeps its number, any other name gets the next one from 1000. The artifact
writes `(let $x value body)` and `(sum $k $v range body)`; the language here has
`(Let value $x body)` and `(Sum range $k $v body)`.

The runner's budgets are per workload: 13 iterations for `batax_1st`, 12 for `batax_2nd`,
30 for everything else, under a 300 s timeout and 1.5 GB.

    python3 slotted/paper_fixtures.py --write    rewrite the suite's tests under slotted/tests/sdql-paper/
    python3 slotted/paper_fixtures.py            list the workloads and Table 1's slotted row for each
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "slotted"))
sc = __import__("slotted-egglog")
slotenc = __import__("slotted-encoder")

FIXTURES = ROOT / "slotted" / "tests" / "artifact" / "sdql"
TESTS = ROOT / "slotted" / "tests" / "sdql-paper"
RULES = ROOT / "slotted" / "languages" / "sdql-rules.egg"
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

#: The workloads the test suite runs under all 44 rules: the ones the encoding finishes in
#: seconds on the debug build the runner uses (ΣMMM's first phase at once, MMM's in about
#: half a minute). The other six that saturate take the release build minutes (TTM's first
#: phase six) to over the artifact's 300 s, and the two BATAX workloads longer still, so
#: `slotted/eval.py` is where those run; `slotted/tests/sdql-paper-batax.egg` and
#: `slotted/tests/sdql-paper-mmm.egg` cover two of them in the suite with rule subsets.
SUITE = (("mmm_sum", "1st"), ("mmm", "1st"))


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
            return names.slot(term)
        return ["Symbol", f'"{term}"']
    op, *args = term
    if op == "var":
        return names.slot(args[0])
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
    src = sc.parse((FIXTURES / src_name).read_text())[0]
    tgt = sc.parse((FIXTURES / tgt_name).read_text())[0]
    return translate(src), translate(tgt)


def reference_language():
    """The SDQL language with the oracle's spelling of each constructor."""
    decls = RULES.with_name("sdql.egg")
    return slotenc.language(decls, decls.with_suffix(".ref"))


def workload_text(kernel, phase, source=None, lang=None):
    """The same two terms spelled for the oracle."""
    source = source or sc.Source(RULES)
    lang = lang or reference_language()
    inp, tgt = workload(kernel, phase)
    return lang.sexpr(source.term(inp, ground=True)), lang.sexpr(source.term(tgt, ground=True))


# ---------------------------------------------------------------------- the tests
def pretty(form, indent=0, width=100):
    """A parsed form, one child per line once it stops fitting; the head keeps its leading atoms."""
    flat = sc.render(form)
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
        ["include", '"slotted/languages/sdql-rules.egg"'],
        ["let", "paper-input", inp],
        ["run", str(rounds)],
        ["let", "paper-target", tgt],
        ["run", "0"],
        ["check", ["=", "paper-input", "paper-target"]],
    ]


def test_text(kernel, phase):
    """One workload's test, as `slotted/tests/sdql-paper/<kernel>_<phase>.egg` holds it."""
    src_name, tgt_name = fixture_names(kernel, phase)
    iters, nodes, classes, saturated = TABLE1[(kernel, phase)]
    label = {"mmm_sum": "ΣMMM", "mttkrp": "MTTKRP", "mmm": "MMM", "ttm": "TTM", "batax": "BATAX"}[kernel]
    head = [
        f";;; The paper artifact's {label} {phase}-pass input and published baseline extraction,",
        ";;; under all 44 fine-grained rules at the artifact's iteration limit.",
        ";;;",
        ";;; GENERATED by `python3 slotted/paper_fixtures.py --write`, which also says how the",
        ";;; artifact's syntax is translated; `slotted/checks/check-paper-sdql.py` checks that this",
        f";;; file is that translation. Provenance (artifact commit {ARTIFACT_COMMIT}):",
        f";;;   input:  sdql/slotted/progs/{src_name}",
        f";;;   target: sdql/baseline/progs/{tgt_name}",
        f";;; Table 1's slotted row: {iters} iterations, {nodes:,} nodes, {classes:,} classes,"
        f" {'saturated' if saturated else 'not saturated'}.",
        "",
    ]
    body = []
    for form in test_forms(kernel, phase):
        if form[0] == "run" and form[1] != "0":
            body.append(";;; Saturate the input alone, for as many iterations as the artifact allowed it.")
        if form[0] == "let" and form[1] == "paper-target":
            body.append(";;; The target arrives only now; `(run 0)` installs it without running SDQL rules.")
        body.append(pretty(form))
    return "\n".join(head + body) + "\n"


def test_path(kernel, phase):
    return TESTS / f"{kernel}_{phase}.egg"


def write_tests():
    TESTS.mkdir(exist_ok=True)
    for kernel, phase in SUITE:
        test_path(kernel, phase).write_text(test_text(kernel, phase))
    return [test_path(k, p) for k, p in SUITE]


def main(argv):
    if argv == ["--write"]:
        for path in write_tests():
            print(f"wrote {path.relative_to(ROOT)}")
        return 0
    if argv:
        print(__doc__.strip().splitlines()[-2:], file=sys.stderr)
        return 2
    for kernel, phase in WORKLOADS:
        iters, nodes, classes, saturated = TABLE1[(kernel, phase)]
        where = "suite" if (kernel, phase) in SUITE else "eval only"
        print(
            f"{kernel}_{phase:<4} limit {iteration_limit(kernel, phase):>2}   paper: {iters:>2} iterations,"
            f" {nodes:>6,} nodes, {classes:>6,} classes, {'saturated    ' if saturated else 'not saturated'}   {where}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
