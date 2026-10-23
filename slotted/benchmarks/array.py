"""Figure 8's functional-array input and target, shared by timings and tests.

The artifact uses four functions over a two-dimensional array, with 0–10 extra
parameters applied to each function. Function binders enclose parameter binders;
the input is eta-reduced, while the target introduces a matrix argument.
"""

from pathlib import Path

from slotted import reference as syntax

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "egglog-experimental/tests/slotted/languages/array.egg"
RULES = SOURCE.with_name("array-rules.egg")
LANG = syntax.language(SOURCE, SOURCE.with_suffix(".ref"))
MAP = ("Sym", "map")


def apply(function, *arguments):
    for argument in arguments:
        function = ("App", function, argument)
    return function


def goal(n, *, wrap_lams=True, nfun=4, dims=2):
    """Input and target terms; optional shapes support focused regression tests."""
    parameters = [("var", 1 + i) for i in range(n)]
    function_slots = [1000 + i for i in range(nfun)]
    functions = [
        apply(("var", slot) if wrap_lams else ("Sym", f"f{i + 1}"), *parameters)
        for i, slot in enumerate(function_slots)
    ]
    fresh_slot = iter(range(100, 1000)).__next__

    def maps(function):
        for _ in range(dims):
            function = ("App", MAP, function)
        return function

    def chained(parts):
        if len(parts) == 1:
            return parts[0]
        slot = fresh_slot()
        body = ("var", slot)
        for function in parts:
            body = ("App", function, body)
        return ("Lam", slot, body)

    start = maps(chained(functions))
    half = nfun // 2
    left, right = maps(chained(functions[half:])), maps(chained(functions[:half]))
    slot = fresh_slot()
    target = ("Lam", slot, ("App", left, ("App", right, ("var", slot))))

    def wrap(term):
        if wrap_lams:
            for i in reversed(range(n)):
                term = ("Lam", 1 + i, term)
            for slot in reversed(function_slots):
                term = ("Lam", slot, term)
        return term

    return wrap(start), wrap(target)
