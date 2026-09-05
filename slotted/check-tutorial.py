#!/usr/bin/env python3
"""Assert every rule in `slotted/tests/user-rules.egg` is the encoder's own output.

The tutorial claims each section shows what a compiler emits for a real rule. This
checks it: comments and line breaks are dropped, and then structure, constructor
names, primitive names, strings and integers must agree exactly, with variable names
agreeing up to a bijection. Variables are renamed in the tutorial for readability, so
that is the only freedom.

`SECTIONS` below is the other half of the claim -- the rule each section shows, where
it comes from, and the encoder call that compiles it. A section's arguments mirror the
generator that owns that rule, so a tutorial rule is the committed generated rule
without its `:ruleset` tail.

Usage:  ./check-tutorial.py [M3 M7 ...]
"""

import os
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
os.chdir(ROOT)
sys.path.insert(0, str(ROOT / "slotted"))
enc = __import__("slotted-encoder")
gen = __import__("gen-node-rules")  # the generic, string-headed family lives there

TUTORIAL = ROOT / "slotted" / "encoding" / "user-rules.egg"

# The tutorial's language IS the generic, string-headed encoding it includes, so every
# rule here is one expressible with `App2`/`App3` and a head string.
_OPS = {op: gen.string_headed(op, "App2") for op in ["eq", "-", "*", "+", "app", "get", "range"]}
_OPS["lambda"] = gen.string_headed("lambda", "App2", ref="lam")
_OPS["binop"] = gen.string_headed("binop", "App3")
_OPS["let"] = gen.string_headed("let", "App3", ref="let")
_OPS["sym"] = enc.Op("sym", "Sym", ["String"])
_OPS["num"] = enc.Op("num", "Num", ["i64"])
LANG = enc.TermLang(_OPS)

MAP = ("sym", "map")
# what xarray.py passes, so an array rule here is its committed text
ARRAY = {"slot_prefix": "s_", "fresh_batch": False}


def nested(lhs, rhs, first=0, **kw):
    """A rule written as one nested pattern, flattened the way a compiler does."""
    root, atoms = enc.flatten(LANG, lhs)
    order = enc.connected_order(LANG, atoms, first=first)
    return enc.compile_rule(LANG, order, ("build", root, enc.rhs_of(LANG, rhs)), **kw)


def flat(atoms, rhs_root, rhs, first=0, **kw):
    """A rule whose atoms are given directly, as `xarray.py` writes them."""
    order = enc.connected_order(LANG, atoms, first=first)
    return enc.compile_rule(LANG, order, ("build", rhs_root, rhs), **kw)


ETA_ATOMS = [
    ("e", "lambda", [("sl", "$x"), ("pv", "b")]),
    ("b", "app", [("pv", "f"), ("sl", "$x")]),
]


def m1():
    return nested(("eq", "?a", "?b"), ("eq", "?b", "?a"))


def m2():
    return nested(("-", "?e", "?e"), ("num", 0))


def m3():
    # the `range` atom leads, so the `get` atom's root is fresh
    return nested(
        ("get", ("range", "?st", "?en"), "?idx"),
        ("+", "?idx", ("-", "?st", ("num", 1))),
        first=1,
    )


def m4():
    return nested(("*", ("*", "?a", "?b"), "?c"), ("*", "?a", ("*", "?b", "?c")))


def m5():
    atoms = [
        ("p", "app", [("cls", MAP), ("pv", "l")]),
        ("l", "lambda", [("sl", "$x"), ("pv", "fgx")]),
        ("fgx", "app", [("pv", "f"), ("pv", "gx")]),
    ]
    rhs = (
        "lambda",
        ("sl", "$in"),
        (
            "app",
            ("app", MAP, ("pv", "f")),
            ("app", ("app", MAP, ("lambda", ("sl", "$x"), ("pv", "gx"))), ("sl", "$in")),
        ),
    )
    return flat(atoms, "p", rhs, conds=[(False, "$x", ["f"])], fresh=["$in"], **ARRAY)


def m6():
    # the `app` atom leads -- `connected_order`'s own default for this rule
    return flat(
        ETA_ATOMS,
        "e",
        ("pv", "f"),
        first=1,
        conds=[(False, "$x", ["f"])],
        **ARRAY,
    )


def m7():
    return nested(
        ("binop", "?f", ("let", "$x", "?e2", "?e1"), ("let", "$x", "?e3", "?e1")),
        ("let", "$x", ("binop", "?f", "?e2", "?e3"), "?e1"),
    )


def m8():
    return flat(
        [("p", "let", [("sl", "$x"), ("sl", "$x"), ("pv", "e")])],
        "p",
        ("pv", "e"),
        **ARRAY,
    )


def m9():
    # the `lambda` atom leads -- what xarray.py ships
    return flat(
        ETA_ATOMS,
        "e",
        ("pv", "f"),
        first=0,
        conds=[(False, "$x", ["f"])],
        **ARRAY,
    )


def m10():
    return nested(("+", "?e", ("num", 0)), "?e")


def m11():
    atoms = [
        ("p", "let", [("sl", "$x"), ("pv", "ab"), ("pv", "e")]),
        ("ab", "app", [("pv", "a"), ("pv", "b")]),
    ]
    rhs = (
        "app",
        ("let", ("sl", "$x"), ("pv", "a"), ("pv", "e")),
        ("let", ("sl", "$x"), ("pv", "b"), ("pv", "e")),
    )
    return flat(atoms, "p", rhs, conds=[(True, "$x", ["a", "b"])], **ARRAY)


# section, the rule it shows, where that rule lives, and the compiler
SECTIONS = [
    ("M1", "eq-comm", "sdql benches/sdql.rs", m1),
    ("M2", "sub-identity", "sdql benches/sdql.rs", m2),
    ("M3", "get-range", "sdql benches/sdql.rs", m3),
    ("M4", "mult-assoc1", "sdql benches/sdql.rs", m4),
    ("M5", "map-fission", "array tests/array/mod.rs", m5),
    ("M6", "eta", "array tests/array/mod.rs", m6),
    ("M7", "let-binop4", "sdql benches/sdql.rs", m7),
    ("M8", "let-var-same", "array tests/array/mod.rs", m8),
    ("M9", "eta", "array tests/array/mod.rs", m9),
    ("M10", "add-zero", "sdql benches/sdql.rs", m10),
    ("M11", "let-app", "array tests/array/mod.rs", m11),
]

# Not a variable. Every primitive name has a `-`, `=` or `!` in it and so is caught by
# the variable pattern instead; these are the ones spelled like an identifier.
FIXED = {
    "rule",
    "let",
    "union",
    "delete",
    "set",
    "guard",
    "or",
    "and",
    "not",
    "true",
    "false",
    "App2",
    "App3",
    "App4",
    "Num",
    "Sym",
    "Scale",
    "Null",
    "Var",
    "ClassSlots",
    "RenamesToLeader",
    "Equated",
    "compose",
    "inverse",
}
VARIABLE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
TOKEN = re.compile(r'\(|\)|"[^"]*"|[^\s()]+')


def strip_comment(line):
    quoted = False
    for i, ch in enumerate(line):
        if ch == '"':
            quoted = not quoted
        elif ch == ";" and not quoted:
            return line[:i]
    return line


def top_forms(text):
    """Every balanced top-level form, comments removed."""
    out, depth, form = [], 0, []
    for raw in text.splitlines():
        line = strip_comment(raw)
        if not line.strip():
            continue
        depth += line.count("(") - line.count(")")
        form.append(line.strip())
        if depth <= 0:
            out.append(" ".join(form))
            form, depth = [], 0
    if form:
        raise SystemExit(f"unbalanced parens in {TUTORIAL}")
    return out


def parse(text):
    toks = TOKEN.findall(text)
    pos = [0]

    def go():
        t = toks[pos[0]]
        pos[0] += 1
        if t != "(":
            return t
        out = []
        while toks[pos[0]] != ")":
            out.append(go())
        pos[0] += 1
        return out

    v = go()
    assert pos[0] == len(toks), f"trailing tokens in {text[:60]}"
    return v


def is_var(tok):
    return bool(VARIABLE.match(tok)) and tok not in FIXED


def alpha_eq(a, b, fwd, bwd, path="/"):
    """None if equal up to a variable bijection, else the first difference."""
    if isinstance(a, list) != isinstance(b, list):
        return f"{path}: {'a list' if isinstance(a, list) else a} vs {'a list' if isinstance(b, list) else b}"
    if isinstance(a, list):
        if len(a) != len(b):
            return f"{path}: arity {len(a)} vs {len(b)}\n       want {a}\n        got {b}"
        for i, (x, y) in enumerate(zip(a, b, strict=True)):
            why = alpha_eq(x, y, fwd, bwd, f"{path}{i}/")
            if why:
                return why
        return None
    if is_var(a) != is_var(b):
        return f"{path}: {a!r} vs {b!r} -- one is a variable, the other is not"
    if not is_var(a):
        return None if a == b else f"{path}: {a!r} vs {b!r}"
    if fwd.setdefault(a, b) != b or bwd.setdefault(b, a) != a:
        return f"{path}: {a!r} is already matched with {fwd.get(a)!r}, and {b!r} with {bwd.get(b)!r}"
    return None


def main():
    which = sys.argv[1:]
    rules = [f for f in top_forms(TUTORIAL.read_text()) if f.startswith("(rule")]
    if len(rules) != len(SECTIONS):
        print(f"FAIL: {TUTORIAL.name} has {len(rules)} rules, this file describes {len(SECTIONS)}")
        return 1
    bad = []
    for (name, rule, where, fn), form in zip(SECTIONS, rules, strict=True):
        if which and name not in which:
            continue
        why = alpha_eq(parse(fn()), parse(form), {}, {})
        print(
            f"  {'ok  ' if why is None else 'FAIL'} {name:<4} {rule:<13} {where}" + (f"\n       {why}" if why else "")
        )
        if why:
            bad.append(name)
    shown = [s for s in SECTIONS if not which or s[0] in which]
    print(
        f"\n{len(shown) - len(bad)}/{len(shown)} sections are the encoder's own output"
        + (f"   FAILED: {', '.join(bad)}" if bad else "")
    )
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
