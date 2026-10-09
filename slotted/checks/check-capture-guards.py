#!/usr/bin/env python3
"""Every rule that rebinds a slot over an outside variable says the two do not alias.

Matching reads a matched binder's bound slot as any name, the name of one of the term's
free variables included: that is a fine alpha-variant of the term, and a language may
want it. It puts one duty on a rule. Where a right-hand side rebinds a slot `$b` over a
variable `v` the left-hand side matched OUTSIDE `$b`, the reading with `$b` as `v`'s
free variable builds a node that captures `v`; `let-lam-diff` reading
`let x = y in (λw. x w)` with `w` as `y` builds `λy. let x = y in x y`, and on the
paper's array study that collapsed every class into one. The rule owes
`(not-free $b v)`, which both the encoding and the reference evaluate.

`capture_guards` in `slotted-encoder.py` derives what a rule owes; this holds the two
rule libraries to it. Under the reference's nested matcher the guards are vacuous, its
bound slots staying injective, which is why the reference's own rule sets can lack them
and `check-reference-rules.py` discounts exactly these when comparing.

Usage:  ./check-capture-guards.py
"""

import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "slotted"))
sc = __import__("slotted-egglog")
slotenc = __import__("slotted-encoder")

LIBRARIES = [
    ROOT / "slotted" / "languages" / "array-rules.egg",
    ROOT / "slotted" / "languages" / "sdql-rules.egg",
    ROOT / "slotted" / "tests" / "sdql-paper-batax.egg",
]


def main():
    bad, rules = [], 0
    for path in LIBRARIES:
        # the source's own language: a library includes its declarations, a test makes them
        src = sc.Source(path)
        lang = src.lang
        for form in sc.parse(path.read_text()):
            if not (isinstance(form, list) and form and form[0] == "rewrite"):
                continue
            r = sc.rewrite_parts(src, form)
            rules += 1
            lhs = slotenc.rhs_of(lang, src.term(r["lhs"], ground=False))
            rhs_term = src.term(r["rhs"], ground=False)
            rhs = slotenc.rhs_of(lang, rhs_term)
            missing = slotenc.missing_capture_guards(lang, lhs, rhs, r["conds"])
            if missing:
                owed = " ".join(f"(not-free {s} {v})" for s, v in sorted(missing))
                print(f"  FAIL {path.name}: {r['name']} rebinds over an outside variable without {owed}")
                bad.append(r["name"])
    print(f"\n{rules - len(bad)}/{rules} rules state the capture guards they owe")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
