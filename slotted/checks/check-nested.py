#!/usr/bin/env python3
"""Check both matching modes against their own reference, including lost aliases."""

import re
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from slotted import runner as run  # noqa: E402
from slotted import verify as V  # noqa: E402
from slotted import workloads as W  # noqa: E402
from slotted.xdiff import xdiff as X  # noqa: E402

# name, initial unions, input, pattern, replacement, whether full matching adds nodes
CASES = [
    ("optional", "(union (G $0 (Null)) (Null))", "(F $1 (Null))", "(F a (G b n))", "(H a b)", True),
    ("repeated-var", "(union (G $0 (Null)) (Null))", "(F $1 (Null))", "(F a (G a n))", "(H a a)", True),
    ("repeated-literal", "(union (G $0 (Null)) (Null))", "(F $1 (Null))", "(F $x (G $x n))", "(H $x $x)", True),
    (
        "siblings",
        "(union (G $0 (Null)) (Null)) (union (K $1 (Null)) (Null))",
        "(F (Null) (Null))",
        "(F (G a n) (K b m))",
        "(H a b)",
        True,
    ),
    (
        "sibling-repeat",
        "(union (G $0 (Null)) (Null)) (union (K $1 (Null)) (Null))",
        "(F (Null) (Null))",
        "(F (G a n) (K a m))",
        "(H a a)",
        True,
    ),
    ("shared", "", "(F $0 (G $0 (Null)))", "(F a (G a n))", "(H a a)", False),
    ("binders", "", "(F (Lam $0 $0) (Lam $1 $1))", "(F (Lam $x a) (Lam $x b))", "(H a b)", True),
    ("named-binders", "", "(F (Lam $a $a) (Lam $a0 $a0))", "(F (Lam $x a) (Lam $x b))", "(H a b)", True),
    ("named-and-numbered", "", "(F $a0 (G $0 (Null)))", "(F a (G b n))", "(H a b)", False),
    (
        "named-shadowing",
        "",
        "(Lam $a (Lam $a (F $a $a0)))",
        "(Lam $x (Lam $y (F $y body)))",
        "(Lam $x (Lam $y (G body $y)))",
        False,
    ),
    ("binder-capture", "", "(F $4 (Lam $5 $5))", "(F a (Lam $x b))", "(Lam $x (F a b))", True),
    (
        "symmetry",
        "(union (F $0 $1) (F $1 $0))",
        "(G $0 (F $0 $1))",
        "(G $x (F a $x))",
        "(H a $x)",
        False,
    ),
]


def reference_term(src, form):
    text = X.LANG.sexpr(src.term(form, ground=True))
    # Exercise the reference's own named-slot parser as well.
    return re.sub(r"\$[+-]?\d+", lambda m: src.slots.sources[int(m[0][1:])], text)


def main():
    config = run.Config(
        egglog=ROOT / "target/debug/egglog-experimental",
        xmulti=ROOT / "slotted/xmulti/target/debug/xmulti",
        checker=ROOT / "target/debug/egraph-isomorphism",
    )
    with tempfile.TemporaryDirectory(prefix="slotted-nested-") as tmp:
        for name, unions, start, lhs, rhs, differs in CASES:
            path = Path(tmp) / f"{name}.egg"
            path.write_text(
                '(include "egglog-experimental/tests/slotted/languages/toy.egg")\n'
                f"{unions}\n(let start {start})\n(rewrite {lhs} {rhs})\n(run 1)\n"
            )
            sizes = []
            for compat in (False, True):
                src = W.syntax.Source(path)

                head = [
                    "rounds 1",
                    *W.ctor_lines(X.LANG),
                    f"term {reference_term(src, W.syntax.parse(start)[0])}",
                    "term (var $0)",
                    *("union " + " ".join(reference_term(src, t) for t in f[1:]) for f in W.syntax.parse(unions)),
                ]
                spec = "\n".join(head + W.rule_lines(X.LANG, path, None, nested=compat)) + "\n"
                enc, ref = (
                    run.Row("regression", name, side, 1)
                    for side in (
                        ("encoding-no-aliasing", "ref-nested-snapshot") if compat else ("encoding", "ref-multi")
                    )
                )
                program = path.read_text()
                V.encoding_counts(program, name, X.LANG, enc, 30, config=config)
                run.run_reference(spec, ref, 30, config=config)
                V.reference_counts(spec, ref, 30, config=config)
                V.compare([enc, ref])
                assert enc.verdict(ref) == "isomorphic", (name, compat, enc.verdict(ref))
                assert (enc.classes, enc.nodes) == (ref.classes, ref.nodes)
                sizes.append(enc.nodes)
            assert (sizes[0] > sizes[1]) if differs else (sizes[0] == sizes[1]), (name, sizes)
    print(f"OK: {len(CASES)} cases match both reference matchers with their respective aliasing policies")


if __name__ == "__main__":
    main()
