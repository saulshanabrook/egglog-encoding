#!/usr/bin/env python3
"""Check both matching modes against their own reference, including lost aliases."""

import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / "slotted"), str(ROOT / "slotted" / "xdiff")]
import eval as E  # noqa: E402
import xdiff as X  # noqa: E402

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


def compiler_flag(tmp):
    path = Path(tmp) / "flag.egg"
    path.write_text(
        '(include "slotted/languages/toy.egg")\n'
        "(rewrite (F a (G b n)) (H a b))\n"
        "(check (= (F $0 (G $1 (Null))) (F $0 (G $1 (Null)))))\n"
    )
    result = subprocess.run(
        [sys.executable, E.sc.__file__, path, "--nested-compat", "--desugar", "--own-only"],
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode == 0, result.stderr
    assert "(nested-atom " in result.stdout and "(atom " in result.stdout
    path.write_text('(include "slotted/languages/toy.egg")\n(rewrite (F a b) a :when ((= b (G x y))))\n')
    result = subprocess.run(
        [sys.executable, E.sc.__file__, path, "--nested-compat", "--desugar"],
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode != 0 and "single nested pattern" in result.stderr
    assert "Traceback" not in result.stderr


def main():
    E.EGGLOG = ROOT / "target" / "debug" / "egglog"
    E.XMULTI = ROOT / "slotted" / "xmulti" / "target" / "debug" / "xmulti"
    with tempfile.TemporaryDirectory(prefix="slotted-nested-") as tmp:
        compiler_flag(tmp)
        for name, unions, start, lhs, rhs, differs in CASES:
            path = Path(tmp) / f"{name}.egg"
            path.write_text(
                '(include "slotted/languages/toy.egg")\n'
                f"{unions}\n(let start {start})\n(rewrite {lhs} {rhs})\n(run 1)\n"
            )
            sizes = []
            for compat in (False, True):
                src = E.sc.Source(path)
                head = [
                    "rounds 1",
                    *E.ctor_lines(X.LANG),
                    f"term {X.LANG.sexpr(src.term(E.sc.parse(start)[0], ground=True))}",
                    "term (var $0)",
                    *(
                        "union " + " ".join(X.LANG.sexpr(src.term(t, ground=True)) for t in f[1:])
                        for f in E.sc.parse(unions)
                    ),
                ]
                spec = "\n".join(head + E.rule_lines(X.LANG, path, None, nested=compat)) + "\n"
                enc, ref = (
                    E.Row("regression", name, side, 1)
                    for side in (
                        ("encoding-no-aliasing", "ref-nested-snapshot") if compat else ("encoding", "ref-multi")
                    )
                )
                program = E.sc.compile_source(src, nested_compat=compat)
                E.encoding_counts(program, name, X.LANG, enc, 30)
                E.run_reference(spec, ref, 30, True)
                E.compare([enc, ref])
                assert enc.verdict(ref) == "isomorphic", (name, compat, enc.verdict(ref))
                assert (enc.classes, enc.nodes) == (ref.classes, ref.nodes)
                sizes.append(enc.nodes)
            assert (sizes[0] > sizes[1]) if differs else (sizes[0] == sizes[1]), (name, sizes)
    print(f"OK: {len(CASES)} cases match both reference matchers with their respective aliasing policies")


if __name__ == "__main__":
    main()
