"""Does this language still refuse what it says it refuses, and say why?

Every refusal below is a program the compiler must decline, with the phrase its message
has to carry. Two things rot silently and neither changes any answer:

  * a refusal that stops firing -- the program is then quietly mistranslated, which is
    what `(constructor Succ (S) S)` did before sorts were carriers;
  * a refusal that fires as a PYTHON TRACEBACK rather than a message, which is what
    `(datatype ...)` did. A user-facing error is prose, not a stack.

So each case must exit nonzero, print its phrase, and show no traceback.

    python3 slotted/check-refusals.py
"""

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TMP = ROOT / "target" / "slotted" / "refusal.egg"

LANG = "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n"

#: (what is refused, program, a phrase the message must carry)
CASES = [
    ("a global named with a `$`", LANG + "(let $I (IConst))\n", "may not be named"),
    ("an unbound `#global`", LANG + '(rewrite (Mul a #nope) a :name "r")\n', "no global"),
    (
        "a global bound to a bare slot invocation",
        LANG + "(let v $7)\n",
        "cannot currently store",
    ),
    (
        "a `#global` in a binder column",
        LANG + "(let g (IConst))\n(let bad (Lam #g #g))\n",
        "binder column",
    ),
    (
        "several `:when` clauses",
        LANG + '(rewrite (Mul a b) a :when ((= a (Succ p))) :when ((= b (Succ q))) :name "r")\n',
        "one list",
    ),
    (
        "egglog's `:cost`, which extraction here would not honour",
        "(sort M)\n(constructor Succ (M) M :cost 5)\n",
        "not implemented here",
    ),
    ("an unknown declaration option", "(sort M)\n(constructor Succ (M) M :wat 1)\n", "unknown option"),
    (
        "a negative binder position",
        "(sort M)\n(constructor F (M M) M :binder -1)\n",
        "outside",
    ),
    (
        "an out-of-range binder position",
        "(sort M)\n(constructor F (M M) M :binder 2)\n",
        "outside",
    ),
    (
        "duplicate binder positions",
        "(sort M)\n(constructor F (M M) M :binder 0 0)\n",
        "duplicate",
    ),
    (
        "non-contiguous nested binders",
        "(sort M)\n(constructor F (M M M M) M :binder 0 2)\n",
        "contiguous",
    ),
    (
        "a binder without a covered child",
        "(sort M)\n(constructor F (M M) M :binder 1)\n",
        "followed",
    ),
    (
        "a cross-sort slotted child",
        "(sort A)\n(sort B)\n(constructor A0 () A)\n(constructor B0 () B)\n(constructor F (A B) A)\n",
        "cross-sort slotted children",
    ),
    ("a sort named after a rule variable in the core", "(sort m)\n(constructor F (m) m)\n", "would capture"),
    (
        "a cross-sort union",
        "(datatype* (A (A0)) (B (B0)))\n(let a (A0))\n(let b (B0))\n(union a b)\n",
        "cannot union terms of sorts",
    ),
    (
        "a global used at the wrong sort",
        "(datatype* (A (A0)) (B (B0) (G B)))\n(let a (A0))\n(let bad (G a))\n",
        "this position requires B",
    ),
    (
        "a cross-sort equality check",
        "(datatype* (A (A0)) (B (B0)))\n(check (= (A0) (B0)))\n",
        "cannot compare terms of sorts",
    ),
    (
        "a cross-sort renaming equality check",
        "(datatype* (A (A0)) (B (B0)))\n(check (renaming-= (A0) (B0)))\n",
        "cannot compare terms of sorts",
    ),
    (
        "a holds check naming a constructor from another sort",
        "(datatype* (A (A0)) (B (B0)))\n(check (holds (A0) B0))\n",
        "B nodes, not A nodes",
    ),
    (
        "a cross-sort rewrite result",
        '(datatype* (A (A0)) (B (B0)))\n(rewrite (A0) (B0) :name "bad")\n',
        "where A is required",
    ),
    (
        "a cross-sort side pattern",
        '(datatype* (A (A0)) (B (B0)))\n(rewrite (A0) (A0) :when ((B0)) :name "bad")\n',
        "cross-sort multipatterns",
    ),
    (
        "an ambiguous top-level slot comparison",
        "(datatype* (A (A0)) (B (B0)))\n(check (= $0 $1))\n",
        "no equality sort",
    ),
    (
        "a multi-sort encoding-name collision",
        "(sort A)\n(sort B)\n(constructor SlottedVar_0 () A)\n(constructor B0 () B)\n",
        "reserved by the multi-sort",
    ),
    (
        "a duplicate equality sort declaration",
        "(sort A)\n(sort A)\n(constructor A0 () A)\n",
        "sort is declared more than once",
    ),
    (
        "a duplicate constructor declaration",
        "(sort A)\n(constructor A0 () A)\n(constructor A0 () A)\n",
        "constructor 'A0' is declared more than once",
    ),
    ("a program that declares nothing", "(run 1)\n", "no constructors declared"),
    ("a rewrite whose left side is a bare variable", LANG + '(rewrite x (Mul x x) :name "r")\n', "must be a call"),
    ("egglog's `rule`, which this language does not have", LANG + "(rule ((= a (Null))) ())\n", "not part of"),
    (
        "a payload variable the right-hand side names and no pattern binds",
        '(sort M)\n(constructor N (i64) M)\n(constructor A (M M) M)\n(rewrite (A x y) (N j) :name "r")\n',
        "no pattern binds",
    ),
]


def main():
    TMP.parent.mkdir(parents=True, exist_ok=True)
    bad = []
    for what, program, phrase in CASES:
        TMP.write_text(program)
        r = subprocess.run(
            [sys.executable, "slotted/slotted-egglog.py", str(TMP)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=600,
        )
        out = r.stdout + r.stderr
        if r.returncode == 0:
            print(f"  FAIL {what}: accepted")
            bad.append(what)
        elif "Traceback (most recent call last)" in out:
            print(f"  FAIL {what}: refused with a traceback, not a message")
            bad.append(what)
        elif phrase not in out:
            print(f"  FAIL {what}: message lacks {phrase!r}\n       {out.strip().splitlines()[-1][:120]}")
            bad.append(what)
        else:
            print(f"  ok   {what}")
    TMP.unlink(missing_ok=True)
    print(f"\n{len(CASES) - len(bad)}/{len(CASES)} refusals hold, with a message")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
