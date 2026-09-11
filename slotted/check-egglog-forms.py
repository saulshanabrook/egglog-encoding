"""How much of egglog's rule and declaration grammar does this language accept?

An inventory, asserted rather than remembered. Each probe is a small program and each
carries the verdict it should get:

    ok        accepted and run
    refused   declined with a MESSAGE -- either by design, or a gap stated plainly

A traceback is never a verdict: a user-facing error is prose. A probe whose verdict
CHANGES is reported either way, since accepting more is news and accepting less is a
regression.

This is what says which egglog forms are missing without anyone having to remember. The
gaps it currently records are value primitives over payloads -- egglog's arithmetic and
comparisons -- and the actions `set`/`delete`/`subsume`, which need `rule`.

    python3 slotted/check-egglog-forms.py
"""

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TMP = ROOT / "target" / "slotted" / "forms.egg"

L = "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n"

#: (expected verdict, what, program)
PROBES = [
    # ---- facts in a rule body -----------------------------------------------------
    ("ok", "a nested call as the pattern", L + '(rewrite (Add (Mul x y) z) (Nil) :name "r")\n'),
    ("ok", "(= v <call>), a second pattern", L + '(rewrite (Add x y) (Nil) :when ((= x (Mul p q))) :name "r")\n'),
    ("ok", "(= x y), two variables identified", L + '(rewrite (Add x y) (Nil) :when ((= x y)) :name "r")\n'),
    ("ok", "(!= x y)", L + '(rewrite (Add x y) (Nil) :when ((!= x y)) :name "r")\n'),
    ("ok", "a bare call, meaning it exists", L + '(rewrite (Add x y) (Nil) :when ((Mul x y)) :name "r")\n'),
    ("ok", "a payload literal", L + '(rewrite (Add x y) (Nil) :when ((= x (N 2))) :name "r")\n'),
    ("ok", "a payload variable", L + '(rewrite (Add x y) (Nil) :when ((= x (N i))) :name "r")\n'),
    ("ok", "free/not-free on a slot", L + '(rewrite (Lam $v b) (Nil) :when ((not-free $v b)) :name "r")\n'),
    ("refused", "an i64 primitive over payloads", L + '(rewrite (Add x y) (Nil) :when ((> x y)) :name "r")\n'),
    # ---- the right-hand side ------------------------------------------------------
    ("ok", "builds a term", L + '(rewrite (Add x y) (Mul y x) :name "r")\n'),
    ("ok", "a variable", L + '(rewrite (Add x y) x :name "r")\n'),
    ("ok", "a fresh slot, with no annotation", L + '(rewrite (Add x y) (Lam $s (Add x y)) :name "r")\n'),
    ("refused", "computing a payload", L + '(rewrite (Add (N i) (N j)) (N (+ i j)) :name "r")\n'),
    # ---- rewrite options ----------------------------------------------------------
    ("ok", ":name, as a string literal", L + '(rewrite (Add x y) (Nil) :name "r")\n'),
    ("ok", ":ruleset", "(ruleset rs)\n" + L + '(rewrite (Add x y) (Nil) :ruleset rs :name "r")\n'),
    ("refused", ":subsume", L + '(rewrite (Add x y) (Nil) :subsume :name "r")\n'),
    # ---- declarations -------------------------------------------------------------
    ("ok", "datatype", L + "(let a (N 1))\n(run 0)\n"),
    ("ok", "sort plus constructor", "(sort M)\n(constructor N (i64) M)\n(let a (N 1))\n(run 0)\n"),
    ("ok", "relation", L + "(relation R (M M))\n"),
    ("ok", "function with :merge", L + "(function Cost (M) i64 :merge (min old new))\n"),
    ("refused", "constructor :cost", "(sort M)\n(constructor N (i64) M :cost 5)\n"),
    (
        "ok",
        "datatype*, with independent homogeneous sorts",
        "(datatype* (A (A0) (F A)) (B (B0) (G B)))\n(let a (F (A0)))\n(let b (G (B0)))\n(run 0)\n",
    ),
    # ---- other rule forms ---------------------------------------------------------
    ("refused", "rule", L + "(rule ((= a (Nil))) ())\n"),
    ("refused", "birewrite", L + '(birewrite (Add x y) (Add y x) :name "r")\n'),
    ("refused", "set, which needs rule", L + "(function C (M) i64 :no-merge)\n(rule ((= a (Nil))) ((set (C a) 1)))\n"),
    # ---- commands -----------------------------------------------------------------
    ("ok", "push and pop", L + "(push)\n(let a (Nil))\n(pop)\n"),
    (
        "ok",
        "extract, selecting either carrier",
        "(datatype* (A (A0)) (B (B0)))\n(let a (A0))\n(let b (B0))\n(run 0)\n(extract a)\n(extract b)\n",
    ),
    ("ok", "print-size", L + "(let a (Nil))\n(run 0)\n(print-size)\n"),
    ("refused", "run-schedule, which would skip the phasing", L + "(let a (Nil))\n(run-schedule (run 1))\n"),
]


def verdict_of(program):
    TMP.write_text(program)
    r = subprocess.run(
        [sys.executable, "slotted/slotted-egglog.py", str(TMP)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=1800,
    )
    out = r.stdout + r.stderr
    if "Traceback (most recent call last)" in out:
        return "CRASH", next((ln for ln in reversed(out.splitlines()) if ln.strip()), "")[:80]
    if r.returncode == 0:
        return "ok", ""
    return "refused", next((ln for ln in out.splitlines() if ln.strip()), "")[:80]


def main():
    TMP.parent.mkdir(parents=True, exist_ok=True)
    bad = []
    for want, what, program in PROBES:
        got, detail = verdict_of(program)
        if got == want:
            print(f"  {got:8} {what}")
        else:
            print(f"  {'CHANGED':8} {what}: expected {want}, got {got}\n           {detail}")
            bad.append(what)
    TMP.unlink(missing_ok=True)
    n_ok = sum(1 for w, _, _ in PROBES if w == "ok")
    print(f"\n{len(PROBES) - len(bad)}/{len(PROBES)} egglog forms behave as recorded ({n_ok} accepted)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
