"""Do `multipattern.egg`'s failing claims have teeth?

A `fail (check ...)` passes for two very different reasons: the rule correctly declined
to fire, or the rule could never have fired at all. The second is worthless, and it is
the easy mistake -- naming a term the rule would not produce even when misfiring, or
building the term after the `(run)`. Both happened while that file was written.

So each mutation below removes exactly one join from one rule and names the claims that
must then break. A mutation the file still passes is a claim that is not testing what
its comment says.

This is the .egg corpus's counterpart to `xdiff/mutations.py`, which puts past bugs back
into the compiler and requires the curated cases to notice. Same idea, different subject:
here the rules are mutated and the file's own claims are what must notice.

    python3 slotted/check-multipattern-teeth.py
"""

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "slotted/tests/multipattern.egg"
MUTANT = ROOT / "target/slotted/multipattern-mutant.egg"

#: (what it breaks, text to replace, replacement, the claims that may break)
MUTATIONS = [
    (
        "beta premise unjoined from the function",
        ':when ((= f (Lam $v body)))\n         :name "beta-guarded"',
        ':when ((= zz (Lam $v body)))\n         :name "beta-guarded"',
        {"stuck"},
    ),
    (
        "load-after-store no longer joins on the address",
        ":when ((= m (Store m0 p v)))",
        ":when ((= m (Store m0 pp v)))",
        {"other"},
    ),
    (
        "double-product no longer joins the two factor pairs",
        "(= r (Mul a b))",
        "(= r (Mul aa bb))",
        {"no"},
    ),
    (
        "double-product's top pattern unjoined from the match",
        "(= e (Add l r))",
        "(= ee (Add l r))",
        # any `Root` now qualifies, so either failing claim may be the one reported
        {"no", "no2"},
    ),
    (
        "same-body no longer shares the body",
        "(= g (Lam $w body))",
        "(= g (Lam $w body2))",
        {"q"},
    ),
    (
        "eta's shape premise unjoined from the function",
        "(= f (Lam $w g))",
        "(= zz (Lam $w g))",
        {"notlam"},
    ),
    (
        "eta's slot side condition dropped",
        "(not-free $v f)\n                ",
        "",
        {"held"},
    ),
    (
        "cross-product loses its third disconnected pattern",
        "\n                (= r (Store s1 s2 s3))",
        "",
        {"root2"},
    ),
    (
        "cross-slots stops asking the Add's children to be one slot",
        "(= r (Add $u $u))",
        "(= r (Add $u $u2))",
        {"root4"},
    ),
    (
        "abstract-constant takes its argument from the OTHER lambda",
        "(App (Lam $n (Lam $x (Add $x $n))) a)",
        "(App (Lam $n (Lam $x (Add $x $n))) b)",
        {"f2"},
    ),
    (
        "the payload join stops asking for one number",
        "(= y (Num i))",
        "(= y (Num j))",
        {"mixed"},
    ),
    (
        "abstract-constant stops asking the two constants to differ",
        "(= other (Lam $y (Add $y b)))\n                (!= a b))",
        "(= other (Lam $y (Add $y b))))",
        {"lone"},
    ),
]

BROKE = re.compile(r"check \(RenamesToLeader \$([A-Za-z_][\w-]*)")


def broken_claim(text):
    """The term named by the claim egglog reported, or None if the file passed."""
    m = BROKE.search(text)
    return m.group(1) if m else None


def mask_comments(text):
    """`text` with every comment character replaced by NUL, so an offset found in it is
    an offset into `text` that is not inside a comment."""
    out, in_comment = [], False
    for ch in text:
        if ch == "\n":
            in_comment = False
        elif ch == ";":
            in_comment = True
        out.append("\0" if in_comment else ch)
    return "".join(out)


def replace_code(text, old, new):
    """Replace EVERY occurrence of `old` in `text` that is not inside a comment.

    The sections here quote their own rules, so a plain `str.replace` hit the prose
    above the rule and mutated nothing -- a no-op mutation, which is exactly the
    vacuity this file exists to rule out.

    Every occurrence rather than the first, because a rule asked about in two ways
    is written twice: `(pop)` removes it with its region, so the positive and negative
    halves of the disconnected cases each declare it. Mutating one and not the other
    would leave the half under test untouched. The other mutations name text that
    occurs once, for which this is the same thing.

    Returns None when `old` appears in no code.
    """
    masked = mask_comments(text)
    if old not in masked:
        return None
    out, at = [], 0
    while True:
        i = masked.find(old, at)
        if i < 0:
            out.append(text[at:])
            return "".join(out)
        out.append(text[at:i])
        out.append(new)
        at = i + len(old)


def main():
    src = CORPUS.read_text()
    MUTANT.parent.mkdir(parents=True, exist_ok=True)
    bad = []
    for name, old, new, want in MUTATIONS:
        mutated = replace_code(src, old, new)
        if mutated is None:
            print(f"  STALE  {name}: the text it mutates is in no rule (only prose, or gone)")
            bad.append(name)
            continue
        MUTANT.write_text(mutated)
        r = subprocess.run(
            [sys.executable, "slotted/slotted-egglog.py", str(MUTANT)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=1800,
        )
        got = broken_claim(r.stdout + r.stderr)
        if got in want:
            print(f"  ok     {name}  ->  `{got}` breaks")
        elif got is None:
            # a mutant that fails for some OTHER reason has not shown a claim has teeth
            why = next((ln for ln in (r.stdout + r.stderr).splitlines() if ln.strip()), "")
            note = "the file still passes, so no claim tests it" if why.startswith("ok") else why[:80]
            print(f"  FAIL   {name}  ->  {note}")
            bad.append(name)
        else:
            print(f"  FAIL   {name}  ->  `{got}` broke, expected one of {sorted(want)}")
            bad.append(name)
    MUTANT.unlink(missing_ok=True)
    print(f"\n{len(MUTATIONS) - len(bad)}/{len(MUTATIONS)} multipattern claims have teeth")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
