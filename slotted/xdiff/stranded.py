"""Does a stranded node carry anything no visible node carries?

A class holding a node but no `RenamesToLeader V s V` self-loop is invisible to
every compiled rule, since they all join that self-loop to reach the class's
symmetries. Whether that costs anything depends on whether some *visible* node is
alpha-equivalent to the stranded one -- same operator, same children, edges equal
up to one injective renaming of the node's own slots.

This decides that question by pairing each invisible row against every visible one
and searching for such a renaming. An empty report means the invariant holds on
this case: every fact on a self-loop-less class is also on a self-looped one.
"""

import re
import subprocess
import sys

sys.path.insert(0, "slotted/xdiff")
import xdiff as X

OBS = """
(relation WithSym (String Renaming U Renaming U))
(rule ((= V (App2 f p1 C1 p2 C2)) (RenamesToLeader V s V)) ((WithSym f p1 C1 p2 C2)))
(relation NoSym (String Renaming U Renaming U))
(rule ((= V (App2 f p1 C1 p2 C2))) ((NoSym f p1 C1 p2 C2)))
(print-size App2)
(run 40)
(print-size App2)
(print-function WithSym 100000)
(print-function NoSym 100000)
"""


def split_args(s):
    """Split a printed argument list at top-level spaces."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == " " and depth == 0:
            if cur:
                out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out


def parse_map(s):
    """`(map-of 0 2 1 1)` -> {0: 2, 1: 1}; `(map-of)` -> {}."""
    ns = [int(x) for x in re.findall(r"-?\d+", s)]
    return dict(zip(ns[0::2], ns[1::2], strict=False))


def parse_row(args):
    """`f m1 c1 m2 c2` as printed -> (op, m1, c1, m2, c2)."""
    a = split_args(args)
    return (a[0], parse_map(a[1]), a[2], parse_map(a[3]), a[4])


def slots_of(term):
    """Slot set of a printed `U` term. `None` when it cannot be determined."""
    term = term.strip()
    if term.startswith("(Var "):
        return {int(re.findall(r"-?\d+", term)[0])}
    if term.startswith("(Null"):
        return set()
    if term.startswith("(App2 "):
        a = split_args(term[len("(App2 ") : -1])
        out = set()
        for m, c in ((parse_map(a[1]), a[2]), (parse_map(a[3]), a[4])):
            cs = slots_of(c)
            if cs is None:
                return None
            out |= {m[k] for k in cs if k in m}
        return out
    return None  # e.g. `Unextractable`


def alpha_eq(x, y):
    """Same op and children, edges equal under one injective renaming of node slots.

    Each edge is first restricted to the slots its child actually has: the
    machinery does not force an edge's domain to match, so an edge can carry extra
    entries that mean nothing, and two rows differing only in those are the same
    node.
    """
    if x[0] != y[0] or x[2] != y[2] or x[4] != y[4]:
        return False
    rho = {}
    for mx, my, child in ((x[1], y[1], x[2]), (x[3], y[3], x[4])):
        cs = slots_of(child)
        if cs is None:
            return False
        kx, ky = {k: mx[k] for k in mx if k in cs}, {k: my[k] for k in my if k in cs}
        if set(kx) != set(ky):
            return False
        for k in kx:
            if rho.setdefault(kx[k], ky[k]) != ky[k]:
                return False
    return len(set(rho.values())) == len(rho)  # injective


def run_case(case, machinery=None):
    prog = X.egg_program(case).replace("(print-function SameClass 100000)", OBS)
    if machinery:
        prog = prog.replace(X.MACHINERY, machinery)
    p = X.ROOT / f"inv2-{abs(hash(case.name)) % 99999}.egg"
    p.write_text(prog)
    try:
        r = subprocess.run([str(X.EGGLOG), str(p)], capture_output=True, text=True, cwd=X.ROOT, timeout=600)
    except subprocess.TimeoutExpired:
        return None
    finally:
        p.unlink(missing_ok=True)

    def rows(tag):
        return [
            line.strip().split(" -> ")[0][len(tag) + 2 : -1]
            for line in r.stdout.splitlines()
            if line.strip().startswith(f"({tag} ")
        ]

    sizes = [int(line.strip()) for line in r.stdout.splitlines() if line.strip().isdigit()]
    fix = len(sizes) > 1 and sizes[0] == sizes[1]
    vis, allr = set(rows("WithSym")), rows("NoSym")
    return fix, [x for x in allr if x not in vis], vis


def report(case, machinery=None):
    got = run_case(case, machinery)
    if got is None:
        print(f"{case.name:34} timeout")
        return
    fix, invisible, vis = got
    tag = "fixpoint" if fix else "STILL MOVING"
    if not invisible:
        print(f"{case.name:34} [{tag}] nothing stranded")
        return
    vparsed = [parse_row(v) for v in vis]
    lost = []
    for row in invisible:
        p = parse_row(row)
        if not any(alpha_eq(p, q) for q in vparsed):
            lost.append(row)
    print(f"{case.name:34} [{tag}] stranded {len(invisible)}, of those with no visible alpha-variant: {len(lost)}")
    for row in lost:
        print(f"     UNIQUE: {row[:200]}")


for c in X.curated():
    if c.name.startswith(("X1", "X2")):
        report(c)
