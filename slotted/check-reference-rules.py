#!/usr/bin/env python3
"""Our rule sets are the reference's, name for name.

`sdql.egg` and `array.egg` claim to carry the reference's rules. That claim went
unchecked, and drifted twice in one session: the sdql file said "rule for rule" while
missing `beta`, and then gained `sum-range-2`, which the reference DEFINES but does not
RUN. Counting `Rewrite::new` calls is the trap -- a rule only counts if it reaches the
list handed to the runner.

Compares the `:name` of every rewrite here against the names the reference's own list
holds, and reports both directions.

Usage:  ./check-reference-rules.py
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
REF = pathlib.Path(
    "/home/oflatt/.cargo/git/checkouts/slotted-egraphs-7130c4ea9b57459d/e1bfe1b"
)

#: ours -> (the reference's file, the name of the function returning its rule list, and
#: the names we spell differently)
SUITES = {
    "sdql": (
        ROOT / "slotted" / "languages" / "sdql.egg",
        REF / "benches" / "sdql.rs",
        {},
    ),
    "array": (
        ROOT / "slotted" / "languages" / "array.egg",
        REF / "tests" / "rise" / "rewrite.rs",
        # the reference's name -> ours, where the two chose different words for one rule
        {"beta": "let-intro", "my-let-unused": "let-unused"},
    ),
}

#: Rules the reference runs that we deliberately do not carry, and why. A rule leaving
#: this list is a gap; a rule appearing in it without a reason is not allowed.
EXPECTED_MISSING = {
    "array": {
        "eta-expansion": "left-hand side is a bare pattern variable: it matches every class",
        "let-var-diff": "not written yet",
        "let-app-unopt": "an unoptimised variant of `let-app`, which is here",
        "let-lam-diff-unopt": "an unoptimised variant of `let-lam-diff`, which is here",
        "map-slide-before-transpose": "needs slide and transpose, which this language does not declare",
        "remove-transpose-pair": "needs transpose",
        "separate-dot-hv-simplified": "needs the dot-product operators",
        "separate-dot-vh-simplified": "needs the dot-product operators",
        "slide-before-map": "needs slide",
        "slide-before-map-map-f": "needs slide",
    },
}


def our_names(path):
    return set(re.findall(r":name\s+([\w-]+)", path.read_text()))


def their_names(path):
    """The rules the reference RUNS, not the ones it merely defines.

    The two files build their list differently -- `benches/sdql.rs` with a `vec![]` and
    `tests/rise` with repeated `rewrites.push(..)` -- so neither shape is parsed. A rule
    counts when its constructor is CALLED somewhere other than its own definition, which
    is what `#[allow(unused)]` on `get_sum_vert_fuse_1` is telling the Rust compiler it
    is not.
    """
    src = path.read_text()
    defined = {}
    for m in re.finditer(r"fn (\w+)\(\)[^{]*\{", src):
        fn, start = m.group(1), m.end()
        body = src[start : start + 800]
        name = re.search(r"Rewrite::new(?:_if)?\(\s*\n?\s*\"([^\"]+)\"", body)
        if name:
            defined[fn] = (name.group(1), m.start(), start)

    out = set()
    for fn, (rule, def_start, def_end) in defined.items():
        for call in re.finditer(rf"\b{re.escape(fn)}\(\)", src):
            if not (def_start <= call.start() < def_end):
                out.add(rule)
                break
    return out


def main():
    bad = []
    for name, (mine, theirs, alias) in SUITES.items():
        if not theirs.is_file():
            print(f"  skip {name}: {theirs} not found")
            continue
        ours = our_names(mine)
        ref = {alias.get(r, r) for r in their_names(theirs)}
        extra = sorted(ours - ref)
        missing = sorted(ref - ours)
        unexplained = [m for m in missing if m not in EXPECTED_MISSING.get(name, {})]
        stale = [m for m in EXPECTED_MISSING.get(name, {}) if m in ours or m not in ref]
        ok = not extra and not unexplained and not stale
        bad += [] if ok else [name]
        print(f"  {'ok  ' if ok else 'FAIL'} {name:6} {len(ours)} ours, {len(ref)} run by the reference")
        if extra:
            print(f"       ours but NOT run by the reference: {', '.join(extra)}")
        if unexplained:
            print(f"       run by the reference and missing here: {', '.join(unexplained)}")
        if stale:
            print(f"       recorded as missing but not: {', '.join(stale)}")
    print(f"\n{len(SUITES) - len(bad)}/{len(SUITES)} rule sets match the reference")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
