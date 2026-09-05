#!/usr/bin/env python3
"""Compile every slotted-language test and run it.

A test in `slotted/tests/` is a SLOTTED source when it includes nothing: it declares
its own constructors and the compiler supplies the core and the machinery. A test that
`(include ...)`s something is written in plain egglog against the encoding -- the
machinery tests -- and is run directly by `check-slotted.py`'s `egg-files`.

Usage:
    ./run-slotted-tests.py            compile and run each
    ./run-slotted-tests.py -k sdql    only those whose name contains `sdql`
    ./run-slotted-tests.py --emit     also write each test's own compiled forms to
                                      slotted/tests/snapshots/, so a change in the
                                      encoder shows up as a diff
"""

import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SRC_DIR = ROOT / "slotted" / "tests"
SNAPSHOTS = SRC_DIR / "snapshots"
COMPILE = ROOT / "slotted" / "slotted-egglog.py"


#: The hand-written core. It includes nothing because everything else includes IT, so
#: it is the one file the rule below would otherwise misread as a slotted source.
CORE = "egraph-encoding-11.egg"


def slotted_sources():
    """The tests written in the slotted language.

    Told apart by WHAT they include, not by whether they include anything: a slotted
    source may include another slotted source -- that is how a test over the sdql rules
    gets them without restating 43 -- but never the hand-written core and never a
    generated file, because the compiler supplies the first and generates the second. A
    test written against the encoding includes one of those, which is what makes it not
    a source.
    """
    seen = {}

    def is_source(q):
        """Transitively: everything it reaches has to be a source too.

        The tutorial's test file includes the tutorial, which includes a generated
        machinery file -- so neither is a source, and only following the chain says so.
        """
        key = q.name
        if key in seen:
            return seen[key]
        seen[key] = False  # a cycle is not a source
        if key == CORE:
            return False
        ok = True
        for t in re.findall(r'\(include "([^"]*)"\)', q.read_text()):
            target = ROOT / t
            if not t.startswith("slotted/tests/") or "generated/" in t or not target.exists():
                ok = False
                break
            if not is_source(target):
                ok = False
                break
        seen[key] = ok
        return ok

    # Recursive: `paper/` holds one file per reference test. `snapshots/` is compiled
    # output rather than a source, and is excluded by name rather than by reading it.
    # `slotted/languages/` holds a language and its rules -- no terms, nothing asked --
    # so those come out as the rule libraries the count line reports. They are compiled
    # and loaded here so a broken one is caught where it lives, not in a test that
    # happens to include it.
    files = [q for q in sorted(SRC_DIR.rglob("*.egg")) if SNAPSHOTS not in q.parents]
    files += sorted((ROOT / "slotted" / "languages").glob("*.egg"))
    return [q for q in files if is_source(q)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-k", metavar="SUBSTRING")
    ap.add_argument("--emit", action="store_true", help="also write the snapshots")
    args = ap.parse_args()

    srcs = [p for p in slotted_sources() if not args.k or args.k in p.name]
    if not srcs:
        print("no slotted sources found")
        return 1
    # A source with no claim in it is a rule LIBRARY, not a test. It is still compiled
    # and run, so its rules have to load, but counting it as a passing test would
    # inflate the number with something that asserts nothing.
    libs = {p.name for p in srcs if "(check" not in p.read_text()}

    if args.emit:
        SNAPSHOTS.mkdir(exist_ok=True)

    bad = []
    for src in srcs:
        cmd = [sys.executable, str(COMPILE), str(src), "--run"]
        # A library's rules are already snapshotted by the generator that emits them
        # into `target/slotted/`, so snapshotting its compiled program too
        # would commit the same 43 rules twice.
        if args.emit and src.name not in libs:
            # `--own-only`: the machinery and any included library are snapshotted by
            # the generators that emit them, so a test's snapshot is its own compiled
            # terms, rules and claims -- the part nothing else covers.
            cmd += ["--own-only", "-o", str(SNAPSHOTS / src.name)]
        r = subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT, timeout=1800)
        line = (r.stdout.strip().splitlines() or [""])[0]
        print(f"  {line or r.stderr.strip()[:160]}")
        if r.returncode != 0:
            bad.append(src.name)

    tests = [p for p in srcs if p.name not in libs]
    print(
        f"\n{len(tests) - len([b for b in bad if b not in libs])}/{len(tests)} slotted tests pass"
        + (f", {len(libs)} rule librar{'y loads' if len(libs) == 1 else 'ies load'}" if libs else "")
        + (f"   FAILED: {', '.join(bad)}" if bad else "")
    )
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
