#!/usr/bin/env python3
"""Reference comparisons and generated differential checks for the slotted encoding.

Compiler fixtures, maintenance regressions, and language examples run in cargo test.

A check passes only if its tool exits 0 AND its summary line says everything agreed,
so a tool that runs zero cases fails rather than reporting a vacuous pass. The
recorded totals are floors: adding cases is fine, losing them is not.

Needs `target/debug/egglog-experimental` and
`slotted/xmulti/target/debug/xmulti`.

Usage:
    ./check-slotted.py           everything
    ./check-slotted.py --quick   skip the fuzzers
    ./check-slotted.py -k iso    only checks whose name contains `iso`
    ./check-slotted.py --no-oracle
                                 only what needs no reference build
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EGGLOG = ROOT / "target" / "debug" / "egglog-experimental"
XMULTI = ROOT / "slotted" / "xmulti" / "target" / "debug" / "xmulti"


def ratio(pattern, floor):
    """`n/m <something>` with n == m, and m at least `floor`."""

    def check(out):
        m = re.search(pattern, out, re.M)
        if not m:
            return f"no summary line matching /{pattern}/"
        got, tot = int(m.group(1)), int(m.group(2))
        if got != tot:
            return f"{got}/{tot} passed"
        if tot < floor:
            return f"only {tot} cases, expected at least {floor}"
        return None

    return check


def zero_categories(out):
    """xdiff prints one line per disagreement category; all must be 0."""
    bad = [
        line.strip()
        for line in out.splitlines()
        if re.match(r"^\s+[1-9]\d*\s+[a-zA-Z]", line) and "of those" not in line and "usable baseline" not in line
    ]
    return f"non-zero categories: {'; '.join(bad)}" if bad else None


def none_of(pattern, floor):
    """Require named groups `bad` to be zero and `seen` to meet the coverage floor."""

    def check(out):
        m = re.search(pattern, out, re.M)
        if not m:
            return f"no summary line matching /{pattern}/"
        bad, seen = int(m.group("bad")), int(m.group("seen"))
        if bad:
            return f"{bad} violation(s)"
        if seen < floor:
            return f"only {seen} cases checked, expected at least {floor}"
        return None

    return check


def both(*fns):
    def check(out):
        return next((r for r in (f(out) for f in fns) if r), None)

    return check


def starts_ok(out):
    return None if out.lstrip().startswith("OK:") else "no OK line"


# Check name, Python script/arguments, output validator, fuzzing flag, reference flag.
CHECKS = [
    ("evaluation-correctness", ("slotted/checks/check-eval.py",), starts_ok, False, True),
    ("nested-compatibility", ("slotted/checks/check-nested.py",), starts_ok, False, True),
    (
        "paper-sdql-provenance",
        ("slotted/checks/check-paper-sdql.py",),
        starts_ok,
        False,
        False,
    ),
    (
        "paper-sdql-reference-goal",
        ("slotted/checks/check-paper-sdql.py", "--reference"),
        starts_ok,
        False,
        True,
    ),
    # Capture guards are required in both libraries and the BATAX fixture's copies.
    (
        "capture-guards",
        ("slotted/checks/language.py", "guards"),
        ratio(r"(\d+)/(\d+) rules state the capture guards they owe", 60),
        False,
        False,
    ),
    # Reproductions of OPEN bugs, which must still reproduce. Kept out of `curated()`
    # so a known divergence cannot turn the green checks red, and asserted here so it
    # cannot be quietly lost either -- one that starts agreeing is reported.
    (
        "known-divergences",
        ("slotted/xdiff/isomorphism.py", "known"),
        ratio(r"(\d+)/(\d+) known divergences still diverge", 0),
        False,
        True,
    ),
    (
        # Pin known semantic gaps separately from the green differential suite. If a
        # fix makes either side move, this reports the stale witness instead of quietly
        # accepting a previously wrong answer.
        "known-encoding-limitations",
        ("slotted/xdiff/xsdql.py", "known-encoding-limitations"),
        ratio(r"(\d+)/(\d+) known encoding limitations reproduced", 1),
        False,
        True,
    ),
    (
        "correspondence",
        ("slotted/checks/language.py", "correspondence"),
        ratio(r"OK: (\d+)/(\d+) correspondence files", 2),
        False,
        False,
    ),
    (
        "curated",
        ("slotted/xdiff/xdiff.py",),
        both(ratio(r"(\d+)/(\d+) had a usable baseline", 44), zero_categories),
        False,
        True,
    ),
    (
        "surface-syntax",
        ("slotted/xdiff/surface.py", "120"),
        ratio(r"(\d+)/(\d+) cases agree through the surface syntax", 30),
        False,
        False,
    ),
    (
        "def4-edges",
        ("slotted/xdiff/def4-edges.py",),
        none_of(r"^(?P<bad>\d+) edges over (?P<seen>\d+) cases", 44),
        False,
        False,
    ),
    (
        "renaming-invariants",
        ("slotted/xdiff/invariants.py",),
        both(
            none_of(r"^(?P<seen>\d+) cases checked, non-injective (?P<bad>\d+)", 44),
            none_of(r"^(?P<seen>\d+) cases checked, non-injective \d+, edges wider than their child (?P<bad>\d+)", 44),
        ),
        False,
        False,
    ),
    (
        "stranded-nodes",
        ("slotted/xdiff/stranded.py", "all"),
        none_of(r"^(?P<seen>\d+) cases checked, \d+ stranded rows, (?P<bad>\d+) carrying", 44),
        False,
        False,
    ),
    (
        "iso-selftest",
        ("slotted/xdiff/isomorphism.py", "selftest"),
        # Raw table validation now lives with the native exporter and is exercised
        # by cargo test. These are the remaining checker/runner protocol fixtures.
        ratio(r"(\d+)/(\d+) self-tests pass", 11),
        False,
        True,
    ),
    (
        # A language file's claim to carry the reference's rules, checked name for name.
        "reference-rules",
        ("slotted/checks/check-reference-rules.py",),
        ratio(r"(\d+)/(\d+) rule sets match", 2),
        False,
        True,
    ),
    (
        # Both READERS, not the comparison: the mutation suite damages a graph after
        # extraction, so a blind spot shared by the two sides is what it cannot see.
        "iso-groups",
        ("slotted/xdiff/isomorphism.py", "known-groups"),
        ratio(r"(\d+)/(\d+) groups recovered", 2),
        False,
        True,
    ),
    ("iso-curated", ("slotted/xdiff/isomorphism.py",), ratio(r"(\d+)/(\d+) isomorphic", 51), False, True),
    ("array", ("slotted/xdiff/xarray.py",), ratio(r"(\d+)/(\d+) cases agree", 14), False, True),
    (
        "array-artifact-shapes",
        ("slotted/xdiff/xarray.py", "artifact-shapes"),
        ratio(r"(\d+)/(\d+) array artifact goal shapes match", 11),
        False,
        False,
    ),
    (
        "array-goal-smoke",
        ("slotted/xdiff/xarray.py", "goal-smoke"),
        ratio(r"(\d+)/(\d+) goal cases reached on both sides", 1),
        False,
        True,
    ),
    (
        "array-guards",
        ("slotted/xdiff/xarray.py", "vac"),
        ratio(r"(\d+)/(\d+) guards are load-bearing", 5),
        False,
        True,
    ),
    ("array-iso", ("slotted/xdiff/xarray.py", "iso"), ratio(r"(\d+)/(\d+) isomorphic", 15), False, True),
    # shapes beside the 8 rules, where the two sides could differ and must not
    (
        "array-extra",
        ("slotted/xdiff/xarray.py", "extra"),
        ratio(r"(\d+)/(\d+) cases agree", 1),
        False,
        True,
    ),
    ("sdql", ("slotted/xdiff/xsdql.py",), ratio(r"(\d+)/(\d+) cases agree", 27), False, True),
    # The stronger SDQL check: a witnessed isomorphism, not just the probe partition.
    # The remaining checked encoding divergence lives in its explicit limitation mode
    # rather than weakening this successful-case floor.
    (
        "sdql-iso",
        ("slotted/xdiff/xsdql.py", "iso"),
        ratio(r"(\d+)/(\d+) isomorphic", 27),
        False,
        True,
    ),
]

# Fixed seeds make failures reproducible. Keep the default suite bounded; each
# driver also accepts a case count and seed for larger runs of the same tests.
for seed in (0, 1):
    CHECKS.extend(
        [
            (
                f"iso-fuzz-{seed}",
                # Allow reference timeouts while requiring at least 60 comparisons.
                # Mismatches and unreadable graphs fail the driver.
                ("slotted/xdiff/isomorphism.py", "fuzz", "80", str(seed)),
                ratio(r"(\d+)/(\d+) isomorphic", 60),
                True,
                True,
            ),
            (
                f"order-fuzz-{seed}",
                ("slotted/xdiff/order-independence.py", "20", str(seed)),
                ratio(r"(\d+)/(\d+) order independent", 20),
                True,
                False,
            ),
            (
                f"checker-mutations-{seed}",
                ("slotted/xdiff/checker-mutations.py", "80", str(seed)),
                ratio(r"(\d+)/(\d+) count-changing mutations caught", 300),
                True,
                True,
            ),
        ]
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", help="skip the fuzzers")
    ap.add_argument("-k", metavar="SUBSTRING", help="only checks whose name contains this")
    ap.add_argument(
        "--no-oracle",
        action="store_true",
        help="skip the checks that need the reference implementation built",
    )
    args = ap.parse_args()

    needed = [
        (EGGLOG, "cargo build"),
    ]
    if not args.no_oracle:
        needed.append((XMULTI, "cargo build in slotted/xmulti"))
    for tool, hint in needed:
        if not tool.exists():
            print(f"missing {tool.relative_to(ROOT)} -- run `{hint}`")
            return 2

    picked = [
        c
        for c in CHECKS
        if not (args.quick and c[3]) and not (args.no_oracle and c[4]) and (not args.k or args.k in c[0])
    ]
    failed = []
    for name, cmd, expect, _, _needs_oracle in picked:
        print(f"  .... {name}", flush=True)
        r = subprocess.run([sys.executable, *cmd], capture_output=True, text=True, timeout=7200, cwd=ROOT)
        why = expect(r.stdout) if expect else None
        if r.returncode != 0:
            failure = f"exit {r.returncode}: {r.stderr.strip()[:200]}"
            why = f"{why}; {failure}" if why else failure
        if why:
            tail = [line for line in r.stdout.splitlines() if line.strip()][-6:]
            why += "\n       " + "\n       ".join(tail)
        print(f"  {'ok  ' if why is None else 'FAIL'} {name}" + (f"  {why}" if why else ""), flush=True)
        if why:
            failed.append(name)

    print(
        f"\n{len(picked) - len(failed)}/{len(picked)} checks pass"
        + (f"   FAILED: {', '.join(failed)}" if failed else "")
    )
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
