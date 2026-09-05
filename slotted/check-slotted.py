#!/usr/bin/env python3
"""Every check the slotted encoding has, in one command.

A check passes only if its tool exits 0 AND its summary line says everything agreed,
so a tool that runs zero cases fails rather than reporting a vacuous pass. The
recorded totals are floors: adding cases is fine, losing them is not.

Needs `target/debug/egglog` and `slotted/xmulti/target/debug/xmulti`.

Usage:
    ./check-slotted.py           everything
    ./check-slotted.py --quick   skip the fuzzers
    ./check-slotted.py -k iso    only checks whose name contains `iso`
    ./check-slotted.py --no-oracle
                                 only what needs no reference build
"""

import argparse
import glob
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EGGLOG = ROOT / "target" / "debug" / "egglog"
XMULTI = ROOT / "slotted" / "xmulti" / "target" / "debug" / "xmulti"

# One entry per generated file: the command that writes it. These are BUILD OUTPUT,
# under `target/`, so nothing here is committed -- the tests include them, and
# `make slotted-check` builds them first. `slotted/tests/snapshots/` is the committed
# derived artifact.
GENERATED = {
    "target/slotted/slotted-node-rules.egg": ("slotted/gen-node-rules.py",),
    "target/slotted/slotted-lang-array.egg": ("slotted/gen-node-rules.py",),
    "target/slotted/slotted-lang-sdql.egg": ("slotted/gen-node-rules.py",),
    "target/slotted/slotted-lang-toy.egg": ("slotted/gen-node-rules.py",),
    "target/slotted/slotted-sdql-rules.egg": ("slotted/gen-sdql-rules.py",),
    "target/slotted/slotted-array-rules.egg": ("slotted/xdiff/xarray.py", "egg"),
}


#: Compiled slotted tests. Each is what running that test runs, committed so a change
#: in the compiler shows up as a diff -- the same reason the proof encoding snapshots
#: its generated program.
SNAPSHOT_DIR = ROOT / "slotted" / "tests" / "snapshots"
EMIT_SNAPSHOTS = ("slotted/run-slotted-tests.py", "--emit")


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


def both(*fns):
    def check(out):
        return next((r for r in (f(out) for f in fns) if r), None)

    return check


def starts_ok(out):
    return None if out.lstrip().startswith("OK:") else "no OK line"


def run_egg_files():
    """Every hand-written encoded-level file loads and runs clean.

    `slotted/encoding/` is the hand-written half -- the encoding itself, the tutorial
    that explains it, and the tests that poke at the machinery directly. They are plain
    egglog, written with the renamings spelled out, so they run as they are.
    """
    files = sorted(glob.glob(str(ROOT / "slotted" / "encoding" / "**" / "*.egg"), recursive=True))
    # A test rewritten in the slotted language leaves this directory for
    # `slotted/tests/`, so this floor drops as that one rises; neither may fall alone.
    if len(files) < 9:
        return f"only {len(files)} encoded-level .egg files found"
    bad = []
    for f in files:
        r = subprocess.run([str(EGGLOG), f], capture_output=True, text=True, timeout=1800, cwd=ROOT)
        if r.returncode != 0:
            err = [line for line in r.stderr.splitlines() if "ERROR" in line]
            bad.append(f"{Path(f).name}: {(err[-1] if err else '?')[:120]}")
    if bad:
        return f"{len(bad)}/{len(files)} failed -- " + "; ".join(bad[:3])
    print(f"       {len(files)} files")
    return None


def check_generated():
    """Build the machinery the tests include, and require the generators to be
    deterministic.

    Nothing generated is committed, so there is nothing to be stale against. What is
    still worth holding is that a compiled program is a function of the encoder rather
    than of iteration order -- so each generator runs twice and the output has to match.
    A set or dict iteration creeping in would otherwise surface much later as a
    confusing diff.
    """

    def build():
        for cmd in sorted(set(GENERATED.values())):
            r = subprocess.run([sys.executable, *cmd], capture_output=True, text=True, timeout=1800, cwd=ROOT)
            if r.returncode != 0:
                return f"{cmd[0]} failed: {r.stderr.strip()[:200]}"
        missing = [rel for rel in GENERATED if not (ROOT / rel).exists()]
        return f"not written: {', '.join(missing)}" if missing else None

    if err := build():
        return err
    first = {rel: (ROOT / rel).read_bytes() for rel in GENERATED}
    if err := build():
        return err
    unstable = [rel for rel in GENERATED if (ROOT / rel).read_bytes() != first[rel]]
    if unstable:
        return "generator is not deterministic: " + ", ".join(unstable)
    print(f"       {len(GENERATED)} files built, identical across two runs")
    return None


def check_snapshots():
    """The committed compiled programs match what the compiler emits now."""
    before = {p.name: p.read_bytes() for p in SNAPSHOT_DIR.glob("*.egg")}
    if not before:
        return "no compiled snapshots committed"
    try:
        r = subprocess.run([sys.executable, *EMIT_SNAPSHOTS], capture_output=True, text=True, timeout=3600, cwd=ROOT)
        if r.returncode != 0:
            return f"the compiler failed: {(r.stdout + r.stderr).strip()[-300:]}"
        now = {p.name: p.read_bytes() for p in SNAPSHOT_DIR.glob("*.egg")}
        stale = sorted(set(now) - set(before)) + sorted(n for n in before if before[n] != now.get(n))
    finally:
        for name, text in before.items():
            (SNAPSHOT_DIR / name).write_bytes(text)
    if stale:
        return "stale, rerun with --update: " + ", ".join(stale)
    print(f"       {len(before)} compiled programs byte-identical")
    return None


# name, argv or a callable, what its output must say, whether --quick skips it, and
# whether it needs the reference ORACLE. The oracle is `xmulti`, which links a local
# checkout of `slotted-egraphs`, so a machine without one can still run everything that
# only exercises the encoding against itself -- which is what `--no-oracle` is for, and
# what CI runs until that dependency is fetchable.
CHECKS = [
    # First: the machinery under `target/` is build output, and five tests include it.
    ("generators", check_generated, None, False, False),
    ("egg-files", run_egg_files, None, False, False),
    (
        "slotted-tests",
        ("slotted/run-slotted-tests.py",),
        ratio(r"(\d+)/(\d+) slotted tests pass", 5),
        False,
        False,
    ),
    ("snapshot-drift", check_snapshots, None, False, False),
    (
        "front-ends",
        ("slotted/check-front-ends.py",),
        ratio(r"OK: (\d+)/(\d+) rules compile the same", 1),
        False,
        False,
    ),
    ("handwritten-drift", ("slotted/check-handwritten-encoding.py",), starts_ok, False, False),
    (
        "correspondence",
        ("slotted/check-correspondence.py",),
        ratio(r"OK: (\d+)/(\d+) correspondence files", 2),
        False,
        False,
    ),
    (
        "tutorial-drift",
        ("slotted/check-tutorial.py",),
        ratio(r"(\d+)/(\d+) sections are the encoder's own output", 11),
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
        "mutations",
        ("slotted/xdiff/mutations.py",),
        # 3, not 4: `unordered` stopped discriminating once a rule tried every naming
        # an atom's renaming could take, since a bad atom order no longer loses the
        # matches it used to. That property is measured directly by
        # `order-independence.py` instead, and a mutation that catches nothing is not
        # kept as decoration -- `mutations.py`'s own header says so.
        ratio(r"(\d+)/(\d+) mutations still caught", 3),
        False,
        True,
    ),
    (
        "iso-selftest",
        ("slotted/xdiff/isomorphism.py", "selftest"),
        ratio(r"(\d+)/(\d+) self-tests pass", 3),
        False,
        True,
    ),
    (
        # A language file's claim to carry the reference's rules, checked name for name.
        "reference-rules",
        ("slotted/check-reference-rules.py",),
        ratio(r"(\d+)/(\d+) rule sets match", 2),
        False,
        True,
    ),
    (
        # An example nobody runs is an example nobody checked.
        "language-doc",
        ("slotted/check-language-doc.py",),
        ratio(r"(\d+)/(\d+) examples run", 5),
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
    ("iso-curated", ("slotted/xdiff/isomorphism.py",), ratio(r"(\d+)/(\d+) isomorphic", 44), False, True),
    ("array", ("slotted/xdiff/xarray.py",), ratio(r"(\d+)/(\d+) cases agree", 14), False, True),
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
    ("sdql", ("slotted/xdiff/xsdql.py",), ratio(r"(\d+)/(\d+) cases agree", 18), False, True),
    # the stronger sdql check: a witnessed isomorphism, not just the probe partition.
    # The two recorded divergences are excluded by the mode itself -- they disagree on
    # purpose, so finding no isomorphism between them would say nothing.
    (
        "sdql-iso",
        ("slotted/xdiff/xsdql.py", "iso"),
        ratio(r"(\d+)/(\d+) isomorphic", 16),
        False,
        True,
    ),
    (
        "iso-fuzz",
        ("slotted/xdiff/isomorphism.py", "fuzz", "60"),
        ratio(r"(\d+)/(\d+) isomorphic", 60),
        True,
        True,
    ),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", help="skip the fuzzers")
    ap.add_argument(
        "--update",
        action="store_true",
        help="rewrite the generated snapshots and report which changed, then stop",
    )
    ap.add_argument("-k", metavar="SUBSTRING", help="only checks whose name contains this")
    ap.add_argument(
        "--no-oracle",
        action="store_true",
        help="skip the checks that need the reference implementation built",
    )
    args = ap.parse_args()

    needed = [(EGGLOG, "cargo build")]
    if not args.no_oracle:
        needed.append((XMULTI, "cargo build in slotted/xmulti"))
    for tool, hint in needed:
        if not tool.exists():
            print(f"missing {tool.relative_to(ROOT)} -- run `{hint}`")
            return 2

    if args.update:
        before = {rel: (ROOT / rel).read_bytes() for rel in GENERATED}
        before |= {str(q.relative_to(ROOT)): q.read_bytes() for q in SNAPSHOT_DIR.glob("*.egg")}
        for cmd in sorted(set(GENERATED.values())) + [EMIT_SNAPSHOTS]:
            r = subprocess.run([sys.executable, *cmd], capture_output=True, text=True, timeout=3600, cwd=ROOT)
            if r.returncode != 0:
                print(f"{cmd[0]} failed: {r.stderr.strip()[:300]}")
                return 1
        changed = [rel for rel in before if not (ROOT / rel).exists() or (ROOT / rel).read_bytes() != before[rel]]
        changed += [
            str(q.relative_to(ROOT)) for q in SNAPSHOT_DIR.glob("*.egg") if str(q.relative_to(ROOT)) not in before
        ]
        for rel in changed:
            print(f"  updated {rel}")
        print(f"\n{len(changed)}/{len(before)} snapshots changed")
        return 0

    picked = [
        c
        for c in CHECKS
        if not (args.quick and c[3]) and not (args.no_oracle and c[4]) and (not args.k or args.k in c[0])
    ]
    failed = []
    for name, cmd, expect, _, _needs_oracle in picked:
        print(f"  .... {name}", flush=True)
        if callable(cmd):
            why = cmd()
        else:
            r = subprocess.run([sys.executable, *cmd], capture_output=True, text=True, timeout=7200, cwd=ROOT)
            why = expect(r.stdout) if expect else None
            if why is None and r.returncode != 0:
                why = f"exit {r.returncode}: {r.stderr.strip()[:200]}"
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
