#!/usr/bin/env python3
"""Every runnable example in `slotted/LANGUAGE.md` is a program that passes.

The reference for the language states what a claim means, and prose drifts. A fenced
block marked ```slotted is a WHOLE program: this extracts each one and runs it through
`slotted-egglog.py`, so an example that stopped being true is a failure rather than a
sentence nobody re-read.

Blocks left untagged are syntax illustrations -- a constructor line, a rule shape -- and
are not programs. What has to be true of those is that the forms they use exist, which
the tagged ones exercise.

Usage:  ./check-language-doc.py
"""

import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
DOC = ROOT / "slotted" / "LANGUAGE.md"
COMPILE = ROOT / "slotted" / "slotted-egglog.py"

#: Every claim the doc names in its table, so a claim can be added there and forgotten
#: about here. Each has to appear in at least one runnable example.
CLAIMS = ("=", "!=", "renaming-=", "renaming-!=", "slots", "holds", "not-holds")


def blocks(text):
    return re.findall(r"```slotted\n(.*?)```", text, re.S)


def main():
    text = DOC.read_text()
    progs = blocks(text)
    if not progs:
        print(f"FAIL: {DOC.name} has no ```slotted blocks")
        return 1

    bad = []
    for i, src in enumerate(progs):
        first = next((ln for ln in src.splitlines() if ln.strip() and not ln.startswith(";")), "")
        with tempfile.NamedTemporaryFile("w", suffix=".egg", delete=False) as f:
            f.write(src)
            path = f.name
        r = subprocess.run(
            [sys.executable, str(COMPILE), path], capture_output=True, text=True, timeout=1800, cwd=ROOT
        )
        ok = r.returncode == 0
        if not ok:
            err = [ln for ln in (r.stdout + r.stderr).splitlines() if "ERROR" in ln or "FAIL" in ln]
            bad.append((i, err[-1][:120] if err else "?"))
        pathlib.Path(path).unlink(missing_ok=True)
        print(f"  {'ok  ' if ok else 'FAIL'} block {i}  {first[:58]}")

    # A claim in the table nobody ever runs is a claim nobody checked.
    unused = [c for c in CLAIMS if not any(f"({c} " in p for p in progs)]

    for i, why in bad:
        print(f"       block {i}: {why}")
    if unused:
        print(f"       claims in the table with no runnable example: {', '.join(unused)}")
    print(f"\n{len(progs) - len(bad)}/{len(progs)} examples run" + (f", {len(unused)} claims unexercised" if unused else ""))
    return 1 if bad or unused else 0


if __name__ == "__main__":
    sys.exit(main())
