#!/usr/bin/env python3
"""Every tag in a `.ref` file must be one the oracle actually answers to.

A `.ref` says what the reference calls each constructor, and the harness writes those
tags into the terms and rules it hands the oracle. `define_language!` dispatches on the
tag alone, so a tag renamed in `xmulti/src/main.rs` and not here does not fail loudly:
the oracle either reports a parse error on one case or, worse, parses the text as a
DIFFERENT node. This compares the two.

The variant NAMES are deliberately not compared. The oracle holds several languages in
one enum and had to rename variants where two languages wanted the same one -- `Lam` ->
`Lambda`, `Add` -> `Plus` -- while keeping the tags, and it is the tag that rule and
term text carries.

Usage:  ./check-correspondence.py
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
# A `.ref` sits beside the file that declares its language, which is the slotted source
# where the language has rules and `languages/` where it does not.
REF_DIRS = (ROOT / "slotted" / "languages",)
ORACLE = ROOT / "slotted" / "xmulti" / "src" / "main.rs"

sys.path.insert(0, str(ROOT / "slotted"))
enc = __import__("slotted-encoder")


def oracle_language():
    """`{tag}` and `{variant}` from the oracle's `define_language!` block."""
    text = ORACLE.read_text()
    start = text.index("define_language! {")
    depth, i = 0, start + len("define_language!")
    while True:
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                break
        i += 1
    body = "\n".join(line.split("//")[0] for line in text[start:i].splitlines())
    tags = set(re.findall(r'=\s*"([^"]+)"', body))
    untagged = set(re.findall(r"^\s*([A-Z]\w*)\([^)]*\)\s*,\s*$", body, re.M))
    return tags, untagged


def main():
    tags, untagged = oracle_language()
    if not tags:
        print(f"FAIL: no tags parsed out of {ORACLE.relative_to(ROOT)}")
        return 1
    print(f"  oracle: {len(tags)} tagged, {len(untagged)} untagged ({', '.join(sorted(untagged))})")

    bad = []
    refs = sorted(r for d in REF_DIRS for r in d.glob("*.ref"))
    for ref in refs:
        corr = enc.read_correspondence(ref)
        spec = enc.read_language(ref.with_suffix(".egg"))
        missing = sorted({t for _, t, _ in corr.values() if t and t not in tags})
        # an `=payload` operator has no tag, so the oracle must carry it as an
        # untagged variant -- otherwise the harness is writing a bare payload the
        # oracle would read as a tag
        payload_ops = sorted(op for op, (_, t, _) in corr.items() if t is None)
        note = f", payload ops {payload_ops}" if payload_ops else ""
        if not untagged and payload_ops:
            missing.append("(the oracle has no untagged variant to hold a payload)")
        print(
            f"  {'ok  ' if not missing else 'FAIL'} {ref.name:<12} "
            f"{len(corr)} operators over {len(spec)} constructors{note}"
            + (f"\n       tags the oracle does not answer to: {missing}" if missing else "")
        )
        if missing:
            bad.append(ref.name)

    print(
        f"\n{'OK: ' if not bad else 'FAIL: '}"
        f"{len(refs) - len(bad)}/{len(refs)}"
        " correspondence files agree with the oracle" + (f"   FAILED: {', '.join(bad)}" if bad else "")
    )
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
