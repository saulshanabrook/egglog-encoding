#!/usr/bin/env python3
"""Assert the hand-written node machinery is what the generator would emit.

`slotted/encoding/egraph-encoding-11.egg` writes out one constructor family -- arity 2 --
by hand, so a reader gets a whole constructor's machinery in one file, and
`gen-node-rules.py` leaves that family out of `target/slotted/slotted-node-rules.egg` so each is
declared once. Two copies of the same rules is how they drift apart, so this compares
them: the hand-written region, marked off by

    ;;; BEGIN generated-equivalent region ...
    ;;; END generated-equivalent region

against `gen-node-rules.handwritten_region()`, which is the SHARED block plus the
`HANDWRITTEN` families and their binders -- exactly what would land in the generated
file if the family were not hand-written.

Comments and whitespace are not compared: the hand-written side says more, because
that is the point of writing it out. Rule order, structure and every name inside a
rule are.

Equality inside the markers is only half of it -- a rule about the same constructor
sitting just outside them would be drift the comparison never sees. So this also
refuses any rule outside the region that mentions the hand-written constructors or
`ClassSlots`.

    python3 slotted/check-handwritten-encoding.py

Exits 0 when they agree, 1 with a diff when they do not.
"""

import difflib
import importlib.util
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
GEN = ROOT / "slotted" / "gen-node-rules.py"
HANDWRITTEN = ROOT / "slotted" / "encoding" / "egraph-encoding-11.egg"

BEGIN = ";;; BEGIN generated-equivalent region"
END = ";;; END generated-equivalent region"


def load_generator():
    spec = importlib.util.spec_from_file_location("gen_node_rules", GEN)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def split_at_markers(text):
    """(inside the markers, everything outside them)."""
    lines = text.splitlines()
    starts = [i for i, line in enumerate(lines) if line.startswith(BEGIN)]
    ends = [i for i, line in enumerate(lines) if line.startswith(END)]
    if len(starts) != 1 or len(ends) != 1 or ends[0] < starts[0]:
        raise SystemExit(
            f"{HANDWRITTEN}: expected exactly one `{BEGIN}` line followed by one "
            f"`{END}` line, found {len(starts)} and {len(ends)}"
        )
    return ("\n".join(lines[starts[0] + 1 : ends[0]]), "\n".join(lines[: starts[0]] + lines[ends[0] + 1 :]))


def strip_comment(line):
    """Drop a trailing comment, leaving a `;` that is inside a string alone."""
    quoted = False
    for i, ch in enumerate(line):
        if ch == '"':
            quoted = not quoted
        elif ch == ";" and not quoted:
            return line[:i]
    return line


def normalise(text):
    """Rules only: comments gone, whitespace collapsed, one form per line."""
    out, depth, form = [], 0, []
    for raw in text.splitlines():
        line = strip_comment(raw)
        if not line.strip():
            continue
        depth += line.count("(") - line.count(")")
        form.append(line.strip())
        if depth <= 0:
            out.append(re.sub(r"\s+", " ", " ".join(form)))
            form, depth = [], 0
    if form:
        raise SystemExit(f"unbalanced parens, left over: {' '.join(form)}")
    return out


def strays(outside, names):
    """Rules outside the region that are about what the region is supposed to own."""
    watched = (*names, "ClassSlots")
    return [form for form in normalise(outside) if form.startswith("(rule") and any(n in form for n in watched)]


def main():
    gen = load_generator()
    inside, outside = split_at_markers(HANDWRITTEN.read_text())
    want = normalise(gen.handwritten_region())
    got = normalise(inside)

    loose = strays(outside, gen.HANDWRITTEN)
    if loose:
        print(
            f"OUTSIDE THE REGION: {HANDWRITTEN.relative_to(ROOT)} has "
            f"{len(loose)} rule(s) about "
            f"{', '.join((*gen.HANDWRITTEN, 'ClassSlots'))} that the check cannot "
            "compare, because they are not between the markers:\n"
        )
        for form in loose:
            print(f"  {form}")
        return 1

    if want == got:
        print(
            f"OK: {HANDWRITTEN.relative_to(ROOT)} holds the {len(got)} forms "
            f"gen-node-rules.py emits for {', '.join(gen.HANDWRITTEN)} "
            f"(plus the shared ClassSlots block)"
        )
        return 0

    print(
        f"MISMATCH: the region marked in {HANDWRITTEN.relative_to(ROOT)} is not what "
        f"gen-node-rules.py emits for {', '.join(gen.HANDWRITTEN)}.\n"
        "  `-` is what the generator emits, `+` what the file says.\n"
    )
    for line in difflib.unified_diff(
        want, got, "gen-node-rules.py", str(HANDWRITTEN.relative_to(ROOT)), lineterm="", n=1
    ):
        print(line)
    return 1


if __name__ == "__main__":
    sys.exit(main())
