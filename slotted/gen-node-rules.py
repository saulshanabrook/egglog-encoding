#!/usr/bin/env python3
"""Write the arity-dependent half of the slotted machinery.

Every rule that pattern-matches an e-node has to name each column, so it cannot be
written once for all shapes in egglog. It *can* be written once, and it is:
`slotted/slotted-encoder.py` holds the emitter, and this picks what to
emit and where it goes.

Two kinds of output. `GENERIC` is the string-headed encoding in
`target/slotted/slotted-node-rules.egg`, where the operator is a payload column so any
operator can be written without regenerating. Each `slotted/languages/*.egg`
gets a per-language encoding with one constructor per operator, the shape the
reference crate's `define_language!` produces. Both include
`slotted/encoding/egraph-encoding-11.egg`, which is hand-written and holds the
constructor-independent half -- the sorts, the union-find rules, `Var` normalisation --
plus the ONE constructor family it works through as a worked example.

That family is arity 2, and `HANDWRITTEN` names it: its rules are hand-written there
rather than emitted here, so a reader gets a whole constructor's machinery in one
file. `handwritten_region()` below returns what would be emitted for it, and
`slotted/check-handwritten-encoding.py` asserts the two agree, so the
worked example cannot drift away from what every other arity gets.

Add a constructor to `GENERIC` below, or a language file, and re-run. Do not
edit the output.

    python3 slotted/gen-node-rules.py
"""

import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
enc = __import__("slotted-encoder")

CHILD, BINDER = enc.CHILD, enc.BINDER
CORE, MACHINERY = enc.CORE, enc.MACHINERY
read_language, emit = enc.read_language, enc.emit

# The generic, string-headed encoding, and the file it is written to. One constructor
# per arity with the operator in a payload column, so any operator can be written
# without regenerating anything. The compiler does not know this family: to it these
# are constructors like any others, and a payload column is a payload column.
GENERIC = {
    "App2": ["String", CHILD, CHILD],
    "App3": ["String", CHILD, CHILD, CHILD],
    "App4": ["String", CHILD, CHILD, CHILD, CHILD],
    "Num": ["i64"],
    "Sym": ["String"],
    "Scale": ["i64", CHILD],  # keeps the mixed payload/child case exercised
}
GENERIC_FILE = "target/slotted/slotted-node-rules.egg"

# Here the operator is in a payload rather than the constructor, so a binder cannot be
# declared structurally -- `App2` is not a binder, `App2 "lambda"` is. `emit` takes the
# pairs and pins them by head string.
GENERIC_BINDERS = (("lambda", "App2"), ("let", "App3"))

# Constructors whose rules `slotted/encoding/egraph-encoding-11.egg` hand-writes, along
# with any binder over them and the machinery's SHARED block. They are left out of the
# generated file, which includes that one, so each is declared exactly once.
HANDWRITTEN = ("App2",)


def string_headed(head, ctor, ref=None):
    """The `Op` for one operator of this family, for a term language over it.

    A binder is not structural here, so `GENERIC_BINDERS` pins it by head string, and
    reading that same table is what keeps a term language from disagreeing with the
    rules this file emits.
    """
    sig = list(GENERIC[ctor])
    if (head, ctor) in GENERIC_BINDERS:
        sig[next(i for i, c in enumerate(sig) if c in enc.SLOTTED)] = BINDER
    return enc.Op(head, ctor, sig, pays=[f'"{head}"'], ref=head if ref is None else ref)


def handwritten_region():
    """What `slotted/encoding/egraph-encoding-11.egg` has to hold, rules only.

    The machinery's SHARED block plus the `HANDWRITTEN` constructors and their binders:
    everything this generator could emit but leaves to that file. Comments and blank
    lines are part of the string; `check-handwritten-encoding.py` strips them before
    comparing.
    """
    lang = {name: GENERIC[name] for name in HANDWRITTEN}
    binders = tuple((head, name) for head, name in GENERIC_BINDERS if name in HANDWRITTEN)
    return enc.in_slotted_ruleset(enc.SHARED + "\n" + "\n".join(emit(lang, binders)))

# Per-language encodings: one constructor per operator, the shape the reference crate's
# `define_language!` produces, with no head to indirect through.
#
# A language's constructors are declared WHERE ITS RULES ARE where it has rules, so
# there is one place for them: `sdql` is declared at the top of its slotted source, and
# only the neutral language the fuzzer generates terms in, which has no rules at all,
# still has a file to itself.
LANG_DIR = pathlib.Path("slotted/languages")
SOURCES = {
    "sdql": pathlib.Path("slotted/languages/sdql.egg"),
    "array": pathlib.Path("slotted/languages/array.egg"),
    "toy": LANG_DIR / "toy.egg",
}

LANGUAGES = {name: read_language(p) for name, p in SOURCES.items()}


def main():
    generic = pathlib.Path(GENERIC_FILE)
    generic.parent.mkdir(parents=True, exist_ok=True)
    generic.write_text(
        enc.in_slotted_ruleset(
            enc.MACHINERY_HEADER + ";;;\n;;; The generic, string-headed encoding: one constructor per"
            " arity, the operator in a\n;;; payload column. Arity 2 is hand-written in the"
            " file included below.\n\n"
            f'(include "{MACHINERY}")\n\n' + "\n".join(emit(GENERIC, GENERIC_BINDERS, omit=HANDWRITTEN))
        )
    )
    print(f"wrote {generic} ({len(GENERIC)} constructors, string-headed)")

    # A language file includes the hand-written half DIRECTLY, not the generic
    # encoding: none of them uses a string-headed `App<n>`, so including it would
    # declare a whole constructor family none of their rules can name. `CORE` is what
    # the hand-written half does provide -- `Var` and `Null` -- so a language may
    # still declare those for the record.
    for lang, spec in LANGUAGES.items():
        p = pathlib.Path(f"target/slotted/slotted-lang-{lang}.egg")
        body = (
            enc.MACHINERY_HEADER + f";;;\n;;; Language: {lang}\n\n"
            f'(include "{MACHINERY}")\n\n' + "\n".join(emit(spec, provided=CORE))
        )
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(enc.in_slotted_ruleset(body))
        print(f"wrote {p} ({len(spec)} constructors, one per operator)")


if __name__ == "__main__":
    main()
