#!/usr/bin/env python3
"""Two ways into the encoder must produce the same rule.

`gen-sdql-rules.py` compiles a rule from a Python table against a language SPEC file;
`slotted-egglog.py` compiles it from a slotted SOURCE that declares its own
constructors. Both call `slotted-encoder.py`, so a rule that exists on both sides is a
free cross-check on the two front-ends -- and on the claim that a slotted test is not
a second, quietly diverging encoder.

Compared up to a bijection on variable names, which is the only freedom: a generated
rule carries a `:ruleset`/`:name` tail that a compiled one has no reason to, and that
tail is stripped rather than ignored.

Usage:  ./check-front-ends.py
"""

import importlib.util
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SNAPSHOTS = ROOT / "slotted" / "tests" / "snapshots"

_spec = importlib.util.spec_from_file_location("ct", ROOT / "slotted" / "check-tutorial.py")
ct = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ct)

#: the rule each slotted test shares with a generated file, and where to find it
SHARED = [
    ("sdql-sum-sing.egg", "target/slotted/slotted-sdql-rules.egg", "sum-sing"),
]


def rules_of(path):
    return [f for f in ct.top_forms(path.read_text()) if f.startswith("(rule")]


def main():
    bad = []
    for snap_name, gen_rel, rule in SHARED:
        gen = ROOT / gen_rel
        named = [r for r in rules_of(gen) if f':name "{rule}"' in r]
        if len(named) != 1:
            bad.append(f"{rule}: {len(named)} rules named it in {gen.name}")
            continue
        from_generator = re.sub(r"\s*:ruleset \w+ :name \"" + rule + r"\"\)\s*\Z", ")", named[0])

        snap = SNAPSHOTS / snap_name
        user = [r for r in rules_of(snap) if ":ruleset slotted" not in r]
        if len(user) != 1:
            bad.append(f"{snap_name}: {len(user)} user rules, expected 1")
            continue

        why = ct.alpha_eq(ct.parse(from_generator), ct.parse(user[0]), {}, {})
        print(
            f"  {'ok  ' if why is None else 'FAIL'} {rule:<12} {snap_name} vs {gen.name}"
            + (f"\n       {why}" if why else "")
        )
        if why:
            bad.append(rule)

    print(
        f"\n{'OK: ' if not bad else 'FAIL: '}{len(SHARED) - len(bad)}/{len(SHARED)}"
        " rules compile the same from both front-ends" + (f"   FAILED: {', '.join(bad)}" if bad else "")
    )
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
