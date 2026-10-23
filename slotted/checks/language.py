"""Reference operator correspondences and capture guards in shared rule libraries."""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from slotted import reference as syntax  # noqa: E402

# A `.ref` sits beside the file that declares its language, which is the slotted source
# where the language has rules and `languages/` where it does not.
LANGUAGES = ROOT / "egglog-experimental/tests/slotted/languages"
ORACLE = ROOT / "slotted" / "xmulti" / "src" / "main.rs"


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


def correspondence():
    tags, untagged = oracle_language()
    if not tags:
        print(f"FAIL: no tags parsed out of {ORACLE.relative_to(ROOT)}")
        return 1
    print(f"  oracle: {len(tags)} tagged, {len(untagged)} untagged ({', '.join(sorted(untagged))})")

    bad = []
    refs = sorted(LANGUAGES.glob("*.ref"))
    for ref in refs:
        corr = syntax.read_correspondence(ref)
        spec = syntax.read_language(ref.with_suffix(".egg"))
        missing = sorted({t for t, _ in corr.values() if t and t not in tags})
        # an `=payload` operator has no tag, so the oracle must carry it as an
        # untagged variant -- otherwise the harness is writing a bare payload the
        # oracle would read as a tag
        payload_ops = sorted(op for op, (t, _) in corr.items() if t is None)
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


LIBRARIES = [
    ROOT / "egglog-experimental" / "tests" / "slotted" / "languages" / "array-rules.egg",
    ROOT / "egglog-experimental" / "tests" / "slotted" / "languages" / "sdql-rules.egg",
    ROOT / "egglog-experimental" / "tests" / "slotted" / "sdql-paper-batax.egg",
]


def guards():
    bad, rules = [], 0
    for path in LIBRARIES:
        # the source's own language: a library includes its declarations, a test makes them
        src = syntax.Source(path)
        lang = src.lang
        for form in syntax.parse(path.read_text()):
            if not (isinstance(form, list) and form and form[0] == "rewrite"):
                continue
            r = syntax.rewrite_parts(src, form)
            rules += 1
            lhs = syntax.rhs_of(lang, src.term(r["lhs"], ground=False))
            rhs_term = src.term(r["rhs"], ground=False)
            rhs = syntax.rhs_of(lang, rhs_term)
            missing = syntax.missing_capture_guards(lang, lhs, rhs, r["conds"])
            if missing:
                owed = " ".join(f"(not-free {s} {v})" for s, v in sorted(missing))
                print(f"  FAIL {path.name}: {r['name']} rebinds over an outside variable without {owed}")
                bad.append(r["name"])
    print(f"\n{rules - len(bad)}/{rules} rules state the capture guards they owe")
    return 1 if bad else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("check", choices=("correspondence", "guards"))
    args = parser.parse_args()
    checks = {"correspondence": correspondence, "guards": guards}
    return checks[args.check]()


if __name__ == "__main__":
    sys.exit(main())
