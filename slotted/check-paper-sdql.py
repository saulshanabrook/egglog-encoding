#!/usr/bin/env python3
"""Pin the BATAX evaluation test to the published paper artifact.

The runnable test is written in this repository's slotted surface syntax.  This check
keeps its source term, expected term, selected rewrite rules, and schedule tied to the
original artifact instead of trusting a hand transcription.
"""

import hashlib
import json
import pathlib
import re
import subprocess
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "slotted"))
sc = __import__("slotted-egglog")
slotenc = __import__("slotted-encoder")

ARTIFACT_COMMIT = "83f2e5bee2b3aa45bf97ef1e3a8abe953790c735"
FIXTURES = ROOT / "slotted" / "tests" / "artifact" / "sdql"
TEST = ROOT / "slotted" / "tests" / "sdql-paper-batax.egg"
RULES = ROOT / "slotted" / "languages" / "sdql.egg"
XMULTI = ROOT / "slotted" / "xmulti" / "target" / "debug" / "xmulti"

# SHA-256 of the files at ARTIFACT_COMMIT, excluding a trailing newline.  The
# published files themselves have no newline; the vendored copies follow repository
# text-file convention and do.
HASHES = {
    "batax_2nd.sexp": "299a6064c4cd1ffc97c57122a0b867569190b1385d5fad8316b553e36cafb225",
    "batax_2nd_esat.sexp": "41c45376d39653c8f76d31a982641eda4cc1f9372a7b82035bb8f36e4f7ea642",
}

SELECTED_RULES = {
    "beta",
    "sub-identity",
    "add-zero",
    "sub-zero",
    "eq-comm",
    "sum-sum-vert-fuse-1",
    "sum-sum-vert-fuse-2",
    "sum-range-1",
    "get-to-sum",
    "sum-to-get",
    "get-range",
    "unique-rm",
}

# SHA-256 of the canonical JSON representation produced by `rewrites()` for an
# independent translation of those twelve definitions from the artifact's
# `sdql/slotted/src/rewrite.rs` at ARTIFACT_COMMIT.  Comparing the runnable copy only
# with `languages/sdql.egg` would let both copies drift together and still pass.
ARTIFACT_RULE_SEMANTICS_SHA256 = "b1cb9ae78abfa9a8f46bad55e794c73a704afd3a1116870f0ead7c6e06450030"

SELECTED_CONSTRUCTORS = {
    "Lambda",
    "Sing",
    "Add",
    "Mult",
    "Sub",
    "Equality",
    "Get",
    "Range",
    "IfThen",
    "SubArray",
    "Unique",
    "Sum",
    "Let",
    "Num",
}

OP = {
    "sing": "Sing",
    "+": "Add",
    "*": "Mult",
    "-": "Sub",
    "eq": "Equality",
    "get": "Get",
    "range": "Range",
    "apply": "App",
    "ifthen": "IfThen",
    "binop": "Binop",
    "subarray": "SubArray",
    "unique": "Unique",
}


def slot(atom: str) -> str:
    """Artifact `$var_07`/`var_07` -> the test's alpha-name `$7`."""
    match = re.fullmatch(r"\$?var_0*([1-9][0-9]*)", atom)
    if not match:
        raise ValueError(f"unexpected artifact variable {atom!r}")
    return "$" + match.group(1)


def translate(term: Any) -> Any:
    """Translate the artifact's constructor order to `languages/sdql.egg`."""
    if not isinstance(term, list):
        if re.fullmatch(r"-?[0-9]+", term):
            return ["Num", term]
        if term.startswith("$var_") or term.startswith("var_"):
            return slot(term)
        return ["Symbol", f'"{term}"']

    op, *args = term
    if op == "var":
        return slot(args[0])
    if op == "lambda":
        return ["Lambda", slot(args[0]), translate(args[1])]
    if op == "let":
        # Artifact: binder, value, body.  Local: value, binder, body.
        return ["Let", translate(args[1]), slot(args[0]), translate(args[2])]
    if op == "sum":
        # Artifact: binders, range, body.  Local: range, binders, body.
        return ["Sum", translate(args[2]), slot(args[0]), slot(args[1]), translate(args[3])]
    if op == "merge":
        return [
            "Merge",
            translate(args[3]),
            translate(args[4]),
            slot(args[0]),
            slot(args[1]),
            slot(args[2]),
            translate(args[5]),
        ]
    if op not in OP:
        raise ValueError(f"unexpected artifact operator {op!r}")
    return [OP[op], *(translate(arg) for arg in args)]


def named(forms: list[Any], head: str, name: str) -> list[Any]:
    hits = [form for form in forms if isinstance(form, list) and form[:2] == [head, name]]
    if len(hits) != 1:
        raise ValueError(f"expected one ({head} {name} ...), found {len(hits)}")
    return hits[0]


def rewrites(path: pathlib.Path) -> dict[str, tuple[Any, ...]]:
    src = sc.Source(path)
    out = {}
    for form in sc.parse(path.read_text()):
        if not (isinstance(form, list) and form and form[0] == "rewrite"):
            continue
        rule = sc.rewrite_parts(src, form)
        out[rule["name"]] = tuple(rule[key] for key in ("lhs", "rhs", "conds", "equalities", "diseq", "same", "fresh"))
    return out


def semantic_hash(rules: dict[str, tuple[Any, ...]]) -> str:
    payload = json.dumps(rules, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode()).hexdigest()


def constructors(path: pathlib.Path) -> dict[str, list[Any]]:
    out = {}
    for form in sc.parse(path.read_text()):
        if isinstance(form, list) and form[:1] == ["constructor"]:
            out[form[1]] = form[2:]
    return out


def reference_goal() -> str | None:
    """Run the same reduced MultiPattern goal against the locked Rust reference."""
    if not XMULTI.is_file():
        return f"locked reference executable not found: {XMULTI}"

    lang = slotenc.language(RULES, RULES.with_suffix(".ref"))
    fixture_source = sc.Source(TEST)
    source = sc.parse((FIXTURES / "batax_2nd.sexp").read_text())[0]
    target = sc.parse((FIXTURES / "batax_2nd_esat.sexp").read_text())[0]
    start_text = lang.sexpr(fixture_source.term(translate(source), ground=True))
    goal_text = lang.sexpr(fixture_source.term(translate(target), ground=True))

    rule_source = sc.Source(RULES)
    lines = ["rounds 12", f"term {start_text}"]
    seen = set()
    for form in sc.parse(RULES.read_text()):
        if not (isinstance(form, list) and form and form[0] == "rewrite"):
            continue
        rule = sc.rewrite_parts(rule_source, form)
        if rule["name"] not in SELECTED_RULES:
            continue
        seen.add(rule["name"])
        lhs_term = rule_source.term(rule["lhs"], ground=False)
        rhs = slotenc.pat_sexpr(lang, slotenc.rhs_of(lang, rule_source.term(rule["rhs"], ground=False)))
        root, atoms = slotenc.flatten(lang, lhs_term)
        root, atom_text = slotenc.atom_lines(lang, root, atoms)
        lines += ["rule", *atom_text, f"rhs {root} {rhs}"]
        for want, slot_name, variables in rule["conds"]:
            lines.append(f"cond {'in' if want else 'notin'} {slot_name} {' '.join(variables)}")
    if seen != SELECTED_RULES:
        return f"could not render selected reference rules: missing={sorted(SELECTED_RULES - seen)}"
    lines.append(f"goal {goal_text}")

    try:
        run = subprocess.run(
            [str(XMULTI)],
            input="\n".join(lines) + "\n",
            capture_output=True,
            text=True,
            timeout=60,
        )
    except subprocess.TimeoutExpired:
        return "locked reference timed out on the reduced BATAX goal"
    if run.returncode:
        detail = (run.stderr.strip().splitlines() or [f"exit {run.returncode}"])[-1]
        return f"locked reference failed on the reduced BATAX goal: {detail}"
    if not re.search(r"^GOAL yes$", run.stdout, re.M):
        return f"locked reference did not reach the BATAX target: {run.stdout.strip()}"
    return None


def main() -> int:
    errors: list[str] = []
    for name, expected in HASHES.items():
        path = FIXTURES / name
        data = path.read_bytes()
        if not data.endswith(b"\n") or data.endswith(b"\n\n"):
            errors.append(f"{name}: vendored copy must differ from the artifact by exactly one final newline")
        actual = hashlib.sha256(data.removesuffix(b"\n")).hexdigest()
        if actual != expected:
            errors.append(f"{name}: expected artifact SHA-256 {expected}, got {actual}")

    forms = sc.parse(TEST.read_text())
    try:
        source = sc.parse((FIXTURES / "batax_2nd.sexp").read_text())[0]
        target = sc.parse((FIXTURES / "batax_2nd_esat.sexp").read_text())[0]
        if named(forms, "let", "paper-input")[2] != translate(source):
            errors.append("paper-input is not the translated artifact batax_2nd.sexp")
        if named(forms, "let", "paper-target")[2] != translate(target):
            errors.append("paper-target is not the translated artifact batax_2nd_esat.sexp")
    except (IndexError, ValueError) as exc:
        errors.append(str(exc))

    local, selected = rewrites(RULES), rewrites(TEST)
    if set(selected) != SELECTED_RULES:
        errors.append(
            "selected rule names differ: "
            f"missing={sorted(SELECTED_RULES - set(selected))}, extra={sorted(set(selected) - SELECTED_RULES)}"
        )
    for name in sorted(SELECTED_RULES & set(selected)):
        if selected[name] != local.get(name):
            errors.append(f"{name}: copied rule differs from languages/sdql.egg")
    for label, rules in (
        ("runnable test", selected),
        ("languages/sdql.egg", {n: local[n] for n in SELECTED_RULES if n in local}),
    ):
        actual = semantic_hash(rules)
        if actual != ARTIFACT_RULE_SEMANTICS_SHA256:
            errors.append(
                f"{label}: selected rule semantics differ from the independently translated "
                f"artifact signature {ARTIFACT_RULE_SEMANTICS_SHA256} (got {actual})"
            )

    local_ctors, selected_ctors = constructors(RULES), constructors(TEST)
    if set(selected_ctors) != SELECTED_CONSTRUCTORS:
        errors.append(
            "selected constructors differ: "
            f"missing={sorted(SELECTED_CONSTRUCTORS - set(selected_ctors))}, "
            f"extra={sorted(set(selected_ctors) - SELECTED_CONSTRUCTORS)}"
        )
    for name in sorted(SELECTED_CONSTRUCTORS & set(selected_ctors)):
        if selected_ctors[name] != local_ctors.get(name):
            errors.append(f"{name}: copied constructor differs from languages/sdql.egg")

    # The paper runner gives batax_2nd 12 iterations.  More importantly, the target
    # must not be present during those iterations: otherwise the test proves
    # joinability after seeding the answer, not reachability from the input.
    input_at = forms.index(named(forms, "let", "paper-input"))
    target_at = forms.index(named(forms, "let", "paper-target"))
    runs = [(i, form) for i, form in enumerate(forms) if isinstance(form, list) and form[:1] == ["run"]]
    expected_runs = [["run", "12"], ["run", "0"]]
    if [form for _i, form in runs] != expected_runs:
        errors.append(f"expected schedules {expected_runs}, got {[form for _i, form in runs]}")
    elif not (input_at < runs[0][0] < target_at < runs[1][0]):
        errors.append("paper-target must be declared after the 12 user-rule rounds")
    if ["check", ["=", "paper-input", "paper-target"]] not in forms:
        errors.append("missing input-to-target equivalence criterion")

    with_reference = sys.argv[1:] == ["--reference"]
    if sys.argv[1:] not in ([], ["--reference"]):
        errors.append("usage: check-paper-sdql.py [--reference]")
    if not errors and with_reference and (message := reference_goal()):
        errors.append(message)

    if errors:
        for message in errors:
            print("FAIL:", message)
        return 1
    print(
        "OK: paper SDQL BATAX provenance pinned to "
        f"{ARTIFACT_COMMIT}; 2 fixtures, {len(SELECTED_RULES)} rules, 12 rounds"
        f"{' and locked-reference goal' if with_reference else ''}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
