#!/usr/bin/env python3
"""Pin the paper's SDQL tests to the published artifact.

The runnable tests are written in this repository's slotted surface syntax. This check
keeps their source terms, expected terms, selected rewrite rules, and schedules tied to
the original artifact instead of trusting a hand transcription: the twenty-one vendored
fixtures by hash, the full-rule tests under `slotted/tests/sdql-paper/` as exactly what
`slotted/paper_fixtures.py` writes from those fixtures, the goal-directed BATAX test's
copied rules and constructors against the rule library and an independent translation of
the artifact's `rewrite.rs`, and the MMM subset test's input and rules.
"""

import hashlib
import json
import pathlib
import re
import subprocess
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "slotted"))
sc = __import__("slotted-egglog")
slotenc = __import__("slotted-encoder")
pf = __import__("paper_fixtures")

ARTIFACT_COMMIT = pf.ARTIFACT_COMMIT
FIXTURES = pf.FIXTURES
TEST = ROOT / "slotted" / "tests" / "sdql-paper-batax.egg"
MMM_TEST = ROOT / "slotted" / "tests" / "sdql-paper-mmm.egg"
RULES = ROOT / "slotted" / "languages" / "sdql-rules.egg"
XMULTI = ROOT / "slotted" / "xmulti" / "target" / "debug" / "xmulti"

# SHA-256 of the files at ARTIFACT_COMMIT, excluding a trailing newline.  The
# published files themselves have no newline; the vendored copies follow repository
# text-file convention and do. `<kernel>_<phase>.sexp` is `sdql/slotted/progs/`'s input,
# `<kernel>_<phase>_esat.sexp` is `sdql/baseline/progs/`'s extracted program, and
# `mttkrp_2nd_bestcost.txt` is the cost Table 2 judges that workload by.
HASHES = {
    "batax_1st.sexp": "4e8cc6e565b8159a0b0494cf78e94670b70ae51aa991d708e01d1ee7d37b6db4",
    "batax_1st_esat.sexp": "b750f48ba535dff800cdbe08d1852879977680914bfdaeaa33e9d0f1339ca209",
    "batax_2nd.sexp": "299a6064c4cd1ffc97c57122a0b867569190b1385d5fad8316b553e36cafb225",
    "batax_2nd_esat.sexp": "41c45376d39653c8f76d31a982641eda4cc1f9372a7b82035bb8f36e4f7ea642",
    "mmm_1st.sexp": "a2ed2e54a6160c979a1ae188892b3b24f5a1fc0e7b74ad0ddbef2419fde2e01f",
    "mmm_1st_esat.sexp": "c7fe6295056e304d8947230ae407908306b938a8687ccbaef017c68a726f77bc",
    "mmm_2nd.sexp": "9e13dcf26ac42cd0725e3fabe39f327c9731c9f48547f37e481024c772371baa",
    "mmm_2nd_esat.sexp": "70cd44691dbf53aad355e9980add79dd753c656e405fc997b2304fef59af4571",
    "mmm_sum_1st.sexp": "1dc00f02eb6e904c0d2019acff5e86e284c254f5a4901e1ca710c7e8ee78cfac",
    "mmm_sum_1st_esat.sexp": "4e63d0a53b7d353eacf3653c655201b11f086fccb5a88fb685d9d415dabd9141",
    "mmm_sum_2nd.sexp": "ba9955701a5be6ff2fc02e76351fd6302cdb9fca24a18a31f0804f120b95f723",
    "mmm_sum_2nd_esat.sexp": "ceccd5924fd20ca80cfcb4bb540b000dee5f0f7a568bf65a686da54488111f04",
    "mttkrp_1st.sexp": "c3a7484cdf5b1235ca422d1ecb8b345dee09f7644790f062fc4fd724527b01df",
    "mttkrp_1st_esat.sexp": "9e55c84b24822060499c360057cacc3b657883acef688284b1ba15f5af4b6115",
    "mttkrp_2nd.sexp": "8c7748f40b935661ea42c4cc4e69c3c7cf2a6ef84d8d7301d65c0739b6a863a9",
    "mttkrp_2nd_esat.sexp": "93d8dddc4265bdb38b416d736db6c4109a7d2fc8df7d93a27669dedb5495bcfd",
    "mttkrp_2nd_bestcost.txt": "98f90089b89c6c9335c7a29ac1b93fb304e1e81d6525033ec1f78e9000e0f031",
    "ttm_1st.sexp": "3df79f25a5aed2a23bec831a577f91107ed61aec4a36c370a89b46445107fb9e",
    "ttm_1st_esat.sexp": "4763293256265ae7280f9103dbd0beb27075e7d6c5a4c1c4a609514e4dfc3031",
    "ttm_2nd.sexp": "40766a6668c9dcc9c67f12f31a0d096b1e7d355038271aedcadb86bbc54b69c2",
    "ttm_2nd_esat.sexp": "c018e0fef8d2064d1b5db1b2827abfa804aaba6fe1c5881a263f4f281c4459e6",
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

# `sdql-paper-mmm.egg`: the smallest rule set that still made `beta` substitute through
# renumbered frames (once a crash), and enough to reach MMM's second-phase target.
MMM_RULES = {
    "unique-app2",
    "beta",
    "let-apply1",
    "if-mult2",
    "if-to-mult",
    "sum-fact-1",
    "sum-fact-3",
    "sum-fact-inv-1",
    "sum-sum-vert-fuse-2",
    "get-to-sum",
    "sum-to-get",
    "sum-sing",
    "unique-rm",
}

# SHA-256 of the canonical JSON representation produced by `rewrites()` for an
# independent translation of those twelve definitions from the artifact's
# `sdql/slotted/src/rewrite.rs` at ARTIFACT_COMMIT.  Comparing the runnable copy only
# with `languages/sdql-rules.egg` would let both copies drift together and still pass.
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


def declarations_of(path):
    """The file declaring the constructors a `-rules.egg` writes rules over."""
    return path.with_name(path.name.replace("-rules.egg", ".egg"))


#: the artifact's syntax to this language's, shared with the tests' generator
translate = pf.translate


def named(forms: list[Any], head: str, name: str) -> list[Any]:
    hits = [form for form in forms if isinstance(form, list) and form[:2] == [head, name]]
    if len(hits) != 1:
        raise ValueError(f"expected one ({head} {name} ...), found {len(hits)}")
    return hits[0]


def rewrites(path: pathlib.Path) -> dict[str, tuple[Any, ...]]:
    """Each rewrite's semantics, without the capture guards this port adds.

    Where a right-hand side rebinds a slot over a variable matched outside it, the rule
    here says `(not-free $b v)`, because matching may read the binder as that
    variable's name; the artifact's nested matcher never does, so its rules lack the
    guard and mean the same thing. The signature below is over the artifact's
    semantics, so those guards are discounted; `check-capture-guards.py` requires them.
    """
    src = sc.Source(path)
    out = {}
    for form in sc.parse(path.read_text()):
        if not (isinstance(form, list) and form and form[0] == "rewrite"):
            continue
        rule = sc.rewrite_parts(src, form)
        lhs = slotenc.rhs_of(src.lang, src.term(rule["lhs"], ground=False))
        rhs = slotenc.rhs_of(src.lang, src.term(rule["rhs"], ground=False))
        owed = slotenc.capture_guards(src.lang, lhs, rhs)
        conds = [c for c in rule["conds"] if c[0] or not all((c[1], v) in owed for v in c[2])]
        semantics = dict(rule, conds=conds)
        out[rule["name"]] = tuple(
            semantics[key] for key in ("lhs", "rhs", "conds", "equalities", "diseq", "same", "fresh")
        )
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

    decls = declarations_of(RULES)
    lang = slotenc.language(decls, decls.with_suffix(".ref"))
    fixture_source = sc.Source(TEST)
    source = sc.parse((FIXTURES / "batax_2nd.sexp").read_text())[0]
    target = sc.parse((FIXTURES / "batax_2nd_esat.sexp").read_text())[0]
    start_text = lang.sexpr(fixture_source.term(translate(source), ground=True))
    goal_text = lang.sexpr(fixture_source.term(translate(target), ground=True))  # `$var_NN` -> `$NN`

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

    vendored = {q.name for q in FIXTURES.iterdir() if q.suffix in (".sexp", ".txt")}
    if vendored != set(HASHES):
        errors.append(f"vendored fixtures differ from the pinned set: {sorted(vendored ^ set(HASHES))}")

    # Every workload translates, and each suite test is exactly its translation. A file
    # in the directory that no workload owns would run as a test with no provenance.
    for kernel, phase in pf.WORKLOADS:
        try:
            pf.workload(kernel, phase)
        except (IndexError, ValueError) as exc:
            errors.append(f"{kernel}_{phase}: {exc}")
    for kernel, phase in pf.SUITE:
        path = pf.test_path(kernel, phase)
        if not path.is_file():
            errors.append(f"missing {path.relative_to(ROOT)}; `python3 slotted/paper_fixtures.py --write`")
        elif sc.parse(path.read_text()) != pf.test_forms(kernel, phase):
            errors.append(f"{path.relative_to(ROOT)} is not the translation of its fixtures at the artifact's limit")
    owned = {pf.test_path(k, p).name for k, p in pf.SUITE}
    for stray in sorted(q.name for q in pf.TESTS.glob("*.egg") if q.name not in owned):
        errors.append(f"{stray}: not a workload of the paper's Table 1")

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

    # `sdql-paper-mmm.egg`: the artifact's input and target, the thirteen rules as the
    # library has them, and the artifact's 30 rounds in all.
    mmm_forms = sc.parse(MMM_TEST.read_text())
    try:
        mmm_input, mmm_target = pf.workload("mmm", "2nd")
        if named(mmm_forms, "let", "paper-input")[2] != mmm_input:
            errors.append("sdql-paper-mmm.egg: paper-input is not the translated artifact mmm_2nd.sexp")
        if named(mmm_forms, "let", "paper-target")[2] != mmm_target:
            errors.append("sdql-paper-mmm.egg: paper-target is not the translated artifact mmm_2nd_esat.sexp")
        runs = [f for f in mmm_forms if isinstance(f, list) and f[:1] == ["run"]]
        if not (
            mmm_forms.index(named(mmm_forms, "let", "paper-input"))
            < mmm_forms.index(runs[0])
            < mmm_forms.index(named(mmm_forms, "let", "paper-target"))
        ):
            errors.append("sdql-paper-mmm.egg: paper-target must be declared after the user-rule rounds")
    except (IndexError, ValueError) as exc:
        errors.append(f"sdql-paper-mmm.egg: {exc}")
    mmm_rules = rewrites(MMM_TEST)
    if set(mmm_rules) != MMM_RULES:
        errors.append(f"sdql-paper-mmm.egg: rule names differ: {sorted(set(mmm_rules) ^ MMM_RULES)}")
    mmm_runs = [f for f in mmm_forms if isinstance(f, list) and f[:1] == ["run"]]
    if sum(int(f[1]) for f in mmm_runs) != pf.iteration_limit("mmm", "2nd"):
        errors.append(f"sdql-paper-mmm.egg: the rounds must add up to the artifact's 30, got {mmm_runs}")
    if ["check", ["=", "paper-input", "paper-target"]] not in mmm_forms:
        errors.append("sdql-paper-mmm.egg: missing input-to-target equivalence criterion")

    local, selected = rewrites(RULES), rewrites(TEST)
    for name in sorted(MMM_RULES & set(mmm_rules)):
        if mmm_rules[name] != local.get(name):
            errors.append(f"sdql-paper-mmm.egg: {name} differs from languages/sdql-rules.egg")
    if set(selected) != SELECTED_RULES:
        errors.append(
            "selected rule names differ: "
            f"missing={sorted(SELECTED_RULES - set(selected))}, extra={sorted(set(selected) - SELECTED_RULES)}"
        )
    for name in sorted(SELECTED_RULES & set(selected)):
        if selected[name] != local.get(name):
            errors.append(f"{name}: copied rule differs from languages/sdql-rules.egg")
    for label, rules in (
        ("runnable test", selected),
        ("languages/sdql-rules.egg", {n: local[n] for n in SELECTED_RULES if n in local}),
    ):
        actual = semantic_hash(rules)
        if actual != ARTIFACT_RULE_SEMANTICS_SHA256:
            errors.append(
                f"{label}: selected rule semantics differ from the independently translated "
                f"artifact signature {ARTIFACT_RULE_SEMANTICS_SHA256} (got {actual})"
            )

    local_ctors, selected_ctors = constructors(declarations_of(RULES)), constructors(TEST)
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
        f"OK: paper SDQL provenance pinned to {ARTIFACT_COMMIT}; {len(HASHES)} fixtures,"
        f" {len(pf.SUITE)} full-rule tests, BATAX's {len(SELECTED_RULES)} rules over 12 rounds,"
        f" MMM's {len(MMM_RULES)} over 30"
        f"{' and locked-reference goal' if with_reference else ''}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
