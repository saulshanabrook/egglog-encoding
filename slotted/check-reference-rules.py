#!/usr/bin/env python3
"""Our evaluation rule sets are the reference's, semantics included.

`sdql.egg` and `array.egg` claim to carry the reference's rules. That claim went
unchecked, and drifted twice in one session: the sdql file said "rule for rule" while
missing `beta`, and then gained `sum-range-2`, which the reference DEFINES but does not
RUN. Counting `Rewrite::new` calls is the trap -- a rule only counts if it reaches the
list handed to the runner.

Compares every rewrite here against the rules the reference's own runner list holds:
name, left- and right-hand patterns, and slot-freedom guards.  Slot and pattern-variable
names are alpha-normalised, and the SDQL oracle's parser-only spelling workarounds are
removed before comparison.

Usage:  ./check-reference-rules.py
"""

import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "slotted"))
sc = __import__("slotted-egglog")
slotenc = __import__("slotted-encoder")


def reference_root():
    """Resolve the exact locked Cargo dependency.

    Prefer the local Cargo cache. A build does not necessarily download manifests for
    inactive transitive features, though, while ``cargo metadata`` resolves the whole
    locked graph. A clean CI cache can therefore need one final locked fetch even after
    ``xmulti`` itself built successfully.
    """
    cmd = [
        "cargo",
        "metadata",
        "--format-version",
        "1",
        "--locked",
        "--manifest-path",
        str(ROOT / "slotted" / "xmulti" / "Cargo.toml"),
    ]
    try:
        result = subprocess.run([*cmd, "--offline"], capture_output=True, text=True)
        if result.returncode:
            result = subprocess.run(cmd, check=True, capture_output=True, text=True)
        meta = json.loads(result.stdout)
        manifests = [pathlib.Path(p["manifest_path"]) for p in meta["packages"] if p["name"] == "slotted-egraphs"]
    except (OSError, subprocess.CalledProcessError, KeyError, json.JSONDecodeError) as e:
        raise SystemExit(f"cannot resolve the locked slotted-egraphs dependency: {e}") from e
    if len(manifests) != 1:
        raise SystemExit(f"cargo metadata found {len(manifests)} slotted-egraphs packages, expected one")
    return manifests[0].parent


REF = reference_root()

#: ours -> (the reference's file, the name of the function returning its rule list, and
#: the names we spell differently)
SUITES = {
    "sdql": (
        ROOT / "slotted" / "languages" / "sdql.egg",
        REF / "benches" / "sdql.rs",
        {},
    ),
    "array": (
        ROOT / "slotted" / "languages" / "array.egg",
        REF / "tests" / "rise" / "rewrite.rs",
        # the reference's name -> ours, where the two chose different words for one rule
        {"beta": "let-intro", "my-let-unused": "let-unused"},
    ),
}

#: Rules the reference runs that we deliberately do not carry, and why. A rule leaving
#: this list is a gap; a rule appearing in it without a reason is not allowed.
EXPECTED_MISSING = {
    "array": {
        "eta-expansion": "left-hand side is a bare pattern variable: it matches every class",
        "let-var-diff": "not written yet",
        "let-app-unopt": "an unoptimised variant of `let-app`, which is here",
        "let-lam-diff-unopt": "an unoptimised variant of `let-lam-diff`, which is here",
        "map-slide-before-transpose": "needs slide and transpose, which this language does not declare",
        "remove-transpose-pair": "needs transpose",
        "separate-dot-hv-simplified": "needs the dot-product operators",
        "separate-dot-vh-simplified": "needs the dot-product operators",
        "slide-before-map": "needs slide",
        "slide-before-map-map-f": "needs slide",
    },
}


def our_names(path):
    # egglog spells a rule name as a string literal; the bare form is still accepted
    return set(re.findall(r":name\s+\"?([\w-]+)\"?", path.read_text()))


def their_names(path):
    """The rules the reference RUNS, not the ones it merely defines.

    The two files build their list differently -- `benches/sdql.rs` with a `vec![]` and
    `tests/rise` with repeated `rewrites.push(..)` -- so neither shape is parsed. A rule
    counts when its constructor is CALLED somewhere other than its own definition, which
    is what `#[allow(unused)]` on `get_sum_vert_fuse_1` is telling the Rust compiler it
    is not.
    """
    src = path.read_text()
    defined = {}
    for m in re.finditer(r"fn (\w+)\(\)[^{]*\{", src):
        fn, start = m.group(1), m.end()
        body = src[start : start + 800]
        name = re.search(r"Rewrite::new(?:_if)?\(\s*\n?\s*\"([^\"]+)\"", body)
        if name:
            defined[fn] = (name.group(1), m.start(), start)

    out = set()
    for fn, (rule, def_start, def_end) in defined.items():
        for call in re.finditer(rf"\b{re.escape(fn)}\(\)", src):
            if not (def_start <= call.start() < def_end):
                out.add(rule)
                break
    return out


def local_rules(path):
    """Render the slotted source through the same language metadata as the oracle."""
    src = sc.Source(path)
    lang = slotenc.language(path, path.with_suffix(".ref"))
    out = {}
    for form in sc.parse(path.read_text()):
        if not (isinstance(form, list) and form and form[0] == "rewrite"):
            continue
        rule = sc.rewrite_parts(src, form)
        sides = []
        for side in (rule["lhs"], rule["rhs"]):
            term = src.term(side, ground=False)
            sides.append(slotenc.pat_sexpr(lang, slotenc.rhs_of(lang, term)))
        out[rule["name"]] = (sides[0], sides[1], rule["conds"])
    return out


def rust_functions(src):
    """Function bodies, with braces inside strings/comments ignored."""
    out = {}
    for m in re.finditer(r"\bfn\s+(\w+)\s*\([^)]*\)[^{]*\{", src):
        start, i, depth = m.end(), m.end(), 1
        string = line_comment = block_comment = False
        while i < len(src) and depth:
            c, nxt = src[i], src[i + 1] if i + 1 < len(src) else ""
            if line_comment:
                line_comment = c != "\n"
            elif block_comment:
                if c == "*" and nxt == "/":
                    block_comment = False
                    i += 1
            elif string:
                if c == "\\":
                    i += 1
                elif c == '"':
                    string = False
            elif c == '"':
                string = True
            elif c == "/" and nxt == "/":
                line_comment = True
                i += 1
            elif c == "/" and nxt == "*":
                block_comment = True
                i += 1
            elif c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
            i += 1
        out[m.group(1)] = src[start : i - 1]
    return out


RUST_STRING = re.compile(r'"((?:\\.|[^"\\])*)"', re.S)


def rust_string(text):
    m = RUST_STRING.search(text.strip())
    if not m:
        return None
    # Rust permits literal newlines in an ordinary string; JSON does not.  These
    # sources use only the elementary escapes below, so decode them without changing
    # the literal whitespace that semantic normalisation handles later.
    return m.group(1).replace(r"\n", "\n").replace(r"\"", '"').replace(r"\\", "\\")


def rust_value(expr, env):
    """Evaluate the tiny constant-string subset used to declare these rewrites."""
    expr = expr.strip().removeprefix("&").strip()
    if expr in env:
        return env[expr]
    if re.fullmatch(r"\d+", expr):
        return expr
    if expr.startswith("format!"):
        value = rust_string(expr)
        if value is None:
            return None
        for name, replacement in env.items():
            value = value.replace("{" + name + "}", replacement)
        return value
    return rust_string(expr)


def call_args(body, start):
    """Top-level arguments of the Rewrite constructor beginning at `start`."""
    open_paren = body.index("(", start)
    args, begin, i, depth, string = [], open_paren + 1, open_paren + 1, 0, False
    while i < len(body):
        c = body[i]
        if string:
            if c == "\\":
                i += 1
            elif c == '"':
                string = False
        elif c == '"':
            string = True
        elif c in "([{":
            depth += 1
        elif c in ")]}":
            if c == ")" and depth == 0:
                args.append(body[begin:i].strip())
                return args
            depth -= 1
        elif c == "," and depth == 0:
            args.append(body[begin:i].strip())
            begin = i + 1
        i += 1
    return []


def reference_rules(path):
    """Extract the executable semantic part of each reference Rewrite declaration."""
    src = path.read_text()
    active = their_names(path)
    out = {}
    for _fn, body in rust_functions(src).items():
        call = re.search(r"Rewrite::new(?:_if)?\s*\(", body)
        if not call:
            continue
        env = {}
        for assignment in re.finditer(r"\blet\s+(\w+)\s*=\s*(.*?);", body[: call.start()], re.S):
            value = rust_value(assignment.group(2), env)
            if value is not None:
                env[assignment.group(1)] = value
        args = call_args(body, call.start())
        if len(args) < 3:
            continue
        name, lhs, rhs = (rust_value(a, env) for a in args[:3])
        if name not in active or lhs is None or rhs is None:
            continue

        found = []
        member = re.compile(
            r"(!?)subst\[\"([^\"]+)\"\]\.slots\(\)\.contains"
            r"\(&Slot::(?:numeric\(([^)]+)\)|named\(\"([^\"]+)\"\))\)"
        )
        for m in member.finditer(body[call.start() :]):
            raw_slot = m.group(3) or m.group(4)
            slot = env.get(raw_slot.strip(), raw_slot.strip())
            found.append((not bool(m.group(1)), "$" + slot.removeprefix("$"), m.group(2)))
        if "||" in body[call.start() :] and found:
            assert all(want for want, _slot, _pv in found), f"{name}: unsupported mixed || guard"
            assert len({slot for _want, slot, _pv in found}) == 1, f"{name}: || spans several slots"
            conds = [(True, found[0][1], [pv for _want, _slot, pv in found])]
        else:
            conds = [(want, slot, [pv]) for want, slot, pv in found]
        out[name] = (lhs, rhs, conds)
    return out


def canonical_rule(rule, suite):
    """Alpha-normalise one `(lhs, rhs, guards)` semantic triple."""
    lhs, rhs, conds = rule
    if suite == "sdql":
        lhs, rhs = (re.sub(r"\bsdql-let\b", "let", s).replace("sym:", "") for s in (lhs, rhs))
    pvars, slots = {}, {}

    def pv(m):
        return pvars.setdefault(m.group(), f"?v{len(pvars)}")

    def sl(m):
        return slots.setdefault(m.group(), f"$s{len(slots)}")

    sides = []
    for side in (lhs, rhs):
        side = re.sub(r"\?[A-Za-z_][A-Za-z0-9_]*", pv, side)
        side = re.sub(r"\$[A-Za-z0-9_]+", sl, side)
        sides.append(re.sub(r"\s+", " ", side).strip())

    guards = []
    for want, slot, variables in conds:
        cslot = slots.get(slot)
        cvars = [pvars.get("?" + v) for v in variables]
        if cslot is None or any(v is None for v in cvars):
            guards.append((want, f"unbound:{slot}", tuple(f"unbound:{v}" if v is None else v for v in cvars)))
        else:
            guards.append((want, cslot, tuple(sorted(cvars))))
    return sides[0], sides[1], tuple(sorted(guards))


def main():
    bad = []
    for name, (mine, theirs, alias) in SUITES.items():
        if not theirs.is_file():
            print(f"  FAIL {name}: locked reference source not found: {theirs}")
            bad.append(name)
            continue
        ours_by_name = local_rules(mine)
        ref_by_original_name = reference_rules(theirs)
        ours = set(ours_by_name)
        ref = {alias.get(r, r) for r in their_names(theirs)}
        extra = sorted(ours - ref)
        missing = sorted(ref - ours)
        unexplained = [m for m in missing if m not in EXPECTED_MISSING.get(name, {})]
        stale = [m for m in EXPECTED_MISSING.get(name, {}) if m in ours or m not in ref]
        semantic = []
        for ref_name, their_rule in ref_by_original_name.items():
            our_name = alias.get(ref_name, ref_name)
            if our_name not in ours_by_name:
                continue
            a = canonical_rule(ours_by_name[our_name], name)
            b = canonical_rule(their_rule, name)
            if a != b:
                semantic.append((our_name, a, b))
        unparsed = sorted(their_names(theirs) - set(ref_by_original_name))
        ok = not extra and not unexplained and not stale and not semantic and not unparsed
        bad += [] if ok else [name]
        print(
            f"  {'ok  ' if ok else 'FAIL'} {name:6} {len(ours)} ours, {len(ref)} run by the reference; "
            f"{len(semantic)} semantic mismatch(es)"
        )
        if extra:
            print(f"       ours but NOT run by the reference: {', '.join(extra)}")
        if unexplained:
            print(f"       run by the reference and missing here: {', '.join(unexplained)}")
        if stale:
            print(f"       recorded as missing but not: {', '.join(stale)}")
        if unparsed:
            print(f"       could not extract semantics for: {', '.join(unparsed)}")
        for rule, ours_sem, ref_sem in semantic[:3]:
            print(f"       {rule}: semantics differ")
            print(f"         ours {ours_sem}")
            print(f"         ref  {ref_sem}")
    print(f"\n{len(SUITES) - len(bad)}/{len(SUITES)} rule sets match the reference")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
