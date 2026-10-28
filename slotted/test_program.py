"""Shared input translation and execution for differential tests.

Most tests use the source language. Tests that inspect internal tables append
ordinary egglog observer rules to the CLI's desugared output.
"""

import json
import subprocess
import tempfile
from dataclasses import dataclass
from functools import cache, lru_cache
from pathlib import Path

from slotted import reference as ref

ROOT = Path(__file__).resolve().parents[1]
EGGLOG = ROOT / "target/debug/egglog-experimental"
XMULTI = ROOT / "slotted/xmulti/target/debug/xmulti"


@dataclass
class Rule:
    """One source rewrite, compiled by Rust and translated to the reference."""

    src: ref.Source
    lang: ref.TermLang
    form: list

    @property
    def name(self):
        return ref.rule_name(self.src, self.form)

    @property
    def conds(self):
        return ref.rewrite_parts(self.src, self.form)["conds"]

    @property
    def atoms(self):
        return ref.rule_atoms(self.src, self.lang, ref.rewrite_parts(self.src, self.form))[1]

    def source(self, first_atom=None):
        """Render the rewrite, optionally moving one flattened pattern first."""
        if first_atom is None:
            return ref.render(self.form)
        parts = ref.rewrite_parts(self.src, self.form)
        if parts["same"] or parts["diseq"]:
            raise ValueError("cannot reorder a reference rule with unsupported comparison guards")
        root, atoms = ref.rule_atoms(self.src, self.lang, parts)
        atoms.insert(0, atoms.pop(min(first_atom, len(atoms) - 1)))
        rhs = ref.rhs_of(self.lang, self.src.term(parts["rhs"], ground=False))
        return rewrite(self.lang, atoms, root, rhs, conds=parts["conds"], name=parts["name"])

    def spec_lines(self):
        return ref.rule_lines(self.src, self.lang, self.form)

    def without_guards(self):
        """Keep the patterns while removing slot-membership guards for mutation tests."""
        form = self.form[:3]
        for key, values in ref.keywords(self.src, self.form[3:]):
            if key == ":when":
                values = [[c for c in values[0] if c[0] not in ("free", "not-free")]]
            form.extend([key, *values])
        return Rule(self.src, self.lang, form)


def load_rules(path, lang):
    src = ref.Source(path)
    rules = [Rule(src, lang, form) for form in ref.parse(path.read_text()) if form[:1] == ["rewrite"]]
    names = [r.name for r in rules]
    if None in names or len(set(names)) != len(names):
        raise ValueError(f"{path.name}: fixture rewrites must have unique names")
    return {rule.name: rule for rule in rules}


def reference_spec(lang, rounds, terms, unions, rules, probes):
    """The reference protocol shared by generated cases and source fixtures."""
    lines = [f"rounds {rounds}"]
    lines.extend(f"term {lang.sexpr(t)}" for t in terms)
    lines.extend(f"union {lang.sexpr(a)} {lang.sexpr(b)}" for a, b in unions)
    lines.extend(rules)
    lines.extend(f"probe {lang.sexpr(t)}" for t in probes)
    return "\n".join(lines) + "\n"


def run_reference(spec, timeout, *, result="PARTITION"):
    try:
        run = subprocess.run([str(XMULTI)], input=spec, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "TIMEOUT", f">{timeout}s"
    if run.returncode:
        lines = run.stderr.strip().splitlines()
        detail = next(
            (line for line in lines if "SlotMap::index" in line or "SlotMap::compose" in line),
            next((line for line in lines if "panicked at" in line), lines[-1] if lines else "?"),
        )
        return "ERROR", detail
    values = [
        line.removeprefix(result + " ").strip() for line in run.stdout.splitlines() if line.startswith(result + " ")
    ]
    if len(values) != 1:
        return "ERROR", f"no unique {result} line"
    saturated = all(not line.startswith("SATURATED no") for line in run.stdout.splitlines())
    return ("OK" if saturated else "UNSATURATED"), values[0]


def run_encoding(program, probes, timeout, *, keep=None):
    if keep is None:
        with tempfile.NamedTemporaryFile(prefix="xdiff-", suffix=".egg", mode="w", delete=False) as file:
            file.write(program)
            path = Path(file.name)
    else:
        path = keep
        path.write_text(program)
    try:
        run = subprocess.run(
            [str(EGGLOG), "--slotted-encoded", str(path)], capture_output=True, text=True, timeout=timeout, cwd=ROOT
        )
    except subprocess.TimeoutExpired:
        return "TIMEOUT", f">{timeout}s (program kept at {path})"
    if run.returncode:
        errors = [line for line in run.stderr.splitlines() if "ERROR" in line]
        detail = errors[-1] if errors else run.stderr.strip()[:600]
        return "ERROR", f"{detail}\n    (program kept at {path})"
    partition = parse_same_class(run.stdout, probes)
    if keep is None:
        path.unlink()
    return "OK", partition


@lru_cache(maxsize=32)
def compile_source(text):
    with tempfile.TemporaryDirectory(prefix="slotted-source-") as tmp:
        path = Path(tmp) / "source.egg"
        path.write_text(text)
        run = subprocess.run(
            [
                str(EGGLOG),
                "--slotted",
                "--mode",
                "desugar",
                str(path),
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=60,
        )
        if run.returncode:
            raise RuntimeError(f"Rust compilation failed:\n{run.stderr}\nSource:\n{text}")
        return run.stdout


def term(lang, t):
    """A generated ground term in the public source language."""
    if t[0] == "var":
        return f"${t[1]}"
    op = lang[t[0]]
    kids, pays = op.split(t[1:])
    return node(op, [f"${lang.slot(k)}" if i in op.binders else term(lang, k) for i, k in enumerate(kids)], pays)


def node(op, kids, pays):
    parts = [op.ctor]
    kids, pays = iter(kids), iter(pays)
    for col in op.sig:
        if col in ref.SLOTTED:
            parts.append(next(kids))
        else:
            value = next(pays)
            if isinstance(value, tuple):
                tag, value = value
                if tag == "plit" and col == "String":
                    value = json.dumps(value)
            parts.append(str(value))
    return "(" + " ".join(parts) + ")"


def pattern(lang, t):
    if t[0] in ("pv", "sl"):
        return t[1]
    if t[0] == "cls":
        return term(lang, t[1])
    if t[0] == ref.SUBST:
        return "(subst " + " ".join(pattern(lang, a) for a in t[1:]) + ")"
    op = lang[t[0]]
    kids, pays = op.split(t[1:])
    return node(op, [pattern(lang, k) for k in kids], pays)


def rewrite(lang, atoms, root, rhs, *, conds=(), name=None):
    """Spell a generated multipattern rule as a source rewrite."""
    facts = []
    for r, op, kids, *payloads in atoms:
        pays = payloads[0] if payloads else lang[op].pays
        facts.append(f"(= {r} {node(lang[op], [pattern(lang, k) for k in kids], pays)})")
    facts.extend(f"({'free' if want else 'not-free'} {slot} {' '.join(pvars)})" for want, slot, pvars in conds)
    options = f" :when ({' '.join(facts)})"
    if name:
        options += " :name " + json.dumps(name)
    return f"(rewrite {root} {pattern(lang, rhs)}{options})"


@cache
def machinery(language):
    return compile_source(f'(include "egglog-experimental/tests/slotted/languages/{language}.egg")')


@lru_cache(maxsize=1)
def maintenance():
    """Use the compiler's actual maintenance schedule in internal-table tests."""
    text = compile_source('(include "egglog-experimental/tests/slotted/languages/toy.egg")\n(run 0)')
    return ref.render(next(f for f in ref.parse(text) if f[0] == "run-schedule"))


def program(language, lang, rules, terms, unions, probes, rounds, *, defer_probes=False):
    source = [f'(include "egglog-experimental/tests/slotted/languages/{language}.egg")', *dict.fromkeys(rules)]
    source.extend(f"(let _t{i} {term(lang, t)})" for i, t in enumerate(terms))
    source.extend(f"(union {term(lang, a)} {term(lang, b)})" for a, b in unions)
    # A bare slot has no source-level global representation. The partition
    # observer needs only its class, which is the canonical variable node.
    symbols = lang.symbols_for(lang.default_sort)
    var = f"({symbols.var} 0)"
    probe_terms = [var if t[0] == "var" else f"(let _p{i} {term(lang, t)})" for i, t in enumerate(probes)]
    if not defer_probes:
        source.extend(probe_terms)
    source.append(f"(run {rounds})")
    if defer_probes:
        source.extend(probe_terms)
    # Capture probe values while source globals are still in scope. Desugaring
    # can replace their bindings with shared-table rows, so appended observers
    # must not refer to the original global names.
    source.append(f"(relation ProbeId ({symbols.sort} i64))")
    bindings = [f"(ProbeId {var if t[0] == 'var' else f'$_p{i}'} {i})" for i, t in enumerate(probes)]
    if bindings:
        source.append("(begin " + " ".join(bindings) + ")")
    source.append("(run 0)")
    encoded = compile_source("\n".join(source))
    # Partition queries run after the budget and final maintenance.
    observer = [
        f"""
(ruleset probes)
(relation SameClass (i64 i64))
(rule ((ProbeId a i) (ProbeId b j)
       ({symbols.renames} a m1 l) ({symbols.renames} b m2 l))
      ((SameClass i j)) :ruleset probes)
"""
    ]
    observer += ["(run-schedule (saturate (run probes)))", "(print-function SameClass 100000)"]
    return encoded + "\n".join(observer) + "\n"


def parse_same_class(stdout, n):
    """Turn the printed SameClass rows into the same canonical string the
    reference prints."""
    pairs = set()
    for line in stdout.splitlines():
        line = line.strip()
        if not line.startswith("(SameClass "):
            continue
        nums = line[len("(SameClass ") :].split(")")[0].split()
        pairs.add((int(nums[0]), int(nums[1])))
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x

    for i, j in pairs:
        a, b = find(i), find(j)
        if a != b:
            parent[max(a, b)] = min(a, b)
    groups = {}
    for i in range(n):
        groups.setdefault(find(i), []).append(i)
    gs = sorted("[" + ",".join(str(i) for i in sorted(v)) + "]" for v in groups.values())
    # every probe is added, so nothing is ever missing on this side
    return "".join(gs) + " missing[[]]"


def fixture_blocks(path):
    """The top-level `(push)`/`(pop)` regions contributed by one fixture.

    Included libraries are deliberately excluded: a case is selected by one of the
    fixture's own `let` names, and a library changing its own scopes must not silently
    renumber those cases.
    """
    src = ref.Source(path)
    blocks, block = [], None
    for form, origin in src.body:
        if origin != path or not isinstance(form, list) or not form:
            continue
        if form[0] == "push":
            if block is not None:
                raise ValueError(f"{path.name}: nested push regions are not fixture cases")
            block = []
        elif form[0] == "pop":
            if block is None:
                raise ValueError(f"{path.name}: pop without a fixture case")
            blocks.append(block)
            block = None
        elif block is not None:
            block.append(form)
    if block is not None:
        raise ValueError(f"{path.name}: unterminated fixture case")
    return src, blocks


def fixture_term(term, named):
    """Inline a fixture's `let` globals into the tuple form the oracle accepts."""
    if not isinstance(term, tuple):
        return term
    if term[0] == "name":
        try:
            return named[term[1]]
        except KeyError as exc:
            raise ValueError(f"fixture term refers to unknown global {term[1]!r}") from exc
    return tuple(fixture_term(arg, named) for arg in term)


def fixture_block(path, anchor):
    """Read the unique fixture region that binds `anchor`.

    The result retains names because choosing the seed and observational probes is
    differential-test metadata.  Their term trees and asserted unions remain owned by
    the `.egg` source; the differential harness continues to own its round budget.
    """
    src, blocks = fixture_blocks(path)
    hits = [
        block for block in blocks if any(form[0] == "let" and len(form) == 3 and form[1] == anchor for form in block)
    ]
    if len(hits) != 1:
        raise ValueError(f"{path.name}: expected one fixture case binding {anchor!r}, found {len(hits)}")

    named, unions = {}, []
    for form in hits[0]:
        if form[0] == "let":
            _, name, body = form
            if name in named:
                raise ValueError(f"{path.name}: duplicate global {name!r} in fixture case {anchor!r}")
            term = src.term(body)
            src.lang.bound[name] = term
            named[name] = fixture_term(term, named)
        elif form[0] == "union":
            _, left, right = form
            unions.append(
                (
                    fixture_term(src.term(left), named),
                    fixture_term(src.term(right), named),
                )
            )
    return src, named, unions


def fixture_rewrites(path, *names):
    """Read uniquely named local rewrites from a source fixture."""
    src = ref.Source(path)
    wanted, found = set(names), {}
    for form, origin in src.body:
        if origin != path or not (isinstance(form, list) and form and form[0] == "rewrite"):
            continue
        parts = ref.rewrite_parts(src, form)
        if parts["name"] in wanted:
            if parts["name"] in found:
                raise ValueError(f"{path.name}: duplicate rewrite {parts['name']!r}")
            found[parts["name"]] = form
    missing = wanted - found.keys()
    if missing:
        raise ValueError(f"{path.name}: missing fixture rewrite(s): {', '.join(sorted(missing))}")
    return src, found
