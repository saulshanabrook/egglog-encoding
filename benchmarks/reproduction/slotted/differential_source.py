"""Pure renderers for the frozen differential fixtures; no engine or compiler subprocesses."""

import json
from dataclasses import dataclass

from . import reference as ref
from . import workloads


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
    lines = [f"rounds {rounds}", *workloads.ctor_lines(lang)]
    lines.extend(f"term {lang.sexpr(t)}" for t in terms)
    # The reference's goal is relative to its first term. Seed the shared
    # variable only after the workload inputs so that root keeps its meaning.
    if lang.symbols_for(lang.default_sort).var is not None:
        lines.append("term (var $0)")
    lines.extend(f"union {lang.sexpr(a)} {lang.sexpr(b)}" for a, b in unions)
    lines.extend(rules)
    lines.extend(f"probe {lang.sexpr(t)}" for t in probes)
    return "\n".join(lines) + "\n"


def variable_term(lang, slot):
    constructor = lang.symbols_for(lang.default_sort).var
    if constructor is None:
        raise ValueError(f"{lang.default_sort}: no variable constructor is declared")
    return f"({constructor} {slot})"


def term(lang, t):
    """A generated ground term in the public source language."""
    if t[0] == "var":
        return variable_term(lang, f"${t[1]}")
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


def pattern(lang, t, *, binder=False):
    if t[0] == "pv":
        return t[1]
    if t[0] == "sl":
        return t[1] if binder else variable_term(lang, t[1])
    if t[0] == "cls":
        return term(lang, t[1])
    if t[0] == ref.SUBST:
        return "(subst " + " ".join(pattern(lang, a, binder=i == 1) for i, a in enumerate(t[1:])) + ")"
    op = lang[t[0]]
    kids, pays = op.split(t[1:])
    return node(op, [pattern(lang, k, binder=i in op.binders) for i, k in enumerate(kids)], pays)


def rewrite(lang, atoms, root, rhs, *, conds=(), name=None):
    """Spell a generated multipattern rule as a source rewrite."""
    facts = []
    for r, op, kids, *payloads in atoms:
        pays = payloads[0] if payloads else lang[op].pays
        children = [pattern(lang, k, binder=i in lang[op].binders) for i, k in enumerate(kids)]
        facts.append(f"(= {r} {node(lang[op], children, pays)})")
    facts.extend(f"({'free' if want else 'not-free'} {slot} {' '.join(pvars)})" for want, slot, pvars in conds)
    options = f" :when ({' '.join(facts)})"
    if name:
        options += " :name " + json.dumps(name)
    return f"(rewrite {root} {pattern(lang, rhs)}{options})"


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
            column = ref.SLOT if isinstance(body, str) and ref.SLOT_LITERAL.fullmatch(body) else ref.CHILD
            term = src.term(body, column)
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


def program(language, lang, rules, terms, unions, probes, rounds, *, defer_probes=False):
    """Keep public source/probes; Rust observes partitions after execution."""
    source = [f'(include "egglog-experimental/tests/slotted/languages/{language}.egg")', *dict.fromkeys(rules)]
    if lang.symbols_for(lang.default_sort).var is not None:
        source.append(f"(let _variable_seed {variable_term(lang, '$0')})")
    source += [f"(let _t{i} {term(lang, t)})" for i, t in enumerate(terms)]
    source += [f"(union {term(lang, a)} {term(lang, b)})" for a, b in unions]
    probe_terms = [f"(let _p{i} {term(lang, t)})" for i, t in enumerate(probes)]
    if not defer_probes:
        source += probe_terms
    source.append(f"(run {rounds})")
    if defer_probes:
        source += probe_terms
    return "\n".join(source) + "\n"
