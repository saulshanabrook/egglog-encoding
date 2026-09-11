#!/usr/bin/env python3
"""Compile a test written in the SLOTTED language down to plain egglog.

A slotted test declares its own constructors at the top and then talks about terms,
rules and classes -- never about renamings, edges or `(Var 0)`. This turns that into a
self-contained egglog program: the hand-written core, the machinery for exactly the
constructors declared, and the compiled body. The output includes no generated file,
so there is no build artifact on the path between a test and running it.

THE LANGUAGE

    (constructor Sum (U U U U) U :binder 1 2)   the language, inline. A column in any
                                                declared equality sort is a slotted
                                                child; `:binder` names the child
                                                positions whose slot it binds.

    (let r (Sing Null Null))                    name a term
    (let a (Sum r $5 $6 Null))                  a `$n` in a binder column is the bound
                                                slot; in any other child column it is
                                                a variable occurrence

    (let #g (Sing Null Null))                   `#` marks a GLOBAL, at its binding and
    (rewrite (Mult x #g) x)                     its uses. Bare works too, as in egglog.
                                                `$x` is a slot wherever it appears, so a
                                                global may not be named with a `$`.

    (union a b)                                 assert an equation instead of deriving
                                                one -- how a class gets a symmetry, and
                                                how a slot becomes redundant

    (rewrite (Sum e1 $k $v (Sing $k $v)) e1)    a rule, in terms
    (rewrite lhs rhs :when ((not-free $x f)))   `:when` takes a LIST of facts; this one
                                                is a slot side condition
    (rewrite lhs rhs                            a fact `(= v <call>)` is another
             :when ((= v (Sing a b))            PATTERN: `v` matches this too, and
                    (not-free $k v))            variables shared between the patterns
             :name "sum-sing")                  are the join. `:name` is a string.

    (run 3)                                     three user-rule steps, with the
                                                machinery saturated around each

    (check (= a b))                             a and b are EQUAL: the same term, once
                                                renamings are taken into account
    (check (!= a b))                            and are not
    (check (renaming-= a b))                    equal MODULO SOME RENAMING -- one class,
                                                not necessarily at the same slots
    (check (renaming-!= a b))                   and are not
    (check (slots a $5 $6))                     a's class depends on exactly these
    (check (holds a Mult))                      a's class contains a Mult node
    (check (not-holds a Mult))                  and does not

`slotted/LANGUAGE.md` is the reference for all of these, with the reason each exists.

EVERYTHING ELSE IS EGGLOG'S

Only a form that NAMES A SLOTTED TERM needs compiling, because only a term has to be
encoded. Every other command means the same thing here as it does in egglog and goes
through as written -- `(push)`, `(pop)`, `(print-size)`, `(print-function F 10)`,
`(query-extract ...)`, and whatever egglog gains next. `(extract a)` is the one in
between: its argument is a term, so it is encoded, and what egglog then prints is the
node as the encoding STORES it, renamings and all.

    (extract a)             (F (map-of 0 2) (Var 0) (map-of 0 1) (Var 0))

A check whose claim is none of the ones above is egglog's too, so a one-sort test can
drop to the encoded level -- `(check (RenamesToLeader a m l))` -- without leaving the
language. Multi-sort output uses one indexed family per carrier,
`RenamesToLeader_0`, `RenamesToLeader_1`, and so on.

WHAT `=` MEANS HERE

Egglog's `=` compares two values. A slotted term is not a value: it is a class TOGETHER
WITH a renaming, so `=` here is compiled, not passed through -- it asks whether the two
terms are the SAME TERM. `renaming-=` is the weaker question of whether they are equal
modulo some renaming, which is what two alpha-variants with a renamed free slot are.
`LANGUAGE.md` gives the example that separates them.

Usage:
    ./slotted-egglog.py SRC.egg              run it
    ./slotted-egglog.py SRC.egg --desugar    write the compiled program to stdout
    ./slotted-egglog.py SRC.egg -o OUT.egg   ... or to a file
"""

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "slotted"))
enc = __import__("slotted-encoder")

CARRIER = "U"  # the sort the hand-written core declares
CORE_FILE = "slotted/encoding/egraph-encoding-11.egg"

TOKEN = re.compile(r'\(|\)|"[^"]*"|;[^\n]*|[^\s()]+')
SLOT = re.compile(r"\$\w+\Z")
#: A global may be written with this sigil. egglog writes `$name`, which cannot be
#: borrowed: `$` is a SLOT here, and one spelling cannot mean both. Bare works too, as
#: it does in egglog.
GLOBAL = "#"


def parse(text):
    """Every top-level form, as nested lists of tokens. Comments are dropped."""
    toks = [t for t in TOKEN.findall(text) if not t.startswith(";")]
    pos, out = [0], []

    def go():
        t = toks[pos[0]]
        pos[0] += 1
        if t != "(":
            return t
        form = []
        while toks[pos[0]] != ")":
            form.append(go())
        pos[0] += 1
        return form

    while pos[0] < len(toks):
        out.append(go())
    return out


def render(form):
    """A parsed form back as text, unchanged."""
    return "(" + " ".join(render(x) for x in form) + ")" if isinstance(form, list) else form


class Terms(enc.TermLang):
    """The test's language, plus the names its `let`s bind.

    A name stands for a term already built, so it writes as `$name` -- but its parent
    still needs the SLOTS to put in the edge, which is why a bound name cannot be an
    opaque value here.
    """

    def __init__(self, ops, carriers=None):
        super().__init__(ops, carriers)
        self.bound = {}

    def slots(self, t):
        return self.slots(self.bound[t[1]]) if t[0] == "name" else super().slots(t)

    def sort_of(self, t, expected=None):
        return self.sort_of(self.bound[t[1]], expected) if t[0] == "name" else super().sort_of(t, expected)

    def enc(self, t, expected_sort=None):
        if t[0] == "name":
            actual = self.sort_of(t)
            if expected_sort is not None and actual != expected_sort:
                raise SystemExit(f"global {t[1]!r} has sort {actual}, but this position requires {expected_sort}")
            return f"${t[1]}"
        return super().enc(t, expected_sort)


def payload(tok, ground=True):
    """A payload argument -- a node argument carrying no slots, which is the reference's
    own word for it (`lang.rs`: "payload types that are independent of Slots").

    Ground: the value, not its egglog spelling. A source writes a string payload quoted,
    because that is egglog's syntax, and `Op.split` quotes it again on the way out, so
    the quotes come off here.

    In a PATTERN a payload may be matched or bound, as in egglog: a quoted or numeric
    token is a LITERAL to match on, a bare identifier is a VARIABLE the match binds, and
    two atoms naming the same variable join on it. Tagged, so `compile_rule` can tell
    them apart.
    """
    if not isinstance(tok, str):
        raise SystemExit(
            f"a payload column takes a value, not a call ({tok!r}). egglog's value "
            "primitives -- arithmetic and comparison over payloads -- are not "
            "implemented here, so a payload cannot be computed."
        )
    quoted = len(tok) >= 2 and tok.startswith('"') and tok.endswith('"')
    if ground:
        return tok[1:-1] if quoted else tok
    if quoted or re.fullmatch(r"-?\d+", tok):
        return ("plit", tok[1:-1] if quoted else tok)
    return ("ppv", tok)


class Source:
    """One slotted test: its language, and its body in order."""

    def __init__(self, path):
        self.path = path
        # repo-relative, so a snapshot does not carry the checkout it was built in --
        # falling back to the name for a one-off probe compiled from outside the tree
        try:
            self.relpath = path.resolve().relative_to(ROOT).as_posix()
        except ValueError:
            self.relpath = path.name
        self.spec = {}
        self.output_sorts = {}
        self.child_sorts = {}
        self.body = []
        self.includes = []
        # A program may declare its own sort, and then THAT is the sort its terms have --
        # the core is renamed to it rather than a carrier being invented. Collected first
        # because a column is a slotted child exactly when its sort is a declared one, so
        # the constructors cannot be read until the sorts are known.
        self.sorts = []
        self._ctors = []
        self._read(path)
        if len(set(self.sorts)) != len(self.sorts):
            raise SystemExit(f"{path.name}: an equality sort is declared more than once")
        carriers = enc.carrier_symbols(self.carrier_sorts())
        if len(carriers) > 1:
            reserved = {
                "Renaming",
                "Namings",
                "Idx",
                "slotted",
                "SlottedNodeLayout",
                "SlottedEdgeLayout",
                "SlottedBinderLayout",
            }
            for names in carriers.values():
                reserved.update(
                    (
                        names.var,
                        names.renames,
                        names.equated,
                        names.class_slots,
                        names.subst_pending,
                    )
                )
            collision = next((sort for sort in self.sorts if sort in reserved), None)
            if collision is None:
                collision = next((form[1] for form in self._ctors if form[1] in reserved), None)
            if collision is None:
                collision = next(
                    (
                        form[1]
                        for form, _origin in self.body
                        if isinstance(form, list)
                        and len(form) > 1
                        and form[0] in ("function", "relation", "ruleset")
                        and form[1] in reserved
                    ),
                    None,
                )
            if collision is not None:
                raise SystemExit(
                    f"{path.name}: declaration {collision!r} is reserved by the multi-sort slotted encoding"
                )
        for form in self._ctors:
            name, sig, output, children = enc.read_typed_language_form(form, self.carrier_sorts())
            if name in self.spec:
                raise SystemExit(f"{path.name}: constructor {name!r} is declared more than once")
            foreign = [sort for sort in children if sort != output]
            if foreign:
                raise SystemExit(
                    f"{path.name}: constructor {name} produces {output} but has a slotted child of sort "
                    f"{foreign[0]}; cross-sort slotted children are not supported yet"
                )
            if name in {names.var for names in carriers.values()}:
                raise SystemExit(f"{path.name}: constructor {name!r} is reserved by the slotted encoding")
            self.spec[name] = sig
            self.output_sorts[name] = output
            self.child_sorts[name] = children
        if not self.spec:
            raise SystemExit(
                f"{path.name}: no constructors declared. Write `(datatype U (Succ U) ...)`, "
                "or a `(sort U)` and its `(constructor ...)` lines."
            )
        self.carriers = carriers
        self.lang = Terms(
            {
                c: enc.Op(
                    c,
                    c,
                    sig,
                    sort=self.output_sorts[c],
                    kid_sorts=self.child_sorts[c],
                )
                for c, sig in self.spec.items()
            },
            carriers,
        )

    def _read(self, path):
        """This file's declarations and body, with any included source read first.

        `(include "...")` in a slotted source names ANOTHER SLOTTED SOURCE, and pulls in
        its constructors and its rules -- so a test over the sdql rules says
        `(include "slotted/languages/sdql.egg")` instead of restating 44 of them. A slotted
        source never includes the hand-written core or a generated file: the compiler
        supplies the core and generates the machinery, which is the whole point.
        """
        for form in parse(path.read_text()):
            if isinstance(form, list) and form and form[0] == "include":
                inc = ROOT / form[1].strip('"')
                assert inc.exists(), f"{path.name}: no such file {form[1]}"
                assert "target/" not in inc.as_posix() and inc.name != CORE_FILE.split("/")[-1], (
                    f"{path.name}: a slotted source may only include another slotted source, not {form[1]}"
                )
                self.includes.append(inc)
                self._read(inc)
            elif isinstance(form, list) and form and form[0] == "constructor":
                # stashed rather than kept in the body: `signature` needs the declared
                # sorts, which may come later, and the machinery re-emits the declaration
                self._ctors.append(form)
            elif isinstance(form, list) and form and form[0] == "datatype":
                # egglog's own way to declare a language, and so the first thing anyone
                # coming from egglog writes: one form for the sort and its constructors.
                # Read as exactly that -- the sort, plus one constructor per variant
                # whose output sort is the datatype -- so it reaches the same machinery
                # as `(sort ...)` and `(constructor ...)` written separately.
                self._ctors.extend(self._variants(path, form))
            elif isinstance(form, list) and form and form[0] == "datatype*":
                for group in form[1:]:
                    if not isinstance(group, list):
                        raise SystemExit(f"{path.name}: each `datatype*` entry must be a datatype group, got {group!r}")
                    self._ctors.extend(self._variants(path, ["datatype", *group]))
            else:
                if isinstance(form, list) and len(form) == 2 and form[0] == "sort":
                    self.sorts.append(form[1])
                self.body.append((form, path))

    def _variants(self, path, form):
        """A `(datatype Name (Ctor <sort>*) ...)` as one `constructor` form per variant.

        A variant's options come after its column sorts -- egglog's own `:cost` and
        `:unextractable` sit there, and `:binder` goes in the same place.
        """
        if len(form) < 2 or not isinstance(form[1], str):
            raise SystemExit(f"{path.name}: `datatype` needs a sort name, got {form[1:2]}")
        name = form[1]
        self.sorts.append(name)
        out = []
        for variant in form[2:]:
            if not isinstance(variant, list) or not variant or not isinstance(variant[0], str):
                raise SystemExit(
                    f"{path.name}: a `datatype` variant must be a call like `(Succ {name})`, got {variant!r}"
                )
            ctor, rest = variant[0], variant[1:]
            opts = next((i for i, t in enumerate(rest) if isinstance(t, str) and t.startswith(":")), len(rest))
            out.append(["constructor", ctor, list(rest[:opts]), name, *rest[opts:]])
        return out

    def carrier_sorts(self):
        """The sorts whose columns are slotted children.

        A program's own declarations when it has any, and otherwise the one the
        hand-written core declares.
        """
        return tuple(self.sorts) if self.sorts else (CARRIER,)

    def core(self):
        """The carrier core to inline, or None to include the legacy one as it stands.

        A program that declares no sort gets the file included, which is what every test
        did before sorts were a thing and keeps their snapshots unchanged. A program that
        declares one gets the same core with the carrier RENAMED to it; the core declares
        that sort before its relations and the source declaration is dropped. The rules
        are untouched: they name relations, and with a single sort the relation names do
        not change. Several sorts share the map/naming prelude and get one indexed copy
        of the carrier-specific tables and rules each.
        """
        if not self.sorts:
            return None
        if len(self.sorts) > 1:
            text = (ROOT / CORE_FILE).read_text()
            marker = ";; One `U` value per e-node and per class; a slotted class spans several of them."
            shared, found, _carrier = text.partition(marker)
            assert found, f"{CORE_FILE}: cannot find the carrier-core boundary"
            return shared.rstrip() + "\n\n" + enc.multi_sort_core(self.carriers)
        sort = self.sorts[0]
        text = (ROOT / CORE_FILE).read_text()
        # The rename is textual, which is exact for a name the core does not otherwise
        # use: every mention of `U` there is a declaration. A name the core uses as a
        # RULE VARIABLE would be captured instead, so it is refused.
        #
        # A program naming its sort `U` is asking for the name the core already uses: the
        # rename is the identity, so nothing can capture and there is nothing to refuse.
        body = re.sub(r";[^\n]*", "", text)
        if sort != CARRIER and re.search(rf"\b{re.escape(sort)}\b", body):
            raise SystemExit(
                f"{self.path.name}: the sort name {sort!r} is already used inside the machinery, "
                "so renaming the carrier onto it would capture. Pick another name."
            )
        # every mention of the carrier is a DECLARATION -- the rules name relations, not
        # the sort -- so renaming the whole-word occurrences is exact
        # the core keeps the `(sort ...)` line, so the sort is declared BEFORE the
        # relations that use it; the program's own declaration is dropped instead, in
        # `compile_source`, since two of them is a duplicate binding
        return re.sub(r"\bU\b", sort, text)

    # ------------------------------------------------------------------ terms
    def global_ref(self, name, ground):
        """A `let`-bound global, as a ground reference or as something a pattern can match.

        Ground: the NAME, which compiles to a reference to the value it holds.

        In a pattern it has to be matched, and the encoder's atoms have no case for "the
        value this name holds" -- a child is a variable, a slot literal, or a term. So the
        term the name was bound to is inlined. That is sound rather than approximate: a
        GROUND term's shape determines its class by congruence, so matching the shape and
        naming the class pick out the same thing. Without this a global in a pattern died
        with `KeyError: 'name'`, whichever spelling it wore.
        """
        return ("name", name) if ground else self.lang.bound[name]

    def term(self, form, column=enc.CHILD, ground=True, expected_sort=None):
        """A slotted term as the encoder's tuple form.

        A `$s` means different things in the two settings, and the difference is real
        rather than a spelling. In a GROUND term it is a particular slot -- an integer
        the encoding writes into a renaming -- and in a binder column it IS the bound
        slot, while anywhere else it is a variable occurrence. In a PATTERN it is a
        slot LITERAL, a name the match has to solve for, which the encoder takes as the
        `$s` string in either column.
        """
        if isinstance(form, str):
            if form.startswith(GLOBAL) and len(form) > 1:
                name = form[1:]
                if column is enc.BINDER:
                    raise SystemExit(
                        f"{self.path.name}: {form!r} stands in a binder column, where only a "
                        "slot can. A binder binds a slot, not a global."
                    )
                if name not in self.lang.bound:
                    raise SystemExit(f"{self.path.name}: no global {form!r} is bound here")
                t = self.global_ref(name, ground)
                actual = self.lang.sort_of(t, expected_sort)
                if expected_sort is not None and actual != expected_sort:
                    raise SystemExit(
                        f"{self.path.name}: global {form!r} has sort {actual}, "
                        f"but this position requires {expected_sort}"
                    )
                return t
            if SLOT.match(form):
                # ALWAYS a slot. egglog spells a global `$name`, and this language cannot
                # borrow that: `$0` is a slot, so `$name` was resolved as a global when one
                # of that name happened to be bound and as a slot otherwise -- one spelling
                # meaning two things, decided by what else the file had done. Globals wear
                # `#` instead, and a `$` in a global's name is refused where it is bound.
                if not ground:
                    return form
                slot = int(form[1:]) if form[1:].isdigit() else form[1:]
                return slot if column is enc.BINDER else ("var", slot)
            if form in self.spec:  # a nullary constructor, written bare
                output_sort = getattr(self, "output_sorts", {}).get(form, self.lang[form].sort)
                if expected_sort is not None and output_sort != expected_sort:
                    raise SystemExit(
                        f"{self.path.name}: {form} has sort {output_sort}, but this position requires {expected_sort}"
                    )
                return (form,)
            if form.startswith("?"):
                # a pattern variable. Its NAME is the identifier without the sigil,
                # which is the convention `flatten` keys atoms by and `pat_sexpr`
                # renders back with the `?`, so the reference side reads it too.
                return form[1:]
            if form in self.lang.bound:
                t = self.global_ref(form, ground)
                actual = self.lang.sort_of(t, expected_sort)
                if expected_sort is not None and actual != expected_sort:
                    raise SystemExit(
                        f"{self.path.name}: global {form!r} has sort {actual}, "
                        f"but this position requires {expected_sort}"
                    )
                return t
            # A BARE IDENTIFIER IS A PATTERN VARIABLE, which is how egglog spells one.
            # `?x` is egg's spelling and names the same variable, so a rule may mix
            # them; a bare name that is a global means the global, as in egglog, and
            # `#name` says one outright.
            #
            # Only in a pattern. A ground term -- a `let`, a `union`, a claim -- has
            # nothing to bind a variable, so an unknown name there is an error. A bare
            # name that IS a constructor is read as a nullary call above, so a
            # paren-less `Null` cannot become a wildcard; a misspelling still can,
            # exactly as in egglog.
            assert not ground, f"{self.path.name}: {form!r} is not bound"
            return form
        head, args = form[0], form[1:]
        if head == enc.SUBST:
            # Not a constructor: a call, and only legal on a right-hand side. Its
            # arguments are read like any others so that `b` and `$x` mean here what
            # they mean everywhere else.
            return (head, *(self.term(a, ground=ground, expected_sort=expected_sort) for a in args))
        assert head in self.spec, f"{self.path.name}: unknown constructor {head!r}"
        actual_sort = getattr(self, "output_sorts", {}).get(head, self.lang[head].sort)
        if expected_sort is not None and actual_sort != expected_sort:
            raise SystemExit(
                f"{self.path.name}: {head} has sort {actual_sort}, but this position requires {expected_sort}"
            )
        kinds = self.lang[head].arg_kinds()
        assert len(args) == len(kinds), f"{self.path.name}: {head} takes {len(kinds)} arguments, given {len(args)}"
        parsed, child = [], 0
        child_sorts = getattr(self, "child_sorts", {}).get(head, self.lang[head].kid_sorts)
        for arg, kind in zip(args, kinds, strict=True):
            if kind in enc.SLOTTED:
                parsed.append(self.term(arg, kind, ground, child_sorts[child]))
                child += 1
            else:
                parsed.append(payload(arg, ground))
        return (head, *parsed)

    def encode(self, form, column=enc.CHILD, expected_sort=None):
        """A ground term as the egglog expression for its value."""
        t = self.term(form, column, expected_sort=expected_sort)
        if t[0] == "var":
            sort = expected_sort
            if sort is None:
                if len(self.carriers) > 1:
                    raise SystemExit(
                        f"{self.path.name}: bare top-level slot {form!r} has no equality sort; "
                        "put it under a constructor"
                    )
                sort = next(iter(self.carriers))
            return f"({self.carriers[sort].var} 0)"
        return self.lang.enc(t, expected_sort)

    def sort_of_form(self, form, expected=None, ground=True):
        """Infer a slotted expression's equality sort from its typed context."""
        sort = self.lang.sort_of(self.term(form, ground=ground, expected_sort=expected), expected)
        if sort is None and len(self.carriers) == 1:
            sort = next(iter(self.carriers))
        if sort is None:
            raise SystemExit(
                f"{self.path.name}: {form!r} has no equality-sort context; put the bare slot under a constructor"
            )
        return sort

    def common_sort(self, forms, operation="compare"):
        """Parse forms and require one carrier, allowing contextual bare slots."""
        terms = [self.term(form, enc.CHILD) for form in forms]
        sorts = [self.lang.sort_of(term) for term in terms]
        sort = next((value for value in sorts if value is not None), None)
        if sort is None and len(self.carriers) == 1:
            sort = next(iter(self.carriers))
        if sort is None:
            subject = "a union of two bare slots" if operation == "union" else "comparing bare slots"
            raise SystemExit(f"{self.path.name}: {subject} has no equality sort; put them under constructors")
        if any(value not in (None, sort) for value in sorts):
            verb = "union" if operation == "union" else "compare"
            raise SystemExit(f"{self.path.name}: cannot {verb} terms of sorts {sorts[0]} and {sorts[1]}")
        return sort, terms


def compile_source(src, own_only=False):
    """The whole program, or -- for a snapshot -- only what this file contributes.

    `own_only` drops the machinery and anything an included library brought, because
    both are already snapshotted by the generator that emits them. What is left is the
    forms this test wrote, which is the part no other snapshot covers.
    """
    core = src.core()
    out = [
        f";;; COMPILED from {src.relpath} by slotted/slotted-egglog.py.",
        ";;;",
        ";;; A SNAPSHOT: committed so a change in the compiler shows up as a diff, never",
        ";;; edited by hand, and rewritten by `check-slotted.py --update`. This is what",
        ";;; running that test runs, and the only file it includes is the hand-written core.",
        "",
        f'(include "{CORE_FILE}")' if core is None else core,
        "",
    ]
    if own_only:
        out[2:5] = [
            f";;; Only the forms THIS file contributes. The machinery for its {len(src.spec)} constructors,",
            ";;; and anything an included library brought, are snapshotted by the generators",
            ";;; that emit them -- committing them again per test would be the same thousands",
            ";;; of lines over and over.",
        ]
    else:
        emitted = []
        for sort in src.carrier_sorts():
            spec = {name: sig for name, sig in src.spec.items() if src.output_sorts[name] == sort}
            provided = enc.CORE if len(src.carriers) == 1 else None
            emitted += enc.emit(
                spec,
                provided=provided,
                sort=sort,
                symbols=src.carriers[sort],
            )
        out.append(enc.in_slotted_ruleset("\n".join(emitted)))
    rules = 0
    scopes = []  # globals saved by each open `push`, restored by its `pop`
    extracts = 0
    for form, origin in src.body:
        head = form[0] if isinstance(form, list) else form
        mine = origin == src.path
        keep = mine or not own_only
        if head == "sort" and len(form) == 2 and form[1] in src.carrier_sorts():
            # the core declares the carrier, positioned before the relations that use it,
            # so the program's own declaration of the same sort would be a duplicate
            continue
        if head == "push":
            # `(pop)` in egglog undoes the `let`s the region made, so the compiler's own
            # table of globals has to be undone with it. Left flat, a name bound inside a
            # closed region stayed bound: a later rule mentioning it matched that stale
            # term instead of binding a pattern variable, and a ground mention compiled to
            # a reference egglog no longer had.
            scopes.append(dict(src.lang.bound))
            _emit(out, keep, render(form))
        elif head == "pop":
            if scopes:
                src.lang.bound = scopes.pop()
            _emit(out, keep, render(form))
        elif head == "let":
            _, name, body = form
            # The sigil is optional here, as it is in egglog, which only warns when a
            # global lacks one. A `$` is not optional but forbidden: `$x` is a slot in
            # this language, so a global of that name could never be written back.
            if name.startswith("$"):
                raise SystemExit(
                    f"{src.path.name}: a global may not be named {name!r} -- `$` starts a SLOT "
                    f"here, so `{name}` in a term would mean the slot and never this global. "
                    f"Name it `{name[1:]}`, or `{GLOBAL}{name[1:]}` to mark it."
                )
            name = name[1:] if name.startswith(GLOBAL) and len(name) > 1 else name
            if isinstance(body, str) and SLOT.match(body):
                raise SystemExit(
                    f"{src.path.name}: a global cannot currently store the invocation of bare slot {body}. "
                    "Bind a surrounding term instead; storing only its U class would lose the slot renaming."
                )
            _emit(out, keep, f"(let ${name} {src.encode(body)})")
            src.lang.bound[name] = src.term(body)
        elif head == "union":
            # Asserting an equation between two terms rather than deriving it. The
            # machinery takes it from there: a union between invocations with
            # different slots is what forces slots redundant and what records a
            # class's symmetries.
            _, a, b = form
            sort, _terms = src.common_sort((a, b), "union")
            _emit(out, keep, f"(union {src.encode(a, expected_sort=sort)} {src.encode(b, expected_sort=sort)})")
        elif head == "rewrite":
            _emit(out, keep, compile_rewrite(src, form))
            rules += 1
        elif head == "run":
            _emit(out, keep, schedule(int(form[1]), rules))
        elif head == "extract":
            # What is in the CLASS, printed as the encoding stores it: a node with its
            # edges' renamings spelled out. Reading it is how you see that a slot is
            # redundant, or which invocation a class settled on.
            #
            # Extracting the term's own value does not work. A slotted class spans
            # several egglog values -- one per invocation, related by `RenamesToLeader`
            # and NOT by egglog's union -- and the machinery deletes the non-canonical
            # ones, so a term whose class settled elsewhere has no node left to extract.
            # egglog's `extract` takes an expression while `RenamesToLeader` is a
            # relation, so a one-off function is what bridges them: set it to the
            # leader, run that one rule, extract the function.
            extracts += 1
            fn, rs = f"_leader{extracts}", f"_extract{extracts}"
            sort = src.sort_of_form(form[1])
            symbols = src.carriers[sort]
            # `:merge new` rather than no merge: a term reaches its leader by every
            # renaming in the orbit, so the rule fires once per row and sets the same
            # leader each time.
            _emit(out, keep, f"(function {fn} () {sort} :merge new)")
            _emit(out, keep, f"(ruleset {rs})")
            _emit(
                out,
                keep,
                f"(rule (({symbols.renames} {src.encode(form[1], expected_sort=sort)} _m _l)) "
                f"((set ({fn}) _l)) :ruleset {rs})",
            )
            _emit(out, keep, f"(run-schedule (saturate (run {rs})))")
            _emit(out, keep, f"(extract ({fn}))")
        elif head in ("check", "fail"):
            _emit(out, keep, compile_check(src, form))
        elif head in ("rule", "birewrite"):
            # `rewrite` is the only rule form here, and passing either of these through
            # is worse than rejecting it. At the slotted level neither can typecheck --
            # an encoded constructor takes a `Renaming` before each child, so `(F x y)`
            # is the wrong arity. Written at the ENCODED level one typechecks, passes
            # through, and then never fires: `rules` below counts only `rewrite`s, so
            # `(run N)` emits a schedule with no user-rule steps at all. Silence is the
            # worst of the three outcomes, so say it instead.
            advice = (
                "write the two directions as two `rewrite`s"
                if head == "birewrite"
                else "use `rewrite`, with `:when` for a side condition"
            )
            raise SystemExit(
                f"{src.path.name}: `{head}` is not part of the slotted language -- {advice}. "
                f"A `{head}` here would be passed through to egglog against the ENCODED "
                "tables and would not run."
            )
        elif head in ("run-schedule", "run-report"):
            raise SystemExit(
                f"{src.path.name}: `{head}` cannot pass through. A `(run N)` here compiles "
                "to a phased schedule -- the machinery saturated around each user-rule "
                "step -- so a schedule written by hand would run the user rules without "
                "it. Use `(run N)`."
            )
        else:
            # Everything else is egglog's, and means the same thing here: a command
            # that names no slotted term needs no compiling. `print-size`,
            # `print-function`, `query-extract`, `push`/`pop`, and whatever egglog
            # gains next all work without this file learning about them.
            _emit(out, keep, render(form))
    return "\n".join(out) + "\n"


def _emit(out, keep, text):
    if keep:
        out.append(text)


def schedule(steps, rules):
    """The phased schedule: the machinery saturated around each user-rule step.

    With no rules there is nothing to interleave, so one saturation is the whole run.
    """
    if not rules or steps == 0:
        return "(run-schedule (saturate (run slotted)))"
    return (
        f"(run-schedule (saturate (run slotted))\n              (repeat {steps} (seq (run) (saturate (run slotted)))))"
    )


KEYWORDS = (":name", ":when", ":ruleset", ":lead", ":fresh")

#: egglog's own `rewrite` options this language does not implement, and why. Named so the
#: refusal says what is missing rather than listing what is not.
EGGLOG_REWRITE_OPTIONS = {
    ":subsume": "subsumption has no meaning for a class the machinery keeps several "
    "values for, and the actions it belongs with -- `set`, `delete` -- are not here either",
}


def keywords(src, rest):
    """`:kw value...` pairs, where a keyword may take more than one value.

    `:fresh $k $v` is the reason this is not a walk in twos.
    """
    out = []
    while rest:
        kw = rest[0]
        if kw not in KEYWORDS:
            if kw in EGGLOG_REWRITE_OPTIONS:
                raise SystemExit(
                    f"{src.path.name}: `{kw}` is egglog's and is not implemented here -- {EGGLOG_REWRITE_OPTIONS[kw]}."
                )
            raise SystemExit(f"{src.path.name}: expected one of {KEYWORDS}, got {kw!r}")
        i = 1
        while i < len(rest) and rest[i] not in KEYWORDS:
            i += 1
        out.append((kw, rest[1:i]))
        rest = rest[i:]
    return out


def compile_rewrite(src, form, tail=")", bugs=frozenset(), **kw):
    """`(rewrite lhs rhs [:name n] [:when c] [:lead N] [:fresh $s...])`.

    `:lead` names the atom the query starts from, counting over the flattened pattern.
    It defaults to 0 -- the pattern's outermost node -- which is what every shipped
    generator pins, so a rule compiled here is the same text as the committed generated
    one. The answer may not depend on the lead, and a test can say another to check
    that: leading anywhere below the root makes the atoms above it come out
    child-before-parent, which is the fresh-root case.

    `:fresh` names the slots the right-hand side binds that the pattern never mentions,
    so the compiler mints them against everything the match already used.

    `tail` closes the rule and is where a ruleset and a name go, so it carries the
    closing paren -- the generated `sdql` file wants one, a compiled test does not.
    """
    parts = rewrite_parts(src, form)
    conds, fresh, lead = parts["conds"], parts["fresh"], parts["lead"]
    diseq, same = parts["diseq"], parts["same"]
    if parts["ruleset"] and ":ruleset" not in tail:
        tail = f" :ruleset {parts['ruleset']}" + tail
    lhs, rhs = parts["lhs"], parts["rhs"]
    if parts["name"] and ":name" not in tail:
        # egglog reports a rule by its `:name` and takes it as a string literal. It
        # panics on a name already live in the scope, so reuse is only legal once a
        # `(pop)` has removed the earlier rule. Skipped when the caller's tail already
        # names the rule -- `gen-sdql-rules.py` appends its own, and two `:name` options
        # on one rule is not valid egglog.
        tail = f' :name "{parts["name"]}"' + tail
    if uses_subst(rhs):
        # `slotted-subst` extracts a term and adds the result back, so it both reads
        # and writes tables: callable from the head of a `:naive` rule, not a seminaive
        # one.
        tail = " :naive" + tail
    # A pattern has to be a CALL. A bare variable on the left matches every class, so the
    # rule says nothing, and egglog rejects it too. Without this, `flatten` indexes
    # `lang[t[0]]` and on a string that is its first CHARACTER, so the failure was a
    # `KeyError` naming a letter.
    if not isinstance(lhs, list):
        raise SystemExit(
            f"{src.path.name}: a rewrite's left side must be a call, got {lhs!r} -- "
            "a bare variable there matches everything"
        )
    root, atoms = enc.flatten(src.lang, src.term(lhs, ground=False))
    # each `:when (= v <call>)` is another rooted pattern; `tmp` is per-equality so the
    # names `flatten` invents for nested sub-terms cannot collide between them
    for i, (var, pat) in enumerate(parts["equalities"]):
        _, extra = enc.flatten(src.lang, src.term(pat, ground=False), root=var, tmp=f"?_w{i}_")
        atoms += extra
    root_sort = src.lang[atoms[0][1]].sort
    foreign = next((src.lang[atom[1]].sort for atom in atoms if src.lang[atom[1]].sort != root_sort), None)
    if foreign is not None:
        raise SystemExit(
            f"{src.path.name}: a rule rooted in {root_sort} has a side pattern in {foreign}; "
            "cross-sort multipatterns are not supported"
        )
    order = enc.connected_order(src.lang, atoms, first=lead)
    return enc.compile_rule(
        src.lang,
        order,
        ("build", root, enc.rhs_of(src.lang, src.term(rhs, ground=False))),
        conds=conds,
        diseq=diseq,
        same=same,
        fresh=fresh,
        bugs=bugs,
        tail=tail,
        # a caller's own spellings -- `slot_prefix`, `fresh_batch` -- so a generator
        # that already committed its output can keep emitting the same text
        **kw,
    )


def uses_subst(form):
    """Whether a right-hand side calls the substitution primitive."""
    return isinstance(form, list) and (form[0] == enc.SUBST or any(uses_subst(a) for a in form))


def unquote(token):
    """A `"name"` token as its text. egglog spells a rule name as a string literal."""
    return token[1:-1] if len(token) >= 2 and token.startswith('"') and token.endswith('"') else token


def when_facts(src, vals):
    """The facts of one `:when` clause, in either spelling.

    egglog takes ONE argument and reads it as a LIST of facts:

        :when ((= a b) (not-free $x f))

    which is the spelling to write, since it is the one egglog accepts. A clause whose
    first element is itself a list is that form. A bare fact, `:when (= a b)`, is taken
    too -- egglog rejects it outright, so it is a convenience here and not a spelling
    this language documents.
    """
    if len(vals) == 1 and isinstance(vals[0], list) and (not vals[0] or isinstance(vals[0][0], list)):
        return vals[0]
    return vals


def rewrite_parts(src, form):
    """One `(rewrite ...)` broken out, so nothing parses these keywords twice.

    `xarray.py` needs the same pieces to build its own rule objects, and a second
    reading of `:when` is a second place for the two to disagree.
    """
    assert form[0] == "rewrite", form[:1]
    out = {
        "name": None,
        "lhs": form[1],
        "rhs": form[2],
        "conds": [],
        "equalities": [],
        "diseq": [],
        "same": [],
        "fresh": [],
        "ruleset": None,
        "lead": 0,
    }
    kws = keywords(src, form[3:])
    # egglog ASSIGNS `:when` rather than accumulating it, so of several clauses only the
    # LAST survives there while all of them constrain here. That is a difference in
    # meaning, not in spelling, so it is refused instead of silently disagreeing.
    if sum(1 for key, _ in kws if key == ":when") > 1:
        raise SystemExit(
            f"{src.path.name}: several `:when` clauses. egglog takes one, holding every fact "
            "in a list -- `:when ((= a b) (= c d))` -- and keeps only the last clause when "
            "given more, so this would not mean here what it means there. Use one list."
        )
    for key, vals in kws:
        if key == ":name":
            out["name"] = unquote(vals[0])
        elif key == ":ruleset":
            out["ruleset"] = vals[0]
        elif key == ":lead":
            out["lead"] = int(vals[0])
        elif key == ":fresh":
            out["fresh"] += list(vals)
        elif key == ":when":
            # EVERY fact in the clause. Reading only the first dropped the rest in
            # silence, leaving a rule that looked constrained and was not.
            for cond in when_facts(src, vals):
                want, *rest = cond
                if want in src.spec:
                    # A BARE CALL as a fact, which in egglog means "such a node exists".
                    # It is another pattern with nothing joining it to the rest, so it
                    # gets a root of its own.
                    out["equalities"].append((f"_fact{len(out['equalities'])}", cond))
                elif want == "=" and len(rest) == 2 and isinstance(rest[1], str):
                    # `(= x y)` between two VARIABLES identifies them: the same class
                    # reached by the same renaming, which is what `=` means here.
                    a, b = (v.lstrip("?") for v in rest)
                    out["same"].append((a, b))
                elif want == "=":
                    # NOT a side condition: another rooted pattern, which is how a
                    # rewrite says a multipattern. `(= v <call>)` means "v also matches
                    # this", so the pattern is flattened with `v` as its root and its
                    # atoms join the left-hand side's. Several of them give an arbitrary
                    # multipattern, and one may introduce variables the main pattern
                    # never mentions.
                    assert len(rest) == 2, f"{src.path.name}: `=` takes a variable and a pattern, got {rest}"
                    var, pat = rest
                    assert isinstance(var, str) and not var.startswith("$"), (
                        f"{src.path.name}: the left of a `:when =` must be a variable, got {var!r}"
                    )
                    assert isinstance(pat, list), (
                        f"{src.path.name}: the right of a `:when =` must be a call, got {pat!r} -- "
                        "a bare variable there would identify two variables, which this does not do yet"
                    )
                    out["equalities"].append((var.lstrip("?"), pat))
                elif want == "!=":
                    # egglog registers `!=` as a fact (`|a: #, b: #| -?> ()`), so a rule
                    # may say two things differ. Here it means NOT THE SAME INVOCATION,
                    # matching what `=` means in this language: the same class reached by
                    # the same renaming. Two invocations of one class differ.
                    assert len(rest) == 2, f"{src.path.name}: `!=` takes two variables, got {rest}"
                    a, b = rest
                    assert isinstance(a, str) and isinstance(b, str), (
                        f"{src.path.name}: `!=` compares two variables, got {rest}"
                    )
                    out["diseq"].append((a.lstrip("?"), b.lstrip("?")))
                else:
                    if want not in ("free", "not-free"):
                        raise SystemExit(
                            f"{src.path.name}: {want!r} is not a fact this language knows. "
                            "A fact is a call, `(= v <call>)`, `(= x y)`, `(!= x y)`, or "
                            "`free`/`not-free` on a slot. egglog's value primitives -- "
                            "arithmetic and comparison over payloads -- are not implemented."
                        )
                    slot, *pvars = rest
                    # A CALL is allowed where a variable is, and desugars to an equality
                    # plus a condition on the name it binds. That is what lets a condition
                    # be about the term the rule MATCHED: `(rewrite lhs rhs)` gives the
                    # matched root no name, and unlike a right-hand side a condition takes
                    # a variable rather than a term, so without this there was no way to
                    # say it at all. Writing the pattern again names the same class, by
                    # congruence on a ground match.
                    names = []
                    for v in pvars:
                        if isinstance(v, list):
                            fresh = f"_cond{len(out['equalities'])}"
                            out["equalities"].append((fresh, v))
                            names.append(fresh)
                        else:
                            names.append(v.lstrip("?"))
                    out["conds"].append((want == "free", slot, names))
    return out


def rule_name(src, form):
    """A rewrite's `:name`, or None."""
    return rewrite_parts(src, form)["name"]


def compile_check(src, form):
    """A claim about slotted classes, not about egglog values."""
    negated = form[0] == "fail"
    if negated:
        assert form[1][0] == "check", f"{src.path.name}: fail takes a check"
        form = form[1]
    claim = form[1]
    kind, args = claim[0], claim[1:]
    if kind in ("=", "!="):
        # ONE renaming, not two. `(RenamesToLeader f m l)` is `f = m*l`, so two terms
        # are equal when they are the same INVOCATION -- reached from the leader by the
        # same renaming -- and not merely when they land in the same class. The paper's
        # `fgh::transitive_symmetry` is the case that separates them: after
        # f($1,$2) = g($2,$1) and g($1,$2) = h($1,$2) the terms f($1,$2) and h($1,$2)
        # share a class but differ by the swap, so they are NOT equal, while f($1,$2)
        # and h($2,$1) are.
        sort, terms = src.common_sort(args)
        symbols = src.carriers[sort]
        atoms, maps = [], []
        for i, (x, t) in enumerate(zip(args, terms, strict=True)):
            m = f"_m{i}"
            if t[0] == "var":
                # A bare slot is not a node: it is the variable class under a renaming.
                # Its invocation is `(Var 0)`'s with that one slot sent to this one, so
                # WHICH slot it names lives in the composition rather than in the value.
                atoms.append(f"({symbols.renames} ({symbols.var} 0) {m} _l)")
                maps.append(f"(compose (map-of 0 {t[1]}) {m})")
            else:
                atoms.append(f"({symbols.renames} {src.encode(x, expected_sort=sort)} {m} _l)")
                maps.append(m)
        body = f"(check {' '.join(atoms)} (= {maps[0]} {maps[1]}))"
        if (kind == "!=") != negated:
            return f"(fail {body})"
        return body
    if kind in ("renaming-=", "renaming-!="):
        # Same CLASS, by SOME renaming -- strictly weaker than `=`, which pins the
        # renaming down. The pair it exists for is two terms that are alpha-variants
        # of each other with a free slot renamed: they are not equal, because no one
        # renaming reaches both, yet they are the same class.
        sort, _terms = src.common_sort(args)
        table = src.carriers[sort].renames
        a, b = (src.encode(x, expected_sort=sort) for x in args)
        body = f"(check ({table} {a} _m1 _l) ({table} {b} _m2 _l))"
        if (kind == "renaming-!=") != negated:
            return f"(fail {body})"
        return body
    if kind in ("holds", "not-holds"):
        # "this class contains an application of this operator", which is what a rule
        # having fired looks like when the built term is not worth writing out -- or,
        # negated, what a guard refusing looks like: nothing of that shape appeared.
        sort = src.sort_of_form(args[0])
        a = src.encode(args[0], expected_sort=sort)
        ctor = args[1]
        assert ctor in src.spec, f"{src.path.name}: unknown constructor {ctor!r}"
        if src.output_sorts[ctor] != sort:
            raise SystemExit(f"{src.path.name}: {ctor} contains {src.output_sorts[ctor]} nodes, not {sort} nodes")
        table = src.carriers[sort].renames
        ncols = sum(2 if c in enc.SLOTTED else 1 for c in src.spec[ctor])
        cols = " ".join(f"_c{i}" for i in range(ncols))
        body = f"(check ({table} {a} _m1 _l) ({table} _n _m2 _l) (= _n ({ctor}{' ' + cols if cols else ''})))"
        if (kind == "not-holds") != negated:
            return f"(fail {body})"
        return body
    if kind == "slots":
        sort = src.sort_of_form(args[0])
        a = src.encode(args[0], expected_sort=sort)
        table = src.carriers[sort].class_slots
        slots = " ".join(f"{s[1:]} {s[1:]}" for s in args[1:])
        body = f"(check (= ({table} {a}) (map-of {slots})))" if slots else f"(check (= ({table} {a}) (map-empty)))"
        return f"(fail {body})" if negated else body
    # Not one of the slotted claims, so it is an ordinary egglog check about the
    # encoding -- `(check (RenamesToLeader ...))` and the like. It names no slotted
    # term, so it goes through as written.
    #
    # `form` is the inner check by now, so a `(fail ...)` around it has to be put back.
    return f"(fail {render(form)})" if negated else render(form)


def tally(src):
    """What the program actually did, for the line printed after it runs.

    `ok` on its own only ever meant "egglog exited 0", which is a different claim for
    each kind of file: for one with claims it means they all held, and for a rule
    library -- constructors and rewrites, no terms and nothing asked -- it means the
    file loaded and NOTHING was checked. Saying which is which is the point.
    """
    n = {}
    for form, _ in src.body:
        head = form[0] if isinstance(form, list) else form
        n[head] = n.get(head, 0) + 1
    claims = n.get("check", 0) + n.get("fail", 0)
    parts = []
    # `rewrite` at the slotted level, `rule` at the encoded one -- both are rules.
    rules = n.get("rewrite", 0) + n.get("rule", 0)
    for count, word in (
        (n.get("let", 0), "term"),
        (n.get("union", 0), "union"),
        (rules, "rule"),
        (claims, "claim"),
    ):
        if count:
            parts.append(f"{count} {word}{'s' if count != 1 else ''}")
    if not claims:
        # The case worth spelling out: nothing was asked, so nothing was checked. Only
        # that -- who reads the file is not something this can see, and guessing it
        # ("included by other files") was wrong for `array.egg`, which nothing includes.
        library = rules and not n.get("let", 0)
        parts.append("nothing asked -- a language and its rules, not a test" if library else "nothing asked")
    return ", ".join(parts) if parts else "empty"


def main():
    ap = argparse.ArgumentParser(
        description="Run a program written in the slotted language.",
        epilog=(
            "Reads like egglog: `slotted-egglog.py prog.egg` runs it, and --desugar asks "
            "for the egglog program it compiles to instead of running it."
        ),
    )
    ap.add_argument("src", type=pathlib.Path, help="a program in the slotted language")
    ap.add_argument(
        "--desugar",
        action="store_true",
        help="write the compiled egglog program instead of running it",
    )
    ap.add_argument("-o", "--out", type=pathlib.Path, help="for --desugar: write here, not stdout")
    ap.add_argument(
        "--own-only",
        action="store_true",
        help="for --desugar: only the forms this file contributes, not its library's",
    )
    ap.add_argument(
        "--run",
        action="store_true",
        help="run it (the default; accepted so older invocations keep working)",
    )
    args = ap.parse_args()

    src = Source(args.src)
    text = compile_source(src)

    # Desugaring is asked for; running is what happens otherwise. `-o` and `--own-only`
    # imply it, since neither means anything for a run.
    desugar = args.desugar or args.out is not None or args.own_only
    if desugar:
        out = compile_source(src, own_only=args.own_only) if args.own_only else text
        if args.out:
            args.out.write_text(out)
        else:
            sys.stdout.write(out)
        return 0

    with tempfile.NamedTemporaryFile("w", suffix=".egg", delete=False) as f:
        f.write(text)
        path = f.name
    r = subprocess.run(
        [str(ROOT / "target" / "debug" / "egglog"), path], capture_output=True, text=True, cwd=ROOT, timeout=1800
    )
    if r.returncode != 0:
        err = [line for line in r.stderr.splitlines() if "ERROR" in line]
        print(f"FAIL {args.src.name}: {(err[-1] if err else r.stderr.strip())[:300]}")
        # kept only on failure, which is when there is something to read in it
        print(f"     compiled program kept at {path}")
        return 1
    pathlib.Path(path).unlink(missing_ok=True)
    if r.stdout.strip():
        # whatever the program itself asked for -- `extract`, `sizes`
        sys.stdout.write(r.stdout)
    print(f"ok   {args.src.name}   {tally(src)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
