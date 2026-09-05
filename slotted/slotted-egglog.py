#!/usr/bin/env python3
"""Compile a test written in the SLOTTED language down to plain egglog.

A slotted test declares its own constructors at the top and then talks about terms,
rules and classes -- never about renamings, edges or `(Var 0)`. This turns that into a
self-contained egglog program: the hand-written core, the machinery for exactly the
constructors declared, and the compiled body. The output includes no generated file,
so there is no build artifact on the path between a test and running it.

THE LANGUAGE

    (constructor Sum (U U U U) U :binder 1 2)   the language, inline. A `U` column is
                                                a slotted child; `:binder` names the
                                                child positions whose slot it binds.

    (let r (Sing Null Null))                    name a term
    (let a (Sum r $5 $6 Null))                  a `$n` in a binder column is the bound
                                                slot; in any other child column it is
                                                a variable occurrence

    (union a b)                                 assert an equation instead of deriving
                                                one -- how a class gets a symmetry, and
                                                how a slot becomes redundant

    (rewrite (Sum ?e1 $k $v (Sing $k $v)) ?e1)  a rule, in terms
    (rewrite lhs rhs :when (not-free $x ?f))    ... with a slot side condition

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

A check whose claim is none of the ones above is egglog's too, so a test can drop to
the encoded level -- `(check (RenamesToLeader a m l))` -- without leaving the language.

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

CORE_FILE = "slotted/encoding/egraph-encoding-11.egg"

TOKEN = re.compile(r'\(|\)|"[^"]*"|;[^\n]*|[^\s()]+')
SLOT = re.compile(r"\$\w+\Z")


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

    def __init__(self, ops):
        super().__init__(ops)
        self.bound = {}

    def slots(self, t):
        return self.slots(self.bound[t[1]]) if t[0] == "name" else super().slots(t)

    def enc(self, t):
        return f"${t[1]}" if t[0] == "name" else super().enc(t)


def payload(tok):
    """A payload argument as the encoder wants it: the value, not its egglog spelling.

    A source writes a string payload quoted, because that is what egglog syntax is, and
    `Op.split` quotes it again on the way out -- so the quotes come off here.
    """
    return tok[1:-1] if len(tok) >= 2 and tok.startswith('"') and tok.endswith('"') else tok


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
        self.body = []
        self.includes = []
        self._read(path)
        assert self.spec, f"{path.name}: no (constructor ...) declaration"
        self.lang = Terms({c: enc.Op(c, c, sig) for c, sig in self.spec.items()})

    def _read(self, path):
        """This file's declarations and body, with any included source read first.

        `(include "...")` in a slotted source names ANOTHER SLOTTED SOURCE, and pulls in
        its constructors and its rules -- so a test over the sdql rules says
        `(include "slotted/languages/sdql.egg")` instead of restating 43 of them. A slotted
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
                self.spec.update(enc.read_language_form(form))
            else:
                self.body.append((form, path))

    # ------------------------------------------------------------------ terms
    def term(self, form, column=enc.CHILD, ground=True):
        """A slotted term as the encoder's tuple form.

        A `$s` means different things in the two settings, and the difference is real
        rather than a spelling. In a GROUND term it is a particular slot -- an integer
        the encoding writes into a renaming -- and in a binder column it IS the bound
        slot, while anywhere else it is a variable occurrence. In a PATTERN it is a
        slot LITERAL, a name the match has to solve for, which the encoder takes as the
        `$s` string in either column.
        """
        if isinstance(form, str):
            if SLOT.match(form):
                if not ground:
                    return form
                slot = int(form[1:]) if form[1:].isdigit() else form[1:]
                return slot if column is enc.BINDER else ("var", slot)
            if form in self.spec:  # a nullary constructor, written bare
                return (form,)
            if form.startswith("?"):
                # a pattern variable. Its NAME is the identifier without the sigil,
                # which is the convention `flatten` keys atoms by and `pat_sexpr`
                # renders back with the `?`, so the reference side reads it too.
                return form[1:]
            assert form in self.lang.bound, f"{self.path.name}: {form!r} is not bound"
            return ("name", form)
        head, args = form[0], form[1:]
        if head == enc.SUBST:
            # Not a constructor: a call, and only legal on a right-hand side. Its
            # arguments are read like any others so that `?b` and `$x` mean here what
            # they mean everywhere else.
            return (head, *(self.term(a, ground=ground) for a in args))
        assert head in self.spec, f"{self.path.name}: unknown constructor {head!r}"
        kinds = self.lang[head].arg_kinds()
        assert len(args) == len(kinds), f"{self.path.name}: {head} takes {len(kinds)} arguments, given {len(args)}"
        return (
            head,
            *(self.term(a, k, ground) if k in enc.SLOTTED else payload(a) for a, k in zip(args, kinds, strict=True)),
        )

    def encode(self, form, column=enc.CHILD):
        """A ground term as the egglog expression for its value."""
        t = self.term(form, column)
        return "(Var 0)" if t[0] == "var" else self.lang.enc(t)


def compile_source(src, own_only=False):
    """The whole program, or -- for a snapshot -- only what this file contributes.

    `own_only` drops the machinery and anything an included library brought, because
    both are already snapshotted by the generator that emits them. What is left is the
    forms this test wrote, which is the part no other snapshot covers.
    """
    out = [
        f";;; COMPILED from {src.relpath} by slotted/slotted-egglog.py.",
        ";;;",
        ";;; A SNAPSHOT: committed so a change in the compiler shows up as a diff, never",
        ";;; edited by hand, and rewritten by `check-slotted.py --update`. This is what",
        ";;; running that test runs, and the only file it includes is the hand-written core.",
        "",
        f'(include "{CORE_FILE}")',
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
        out.append(enc.in_slotted_ruleset("\n".join(enc.emit(src.spec, provided=enc.CORE))))
        if any(uses_subst(rewrite_parts(src, f)["rhs"]) for f, _ in src.body
               if isinstance(f, list) and f and f[0] == "rewrite"):
            # The half a `subst` rule needs and does not carry itself: the
            # relation it writes into, and the one phase-two rule that reads it.
            out.append(enc.SUBST_MACHINERY)
    rules = 0
    extracts = 0
    for form, origin in src.body:
        head = form[0] if isinstance(form, list) else form
        mine = origin == src.path
        keep = mine or not own_only
        if head == "let":
            _, name, body = form
            _emit(out, keep, f"(let ${name} {src.encode(body)})")
            src.lang.bound[name] = src.term(body)
        elif head == "union":
            # Asserting an equation between two terms rather than deriving it. The
            # machinery takes it from there: a union between invocations with
            # different slots is what forces slots redundant and what records a
            # class's symmetries.
            _, a, b = form
            _emit(out, keep, f"(union {src.encode(a)} {src.encode(b)})")
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
            # `:merge new` rather than no merge: a term reaches its leader by every
            # renaming in the orbit, so the rule fires once per row and sets the same
            # leader each time.
            _emit(out, keep, f"(function {fn} () U :merge new)")
            _emit(out, keep, f"(ruleset {rs})")
            _emit(
                out,
                keep,
                f"(rule ((RenamesToLeader {src.encode(form[1])} _m _l))"
                f" ((set ({fn}) _l)) :ruleset {rs})",
            )
            _emit(out, keep, f"(run-schedule (saturate (run {rs})))")
            _emit(out, keep, f"(extract ({fn}))")
        elif head in ("check", "fail"):
            _emit(out, keep, compile_check(src, form))
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


KEYWORDS = (":name", ":when", ":lead", ":fresh")


def keywords(src, rest):
    """`:kw value...` pairs, where a keyword may take more than one value.

    `:fresh $k $v` is the reason this is not a walk in twos.
    """
    out = []
    while rest:
        kw = rest[0]
        if kw not in KEYWORDS:
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
    lhs, rhs = parts["lhs"], parts["rhs"]
    if uses_subst(rhs):
        # `slotted-subst` extracts a term and adds the result back, so it both reads
        # and writes tables: callable from the head of a `:naive` rule, not a seminaive
        # one.
        tail = " :naive" + tail
    root, atoms = enc.flatten(src.lang, src.term(lhs, ground=False))
    order = enc.connected_order(src.lang, atoms, first=lead)
    return enc.compile_rule(
        src.lang,
        order,
        ("build", root, enc.rhs_of(src.lang, src.term(rhs, ground=False))),
        conds=conds,
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


def rewrite_parts(src, form):
    """One `(rewrite ...)` broken out, so nothing parses these keywords twice.

    `xarray.py` needs the same pieces to build its own rule objects, and a second
    reading of `:when` is a second place for the two to disagree.
    """
    assert form[0] == "rewrite", form[:1]
    out = {"name": None, "lhs": form[1], "rhs": form[2], "conds": [], "fresh": [], "lead": 0}
    for key, vals in keywords(src, form[3:]):
        if key == ":name":
            out["name"] = vals[0]
        elif key == ":lead":
            out["lead"] = int(vals[0])
        elif key == ":fresh":
            out["fresh"] += list(vals)
        elif key == ":when":
            want, slot, *pvars = vals[0]
            assert want in ("free", "not-free"), f"unknown condition {want!r}"
            out["conds"].append((want == "free", slot, [v.lstrip("?") for v in pvars]))
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
        atoms, maps = [], []
        for i, x in enumerate(args):
            t = src.term(x, enc.CHILD)
            m = f"_m{i}"
            if t[0] == "var":
                # A bare slot is not a node: it is the variable class under a renaming.
                # Its invocation is `(Var 0)`'s with that one slot sent to this one, so
                # WHICH slot it names lives in the composition rather than in the value.
                atoms.append(f"(RenamesToLeader (Var 0) {m} _l)")
                maps.append(f"(compose (map-of 0 {t[1]}) {m})")
            else:
                atoms.append(f"(RenamesToLeader {src.encode(x)} {m} _l)")
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
        a, b = (src.encode(x) for x in args)
        body = f"(check (RenamesToLeader {a} _m1 _l) (RenamesToLeader {b} _m2 _l))"
        if (kind == "renaming-!=") != negated:
            return f"(fail {body})"
        return body
    if kind in ("holds", "not-holds"):
        # "this class contains an application of this operator", which is what a rule
        # having fired looks like when the built term is not worth writing out -- or,
        # negated, what a guard refusing looks like: nothing of that shape appeared.
        a = src.encode(args[0])
        ctor = args[1]
        assert ctor in src.spec, f"{src.path.name}: unknown constructor {ctor!r}"
        ncols = sum(2 if c in enc.SLOTTED else 1 for c in src.spec[ctor])
        cols = " ".join(f"_c{i}" for i in range(ncols))
        body = (
            f"(check (RenamesToLeader {a} _m1 _l) (RenamesToLeader _n _m2 _l)"
            f" (= _n ({ctor}{' ' + cols if cols else ''})))"
        )
        if (kind == "not-holds") != negated:
            return f"(fail {body})"
        return body
    if kind == "slots":
        a = src.encode(args[0])
        slots = " ".join(f"{s[1:]} {s[1:]}" for s in args[1:])
        body = (
            f"(check (= (ClassSlots {a}) (map-of {slots})))" if slots else f"(check (= (ClassSlots {a}) (map-empty)))"
        )
        return f"(fail {body})" if negated else body
    # Not one of the slotted claims, so it is an ordinary egglog check about the
    # encoding -- `(check (RenamesToLeader ...))` and the like. It names no slotted
    # term, so it goes through as written.
    #
    # `form` is the inner check by now, so a `(fail ...)` around it has to be put back:
    # dropping it turned a negative claim into the positive one, silently.
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
        # Whatever the program itself printed -- `extract`, `sizes`. It used to be
        # captured and dropped, so a file could ask for output and get none.
        sys.stdout.write(r.stdout)
    print(f"ok   {args.src.name}   {tally(src)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
