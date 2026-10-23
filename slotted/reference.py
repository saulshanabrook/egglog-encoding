"""Fixture syntax, language metadata, and translation to the slotted reference.

These helpers describe test inputs and reference operator correspondences. The
Rust CLI owns encoding, execution, and logical graph export.
"""

import re
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHILD = object()
BINDER = object()
SLOTTED = (CHILD, BINDER)
SUBST = "subst"
TOKEN = re.compile(r'\(|\)|"(?:\\.|[^"\\])*"|;[^\n]*|[^\s()]+')
SLOT_LITERAL = re.compile(r"\$(?:[+-]?\d+|\w+)\Z")
KEYWORDS = (":name", ":when")


@dataclass(frozen=True)
class CarrierSymbols:
    """Generated constructor and relation names for one equality sort."""

    sort: str
    var: str
    renames: str
    equated: str
    free_vars: str
    subst_pending: str
    shape_equal: str
    invocation: str
    group: str
    group_replace: str
    coset_reps: str
    big_reading: str
    reading: str

    @classmethod
    def create(cls, sort, index):
        return cls(
            sort,
            f"SlottedVar_{index}",
            f"RenamesToLeader_{index}",
            f"Equated_{index}",
            f"FreeVars_{index}",
            f"SubstPending_{index}",
            f"ShapeEqual_{index}",
            f"Invocation_{index}",
            f"EclassGroup_{index}",
            f"GroupReplace_{index}",
            f"CosetReps_{index}",
            f"BigReading_{index}",
            f"Reading_{index}",
        )


def carrier_symbols(sorts):
    """The table names for one declared equality sort, in declaration order."""
    return {sort: CarrierSymbols.create(sort, i) for i, sort in enumerate(tuple(sorts))}


def read_language(path, sorts=("U",)):
    """Parse annotated constructor declarations."""
    language = {}
    for raw in path.read_text().splitlines():
        line = raw.split(";")[0].strip()
        if not line.startswith("(constructor "):
            continue
        head, _, rest = line[len("(constructor ") :].partition("(")
        cols_text, _, tail = rest.partition(")")
        name = head.strip()
        # `tail` is the output sort, then the options, then the closing paren
        tokens = tail.rstrip(")").split()
        opts = next((i for i, t in enumerate(tokens) if t.startswith(":")), len(tokens))
        language[name] = signature(cols_text.split(), constructor_options(name, tokens[opts:]), sorts, name)
    return language


def constructor_options(name, tokens):
    """Read the binder annotation in a fixture declaration."""
    if not tokens:
        return []
    if tokens[0] != ":binder":
        raise ValueError(f"{name}: reference fixture expects only :binder, got {tokens}")
    return [int(t) for t in tokens[1:]]


def signature(cols, binders, sorts=("U",), name="constructor"):
    """Columns and the binding child positions as the encoder's signature."""
    child_count = sum(col in sorts for col in cols)
    if len(set(binders)) != len(binders):
        raise SystemExit(f"constructor {name}: duplicate `:binder` position")
    if any(pos < 0 or pos >= child_count for pos in binders):
        raise SystemExit(f"constructor {name}: `:binder` position is outside its {child_count} child columns")
    if binders:
        lo, hi = min(binders), max(binders)
        if sorted(binders) != list(range(lo, hi + 1)):
            raise SystemExit(f"constructor {name}: `:binder` positions must be contiguous")
        if hi + 1 >= child_count:
            raise SystemExit(f"constructor {name}: `:binder` columns must be followed by the child they cover")

    sig, seen_kids = [], 0
    for col in cols:
        if col in sorts:
            sig.append(BINDER if seen_kids in binders else CHILD)
            seen_kids += 1
        else:
            sig.append(col)
    return sig


def read_typed_language_form(form, sorts=("U",)):
    """One constructor declaration with the sort information the generic recipe erases."""
    assert form[0] == "constructor" and isinstance(form[2], list), form
    name, cols, output = form[1], form[2], form[3]
    if output not in sorts:
        raise SystemExit(
            f"constructor {name}: output sort {output!r} is not one of the declared equality sorts ({', '.join(sorts)})"
        )
    sig = signature(cols, constructor_options(name, form[4:]), sorts, name)
    return name, sig, output, tuple(col for col in cols if col in sorts)


def read_correspondence(path):
    """Map egglog constructors to reference tags or bare payloads with a prefix."""
    out = {}
    for raw in path.read_text().splitlines():
        line = raw.split(";")[0].strip()
        if not line:
            continue
        ctor, ref, *rest = line.split()
        assert ctor not in out, f"{path.name}: duplicate constructor {ctor}"
        if ref == "=payload":
            assert len(rest) <= 1, f"{ctor}: one prefix at most, got {rest}"
            out[ctor] = (None, rest[0] if rest else "")
        else:
            assert not rest, f"{ctor}: a tag takes no further field, got {rest}"
            out[ctor] = (ref, "")
    return out


def language(spec, ref):
    """A `TermLang` from a language file and its correspondence file."""
    sigs = read_language(spec)
    corr = read_correspondence(ref)
    named = set(corr)
    assert named == set(sigs), (
        f"{spec.name} declares {sorted(set(sigs) - named)} that {ref.name} does not name, "
        f"and {ref.name} names {sorted(named - set(sigs))} that it does not declare"
    )
    ops = {ctor: Op(ctor, sigs[ctor], ref=tag, ref_prefix=prefix) for ctor, (tag, prefix) in corr.items()}
    return TermLang(ops)


def cols_of(sig):
    """Column names for a signature: payload vars, and (edge, child) per child."""
    payloads, edges, kids, order = [], [], [], []
    for _i, col in enumerate(sig):
        if col in SLOTTED:
            e, k = f"m{len(kids) + 1}", f"c{len(kids) + 1}"
            edges.append(e)
            kids.append(k)
            order.append((e, k))
        else:
            p = f"p{len(payloads) + 1}"
            payloads.append(p)
            order.append((p,))
    return payloads, edges, kids, order


def pattern(name, sig, edges=None, kids=None, payloads=None):
    """`(Name p1 m1 c1 ...)`, with any column list overridden."""
    dp, de, dk, order = cols_of(sig)
    payloads, edges, kids = payloads or dp, edges or de, kids or dk
    out, pi, ci = [], 0, 0
    for slot in order:
        if len(slot) == 2:
            out += [edges[ci], kids[ci]]
            ci += 1
        else:
            out.append(payloads[pi])
            pi += 1
    return f"({name} {' '.join(out)})"


def pay_text(op, pay):
    """A payload as the ORACLE spells it."""
    if isinstance(pay, tuple):
        if pay[0] == "ppv":
            raise SystemExit(
                f"{op.ctor}: the oracle cannot be asked about a payload VARIABLE "
                f"({pay[1]!r}); its patterns have no place for one."
            )
        pay = pay[1]
    return pay.strip('"')


class Op:
    """An egglog constructor's columns, binders, and reference spelling."""

    def __init__(
        self,
        ctor,
        sig=(),
        pays=None,
        ref=None,
        ref_prefix="",
        sort="U",
        kid_sorts=None,
    ):
        self.ctor = ctor
        self.sig = list(sig)
        self.sort = sort
        self.kid_sorts = list(kid_sorts) if kid_sorts is not None else [sort] * sum(c in SLOTTED for c in self.sig)
        assert len(self.kid_sorts) == sum(c in SLOTTED for c in self.sig), (
            f"{ctor}: {len(self.kid_sorts)} child sort(s) for {sum(c in SLOTTED for c in self.sig)} slotted column(s)"
        )
        npay = sum(1 for c in self.sig if c not in SLOTTED)
        self.pays = list(pays) if pays is not None else [None] * npay
        assert len(self.pays) == npay, f"{ctor}: {npay} payload column(s)"
        self.ref = ref
        self.ref_prefix = ref_prefix

    @property
    def kid_cols(self):
        """The slotted columns, in order."""
        return [c for c in self.sig if c in SLOTTED]

    @property
    def binders(self):
        """The child positions -- counted over children -- whose slot the node binds."""
        return [i for i, c in enumerate(self.kid_cols) if c is BINDER]

    @property
    def covered(self):
        """The one child column a binder scopes over: the next one along."""
        return max(self.binders) + 1 if self.binders else None

    def arg_kinds(self):
        """One entry per term argument: `CHILD`, `BINDER`, or the payload's sort."""
        out, pi = [], 0
        for col in self.sig:
            if col in SLOTTED:
                out.append(col)
            else:
                if self.pays[pi] is None:
                    out.append(col)
                pi += 1
        return out

    def split(self, args):
        """`(kids, pays)`: the arguments in slotted columns, and a literal per
        payload column -- the operator's own where it pins one, else the argument
        spelled for its sort."""
        kids, pays, ai, pi = [], [], 0, 0
        for col in self.sig:
            if col in SLOTTED:
                kids.append(args[ai])
                ai += 1
            else:
                lit = self.pays[pi]
                if lit is None:
                    a = args[ai]
                    # a pattern's payload arrives tagged and is spelled by the reference translator
                    lit = a if isinstance(a, tuple) else (f'"{a}"' if col == "String" else str(a))
                    ai += 1
                pays.append(lit)
                pi += 1
        assert ai == len(args), f"{self.ctor}: {len(args)} argument(s) for {ai} column(s)"
        return kids, pays


class TermLang:
    """Test terms keyed by egglog constructor name: `{constructor: Op}`."""

    VAR = "var"

    def __init__(self, ops, carriers=None):
        self.ops = dict(ops)
        declared = []
        for op in self.ops.values():
            for sort in (op.sort, *op.kid_sorts):
                if sort not in declared:
                    declared.append(sort)
        self.carriers = carriers or carrier_symbols(declared or ("U",))
        self.default_sort = next(iter(self.carriers))

    def __getitem__(self, name):
        return self.ops[name]

    def __contains__(self, name):
        return name in self.ops

    def symbols_for(self, sort):
        return self.carriers[sort]

    def sort_of(self, t, expected=None):
        """The equality sort of a term; a bare variable inherits its context."""
        if t[0] == self.VAR:
            return expected
        return self.ops[t[0]].sort

    @staticmethod
    def slot(arg):
        """A binder column's argument as a bare slot."""
        return arg[1] if isinstance(arg, tuple) else arg

    def slots(self, t):
        """The term's FREE slots."""
        if t[0] == self.VAR:
            return {t[1]}
        op = self.ops[t[0]]
        kids, _ = op.split(t[1:])
        bound = {self.slot(kids[i]) for i in op.binders}
        free = set()
        for i, k in enumerate(kids):
            if i in op.binders:
                continue
            s = self.slots(k)
            free |= (s - bound) if i == op.covered else s
        return free

    def refresh_shadowed_binders(self, t):
        """Give repeated binder columns the reference language's `Bind` meaning.

        `Sum(A, Bind<Bind<A>>)` and `Merge(A, A, Bind<Bind<Bind<A>>>)` are
        lexically nested binders even though the encoding flattens their names into
        sibling columns.  If two layers use the same source name, the innermost one
        shadows the outer one.  Leaving both columns equal instead identifies two
        private slots and produces a different e-node.  Alpha-refresh only the
        shadowed OUTER column; occurrences in the covered body continue to name the
        innermost binder.

        Fresh names avoid every slot written anywhere in this term, including
        uncovered columns.  Running this over the whole tree before recursive
        encoding also avoids colliding with an enclosing binder.
        """

        def all_slots(x):
            if isinstance(x, str):
                return {x} if x.startswith("$") else set()
            if x[0] == self.VAR:
                return {x[1]}
            if x[0] not in self.ops:  # a front-end's opaque, already-bound name
                return set()
            op = self.ops[x[0]]
            out = set()
            for kind, arg in zip(op.arg_kinds(), x[1:], strict=True):
                if kind is BINDER:
                    out.add(self.slot(arg))
                elif kind is CHILD:
                    out |= all_slots(arg)
            return out

        used = all_slots(t)
        pattern_slots = any(isinstance(s, str) and s.startswith("$") for s in used)
        fresh_index = [0]

        def fresh():
            if pattern_slots:
                while True:
                    s = f"$__shadow{fresh_index[0]}"
                    fresh_index[0] += 1
                    if s not in used:
                        used.add(s)
                        return s
            s = 0
            while s in used:
                s += 1
            used.add(s)
            return s

        def go(x):
            if isinstance(x, str):
                return x
            if x[0] == self.VAR or x[0] not in self.ops:
                return x
            op = self.ops[x[0]]
            args = [
                go(a) if kind is CHILD and isinstance(a, tuple) else a
                for kind, a in zip(op.arg_kinds(), x[1:], strict=True)
            ]
            kids, _pays = op.split(args)
            seen = set()
            for i in reversed(op.binders):
                name = self.slot(kids[i])
                if name in seen:
                    # `args` and child positions differ when fixed payload columns are
                    # present; find this child column in the argument walk.
                    child_index = -1
                    for ai, kind in enumerate(op.arg_kinds()):
                        if kind in SLOTTED:
                            child_index += 1
                            if child_index == i:
                                args[ai] = fresh()
                                break
                else:
                    seen.add(name)
            return (x[0], *args)

        return go(t)

    def sexpr(self, t):
        """Reference / oracle syntax."""
        if t[0] == self.VAR:
            return f"(var ${t[1]})"
        op = self.ops[t[0]]
        kids, pays = op.split(t[1:])
        if op.ref is None:
            # a payload leaf, written as its payload
            return op.ref_prefix + pay_text(op, pays[0])
        assert not (kids and None in op.pays), f"{op.ctor}: no oracle syntax for a payload argument beside a child"
        parts = [f"${self.slot(k)}" if i in op.binders else self.sexpr(k) for i, k in enumerate(kids)]
        return f"({op.ref} {' '.join(parts)})" if parts else op.ref

    def shift(self, t, k):
        """Add `k` to every slot in a term. Slot names carry no meaning, so no answer
        may change."""
        if t[0] == self.VAR:
            return (t[0], t[1] + k)
        out = []
        for kind, a in zip(self.ops[t[0]].arg_kinds(), t[1:], strict=True):
            if kind is CHILD:
                out.append(self.shift(a, k))
            elif kind is BINDER:
                out.append(self.shift(a, k) if isinstance(a, tuple) else a + k)
            else:
                out.append(a)
        return (t[0], *out)


def slot_literals(t, out=None):
    """Every slot literal a term mentions, as the `$x` strings a pattern writes."""
    out = set() if out is None else out
    if isinstance(t, tuple):
        if len(t) == 2 and t[0] == "sl":
            out.add(t[1])
        else:
            for a in t:
                slot_literals(a, out)
    return out


def _binder_scopes(lang, t, under=frozenset(), out=None):
    """For each pattern variable, the binder slots each of its occurrences sits under."""
    out = {} if out is None else out
    if not isinstance(t, tuple) or len(t) < 2 or t[0] == "sl":
        return out
    if t[0] == "pv":
        out.setdefault(t[1], []).append(frozenset(under))
        return out
    if t[0] == SUBST:
        for a in t[1:]:
            _binder_scopes(lang, a, under, out)
        return out
    op = lang[t[0]]
    kids, _pays = op.split(t[1:])
    bound = frozenset(kids[i][1] for i in op.binders if isinstance(kids[i], tuple) and kids[i][0] == "sl")
    for i, k in enumerate(kids):
        _binder_scopes(lang, k, under | bound if i == op.covered else under, out)
    return out


def capture_guards(lang, lhs, rhs):
    """The `(not-free $b v)` guards a rule owes, as `($b, v)` pairs.

    A matched binder's bound slot may be read as any name -- the name of one of the
    term's free variables included, which is a fine alpha-variant of the term. That is
    the matcher's semantics here and in the reference's `MultiPattern`, and a language
    may want it (a bound variable identified with a free one, as `bound-aliasing`
    does). It puts one duty on a rule: where its right-hand side rebinds a slot `$b`
    over a variable `v` that the left-hand side did NOT match under `$b`, the reading
    with `$b` as `v`'s free variable builds a node that captures `v`. `let-lam-diff`
    reading `let x = y in (λw. x w)` with `w` as `y` builds `λy. let x = y in x y`. So
    such a rule has to say `(not-free $b v)`, and this is the list of those it owes.
    Under the reference's nested matcher the guards are vacuous, its bound slots
    staying injective, so a reference rule set can lack them and still be faithful.

    A slot the right-hand side alone binds is minted fresh and owes nothing.
    """
    if not isinstance(rhs, tuple) or rhs[0] in ("pv", "sl", SUBST):
        return set()
    seen_in_lhs = slot_literals(lhs)
    on_left, on_right = _binder_scopes(lang, lhs), _binder_scopes(lang, rhs)
    owed = set()
    for v, occurrences in on_right.items():
        left = on_left.get(v)
        if not left:
            continue
        for under in occurrences:
            for b in under:
                if b in seen_in_lhs and all(b not in o for o in left):
                    owed.add((b, v))
    return owed


def missing_capture_guards(lang, lhs, rhs, conds):
    """The owed guards a rule does not state."""
    stated = {(slot, v) for want, slot, pvars in conds if not want for v in pvars}
    return capture_guards(lang, lhs, rhs) - stated


def has_pay_var(t):
    """Does this sub-term bind a payload VARIABLE anywhere?"""
    if not isinstance(t, tuple):
        return False
    if len(t) == 2 and t[0] == "ppv":
        return True
    return any(has_pay_var(a) for a in t)


def plain_pays(t):
    """This sub-term with its payload literals untagged, for the ground spellers."""
    if not isinstance(t, tuple):
        return t
    if len(t) == 2 and t[0] == "plit":
        return t[1]
    if len(t) == 2 and t[0] in ("pv", "sl", "cls", "var", "name"):
        return t
    return tuple(plain_pays(a) for a in t)


class PatternNames:
    """Fresh pattern names that do not collide with source names."""

    def __init__(self, form):
        self.used = set()

        def reserve(value):
            if isinstance(value, str):
                self.used.add(value)
            elif isinstance(value, (list, tuple)):
                for child in value:
                    reserve(child)

        reserve(form)

    def fresh(self, stem):
        name, suffix = stem, 0
        while name in self.used:
            suffix += 1
            name = f"{stem}_{suffix}"
        self.used.add(name)
        return name


def flatten(lang, term, root=None, tmp="_t", *, names=None):
    """A nested pattern as depth-1 atoms, pre-order, so every atom's root is a child
    of an earlier one -- which is the connectivity the recipe requires."""
    term = lang.refresh_shadowed_binders(term)
    names = names or PatternNames(term)
    if root is None:
        root = names.fresh("_p")
    else:
        names.used.add(root)
    atoms, ctr = [], [0]

    def go(t, name):
        kids, nested = [], []
        cs, pays = lang[t[0]].split(t[1:])
        for c in cs:
            if isinstance(c, str):
                kids.append(("sl", c) if c.startswith("$") else ("pv", c))
            elif not lang[c[0]].kid_cols and not has_pay_var(c):
                kids.append(("cls", plain_pays(c)))
            else:
                ctr[0] += 1
                nm = names.fresh(f"{tmp}{ctr[0]}")
                kids.append(("pv", nm))
                nested.append((c, nm))
        atoms.append((name, t[0], kids, pays))
        for c, nm in nested:
            go(c, nm)

    go(term, root)
    return root, atoms


def rhs_of(lang, t):
    """A plain nested term as a right-hand side in the grammar above: a bare string
    is a pattern variable unless it starts with `$`, and a payload argument is left
    alone."""
    t = lang.refresh_shadowed_binders(t)
    if isinstance(t, str):
        return ("sl", t) if t.startswith("$") else ("pv", t)
    if t[0] == SUBST:
        assert len(t) == 4, f"{SUBST} takes a body, a slot and a term: {t}"
        return (SUBST, *(rhs_of(lang, a) for a in t[1:]))
    out = [rhs_of(lang, a) if kind in SLOTTED else a for kind, a in zip(lang[t[0]].arg_kinds(), t[1:], strict=True)]
    return (t[0], *out)


def atom_lines(lang, root, atoms, var="var", *, names=None):
    """A flattened pattern as the oracle's `MultiPattern` atom lines.

    `(root_name, lines)`, preserving source variable names. The reference protocol
    adds its own `?` prefix. An atom's children are pattern variables and slot literals, so:

      * a slot literal in a BINDER column is the bare `$x` that `Bind` holds; a pattern
        variable there is refused by the compiler, and is an error here;
      * anywhere else it is the TERM `(var $x)`, which needs an atom of its own, since
        an atom's child has to be a pattern variable;
      * a child reached through its own class -- a payload leaf written literally --
        gets an ATOM OF ITS OWN, since it cannot sit in a child position either, and the
        child refers to that; its payload is marked `#` so it stays a payload.

    Asking the reference the flattened question makes the comparison like-for-like:
    the encoding implements `MultiPattern`, not the reference's distinct nested
    pattern language.
    """
    out, extra = [], [0]
    for name, op, kids, *_pays in atoms:
        binders = set(lang[op].binders)
        spelled = []
        for i, (kind, c) in enumerate(kids):
            if kind == "pv" and i in binders:
                raise SystemExit(f"a pattern variable ({c}) cannot stand in {op}'s binder column")
            if kind == "pv" or (kind == "sl" and i in binders):
                spelled.append(c)
            elif kind == "sl":
                extra[0] += 1
                v = names.fresh(f"_sl{extra[0]}") if names else f"_sl{extra[0]}"
                out.append(f"atom {v} {var} {c}")
                spelled.append(v)
            else:
                # a leaf reached through its own class. It cannot sit in a child position
                # either -- an atom's child has to be a pattern variable -- so it gets an
                # atom of its own and the child refers to that. Its payload is marked `#`
                # so it stays a payload rather than becoming a variable.
                extra[0] += 1
                v = names.fresh(f"_cl{extra[0]}") if names else f"_cl{extra[0]}"
                leaf = lang.sexpr(c)
                if leaf.startswith("("):
                    head, *pays = leaf[1:-1].split()
                    out.append(f"atom {v} {head} " + " ".join(f"#{x}" for x in pays))
                else:
                    out.append(f"atom {v} {leaf}")
                spelled.append(v)
        out.append(f"atom {name} {lang[op].ref or op} {' '.join(spelled)}")
    return root, out


def pat_sexpr(lang, t, binder=False):
    """A pattern term -- an atom's child, or a right-hand side -- in the oracle's
    syntax."""
    if t[0] == "pv":
        return f"?{t[1]}"
    if t[0] == "sl":
        return t[1] if binder else f"(var {t[1]})"
    if t[0] == "cls":
        return lang.sexpr(t[1])
    if t[0] == SUBST:
        # The reference's own spelling of a substitution, `b[x := t]`, which its
        # `Pattern::parse` accepts on a right-hand side (`src/rewrite/pattern.rs`).
        # Not a constructor, so `lang[...]` below would not find it.
        b, sl, tt = t[1:]
        return f"{pat_sexpr(lang, b)}[(var {sl[1]}) := {pat_sexpr(lang, tt)}]"
    op = lang[t[0]]
    kids, pays = op.split(t[1:])
    if op.ref is None:
        # a payload leaf, written as its payload -- with the prefix the oracle needs to
        # read it as a payload rather than a tag, exactly as `TermLang.sexpr` does for
        # a ground term. The two renderers have to agree: one writes a rule's pattern
        # and the other the terms that rule has to match.
        return op.ref_prefix + pay_text(op, pays[0])
    assert not (kids and None in op.pays), f"{op.ctor}: no oracle syntax for a payload argument beside a child"
    parts = [pat_sexpr(lang, k, binder=(i in op.binders)) for i, k in enumerate(kids)]
    return f"({op.ref} {' '.join(parts)})" if parts else op.ref


class Slots:
    """Stable ground-slot identities, separate from globals and pattern slots."""

    def __init__(self):
        self.names = {}
        self.sources = {}
        self.used = set()
        self.next = -(1 << 63)

    def intern(self, source):
        if not SLOT_LITERAL.fullmatch(source):
            raise SystemExit(f"expected a slot literal, got {source!r}")
        name = source[1:]
        number = int(name) if re.fullmatch(r"[+-]?[0-9]+", name) else None
        if number is not None and not -(1 << 63) <= number < 1 << 63:
            raise SystemExit(f"slot {source} is outside the signed 64-bit range")
        key = str(number) if number is not None else name
        if key not in self.names:
            if number is not None and number not in self.used:
                slot = number
            else:
                while self.next in self.used:
                    self.next += 1
                slot = self.next
            self.names[key] = slot
            self.sources[slot] = f"${key}"
            self.used.add(slot)
        return self.names[key]


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


class Terms(TermLang):
    """The test's language, plus the names its `let`s bind."""

    def __init__(self, ops, carriers=None):
        super().__init__(ops, carriers)
        self.bound = {}

    def slots(self, t):
        return self.slots(self.bound[t[1]]) if t[0] == "name" else super().slots(t)

    def sort_of(self, t, expected=None):
        return self.sort_of(self.bound[t[1]], expected) if t[0] == "name" else super().sort_of(t, expected)


def payload(tok, ground=True):
    """A payload argument -- a node argument carrying no slots, which is the reference's
    own word for it (`lang.rs`: "payload types that are independent of Slots")."""
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

    def __init__(self, path, *, text=None):
        self.path = path
        self.slots = Slots()
        self.spec, self.output_sorts, self.child_sorts = {}, {}, {}
        self.body, self.sorts, self._ctors, self.includes = [], [], [], []
        self._read(path, text=text)
        self.carriers = carrier_symbols(self.sorts)
        for form in self._ctors:
            name, sig, output, children = read_typed_language_form(form, self.sorts)
            self.spec[name] = sig
            self.output_sorts[name] = output
            self.child_sorts[name] = children
        self.lang = Terms(
            {c: Op(c, sig, sort=self.output_sorts[c], kid_sorts=self.child_sorts[c]) for c, sig in self.spec.items()},
            self.carriers,
        )

    def _read(self, path, *, text=None):
        """This file's declarations and body, with any included source read first."""
        for form in parse(path.read_text() if text is None else text):
            if isinstance(form, list) and form and form[0] == "include":
                inc = ROOT / form[1].strip('"')
                assert inc.exists(), f"{path.name}: no such file {form[1]}"
                assert "target/" not in inc.as_posix(), (
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
        """A `(datatype Name (Ctor <sort>*) ...)` as one `constructor` form per variant."""
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

    # ------------------------------------------------------------------ terms
    def global_ref(self, name, ground):
        """A `let`-bound global, as a ground reference or as something a pattern can match."""
        return (
            ("name", name) if ground else as_pattern(self.lang, self.lang.bound[name], self.slots.sources.__getitem__)
        )

    def term(self, form, column=CHILD, ground=True):
        """Read a fixture term for reference translation, without lowering it."""
        if isinstance(form, str):
            if SLOT_LITERAL.fullmatch(form):
                if not ground:
                    return form
                slot = self.slots.intern(form)
                return slot if column is BINDER else ("var", slot)
            if form in self.lang.bound:
                return self.global_ref(form, ground)
            if not ground:
                return form
            raise ValueError(f"{self.path.name}: unbound fixture term {form!r}")
        head, *args = form
        if head == SUBST:
            return (head, *(self.term(a, ground=ground) for a in args))
        op = self.lang[head]
        return (
            head,
            *(
                self.term(arg, kind, ground) if kind in SLOTTED else payload(arg, ground)
                for arg, kind in zip(args, op.arg_kinds(), strict=True)
            ),
        )


def keywords(src, rest):
    """`:kw value...` pairs, where a keyword may take more than one value."""
    out = []
    while rest:
        kw = rest[0]
        if kw not in KEYWORDS:
            raise SystemExit(f"{src.path.name}: expected one of {KEYWORDS}, got {kw!r}")
        i = 1
        while i < len(rest) and not (isinstance(rest[i], str) and rest[i].startswith(":")):
            i += 1
        out.append((kw, rest[1:i]))
        rest = rest[i:]
    return out


def unquote(token):
    """A `"name"` token as its text. egglog spells a rule name as a string literal."""
    return token[1:-1] if len(token) >= 2 and token.startswith('"') and token.endswith('"') else token


def rewrite_parts(src, form):
    """Read a fixture rewrite for translation to the reference's pattern language."""
    assert form[0] == "rewrite", form
    names = PatternNames(form)
    out = dict(names=names, name=None, lhs=form[1], rhs=form[2], conds=[], equalities=[], diseq=[], same=[])
    for key, vals in keywords(src, form[3:]):
        if key == ":name":
            out["name"] = unquote(vals[0])
        elif key == ":when":
            for cond in vals[0]:
                want, *rest = cond
                if want in src.spec:
                    out["equalities"].append((names.fresh("_fact"), cond))
                elif want in ("=", "!=") and isinstance(rest[1], str):
                    out["same" if want == "=" else "diseq"].append(tuple(rest))
                elif want == "=":
                    out["equalities"].append((rest[0], rest[1]))
                elif want in ("free", "not-free"):
                    slot, *pvars = rest
                    variables = []
                    for v in pvars:
                        if isinstance(v, list):
                            fresh = names.fresh("_cond")
                            out["equalities"].append((fresh, v))
                            variables.append(fresh)
                        else:
                            variables.append(v)
                    out["conds"].append((want == "free", slot, variables))
                else:
                    raise ValueError(f"unsupported reference condition: {cond}")
    return out


def rule_name(src, form):
    """A rewrite's `:name`, or None."""
    return rewrite_parts(src, form)["name"]


class NestedPatternUnsupported(ValueError):
    """A source rule needs multiple patterns, which ref-nested cannot express."""


def rule_atoms(src, lang, parts):
    """Flatten a rewrite's multipattern using one fresh-name supply."""
    lhs = src.term(parts["lhs"], ground=False)
    names = parts["names"]
    if isinstance(lhs, str):
        if lhs.startswith("$"):
            raise ValueError("reference rewrite root must be a constructor or a pattern variable")
        root, atoms = lhs, []
    else:
        root, atoms = flatten(lang, lhs, names=names)
    for name, pattern in parts["equalities"]:
        _, extra = flatten(lang, src.term(pattern, ground=False), root=name, names=names)
        atoms.extend(extra)
    bound = {a[0] for a in atoms}
    bound.update(child for _, _, kids, _ in atoms for kind, child in kids if kind == "pv")
    if root not in bound:
        raise ValueError("reference rewrite root must be bound by a constructor pattern")
    return root, atoms


def rule_lines(src, lang, form, *, nested=False):
    """Translate one source rewrite, including its multipattern, to oracle spec lines.

    Reject conditions the oracle protocol cannot express instead of comparing a
    weaker rule. All atoms share a fresh-name supply, including literal leaves.
    """
    parts = rewrite_parts(src, form)
    if parts["same"] or parts["diseq"]:
        raise ValueError(f"{src.path.name}: unsupported reference rewrite options: {render(form)}")
    lhs = src.term(parts["lhs"], ground=False)
    rhs = pat_sexpr(lang, rhs_of(lang, src.term(parts["rhs"], ground=False)))
    if nested:
        if parts["equalities"] or isinstance(lhs, str):
            raise NestedPatternUnsupported("requires a single nested pattern; found multipattern :when conditions")
        out = ["rule", f"nested {pat_sexpr(lang, rhs_of(lang, lhs))}", f"rhs root {rhs}"]
    else:
        root, atoms = rule_atoms(src, lang, parts)
        root, text = atom_lines(lang, root, atoms, names=parts["names"])
        out = ["rule", *text, f"rhs {root} {rhs}"]
    for want, slot, pvars in parts["conds"]:
        out.append(f"cond {'in' if want else 'notin'} {slot} {' '.join(pvars)}")
    return out


def as_pattern(lang, t, slot_name=lambda n: f"${n}"):
    """A term read as GROUND, written the way a pattern writes it."""
    if isinstance(t, str):
        return t
    if t[0] == "name":
        return as_pattern(lang, lang.bound[t[1]], slot_name)
    if t[0] == lang.VAR:
        return slot_name(t[1])
    op = lang[t[0]]
    out = []
    for kind, a in zip(op.arg_kinds(), t[1:], strict=True):
        if kind is BINDER:
            out.append(a if isinstance(a, str) else slot_name(lang.slot(a)))
        elif kind is CHILD:
            out.append(as_pattern(lang, a, slot_name))
        else:
            out.append(a)
    return (t[0], *out)
