# The slotted language

What `slotted/slotted-egglog.py` accepts, and how it differs from egglog.

A file here is an egglog program with a few additions. Run one directly:

```
python3 slotted/slotted-egglog.py slotted/tests/paper/figure-3.egg
python3 slotted/slotted-egglog.py slotted/tests/paper/figure-3.egg --desugar   # see the egglog
```

The additions exist because a slotted term is not an egglog value. A term denotes a
class **together with** a renaming — an *invocation* — and egglog has no notion of
that. Everything below is either a way to write such a term, or a way to ask a question
about one. **Every other egglog command means what it always meant** and is passed
through untouched: `push`, `pop`, `print-size`, `print-function`, `query-extract`, and
whatever egglog gains next.

---

## Declaring a language

```
(constructor Lam (U U) U :binder 0)
(constructor Let (U U U) U :binder 1)
(constructor App (U U) U)
(constructor Num (i64) U)
```

A `U` column is a slotted child. Any other column is a payload and carries no slots.
`:binder` names the child positions whose slot the node binds, counting over the `U`
columns only — so `Lam` binds the slot in its first child, and `Let` binds the slot in
its second.

A binder covers the column *after* the one it binds, which is what wrapping a single
child in `Bind` means. So `Let`'s bound slot is stripped from its third column and not
from its first: `let x = x in f x` keeps the value's occurrence free.

There is no `(datatype …)`; a constructor is declared one per line, and the file needs
no include — the compiler emits the machinery for exactly the constructors declared.

## Writing terms

```
(let id (Lam $0 $0))                    ; lam $0. $0
(let k  (Lam $0 $3))                    ; lam $0. $3, which keeps $3 free
(let t  (App (Num 0) $7))
```

`$n` is a slot. In a binder column it **is** the bound slot; anywhere else it is an
occurrence of that slot. Writing `$0` twice in one term means the same slot twice.

## Asserting an equation

```
(union a b)
```

Egglog's `union` equates two values. This one equates two *terms*, which is a different
and stronger thing: it is how a class acquires a symmetry, and how a slot becomes
redundant. Unioning `f($0,$1)` with `f($1,$0)` gives that class the swap; unioning
`f($0,$1)` with `f($1,$2)` leaves the class with no slots at all, because it cannot
depend on any of them.

## Rules

```
(rewrite (Lam $x (App ?f $x)) ?f
         :name eta
         :when (not-free $x ?f))

(rewrite (Sum ?e1 $k $v (Sing $k $v)) ?e1)

(rewrite (Let ?t $x ?body) (subst ?body $x ?t) :name beta)
```

`?x` is a pattern variable standing for a subterm; `$x` is a slot literal the match
solves for. `:when (free $x ?f)` and `:when (not-free $x ?f)` are side conditions on
whether a slot is among a variable's free slots — the reference's
`subst[v].slots().contains(…)`.

`:fresh $s` names a slot the right-hand side binds that the pattern never mentions, so
the compiler mints one. `:name` names the rule.

`subst` is the one right-hand-side head that is not a constructor. `(subst ?body $x ?t)`
is `?body[(var $x) := ?t]` — the reference's `b[x := t]`. It is a *call*, so there is
nothing to build; `slotted/tests/sdql-beta.egg` explains what the compiler emits for it.

## Running

```
(run 3)
```

Three user-rule steps, with the machinery saturated around each. Saturating between
steps is not optional: the invariants have to hold before the next user rule looks at
the graph.

## Asking questions

Egglog's `check` asks about values. These ask about terms.

| claim | means |
| --- | --- |
| `(= a b)` | `a` and `b` are **equal** — the same term, once renamings are taken into account |
| `(!= a b)` | they are not |
| `(renaming-= a b)` | `a` and `b` are equal **modulo some renaming** — one e-class, but not necessarily at the same slots |
| `(renaming-!= a b)` | they are not |
| `(slots a $5 $6)` | `a`'s class depends on exactly these slots (`(slots a)` means none) |
| `(holds a Mult)` | `a`'s class contains a `Mult` node |
| `(not-holds a Mult)` | it does not |

All of them at once:

```slotted
(constructor Lam (U U) U :binder 0)
(constructor Mult (U U) U)
(constructor Null () U)

(let k (Lam $0 $3))              ; lam $0. $3 -- returns $3, ignores its argument
(let id (Lam $0 $0))             ; lam $0. $0
(let m (Mult $1 (Null)))
(run 0)

(check (slots k $3))             ; k depends on $3, and on nothing else
(check (slots id))               ; the identity depends on no slot: its own is bound
(check (holds m Mult))           ; m's class contains a Mult node
(check (not-holds k Mult))       ; k's class does not
(check (renaming-!= k m))        ; and they are not equal, under any renaming
```

### Why two kinds of equality

Because a term is a class *and* a renaming, and the two questions come apart. Take two
alpha-variants whose free slot is renamed:

```slotted
(constructor Lam (U U) U :binder 0)
(let p (Lam $0 $3))
(let q (Lam $0 $4))
(run 0)
(check (renaming-= p q))   ; equal modulo a renaming: both are "a constant function"
(check (!= p q))           ; but not equal: one returns $3, the other $4
```

Rename `$3` to `$4` and `p` becomes `q`, which is what `renaming-=` says. They are still
different terms.

The other direction matters too. `=` is not "syntactically identical" either — it is
equality modulo everything the e-graph already knows, including a class's symmetries.
If commutativity has put the swap in `f`'s group, then

```slotted
(constructor F (U U) U)
(rewrite (F ?x ?y) (F ?y ?x) :name comm)
(let a (F $1 $2))
(let b (F $2 $1))
(run 5)
(check (= a b))
```

holds, because by Def. 6 two invocations of a class agree when the renaming between
them lies in that group.

The case that pins the distinction down is the reference's own
`fgh::transitive_symmetry` — see `slotted/tests/paper/fgh-transitive-symmetry.egg`.
After `f($1,$2) = g($2,$1)` and `g($1,$2) = h($1,$2)`, the terms `f($1,$2)` and
`h($1,$2)` are in one class but differ by the swap, so they are `renaming-=` and
`!=`, while `f($1,$2)` and `h($2,$1)` are `=`.

### How they desugar

The difference is one line. Both ask for a common leader; only `=` also asks
that the two renamings agree.

```
(renaming-= p q)   (check (RenamesToLeader $p _m1 _l) (RenamesToLeader $q _m2 _l))

(= p q)            (check (RenamesToLeader $p _m0 _l) (RenamesToLeader $q _m1 _l)
                          (= _m0 _m1))
```

`(RenamesToLeader f m l)` is `f = m*l`. A class is a connected component of that
relation and its leader is the component's canonical member, so *sharing a leader* is
exactly *being in one e-class*. `renaming-=` says only that; `=` adds that one
renaming reaches both, which is what makes it equality of terms.

**A trap.** `renaming-=` between two bare slots is always true, because every variable is
one e-class:

```slotted
(constructor F (U U) U)
(let a (F $1 $2))                 ; something for the graph to hold
(run 0)
(check (renaming-= $3 $4))        ; holds -- both are the variable class
(check (!= $3 $4))                ; also holds -- they are different variables
```

Both desugar with the class `(Var 0)` on each side; `=` recovers *which* slot
by composing `{0 -> 3}` and `{0 -> 4}` onto the two renamings, and `renaming-=` has
nothing to compose onto. So `(renaming-= a $5)` does **not** say "a is the variable `$5`"
— it says only "a is a variable". Use `=` for that.

### What happened to egglog's `=`

A slotted file's `=` is the one above: it compiles to the shared-renaming check, not to
egglog's comparison of two stored values. That third notion is no longer reachable from
here, and nothing is lost by it.

For two **nodes** it was not a different question anyway. The machinery has a rule that
unions two values reaching their leader by the same renaming, up to a symmetry of the
class, so term equality already implied it — checked, with no explicit union in either
case:

```
(rewrite (F ?x ?y) (F ?y ?x) :name comm)
(let f12 (F $1 $2))
(let f21 (F $2 $1))
(let i0 (Lam $0 $0))
(let i5 (Lam $5 $5))
(run 5)
;; both hold, at the encoded level: the swap is in the group, and alpha-variants merge
```

For a **bare slot** it could not express the claim at all. A slot's identity lives in
the renaming, not in the value: `$9` and `$0` are the same value `(Var 0)` and different
terms, so `(= a $9)` has no stored-value spelling.

Both halves of that are checked in `slotted/encoding/value-equality.egg`, which runs at
the encoded level where both questions can be asked at once: alpha-variants and a
symmetry each end up as ONE egglog value, while two invocations of one class stay two.

A test that really is about the encoding's own tables belongs in `slotted/encoding/`,
which runs as plain egglog and can say whatever it likes.

### Dropping to the encoded level

A `check` whose claim is neither the slotted ones nor `=` is passed through to egglog,
so a test can ask about the encoding itself without leaving the language:

```
(check (RenamesToLeader a m l))
```

`(RenamesToLeader f m l)` is `f = m*l`, with `m` carrying `l`'s slots to `f`'s. That
relation is what `=` and `renaming-=` are defined in terms of: `=` asks
for **one** renaming reaching both terms from the leader, `renaming-=` lets each have its
own. Unlike `=`, it says plainly that it is dropping a level.

## Extraction and printing

`(extract a)` gives a term from `a`'s **class**, printed as the encoding stores it —
renamings spelled out:

```
(extract a)     (F (map-of 0 2) (Var 0) (map-of 0 1) (Var 0))
```

That is `f($2,$1)`. There is no pretty-printer back to slotted syntax yet.

It goes through the class's **leader**, and has to. A slotted class spans several egglog
values, related by `RenamesToLeader` rather than by egglog's union, and the machinery
deletes the non-canonical ones — so asking egglog to extract the term's own value fails
outright whenever the class settled on a different invocation:

```slotted
(constructor Lam (U U) U :binder 0)
(let p (Lam $0 $3))
(let q (Lam $0 $4))
(run 0)
(extract q)      ; used to be: extraction failure -- q's node was canonicalised away
```

Since egglog's `extract` takes an expression and `RenamesToLeader` is a relation, the
compiler declares a one-off function, lets one rule set it to the leader, runs that
rule, and extracts the function. The answer is therefore in the LEADER's frame, not
necessarily the frame of the term you asked about: `(extract q)` above prints
`lam $0. $3`.

## What `ok` tells you

A run reports what it did, because "ok" means different things for different files.
A file under `slotted/tests/` asks something; a file under `slotted/languages/` is a
language and its rules, so running it only says that it loaded:

```
ok   figure-3.egg   4 terms, 1 union, 3 claims
ok   array.egg   8 rules, nothing asked -- a rule library, included by other files
```

The second has no terms and no claims, so nothing was checked — it only loaded.

## Files

| path | what it is |
| --- | --- |
| `slotted/tests/` | programs in this language that ASK something: terms, and claims about them. Run by `slotted/run-slotted-tests.py` |
| `slotted/tests/paper/` | one file per test in the reference's own suites |
| `slotted/languages/` | a language and its rewrite rules, with no terms and nothing asked — `toy`, `array`, `sdql`, each an `.egg` beside a `.ref` saying how the reference spells its operators. Included by the tests that exercise them, and loaded on their own so a broken one is caught here |
| `slotted/encoding/` | the encoding itself, written by hand at the encoded level, plus the tutorial that explains it. `value-equality.egg` is where this file's claims about `=` are checked |
| `slotted/slotted-egglog.py` | the compiler; its module docstring is the short form of this file |
| `slotted-user-rules.md` | how a rule is compiled, and why each piece is there |
