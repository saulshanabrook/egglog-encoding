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
(datatype U
  (Lam U U :binder 0)
  (Let U U U :binder 1)
  (App U U)
  (Num i64))
```

or the same thing the long way, which egglog also accepts:

```
(sort U)
(constructor Lam (U U) U :binder 0)
(constructor Let (U U U) U :binder 1)
(constructor App (U U) U)
(constructor Num (i64) U)
```

Every equality sort a program declares is a **carrier**: a column in a carrier is a
slotted child. Programs may have several independent carriers, either as separate
`sort`/`constructor` declarations or as a `datatype*`:

```
(datatype*
  (Expr (EVar Expr) (ELam Expr Expr :binder 0))
  (Type (TVar Type) (TForall Type Type :binder 0)))
```

Each carrier gets its own variable constructor and its own
`RenamesToLeader_N`, `Equated_N`, `ClassSlots_N`, and `SubstPending_N` tables;
`Renaming`, `Namings`, `Idx`, layout metadata, and the `slotted` schedule are shared.
The suffix is the carrier's zero-based declaration order. A one-carrier program keeps
the historical unsuffixed table names and encoding behavior.

For now every constructor is homogeneous: all its slotted children must have the same
carrier as its result. Thus `(constructor App (Expr Expr) Expr)` is supported, while
`(constructor Ann (Expr Type) Expr)` is rejected explicitly. Cross-carrier edges require
child-sort-specific canonicalisation and substitution and are future work; treating the
`Type` column as an inert payload would be unsound.

A rewrite and all of its `:when` patterns likewise stay in one carrier, and `union` and
the slotted equality checks require both terms to have the same carrier. Globals retain
the carrier of the term bound to them. These mistakes are diagnosed by the source
compiler rather than left to erased generated `Id` columns.

Any other supported base column — currently `i64` or `String` — is a payload and
carries no slots. Container-valued constructor columns are outside this front end's
current contract. In particular, `subst` rejects an erased runtime `Id` column that the
generated layout has not identified as a slotted edge rather than guessing whether it
is a container. A top-level bare slot in a multi-carrier program is also rejected when
there is no constructor context from which to infer its carrier.

`:binder` names the child positions whose slot the node binds, counting over the
carrier columns only — so `Lam` binds the slot in its first child and `Let` in its
second. It may stand anywhere among a declaration's options, and on a `datatype`
variant it goes after the columns, where egglog puts a variant's options.

A binder covers the column *after* the one it binds, which is what wrapping a single
child in `Bind` means. So `Let`'s bound slot is stripped from its third column and not
from its first: `let x = x in f x` keeps the value's occurrence free.

Several binder columns represent nested `Bind` layers around that one covered child,
so they must be distinct, contiguous child positions immediately before it. Duplicate,
negative, out-of-range, or non-contiguous `:binder` indices are rejected rather than
given an accidental scope.

egglog's own declaration options — `:cost`, `:unextractable`,
`:internal-term-constructor` — are refused rather than ignored: extraction here would
not honour them.

No include is needed either way; the compiler emits the machinery for exactly the
constructors declared.

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
(rewrite (Lam $x (App f $x)) f
         :name "eta"
         :when ((not-free $x f)))

(rewrite (Sum e1 $k $v (Sing $k $v)) e1)

(rewrite (Let t $x body) (subst body $x t) :name "beta")
```

A **pattern variable** stands for a subterm and may be written bare, `x`, which is
egglog's spelling, or with a sigil, `?x`, which is egg's. They name the same variable, so
one rule may mix them. A bare name that is a `let`-bound global means that global, and a
bare name that is a constructor is a call — so a paren-less `Null` stays `(Null)` rather
than becoming a variable that matches everything. `$x` is a slot literal the match solves
for.

There is one known lowering limitation for explicit slot occurrences. `MultiPattern`
has one rule-global slot namespace, while the source syntax determines which binder
declaration covers each occurrence. Thus the three printed `$x`s in
`(Let $x $x $x)` mean “a free initializer slot, a new binder, and that binder's body
occurrence,” not one global slot. The compiler currently preserves the spelling and
can miss that match. Spelling the roles distinctly, `(Let $free $bound $bound)`, is the
scope-preserving form; [issue #81](https://github.com/saulshanabrook/egglog-encoding/issues/81)
tracks making the compiler do that internally while still projecting matches back to
the names guards and right-hand sides use. This does not forbid an unconstrained
pattern variable outside a binder from carrying the same printed slot, which is the
behavior required by reference issue #48.

**`$` is a slot; `#` is a global.** egglog spells a global `$name`, and this language
cannot borrow that spelling, because `$0` is already a slot. So a global may be marked
`#name`, at its binding and at its uses, and `$x` is a slot wherever it appears:

```slotted
(datatype M (IConst) (Mul M M) (Lam M M :binder 0))

(let #j (IConst))
(rewrite (Mul a #j) a :name "id-right")

; `k` is a global and `$k` is a slot -- the two never read alike
(let k (IConst))
(rewrite (Lam $k (Mul #k $k)) #k :name "slot-not-global")

(let mj (Mul (IConst) (IConst)))
(let ek (Lam $0 (Mul (IConst) $0)))
(run 5)

(check (= mj (IConst)))
(check (= ek (IConst)))
```

The sigil is optional, as it is in egglog, which only warns when a global lacks one —
`(let j …)` and a bare `j` mean the same thing. Naming a global with a `$` is not
optional but refused: `$j` in a term would be the slot and never the global.

A rewrite's **left side must be a call**. A bare variable there matches every class, so
the rule would say nothing.

`:when` takes **one** argument, a list of facts — `:when ((= a b) (not-free $x f))`.
That is egglog's spelling and the only one it accepts, so all of a rule's facts go in
that one list. A bare fact without the list, `:when (= a b)`, is taken here as a
convenience; egglog rejects it. Several `:when` clauses are refused rather than merged,
because egglog keeps only the last one and the rule would not mean there what it means
here.

There are two kinds of fact:

| fact | meaning |
| --- | --- |
| `(free $x f)`, `(not-free $x f)` | whether a slot is among a variable's free slots — the reference's `subst[v].slots().contains(…)`. A side condition on the match's *slots* |
| `(= v <call>)` | `v` also matches `<call>`. Another **pattern**, not a side condition: it constrains the match's *shape*, and several give an arbitrary multipattern |
| `(!= x y)` | the two are not the same **invocation** — not the same class reached by the same renaming, so two invocations of one class differ. Non-monotonic, as in egglog: classes that differ now may be unioned later, and a match this admitted is not withdrawn |

An `(= v <call>)` pattern nests as deep as you like, and the variables it introduces need
not appear on the left at all:

```slotted
(constructor Null () U)
(constructor Succ (U) U)
(constructor Prev (U) U)

; fires only where x is at least three deep, and returns what is under the third Succ
(rewrite (Prev x) y :when ((= x (Succ (Succ (Succ y))))) :name "reach-in")

(let s3 (Prev (Succ (Succ (Succ (Null))))))
(let s2 (Prev (Succ (Succ (Null)))))
(run 10)

(check (= s3 (Null)))
(fail (check (= s2 (Null))))     ; two deep, so the condition fails and the rule does not fire
```

Several `:when` patterns joined by **shared variables** are a multipattern. A variable
occurring in two patterns has to match the same thing in both, which is the join:

```slotted
(constructor Num (i64) U)
(constructor Mem0 () U)
(constructor Store (U U U) U)
(constructor LoadFrom (U U) U)

; the value a store wrote, read back at the same address: `m` and `p` join the patterns
(rewrite (LoadFrom m p) v :when ((= m (Store m0 p v))) :name "load-after-store")

(let m1 (Store (Mem0) (Num 7) (Num 42)))
(let got (LoadFrom m1 (Num 7)))
(let other (LoadFrom m1 (Num 8)))
(run 4)

(check (= got (Num 42)))
(fail (check (= other (Num 42))))    ; a different address, so `p` does not join
```

A shared **slot literal** is not a join. Each pattern looks its own node up and gets its
own name for that node's bound slot, so the same `$x` in two binder columns constrains
nothing:

```slotted
(constructor Num (i64) U)
(constructor Lam (U U) U :binder 0)
(constructor Pair (U U) U)
(constructor Fired () U)

; `$x` twice relates the two lambdas not at all
(rewrite (Pair f g) (Fired) :when ((= f (Lam $x c))
                                   (= g (Lam $x d))) :name "inert")

(let unrelated (Pair (Lam $0 (Num 1)) (Lam $0 (Num 2))))
(run 4)

(check (= unrelated (Fired)))        ; fires, though the two lambdas are unrelated
```

To relate two binders, share the *body* instead — a variable under two binder columns
joins up to renaming. `slotted/tests/multipattern.egg` works through both, along with
joins on several variables at once and a four-pattern chain.

A right-hand-side slot the pattern never mentions is **minted**, with nothing to write:
`(rewrite (F x y) (Lam $s (App (F x y) $s)))` binds a fresh `$s`. That is what the
reference does too. `:fresh $s` says it explicitly and is still accepted, but adds
nothing. `:name` names the rule.

`subst` is the one right-hand-side head that is not a constructor. `(subst body $x t)`
is `body[(var $x) := t]` — the reference's `b[x := t]`. It is a *call*, so there is
nothing to build; `slotted/tests/sdql-beta.egg` explains what the compiler emits for it.
The primitive extracts one smallest source term, performs capture-avoiding substitution,
and adds the result back. Generated hidden layout facts distinguish real children from
binder-marker edges, so markers add no extraction cost, a binder for `$x` shadows the
substitution below its covered child, and a conflicting private binder is alpha-refreshed
before it can capture a free slot of `t`. Cases E--G in that file pin all three properties;
`slotted/encoding/subst.egg` shows the encoded calls and string-head discriminator.

**`rewrite` is the only rule form.** egglog's `rule` and `birewrite` are not part of this
language and the compiler rejects them rather than passing them through — write a
`birewrite`'s two directions as two `rewrite`s. A rewrite's right-hand side is one of
three things — a variable, a term to build, or `subst` — and its conclusion is always that
the two sides are equal. egglog's other actions have no spelling here: `set` and `delete`
would have to name one row of a class that spans several, and `subsume` interacts with the
alpha-finder retiring rows. `slotted/encoding/user-rules.egg` M12 sets out the three
right-hand sides and what each compiles to.

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
(rewrite (F x y) (F y x) :name "comm")
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
egglog's comparison of two stored values. That third notion is not reachable from here,
and nothing is lost by it.

For two **nodes** it is not a different question anyway. The machinery has a rule that
unions two values reaching their leader by the same renaming, up to a symmetry of the
class, so term equality already implied it — checked, with no explicit union in either
case:

```
(rewrite (F x y) (F y x) :name "comm")
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
(extract q)      ; q's node is canonicalised away, so this extracts through the leader
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
