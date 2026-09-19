Encodes a slotted e-graph — one where a class carries named slots and nodes are equal up to renaming them — as ordinary egglog tables and rules.

# Overview

A slotted e-graph, from Schneider et al., *Slotted E-Graphs* (PLDI 2025), gives every e-class a set of **slots** and lets a
node reach a child under a **renaming** of them. That is what makes
`(lam $0 $0)` and `(lam $1 $1)` one class rather than two, without a separate
alpha-equivalence pass.

Egglog has no notion of a slot, so the encoding puts one in: a child column
becomes *two* columns, a renaming and a class, and a handful of relations track
which invocation of a class a value stands for. Everything is ordinary egglog —
the compiler emits it, nothing in the Rust is slotted-aware beyond a few
primitives on renamings.

`slotted/LANGUAGE.md` is the source language a person writes. This file is the
level below it: what that language compiles *to*, and why each table exists.

The running example is:

```
(sort Math)
(constructor Add (Math Math) Math)
(let a (Add $0 $1))
(let b (Add $1 $0))
(union a b)
(rewrite (Add x y) (Add y x) :name "comm")
```

Run `python3 slotted/slotted-egglog.py FILE.egg --desugar` on any program to see
its full encoding; every listing below is real output, with comments trimmed.

# The idea in one paragraph

A slotted class is **not** one egglog value. It is a set of values — one per
*invocation*, that is, per way of naming the class's slots — related by
`RenamesToLeader` and *not* by egglog's `union`. One invocation is the leader;
the rest are deleted once they are known to be renamings of it. So "are these
two terms equal?" is not egglog's `=`: it asks whether the two reach the leader
by the *same* renaming.

# Per-carrier tables

One family per declared equality sort. A program declaring several gets one
indexed family each — `RenamesToLeader_0`, `RenamesToLeader_1` — and nothing is
shared between them but the renaming sort itself.

```
(sort Renaming (Map i64 i64))
(sort Math)
(constructor Var (i64) Math)
(relation RenamesToLeader (Math Renaming Math))
(relation Equated (Math Renaming Math))
(function ClassSlots (Math) Renaming :merge (map-intersect old new))
(relation SubstPending (Math Renaming Renaming Math))
```

**`Renaming`** is a partial injection on slots, spelled as a map from `i64` to
`i64`. `compose`, `inverse`, `map-image` and `map-domain` are primitives on it.

**`Var`** is the one variable class. Every variable is `(Var 0)` reached by an
edge `0 -> s`, so *which* slot a variable names lives in the renaming and not in
the value. Its class slots are seeded outright:

```
(set (ClassSlots (Var 0)) (map-of 0 0))
```

**`RenamesToLeader f m l`** reads `f = m * l`: `m` carries `l`'s slots to `f`'s.
A class is a connected component of this relation, and its leader is the
component's canonical member. A **self-loop** `(RenamesToLeader c p c)` with `p`
not the identity is a **symmetry** — the class is equal to itself under a
permutation of its slots, which is how the example's `union` records that `Add`
is commutative.

**`Equated`** holds the same fact with no orientation chosen. Orientation is a
function of value order, so a row oriented before a merge can be backwards after
one; `Equated` is what the machinery derives `RenamesToLeader` from, and a stale
row is deleted and re-derived rather than repaired in place. Repairing in place
does not converge — transitivity keeps re-deriving the backwards row.

```
(rule ((Equated a m b) (!= a b) (= a (ordering-max a b)))
      ((RenamesToLeader a m b)) :ruleset slotted)
(rule ((RenamesToLeader f m l) (!= f l) (= l (ordering-max f l)))
      ((delete (RenamesToLeader f m l))) :ruleset slotted)
```

**`ClassSlots c`** is the slots the class actually depends on, as an identity
renaming. It is held directly rather than read off a self-loop, because a
self-loop is derived from a *node* and so can name more slots than the class
has. Its merge is `map-intersect`, so it only ever shrinks — which is what makes
a slot **redundant**: union two invocations that disagree on a slot and the
class stops depending on it. A slotless class has one invocation, so all its
spellings are the same term.

# Per-constructor machinery

A child column expands to a renaming column and a class column, so
`(constructor Add (Math Math) Math)` becomes:

```
(constructor Add (Renaming Math Renaming Math) Math)
```

and `(Add $0 $1)` is stored as
`(Add (map-of 0 0) (Var 0) (map-of 0 1) (Var 0))`. Each constructor then gets
one block of rules. Three are worth reading.

**Class slots**, an upper bound the merge narrows:

```
(rule ((= e1 (Add m1 c1 m2 c2)))
      ((set (ClassSlots e1) (map-union (map-image m1) (map-image m2)))) :ruleset slotted)
```

**A self-loop**, so a query can reach any class that holds a node:

```
(rule ((= e1 (Add m1 c1 m2 c2))
       (= m (map-union (map-image m1) (map-image m2))))
      ((RenamesToLeader e1 m e1)) :ruleset slotted)
```

**The alpha-finder**, which is the heart of it: two nodes with the same children
that differ only by a renaming are one invocation, so one is deleted and the
renaming between them recorded.

```
(rule ((= e1 (Add m1_o c1 m2_o c2))
       (= e2 (Add b1 c1 b2 c2))
       (= e1 (ordering-max e1 e2))
       (RenamesToLeader c1 sym1 c1)
       (RenamesToLeader c2 sym2 c2)
       (= m1 (compose m1_o sym1))
       (= m2 (compose m2_o sym2))
       (= m (find-mapping m1 m2 b1 b2))
       ...)
      ((Equated e1 m e2)
       (delete (Add m1_o c1 m2_o c2))) :ruleset slotted)
```

`find-mapping` solves for the renaming carrying one tuple of edges onto another.
The `RenamesToLeader c sym c` atoms are the children's *symmetries*: two nodes
may agree only after permuting a child's slots, so the solve quantifies over the
group. The same solve is kept non-destructively by a second rule, which is how a
child's symmetry becomes the parent's.

Because this deletes rows, a class keeps exactly one node per shape — which is
why a claim about a term matches it rather than spelling it out. A term the
e-graph holds need not have a row under the spelling you wrote.

# Binders

`:binder i` marks a child column whose slot the node binds. The bound slot is
stored as an edge `0 -> s` to `(Var 0)` like any other, so a binder is not a
different kind of column — what differs is that the slot is taken out of the
class's slot set over the column the binder **covers**, which is the one right
after it. `let` binds in its body and leaves its value's occurrence free.

When a bound slot collides with a free one the machinery renames the bound one
first, to a slot the node does not use, which keeps it alpha-renameable.

# Matching

A rule's left-hand side is flattened into depth-1 atoms and solved into one
shared frame, one atom at a time. Each atom's renaming is pinned by what is
already known — the edge from its parent, and any slot literal an earlier atom
fixed — and `find-mapping-total` **mints** a fresh name for whatever is left
over.

A mint is a commitment nothing revisits, and that is the encoding's sharpest
edge. Where an atom's slot is not constrained from above — a class that has made
it redundant, or a binder's own slot — the mint decides it, and a later atom that
needed a different answer simply fails to match.

`refine-namings` is the partial remedy: after every atom is solved, it returns
*every* way the match's slots may be merged, and the rule reads one with
`vec-get` against an `Idx` row. Element 0 is the identity, so running out of
indices degrades to not refining — matches are missed, never invented.

# Where the pieces live

| path | what it is |
| --- | --- |
| `slotted/LANGUAGE.md` | the source language: every form and why it exists |
| `slotted/slotted-egglog.py` | the compiler — a program in that language to egglog |
| `slotted/slotted-encoder.py` | the encoding itself: the tables above, and rule compilation |
| `slotted/tests/` | tests written in the source language |
| `slotted/xdiff/` | the differential harness against `memoryleak47/slotted-egraphs` |
| `slotted/xmulti/` | the reference oracle, pinned to an exact revision |

Nothing here is hand-maintained egglog: the machinery is generated from the
constructors a program declares, so a worked example is a program you run
through the compiler rather than a file that can drift from it.
