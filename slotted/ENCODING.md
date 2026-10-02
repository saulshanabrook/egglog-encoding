Encodes a slotted e-graph — one where a class carries named slots and nodes are equal up to renaming them — as ordinary egglog tables and rules.

# Overview

A slotted e-graph, from Schneider et al., [*Slotted E-Graphs* (PLDI 2025)](https://michel-steuwer.github.io/files/publications/2025/PLDI-2025.pdf), gives every e-class a set of **slots** and lets a
node reach a child under a **renaming** of them. That is what makes
`(lam $0 $0)` and `(lam $1 $1)` one class rather than two, without a separate
alpha-equivalence pass.

Egglog has no notion of a slot, so the encoding puts one in: a child column
becomes *two* columns, a renaming and a class, and a handful of relations track
which invocation of a class a value stands for. The graph representation and
maintenance are ordinary egglog tables and rules. Rust primitives implement
renaming and group operations, the frame constraint solver used in matching, and
extraction-based substitution.

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
its full encoding. The listings below are explanatory fragments: names and schedules
are shortened, and the matching example combines stages that the compiler emits
separately. They are not a standalone program or byte-for-byte compiler snapshots.

**How to read this document.** This is an implementation guide. Part I explains the
representation, maintenance, and matching; it already uses the current shape index,
stored groups, and canonical invocation keys. Part II explains further implementation
choices and their costs. The core explanation below distinguishes the semantic
obligations from those implementation choices.
The contract at the end numbers the requirements the code cites. There is currently
no separately executable, unoptimized version checked by the suite; deleting Part II
from generated output is not a supported way to obtain one.

# The idea in one paragraph

A slotted class may have several egglog values representing materialized
*invocations*: ways of naming its slots. `RenamesToLeader` connects them to a
leader. Nodes move to the leader; follower values remain usable through that
relation. Equality of invocations requires a common leader and renamings that
agree up to a **symmetry** of its slots. Maintenance uses egglog's `union` to
deduplicate invocations equal in that sense; having the same leader alone is
insufficient. A user equation introduces a new equality in a specified slot frame.

# The core encoding

Consider one carrier and a binary constructor. Write `F(m, a, n, b)` for a node
whose children are the invocations `m * a` and `n * b`. Define `S(c)` as the class's
public slots, `G(c)` as its symmetries, and `R(a, r, b)` as `a = r * b`, with `r`
mapping from `b`'s slots to `a`'s. These are mathematical names for the information.
Symmetries can be enumerated as relation rows `Sym(c, g)`; storing a whole group
in one value is an implementation choice.

The encoding has five parts:

1. **Representation and equality.** Separate node-local slots from `S(c)`. A child
   edge is injective and has exactly its child's public slots as its domain. Two
   invocations reaching leader `c` by `m` and `n` are equal when
   `m = n ∘ g` for some `g ∈ G(c)`. Sharing `c` alone does not establish equality.
2. **Congruence modulo renaming.** Compare two rows with the same constructor and
   canonical children. For rows `a = F(m1,c1,m2,c2)` and
   `b = F(n1,c1,n2,c2)`, enumerate `g1 ∈ G(c1)` and `g2 ∈ G(c2)` and solve for an
   injective node renaming `r` satisfying `r ∘ n1 = m1 ∘ g1` and
   `r ∘ n2 = m2 ∘ g2`. A solution establishes `a = r * b`; comparing a row with
   itself can discover a symmetry. This pairwise rule explains the operation that
   the current `node-shape` and shape index accelerate.
3. **Maintenance.** Compose renaming paths, reconcile competing leaders, transport
   and intersect class slots, and close symmetries under composition on the surviving
   slots. Migrate nodes to leaders and update child edges. Migration needs a total
   extension of the inverse leader renaming over the node's slots: assign fresh
   names to slots the class has made redundant. Simply composing with a partial
   inverse can erase node data.
4. **Binders.** A binder removes its name from the public slots contributed by its
   covered child, leaving other children alone. A bound name colliding with a free
   name elsewhere in the node must first be refreshed. These scope rules belong in
   the core explanation.
5. **Matching and rewriting.** Join depth-1 node matches, equate their slot
   occurrences through shared pattern variables, and enforce distinctness within
   each node, class, and set of distinct literals. Account for repeated variables
   modulo symmetry and enumerate all consistent refinements of the placeholders
   reached by pattern variables or carried literals. Then check freshness conditions
   and build the right-hand side in the root's frame. Refinement is needed to match
   the reference multipattern matcher; eager fresh naming or the nested matcher is
   not a substitute for it.

At a maintenance fixed point, leader components decode to slotted classes, `S` and
`G` to their slot sets and groups, and constructor rows to nodes modulo renaming and
child symmetries.
Raw egglog values and rows are not themselves the slotted class and node counts.
A correctness argument must establish that maintenance enforces these invariants
without introducing unintended equalities, and that a compiled rewrite produces
the intended matches and unions. Differential tests provide evidence for the
implementation, not a proof of this correspondence.

The distinction between the required operations and their implementation is:

| Required operation | Implementation choice to explain separately |
| --- | --- |
| Congruence modulo renaming and child symmetry | Canonical shapes, `_shape_F` hashcons, and sharing the shape/symmetry walk |
| Symmetry closure and equality of invocations | `EclassGroup` values and the `Invocation` index keyed by `coset-min` |
| Complete matching modulo symmetries | Coset representatives on pinned slots and cached reading indexes |
| Apply every match refinement in a user round | Stored match relations, dynamic refinement indexes, and staged application |
| Represent newly built nodes in the correct frame | Canonical construction below the root and removal of duplicate physical rows |
| Restore maintenance invariants between user rounds | Phased schedules and removal of unused follower state |
| Substitute into a selected representative term | Cached extraction and results, shared templates, and lazy comparison |

Substitution's representative-selection policy belongs in the specification when
comparing final graphs: choosing a different representative can build a different
graph. Optimizations must preserve selection over the decoded nodes, not merely
preserve the set of represented equalities. The storage of the selected tree as
shared templates is an optimization.
The current multipattern comparison deliberately aligns representative selection on
both sides; the nested comparison uses the reference's syntactic policy. See
*Against the reference* for that distinction and the paper artifact's policies.

This is a semantic overview of the current encoding. It retains slot restriction,
fresh extension during migration, binder scope, symmetry-aware matching, and complete
refinement; these are correctness requirements, not optional optimizations. It is
not a separately executable baseline: the present suite validates the current
compiler and primitives, including their optimizations.

# Part I. Representation, maintenance, and matching

## Tables, once per sort

Everything in this section is emitted once per equality sort the program declares,
with the sort's position as a suffix: a program with two slotted sorts gets
`RenamesToLeader_0` and `RenamesToLeader_1`. Their class tables are separate; support
sorts, layout metadata, refinement indexes, and schedules are shared. The listings
below drop that suffix, and the `_` the generator puts
in front of its own variables.

```
(sort Renaming (Map i64 i64))
(sort Math)
(constructor Var (i64) Math)
(relation RenamesToLeader (Math Renaming Math))
(relation Equated (Math Renaming Math))
(function ClassSlots (Math) Renaming :merge (map-intersect old new))
(relation SubstPending (Math Renaming Renaming Math))
(function ShapeEqual (Math Renaming Math) Unit :no-merge)
(function Invocation (Math Renaming) Math :merge ((union old new) old))
(function EclassGroup (Math) Group :merge (set-union old new))
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
component's canonical member. Maintenance seeds an identity row for each value;
the follower cleanup removes it once a distinct leader is known. At a maintenance
fixed point, self-edges are identities and symmetries live in `EclassGroup`.
Native egglog unions can temporarily turn a nonidentity edge into a self-edge;
maintenance transfers that information into the group.

**`Equated`** holds the same fact with no orientation chosen. Orientation is a
function of value order, so a row oriented before a merge can be backwards after
one; `Equated` is what the machinery derives `RenamesToLeader` from, and a stale
row is deleted and re-derived rather than repaired in place. Repairing in place
does not converge — transitivity keeps re-deriving the backwards row.

**`ClassSlots c`** is the slots the class actually depends on, as an identity
renaming. It is held directly rather than read off the group, because it is
what every renaming is spelled on (C15), so it has to come first. Its merge is
`map-intersect`, so it only ever shrinks. Equating `f($x,$y)` with `g($x)` makes
`$y` **redundant**: the class no longer depends on it even though an `f` node may
still carry it. Equating `f($x,$y)` with `f($y,$x)` can instead add a symmetry
without dropping either slot. A slotless class has one invocation.

**`SubstPending root q mr r`** is a substitution's answer on its way back: `r` is the
class the primitive built and `mr` its renaming, and `q` carries `r`'s slot names into
the root's (C12).

**`ShapeEqual a m b`** is an `Equated` row on its way in. The shape index (C14) states
it from a merge block, which may `set` a function but not insert into a relation.

**`Invocation c m`** names the invocation "`c` read through `m`". Every member of a
class registers under the names of its readings, and the function's merge unions two
members that share one, which is how one invocation stays one egglog value.

**`EclassGroup c`** is the class's symmetry group as one value: the renamings `p` of
its own slots under which `c` is equal to itself. That is how the example's `union`
records that `Add` is commutative: `Add($0,$1)` equated with `Add($1,$0)` is one class
whose group holds the swap `{0 -> 1, 1 -> 0}` beside the identity. It is the whole
group, closed under composition, not a set of generators — a query looks a composite
element up directly, so it has to be there. Every rule that learns a symmetry writes
here, and the shape primitives take the value whole, to spell a node once over every
reading its children allow rather than once per reading (C14). `Group` is the sort, the
reference's data structure of the same name; `EclassGroup` is the class's field of it.
Rules access group elements through primitives or indexed views, rather than a
direct set-membership join. Primitives such as `coset-min`, `group-slot-closure`,
`coset-same`, and the frame's own bindings walk the group internally.

## The rules, once per sort

Seventeen rules and two facts, none of which mentions a constructor. Part II adds
five more.

**Orienting `Equated`.** The larger value is the follower, so a leader is the least
member of its component. An equation of a class with *itself* is a symmetry rather than
an edge. Either way the renaming is spelled on the two classes' slot sets (C15): an
entry on a slot a class has made redundant says nothing, and left in it makes one edge
many rows, which every closure rule below then multiplies.

```
(rule ((Equated a m b) (!= a b) (= a (ordering-max a b))
       (= csa (ClassSlots a)) (= csb (ClassSlots b)))
      ((RenamesToLeader a (compose csa (compose m csb)) b)) :ruleset slotted)
(rule ((Equated a m b) (!= a b) (= b (ordering-max a b))
       (= csa (ClassSlots a)) (= csb (ClassSlots b)))
      ((RenamesToLeader b (compose csb (compose (inverse m) csa)) a)) :ruleset slotted)
(rule ((Equated a m a) (= cs (ClassSlots a)))
      ((set (EclassGroup a) (set-of (compose cs (compose m cs))))) :ruleset slotted)
```

**Seeding identities and moving self-edges into the group.** The identity is both the
reflexive row of the edge relation and the unit of the group. At a maintenance fixed
point a remaining self-edge is an identity. egglog's own `union` can identify the two
ends of an edge and leave one that is not; what such a row says is that the class is equal to itself under that
renaming, so it is a symmetry and is moved into the group. That is what lets every rule
below read this relation as followers and identities.

```
(rule ((= cs (ClassSlots c)))
      ((RenamesToLeader c cs c)
       (set (EclassGroup c) (set-of cs))) :ruleset slotted)
(rule ((RenamesToLeader c m c) (= cs (ClassSlots c)) (!= m cs))
      ((set (EclassGroup c) (set-of (compose cs (compose m cs))))
       (delete (RenamesToLeader c m c))) :ruleset slotted)
```

**Dropping a stale edge.** egglog's own `union` can change which of two values is the
larger, leaving an edge that points from the smaller to the larger. It is deleted;
transitivity re-derives it the right way round.

```
(rule ((RenamesToLeader f m l) (!= f l) (= l (ordering-max f l)))
      ((delete (RenamesToLeader f m l))) :ruleset slotted)
```

**Carrying class slots along an edge**, in both directions. One member's slot set,
taken through the renaming, bounds the other's; the merge intersects, so the whole
component settles on the slots every member has.

```
(rule ((RenamesToLeader a m b) (= slots (ClassSlots a)))
      ((set (ClassSlots b) (map-image (compose (inverse m) slots)))) :ruleset slotted)
(rule ((RenamesToLeader a m b) (= slots (ClassSlots b)))
      ((set (ClassSlots a) (map-image (compose m slots)))) :ruleset slotted)
```

**A class's slots are closed under its symmetries.** If `c = g * c` and `g` sends a slot
the class has to one it does not, the two cannot be told apart, so both are redundant.
`group-slot-closure` keeps the slots every element carries onto slots the class has, in
either direction, and the merge intersects; re-firing as the slots narrow is what
settles `f($0,$1) = f($1,$2)` on the empty slot set: no slot survives being renamed to
its successor forever.

```
(rule ((= grp (EclassGroup c)) (= slots (ClassSlots c)))
      ((set (ClassSlots c) (group-slot-closure grp slots))) :ruleset slotted)
```

**Transitivity.** Two edges compose into an equation. The middle of a path is never its
own end, because the only row there from a value to itself is its identity and a path
through one restates the path it came from. Composing an edge with a symmetry is a real
thing to want, and it belongs to the invocation rule below, which puts the result in a
key rather than in a new edge.

```
(rule ((RenamesToLeader e1 m12 e2)
       (RenamesToLeader e2 m23 e3)
       (!= e2 e3))
      ((Equated e1 (compose m12 m23) e3)) :ruleset slotted)
```

**One leader per follower.** A follower with edges to two leaders makes the leaders
equal and keeps the edge to the smaller. Two different edges to the *same* leader make
a symmetry of that leader, and the one with the larger renaming goes. Only edges
already spelled on their classes' slots take part: an edge a narrowing has outdated
belongs to the restatement rule below, and two deleting rules must not choose
differently between an edge and its restatement.

```
(rule ((RenamesToLeader a m1 b)
       (RenamesToLeader a m2 c)
       (!= a c) (!= a b)
       (= csa (ClassSlots a)) (= csb (ClassSlots b)) (= csc (ClassSlots c))
       (= m1 (compose csa (compose m1 csb)))
       (= m2 (compose csa (compose m2 csc)))
       (= (ordering-max b c) b)
       (guard (or (bool-!= b c)
                  (and (bool= b c) (bool-!= m1 m2) (bool= (ordering-max m1 m2) m1)))))
      ((delete (RenamesToLeader a m1 b))
       (Equated b (compose (inverse m1) m2) c)) :ruleset slotted)
```

**A renaming outlives a narrowing.** `ClassSlots` only ever shrinks, and an edge
oriented before a class dropped a slot still names it. The edge is restated on what the
classes have now; this is the one rule that deletes an edge without a leader having
changed.

```
(rule ((RenamesToLeader f m l)
       (= csf (ClassSlots f)) (= csl (ClassSlots l))
       (= m2 (compose csf (compose m csl)))
       (!= m m2))
      ((delete (RenamesToLeader f m l))
       (RenamesToLeader f m2 l)) :ruleset slotted)
```

**A group is spelled on its class's slots and closed under composition**, and one rule
keeps it so. A symmetry outlives a narrowing for the same reason an edge does: left as
it was it would rename a slot the class no longer has, and every rule reading the group
would carry that slot back in, so `group-restrict` respells every element on the slots
the class has now. And two nodes of one class each state their own symmetries, so the
class's group is the one those generate; `group-close` takes the closure. Storing the
closure rather than generators is what lets a match look up the element it needs in one
join. The rule is whole-set because the function's merge only ever unions: shrinking is
a delete and a set, and two rules shrinking one set in one iteration would lose an edit
or, under the union, undo each other forever.

```
(rule ((= s (EclassGroup c))
       (= cs (ClassSlots c))
       (= s2 (group-close (group-restrict s cs)))
       (!= s s2))
      ((delete (EclassGroup c))
       (set (EclassGroup c) s2)) :ruleset slotted)
```

**One variable class.** `(Var v)` with `v` other than 0 is restated as `(Var 0)` under
`{0 -> v}` and deleted. `Var` is handled separately from the user constructors, so
its identity is seeded as a fact.

```
(rule ((= e (Var v)) (!= v 0))
      ((Equated e (map-insert (map-empty) 0 v) (Var 0))
       (delete (Var v))) :ruleset slotted)
(RenamesToLeader (Var 0) (map-insert (map-empty) 0 0) (Var 0))
(set (EclassGroup (Var 0)) (set-of (map-insert (map-empty) 0 0)))
```

**The same invocation is one value.** Two renamings of a leader's slots name one
invocation exactly when they differ by a symmetry, so the invocation has a canonical
name: the least of `m ∘ g` over the group, which `coset-min` picks. A member reaching
leader `c` by `m` registers under that name, and two members that register under one
name are unioned by the function's merge. This is where "the same class by the same
renaming" becomes egglog equality, and why a claim's `=` compares renamings up to a
symmetry: a `check` compares the classes two terms reach with egglog's `=`, which is
only right once equal invocations are one value. It also keeps the graph small — a
built node whose class already existed is a value of its own until it is identified
with the member it duplicates, and every such value carries an edge and slots that
every rule over the graph then reads. The cost is one `set` per edge, whatever the
group holds; a follower whose group has been emptied has no name yet and waits.

```
(rule ((RenamesToLeader a m c)
       (= grp (EclassGroup c))
       (= name (coset-min m grp)))
      ((set (Invocation c name) a)) :ruleset slotted)
```

**A substitution's answer.** Once the class the primitive built has its slot set, the
pending row becomes an equation between the root and that class in the root's slot
names.

```
(rule ((SubstPending root q mr r) (= cs (ClassSlots r)))
      ((Equated root (compose q (compose mr cs)) r)) :ruleset slotted)
```

**A shape collision.** What the shape index's merge block wrote enters the class
relation like any other equation.

```
(rule ((ShapeEqual a m b))
      ((Equated a m b)) :ruleset slotted)
```

## Per-constructor machinery

A child column expands to a renaming column and a class column, so
`(constructor Add (Math Math) Math)` becomes:

```
(constructor Add (Renaming Math Renaming Math) Math)
```

and `(Add $0 $1)` is stored as
`(Add (map-of 0 0) (Var 0) (map-of 0 1) (Var 0))`. Each constructor then gets one
block of rules: class slots, the shape index, migration, and one child-update per child
column.

**Class slots**, an upper bound the merge narrows:

```
(rule ((= e1 (Add m1 c1 m2 c2)))
      ((set (ClassSlots e1) (map-union (map-image m1) (map-image m2)))) :ruleset slotted)
```

**The shape index**, which is the heart of it. Two rows are one node up to renaming
exactly when they have the same *shape*: the row with its slots renumbered 0, 1, 2… by
first occurrence, scanning the edges in order and each edge by child slot. `(shape m1
m2)` returns the renumbered edges followed by the renaming from those numbers back to
the row's own names. Every row is entered into a function per constructor, keyed by the
shape and holding one class that has the node with the renaming from the shape's names
into that class's. A second class arriving at a key is that node under another
renaming, and the function's merge block states the equation between the two. This is
the reference's hashcons on shapes: one lookup per row.

```
(function _shape_Add (Renaming Math Renaming Math) (Math Renaming)
  :merge ((set (ShapeEqual old0 (compose old1 (inverse new1)) new0) ())
          (values old0 old1)))
(function _shapeof_Add (Renaming Group Renaming Group)
  (Renaming Renaming Renaming Group) :no-merge)

(rule ((= c (Add m1 c1 m2 c2))
       (= g1 (EclassGroup c1)) (= g2 (EclassGroup c2))
       (= sh (node-shape (vec-of m1 m2) (vec-of g1 g2))))
      ((set (_shape_Add (vec-get sh 0) c1 (vec-get sh 1) c2) (values c (vec-get sh 2)))
       (set (_shapeof_Add m1 g1 m2 g2)
            (values (vec-get sh 0) (vec-get sh 1) (vec-get sh 2)
                    (symmetries-of sh 3)))) :ruleset slotted)
(rule ((= c (Add m1 c1 m2 c2))
       (= g1 (EclassGroup c1)) (= g2 (EclassGroup c2))
       (= (values s1 s2 back syms) (_shapeof_Add m1 g1 m2 g2))
       (= cs (ClassSlots c)))
      ((set (EclassGroup c) (group-restrict syms cs))) :ruleset slotted)
```

`node-shape` takes each child's group and walks the readings those groups allow, once.
It returns the canonical edges, then the renaming back to the node's own names, then one
renaming per symmetry the node gives its class; `symmetries-of` reads that tail. The
canonical edges are the key, so two nodes that agree only after permuting a child's
slots arrive at one key. A row costs one insertion, whatever the groups hold.
`ShapeEqual` is a function rather than a relation because a merge block may `set` a
function, and one rule per sort hands its rows to `Equated`.

The tail is what a node says about its *own* class: a reading that spells the node the
same way up to a renaming of the node's own slots says the class equals itself under
that renaming, which is how a child's symmetry becomes its parent's. That is the
reference's `determine_self_symmetries`. The index rule caches it with the shape in
`_shapeof_Add`, and a second rule carries it into the group, because that write waits for
one more thing: the class's slots, on which the symmetries are spelled before they
enter the group (C15). A row may carry a slot its class has dropped, and a symmetry
over it is what the group's normalisation strips; written unrestricted, every re-firing
would add it and the normalisation remove it, and around a cycle of classes that never
settles. The index write must not wait for the slots — made to, it loses an
identification on the BATAX-12 workload — so the two writes are two rules, and the
walk runs once.

**Migration** rebuilds a follower's node in the leader's slot names and unions it into
the leader. `R` takes the node's slots to the leader's, agreeing with the edge where
the leader has the slot and minting a name where the class has dropped it. After this
every node lives in a leader, and a follower is a name in `RenamesToLeader` and
nothing more.

```
(rule ((RenamesToLeader e2 m e1)
       (= e2 (Add m1 c1 m2 c2))
       (!= e1 e2)
       (= e2 (ordering-max e1 e2))
       (= nodeslots (map-union (map-image m1) (map-image m2)))
       (= R (find-mapping-total (map-domain m) nodeslots (map-domain m) m))
       (= n1 (compose R m1))
       (= n2 (compose R m2)))
      ((union e1 (Add n1 c1 n2 c2))
       (delete (Add m1 c1 m2 c2))) :ruleset slotted)
```

**Child-update** rebuilds a node whose child has a leader so that it points at the
leader, its edge composed with the child's renaming. The child's own identity row counts
too, and only if the edge changes: that is a child that has dropped a slot the edge
still names, and composing narrows the parent's edge as well, which is how redundancy
travels upward. Any other row from the child to itself is refused, which is what the
idempotence guard says. A symmetry is not a row of this relation, but egglog's own
`union` can make one by identifying the two ends of an edge, and rewriting a node
through a symmetry of its child gives a row per group element and never settles. One
such rule per child column; the one for the second column is the same with `m2` and
`c2`.

```
(rule ((RenamesToLeader c1 m c')
       (= node (Add m1 c1 m2 c2))
       (= c1 (ordering-max c1 c'))
       (guard (or (bool-!= c1 c') (bool= (compose m m) m)))
       (guard (or (bool-!= c1 c') (bool-!= (compose m1 m) m1))))
      ((union node (Add (compose m1 m) c' m2 c2))
       (delete (Add m1 c1 m2 c2))) :ruleset slotted)
```

Migration deletes rows, so a class need not have a row under the spelling you wrote —
which is why a claim about a term matches it rather than spelling it out. Without
the row-deduplication rule a class can still hold several readings of one node;
Part II explains how the current implementation keeps one.

## Binders

`:binder i` marks a child column whose slot the node binds. The bound slot is
stored as an edge `0 -> s` to `(Var 0)` like any other, so a binder is not a
different kind of column — what differs is that the slot is taken out of the
class's slot set over the column the binder **covers**, which is the one right
after it. `let` binds in its body and leaves its value's occurrence free.

One rule per bound slot does the taking out: the node's edge to its leader is
restated without the bound slot, and the class-slot transport above then intersects
that slot away, so the class does not depend on what it binds.

```
(rule ((RenamesToLeader (Lam mvar (Var 0) m2 c2) ml l)
       (= v (map-get mvar 0)))
      ((Equated (Lam mvar (Var 0) m2 c2) (inverse (map-remove (inverse ml) v)) l)) :ruleset slotted)
```

In the constructor's own block the binder column needs no special case in the shape
index, since the variable class's group holds the identity alone, and its
child-update also requires `(map-get (compose m1 m) 0)` to exist: a bound name may be
renamed but not lost.

When a bound slot collides with a free one the machinery renames the bound one
first, to a slot the node does not use, which keeps it alpha-renameable.

## Matching

egglog finds the e-nodes a rule's left-hand side matches; what the match says about
**slots** is a set of constraints on those nodes, checked by a handful of primitives
inside the same query. This section walks one rule through, the SDQL library's
`sum-fact-3`:

```
(rewrite (Sum R $x $y (Sing e1 e2))
         (Sing e1 (Sum R $x $y e2))
         :name "sum-fact-3"
         :when ((not-free $x e1) (not-free $y e1)))
```

`Sum` binds `$x` and `$y` over its body (its `:binder 1 2` columns), so the rule pulls a
singleton's key out of a sum when the key does not mention the bound variables.

### Flattening

egglog matches one e-node per atom, so the left-hand side becomes depth-1 atoms, one
per constructor, every child a pattern variable or a slot literal. The flattener names
the nodes it has to invent with a `_` prefix, which no author's name begins with:

```
_p  = (Sum R $x $y _t1)      the root
_t1 = (Sing e1 e2)           the Sing node under it
```

`R`, `e1` and `e2` are pattern variables. Each stands for an **invocation**: a class
and a renaming of that class's slots into the pattern's (C1). `$x` and `$y` are slot
literals, names the pattern gives to slots of its own. Each atom becomes one egglog
row pattern with a variable per column: `cls_p` and `cls_t1` for the two classes,
`e0_R` for atom 0's edge to `R`, `e1_e1` for atom 1's edge to `e1`, and so on. An
edge is a renaming from the child class's slots to the node's; a binder column's edge
sends `0` to the bound slot.

### Occurrences

The matched `Sum` node has slots numbered however the e-graph stores them, the matched
`Sing` node has its own numbering, and so does every class a variable is bound to. The
pattern needs to know which of all these are the *same* slot. So the frame speaks of
**occurrences**, one name for every place a slot shows up in the match:

| occurrence | reads as |
| --- | --- |
| `Node(a, s)` | slot `s` of the e-node matched at the atom labelled `a` |
| `Var(v, t)` | slot `t` of the class pattern variable `v` is bound to |
| `Lit("$x")` | the slot the pattern calls `$x`, or one the right-hand side minted |

`Node(_t1, 1)` means "whatever the matched `Sing` node calls slot 1", and
`Var(e1, 0)` means "whatever `e1`'s class calls slot 0": relative names, the two ends
of an edge egglog matched. Only `Lit` is a name of the pattern's own. A node and its
class are kept apart because a node may carry a slot its class has made redundant
(C4), and a child's class numbers its slots differently from the node that holds it,
with the edge as the translation.

Every column of a matched node is then an equation between occurrences:

- the root column: `Node(a, s) = Var(p, s)` for each slot `s` of `p`'s class, the node
  is an invocation of its own class (through a symmetry of the class when `p` was
  matched by an earlier atom, C5);
- a child carrying `v` by edge `e`: `Node(a, e(t)) = Var(v, t)` for each slot `t` of
  `v`'s class;
- a literal at edge `e`: `Node(a, e(0)) = Lit("$x")`.

Take a match of `sum-fact-3` against `(Sum r $x $y (Sing $z $x))`, where `r` is some
term with one free slot. Say the `Sum` node stores `r`'s slot as 0, `z` as 1, `x` as 2
and `y` as 3, so its class's slots are `{0, 1}`; the `Sing` node stores `z` as 0 and
`x` as 1, and the edge from the `Sum` node to it is `{0 -> 1, 1 -> 2}`; the bare slots
`$z` and `$x` are the variable class with its one slot 0, reached by the edges
`{0 -> 0}` and `{0 -> 1}`. The equations close into four blocks:

```
{ Node(_p,0)  Var(_p,0)  Var(R,0) }                                   R's one slot
{ Node(_p,1)  Var(_p,1)  Node(_t1,0)  Var(_t1,0)  Var(e1,0) }         z, free in the root
{ Node(_p,2)  Lit("$x")  Node(_t1,1)  Var(_t1,1)  Var(e2,0) }         the bound x, reached again as e2
{ Node(_p,3)  Lit("$y") }                                             the bound y, unused below
```

The second block is the interesting one: the `Sum` atom put `Node(_p,1)` with
`Var(_t1,0)`, and the `Sing` atom put `Var(_t1,0)` with `Node(_t1,0)` and `Var(e1,0)`.
`Var(_t1, 0)` is the same occurrence in both atoms, so joining them identifies the
parent's edge with the child's own slot. That is the reference matcher's `unify`,
and it needs no order: the join takes the union of the equations and re-closes.

### The frame

A **frame** is the closure of these equations. Its **blocks** are the pattern's
slots: two occurrences in one block are one slot, and the blocks are numbered
canonically, `anchor` making the root's class slots their own numbers. Above, anchored
at `_p`, the blocks are slots 0, 1, 2, 3 in the order written, so `(ren m "e1")` is
`{0 -> 1}`, `(ren m "e2")` and `(ren m "$x")` are `{0 -> 2}`, and `(not-free m "$x"
(names "e1"))` asks whether slot 2 lies in `e1`'s image `{1}`: it does not, and the
rule fires. Had `e1` been `(var $x)`, `Lit("$x")` and `Var(e1, 0)` would share a
block and the condition would refuse.

The equations say which occurrences are one slot; the **cliques** say which are
different. A clique is a set of occurrences every two of which must be distinct slots,
so no two may share a block:

- the slots of one e-node, `Node(a, ·)`: a node's slots are distinct positions;
- the slots of one class, `Var(v, ·)`: a renaming is injective;
- the different literals: the pattern asked for two names.

A frame is **consistent** when no clique is broken; `atom` and `frame-join` return
nothing otherwise, so a reading that identifies two slots of one node simply fails to
join. The cliques are not stored: `sort/slotted/frame.rs` in the egglog crate reads them off
the occurrences (`apart`). The reference matcher keeps the same information as pairwise
disequality constraints. In the match above every block holds a slot of the root
node, so the node clique pins all four and `refinements` holds the frame alone; C8
says when it has more to do.

The primitives:

| primitive | what it says |
| --- | --- |
| `(root "p" cs [sym\|grp])` | the atom's node is an invocation of `p`'s class, whose exact slots are `cs`; through the symmetry `sym`, or through some element of the group `grp` that `refinements` decides, if `p` was matched before |
| `(child "v" e cs [sym\|grp])` | the column with edge `e` carries `v`: `Node(a, e(t)) = Var(v, t)` for each class slot `t`, through `sym` or an element of `grp` likewise |
| `(lit "$x" e)`, `(bound "$x" e)` | the column is the literal `$x`: `Node(a, e(0)) = Lit("$x")`; `bound` is a binder column, whose literal is node data and not carried into refinement |
| `(leaf e)` | a payload leaf reached through its own class: node slots, nothing more |
| `(atom "a" binding...)` | one atom's constraints, closed; fails if its own columns break a clique |
| `(frame-join f g)` | both frames' constraints, closed; fails where a clique breaks. Associative and commutative |
| `(anchor f "p")` | the frame spelled in `p`'s slot names: the rule's root, so its renaming is the identity and the action is egglog's `union` |
| `(refinements f)` | every consistent way to decide the readings left to the frame, and then to merge the blocks refinement may touch, as a `Vec` of frames; `vec-get` reads one and is partial past the last |
| `(mint f (names "$z"...))` | fresh slots for a right-hand side, apart from everything named |
| `(free m "$x" (names v...))`, `(not-free ...)` | is the literal's slot in one of the variables' images |
| `(same m "a" "b")`, `(bool-same ...)` | the two variables are one invocation |
| `(ren m "v")` | `v`'s renaming into the pattern's slots; a literal comes back as `{0 -> slot}` |
| `(node-slots m uncovered covered bound)` | a built node's free slots from its named columns; `(without m slots bound)` for a built child under a binder |

### The compiled rule, plainly

What a rewrite means as one egglog rule, for `sum-fact-3`, with the `_0` that says
which sort's tables these are dropped from the table names. Names in quotes are the
rule's own variables and literals, so a frame is keyed by the words the rule was
written in. This schematic rule explains the match and action together. The compiler
emits separate matching, application, and draining rules, with refinement-index
generation between the first two stages, and constructs inner nodes canonically.
The listing assumes `Idx` covers every refinement; it does not itself implement
that schedule. Part II gives the emitted arrangement.

```
(rule (;; egglog's own match of the two atoms, one row pattern each: an ordinary
       ;; column is an edge and a class, a binder column an edge and the variable
       ;; class (Var 0)
       (= cls_p (Sum e0_R cls_R e0_lit_x (Var 0) e0_lit_y (Var 0) e0_t1 cls_t1))
       (= cls_t1 (Sing e1_e1 cls_e1 e1_e2 cls_e2))
       ;; _t1 is bound by the first atom and read again by the second, so the second
       ;; reading may differ by a symmetry of its class: the whole group goes to the
       ;; binding, and the frame decides the element (C5)
       (= grp_t1 (EclassGroup cls_t1))
       ;; what each atom's columns say about slots: each binding names the column's
       ;; variable or literal, its edge, and the exact slots of its class (C2, C4, C7)
       (= atom_p (atom "_p" (root "_p" (ClassSlots cls_p))
                            (child "R" e0_R (ClassSlots cls_R))
                            (bound "$x" e0_lit_x) (bound "$y" e0_lit_y)
                            (child "_t1" e0_t1 (ClassSlots cls_t1))))
       (= atom_t1 (atom "_t1" (root "_t1" (ClassSlots cls_t1) grp_t1)
                              (child "e1" e1_e1 (ClassSlots cls_e1))
                              (child "e2" e1_e2 (ClassSlots cls_e2))))
       ;; the two joined: where they share _t1 the occurrences are identified (C6);
       ;; nothing here if a clique breaks
       (= f (frame-join atom_p atom_t1))
       ;; spelled in the root's class slots, then every reading of _t1 the rest of the
       ;; frame allows and every consistent merging of what the pattern left open (C8)
       (= refined (refinements (anchor f "_p")))
       (= refined_len (vec-length refined))
       ;; one refinement per index; `vec-get` is partial past the last (C8)
       (Idx refined_len choice)
       (= m (vec-get refined choice))
       ;; the side conditions, read off the refined frame (C9)
       (not-free m "$x" (names "e1"))
       (not-free m "$y" (names "e1")))
      (;; the right-hand side bottom-up, each column's renaming read out of m
       (let built_sum (Sum (ren m "R") cls_R (ren m "$x") (Var 0) (ren m "$y") (Var 0) (ren m "e2") cls_e2))
       ;; the built node's free slots: R's image, and e2's with the bound $x, $y taken out
       (let built_sum_slots (node-slots m (names "R") (names "$x" "$y" "e2") (names "$x" "$y")))
       ;; a built child sits at the identity, its slot set as the edge
       (let built_sing (Sing (ren m "e1") cls_e1 built_sum_slots built_sum))
       ;; the root's own slot set, which the union below does not need
       (let built_sing_slots (map-union (node-slots m (names "e1") (names) (names)) built_sum_slots))
       ;; anchored at _p the root's renaming is the identity, so the equation the rule
       ;; means is egglog's own union (C11)
       (union built_sing cls_p)) :name "sum-fact-3")
```

A right-hand side that is a bare variable is not a union: its renaming need not be the
identity, so the rule states `(Equated cls_root (ren m "a") cls_a)` and the machinery
orients it. A right-hand side that is a call, `(subst body $x t)`, is answered by the
`slotted-subst` primitives, which copy one representative of the body and return an
invocation that `SubstPending` carries back into the root's frame (C12).

### When the rules run

A user step is `(seq (run) MACHINERY)`: the rules, then the machinery to a fixed
point, so a step means one round of every rule against a settled graph. The listings
above abbreviate maintenance into one `slotted` ruleset. The compiler separates
matching from application, generates every needed refinement index between them,
and phases maintenance as follows:

```
(seq (saturate (seq (saturate (run slotted))
                    (saturate (run slotted-migrate))
                    (saturate (run slotted-group))
                    (run slotted-shape)))
     (saturate (run slotted-read)))
```

`slotted` is the core: leaders, slot sets, the closure of the edges. `slotted-migrate`
moves rows and parents onto leaders; `slotted-group` derives each class's group from
its rows' symmetries and closes and restricts it; `slotted-shape` holds the shape
walks and the row dedup; `slotted-read` the coset readings and their index. Each phase
reads what the ones before it settle -- a migration reads leaders, a group reads the
rows where they now live, a shape walk enumerates its children's groups, a reading a
class's own -- so each waits for the ones before it: the walks once per settled state
in an outer loop, the readings once at the very end, since nothing in the core reads
them and a matching rule only runs after. Run together instead, MMM's second phase
walked each `Binop` row thirteen times over, migrated rows twice that then moved
again, and rebuilt groups that a pending migration was about to change; phased, it
runs a third faster and TTM's second phase 40%. The dedup has to share the walk's
phase, and *One row per shape per class* says why.

# Part II. What the generator adds, and why

These choices reduce repeated work and duplicate storage. They are intended to
preserve the decoded graph and the specified matching and substitution policies.
The suite checks the resulting implementation against the multipattern reference;
it does not run a version with all these choices removed. Timings quoted in this
section are historical development measurements, not a reproducible ablation table
for the current revision.

## One row per shape per class

The index says which rows are one node; it removes none. A class can still hold two
rows of one node under two readings: the same node built twice in different frames,
or a node and its image under a symmetry of a child. Every such row is matched, indexed
and migrated again; this caused the version without deduplication to stall on
`redundancy-tests.egg` during development.
One row is enough, and one is what the reference's hashcons keeps. The merge block has
already recorded the symmetry between the two readings, and a pattern reaches the
other reading through the class's group and its children's (C5). So the shape walk
writes the shape into `_shapeof_Add` -- the least spelling of its edges over
its children's groups, the renaming back, and the node's symmetries, as columns -- and
where two live rows of one class have the same children and the same shape, the one
whose edges, as a vector, are the greater is deleted. Both rows are matched as rows,
so the rule only ever compares nodes that exist, and comparing the rows whole is what
makes exactly one of any two go.

```
(function _shapeof_Add (Renaming Group Renaming Group)
  (Renaming Renaming Renaming Group) :no-merge)

;; written by the shape walk of the index rule, from the same `node-shape`
       (set (_shapeof_Add m1 g1 m2 g2)
            (values (vec-get sh 0) (vec-get sh 1) (vec-get sh 2) (symmetries-of sh 3)))

(rule ((= c (Add m1 c1 m2 c2))
       (= g1 (EclassGroup c1)) (= g2 (EclassGroup c2))
       (= (values s1 s2 b1 syms1) (_shapeof_Add m1 g1 m2 g2))
       (= c (Add n1 c1 n2 c2))
       (= (values s1 s2 b2 syms2) (_shapeof_Add n1 g1 n2 g2))
       (= v1 (vec-of m1 m2))
       (= v2 (vec-of n1 n2))
       (!= v1 v2)
       (= v1 (ordering-max v1 v2)))
      ((delete (Add m1 c1 m2 c2))) :ruleset slotted)
```

The cache key contains the computation's immutable inputs: edge maps and group
values. A changed child group selects a different entry. Child class ids are absent,
so a native union cannot merge an obsolete cached result over a current one. The
symmetry rule and deduplication both read the entry for the current child groups.

## One reading per coset of the pinned slots

A nested pattern reads a class through one column of a parent row, and in Part I the
frame decides its reading among the class's whole group, one refinement per element
that fits. When the whole group was enumerated as query rows, the TTM workload's
second phase gave `let-binop3` 166,415 distinct matches at the fixed point where the
reference matcher makes some 14,000 over its whole run, and `sum-merge` ran the frame
primitives on 150,944 candidates to keep 188.

Two readings whose inverses agree on the slots the parent's *other* columns pin,
and differ only on the rest, spell the parent row the same way up to a renaming of the parent's own
slots — a symmetry of the parent's class, which the shape rule derives from that very
row — so what the rule builds from one of them differs from the other's by that
symmetry, and one of each coset suffices. Quotienting the readings this way took
`let-binop3` to 15,513 and the workload from 67 s to 23 s; the matrix-multiplication
workload went from 18.7 s to 9.1 s. This is the reference matcher's
`get_group_compatible_weak_variants`, which enumerates a node's variants modulo its weak
shape.

`group-coset-reps` picks the least element per inverse action on the pinned slots.
A reading maps the nested node's slots into the frame shared with its parent, so
the parent's other columns pin images of that permutation. Grouping by its forward
action instead can omit matches: in the symmetric group on three slots, three
representatives with distinct `g(0)` need not have distinct `g⁻¹(0)`.
The readings live in `CosetReps`, keyed by the class and the pinned slots, with
`Reading` as their index: a row per element, read out by its position through
`GroupIdx`, deleted when the set no longer holds it, and refused outright past
`GroupIdx`'s 512 entries; a class has few distinct keys, however many rows read it.
The index join is in two tiers: the first eight positions are joined with every set,
and the positions past them only with the sets a `BigReading` row says reach them --
filtering the sets by length inside the join itself cost a fifth of MMM's second
phase, most of it in iterations where nothing matched.
Each row records the key its columns give, in `_pinned_Add`, so a matching rule that
holds the parent row looks the key up and joins the readings on it exactly — egglog
cannot join on a value a primitive computes inside the same rule, and keying the
readings by row instead multiplied the index's work by the number of rows. One rule per
child column that is not a binder; a binder column's child is the variable class, which
no atom reads, though its edge pins its slot. A claim's subterms are read the same way,
parent first.

```
(function CosetReps (Math Renaming) Group :merge new)
(relation Reading (Math Renaming Renaming))
(function _pinned_Add (Renaming Math Renaming Math i64) Renaming :merge new)

(rule ((= row (Add m1 c1 m2 c2))
       (= grp (EclassGroup c1))
       (= pinned (map-domain (compose (map-image m2) m1))))
      ((set (_pinned_Add m1 c1 m2 c2 1) pinned)
       (set (CosetReps c1 pinned) (group-coset-reps grp pinned))) :ruleset slotted)
(rule ((GroupIdx i) (= s (CosetReps c pinned)) (= g (set-get s i)))
      ((Reading c pinned g)) :ruleset slotted)
(rule ((Reading c pinned g) (= s (CosetReps c pinned)) (set-not-contains s g))
      ((delete (Reading c pinned g))) :ruleset slotted)
(rule ((= s (CosetReps c pinned)) (= grp (EclassGroup c))
       (= fresh (group-coset-reps grp pinned)) (!= s fresh))
      ((set (CosetReps c pinned) fresh)) :ruleset slotted)
(rule ((= s (CosetReps c pinned)) (> (set-length s) 512))
      ((panic "a class has more readings than GroupIdx indexes")) :ruleset slotted)
```

The repair rule is there because `:merge new` is not a function of the state: when
egglog merges two class ids, two `CosetReps` rows fall onto one key and whichever
egglog took as the newer survives, which can be the one written under the smaller
group -- a reading missing, a claim that cannot find a row that is there
(`binder-tests.egg`). A stored set that disagrees with the group as it stands is
rewritten, and the correct value is a fixed point.

In the compiled rule the nested root's group becomes a lookup, a join, and one reading
handed to the binding:

```
       (= pinned_t1 (_pinned_Sum e0_R cls_R e0_lit_x (Var 0) e0_lit_y (Var 0) e0_t1 cls_t1 4))
       (Reading cls_t1 pinned_t1 sym_t1)
       (= atom_t1 (atom "_t1" (root "_t1" (ClassSlots cls_t1) sym_t1) ...))
```

A repeated occurrence that is not a nested root — a pattern variable written twice —
keeps the whole group in its binding: the rest of the pattern pins both occurrences'
slots, so the frame finds the one element that fits, or none, at no cost to the join.

## Store the match before acting

egglog joins a body's table atoms first and runs its primitives afterwards, once per
matched row. The plain rule joins `Idx` beside the frame primitives, so every frame is
built once per index. So the generator emits one relation and three
rules per rewrite: the first finds a match and stores its refinements and the classes
the action reads; the second, in the `slotted-apply` ruleset, joins the stored row
with `Idx`, reads one refinement, checks the conditions and acts; and the third deletes
the row once that phase has read it (C13). On the matrix-multiplication workload's
first phase this took the run from 1.16 s to 0.18 s with one thread, the user rules'
apply time, where `--timing-summary` books the primitives, falling from 820 ms to
about 20 ms.

The first rule seeds `Idx(length, 0)` for each nonempty refinement vector. Before
the apply phase, `slotted-refine` fills the indices for each length: each index
offers children `2*i+1` and `2*i+2` below that length. Equal lengths share their
indices. Index generation takes logarithmically many rounds, and a short vector
never scans indices belonging only to longer vectors. Neither frame enumeration
nor index consumption has a fixed alternative limit.
The stored match includes the length as a column, so this restriction is a table
join rather than a primitive filter applied after joining all lengths.

```
(relation _matched_sum-fact-3 (Frames i64 U U U U U))

(rule ((= cls_p (Sum e0_R cls_R e0_lit_x (Var 0) e0_lit_y (Var 0) e0_t1 cls_t1))
       ...
       (= refined (refinements (anchor f "_p")))
       (= refined_len (vec-length refined))
       (> refined_len 0))
      ;; the match, stored: its refinements and every class the action will read (C13)
      ((_matched_sum-fact-3 refined refined_len cls_p cls_R cls_t1 cls_e1 cls_e2)
       (Idx refined_len 0)) :name "sum-fact-3")

(rule ((_matched_sum-fact-3 refined refined_len cls_p cls_R cls_t1 cls_e1 cls_e2)
       (Idx refined_len choice)
       (= m (vec-get refined choice))
       (not-free m "$x" (names "e1"))
       (not-free m "$y" (names "e1")))
      (...the right-hand side, as below...
       (union built_sing cls_p))
      :ruleset slotted-apply :name "sum-fact-3/apply")

;; the stored match is spent, whether or not a refinement passed the conditions
(rule ((_matched_sum-fact-3 refined refined_len cls_p cls_R cls_t1 cls_e1 cls_e2))
      ((delete (_matched_sum-fact-3 refined refined_len cls_p cls_R cls_t1 cls_e1 cls_e2)))
      :ruleset slotted-apply :name "sum-fact-3/drain")
```

A user step becomes `(seq (run) (saturate (run slotted-refine)) (run slotted-apply) MACHINERY)`, where `MACHINERY`
is the phased saturation of *When the rules run*. egglog
finds every match of a ruleset before it applies any action, so the drain never hides
a row from the acting rule, and a row is gone after one phase whether or not a
refinement passed the conditions; a match that recurs after the machinery has changed
its nodes is found afresh.

Substitution also depends on the body's extracted representative, which can improve
without changing the matched `Let` row. Both its match-producing rule and its apply
rule use `:naive`, so each user round revisits those matches even when their explicit
query inputs are unchanged.

## Build below the root canonically

The plain action spells every node it builds in the frame's own slots. Two rules that
build one node in two frames then write two rows and reach two egglog values denoting
one class, and the machinery has to find them equal, migrate the rows of one into the
other, point every parent at the survivor and close the edges that all of that adds.
That cascade runs per built node; removing it made the second-phase workloads three
times faster. So a node below the root is emitted with its edges through `shape`
first, in the canonical numbering and not in this rule's, and its edge into its parent
is the renaming back to the frame, narrowed to the slots the node leaves free (C16).
The root keeps the frame's spelling, since the action unions it with the root's class
and an invocation there must be at the identity (C11), and `union` disposes of it at
once.

```
(let shape_sum (shape (ren m "R") (ren m "$x") (ren m "$y") (ren m "e2")))
(let built_sum (Sum (vec-get shape_sum 0) cls_R (vec-get shape_sum 1) (Var 0)
                    (vec-get shape_sum 2) (Var 0) (vec-get shape_sum 3) cls_e2))
(let built_sum_slots (node-slots m (names "R") (names "$x" "$y" "e2") (names "$x" "$y")))
;; the frame's names for those slots, read off the canonical ones; `compose` drops a
;; canonical slot the node binds
(let built_sum_edge (compose built_sum_slots (vec-get shape_sum 4)))
(let built_sing (Sing (ren m "e1") cls_e1 built_sum_edge built_sum))
```

## A follower keeps nothing

Every rule that reads a group reads it off a class a row or a child column names, and
those are leaders, so a group on a value that has a leader is a copy nothing reads —
one row of it per member per group element, which was most of the edge relation. It is
emptied, and its index rows go with it through the view rules; emptied rather than
deleted, because the view can only follow a set that is there to compare against. Its
identity edge goes too.

```
(rule ((= s (EclassGroup f)) (> (set-length s) 0) (RenamesToLeader f m l) (!= f l))
      ((delete (EclassGroup f))
       (set (EclassGroup f) (set-empty))) :ruleset slotted)
(rule ((RenamesToLeader f g f) (RenamesToLeader f m l) (!= f l))
      ((delete (RenamesToLeader f g f))) :ruleset slotted)
```

## Inside the primitives

Three of the primitives do more than their signature says, for the same reason.

`node-shape` walks the product of the children's groups once and returns the canonical
edges, the renaming back, and the node's own symmetries together, so the key and the
symmetries cost one walk, with `_shapeof_F` carrying both to their consumers.

Interned frames share immutable storage, so reading a frame in a primitive does
not copy its partition or slot maps. `vec-get` and `vec-length` borrow the vector's
storage as well; selecting one refinement does not copy all its siblings.

`group-coset-reps` chooses the least element of each coset, so the reading a rule sees
does not depend on the order egglog stored the group in.

`slotted-subst` copies one representative of the body — the smallest term, and among
equal sizes the least canonical spelling, so every run copies the same one — and that
choice reads the constructor tables, class slots, and layout metadata. Within one
rule-application phase every insert is staged: the execution state owns the parsed
nodes, chosen terms, and memo of results shared by the class and frame primitives.
A call then walks only its own term.

The extraction cost is tree size, counting each child occurrence with exact integer
arithmetic on both sides. This keeps a parent's cost strictly above its children's,
even when a compact shared graph represents a tree larger than a machine integer.
Tie-breaking
templates share their children rather than copying their expanded token sequences.
Each edge carries its public-slot renaming. Every active traversal occurrence owns a
local namespace for its internal slots; no space or integer range is reserved for
all the private slots in the expanded tree. A lazy byte iterator numbers slots by first occurrence and compares
the same canonical spelling as before, stopping at the first difference; a class with
one smallest candidate needs no spelling comparison. Sharing changes storage, not
the extraction objective or tie-break. The multipattern reference keeps its independent,
expanded-template implementation to check that the optimized encoding agrees.

# The contract

What a compiled rule asserts, clause by clause; `compile_query` and
`compile_rule` in `slotted-encoder.py` name these where they emit them. The curated
regressions and differential comparisons exercise these requirements.

**C1. A pattern variable is an invocation.** `x` is a class `cls_x` and a renaming
`(ren m "x")` of that class's slots into the pattern's. Two occurrences agree when
they reach one class by renamings that differ at most by a symmetry of it
(Definition 6). Requiring identical renamings misses symmetric matches; comparing
classes alone accepts invocations that may name different slots.

**C2. Atoms, and the frame.** The left-hand side is flattened into depth-1 atoms,
one per e-node, every child a variable or a literal. Each atom's columns are one
`atom`, and the frame is their `frame-join`. Nothing is ordered: an atom is a function
of its own node's edges, the join is associative and commutative, and the left-nested
tree the compiler writes means nothing. A slot no equation reaches is a placeholder, a
block of its own.

**C3. Atoms are written in a connected order.** `connected_order` puts each atom
after one it shares a variable with, parent before child. Under frames this is only a
convention for readable output; the answer does not depend on it, and `xarray.py`
checks that.

**C4. A variable's renaming is no wider than its class.** Every binding carries the
class's exact slots, `(ClassSlots cls)`, and the frame's occurrences of `v` are those
slots and no others; a node may carry a slot its class has made redundant, and that
slot is the node's alone -- an occurrence like any other, which a variable bound
through it may meet again elsewhere (*Against the reference*, below).

**C5. Repeated occurrences are compared up to symmetry.** A further occurrence of a
bound variable is read through some element of its class's group, so the match
quantifies over the group. The root of a nested atom — a flattener temp, met once as a
column of its parent — looks up the slots the parent's other columns pin in
`_pinned_F`, joins `(Reading cls_x pinned sym_x)`, one row per coset of those slots,
since readings that differ elsewhere are related by a symmetry of the parent's class
the shape index derives, and hands `sym_x` to its binding. Any other repeated
occurrence hands its binding the whole group, `(EclassGroup cls_x)`, and
`refinements` decides the element once the rest of the frame has pinned both
occurrences' slots. A claim compares the two terms' renamings up to the root class's
group with `coset-same`.

**C6. Where two atoms agree on a variable, their occurrences are one.** The join
identifies `Node(a, e(t))` and `Node(b, e'(t))` through `Var(v, t)`, which is the
reference's `unify`, and fails only where that breaks a clique.

**C7. A slot literal is solved, and different literals differ.** `$x` in a column is
read off the node's slot there; the same literal written twice names one slot; two
different literals are two blocks, by the literal clique. In a binder column a
literal is the bound slot (`bound`), and only a literal may stand there.

**C8. Placeholders are refined last.** `refinements` enumerates every consistent way
to merge the blocks a variable or a carried literal reaches -- never two literals, never
two slots of one node or class -- as a `Vec` with the frame itself first, and the rule
reads one per `(Idx refined_len choice)` with `vec-get`.
`slotted-refine` generates every required index before any match is applied, so
all alternatives act within the same user round. This is the reference's `final_refine`.

**C9. Conditions are read after refinement.** `free` and `not-free` are facts over the
refined frame. A matched binder's slot may be read as any name, a free variable's
included, so a rule whose right-hand side rebinds such a slot over a variable matched
outside the binder owes `(not-free $s v)`; `capture_guards` derives what it owes.

**C10. A right-hand-side slot the pattern never pins is fresh.** `mint` adds it after
refinement, apart from every slot the match named; the reference writes
`Slot::fresh()` where the encoding has to invent a name.

**C11. An action is a union in the root's frame.** The frame is anchored at the
rule's root, so the root's renaming is the identity by construction, and the right-hand
side, built bottom-up in the frame's slots -- one `let` per node and one `node-slots`
for its slot set -- is an invocation in the root's own frame. egglog's `union` is then
exactly the equation the rule means, and the machinery's `ClassSlots` merge makes any
slot the two sides disagree on redundant. The one action that is not a union is a
right-hand side that is a bare variable `a`: `a`'s renaming need not be the identity,
so the rule states `(Equated cls_root (ren m "a") cls_a)` and the machinery orients it.

**C12. A right-hand side that is a call is answered by a primitive.** `(subst body $x
t)` cannot be built as a node: `slotted-subst` copies one representative of the body
-- the smallest term, and among equal sizes the least canonical spelling, so every run
copies the same one -- and returns an invocation, which `SubstPending` carries back
into the root's frame.

**C13. A match is stored before it is acted on.** egglog runs a body's primitives
after its table join, once per row, so a rule that joined `Idx` beside its frame
primitives would build the frame once per index. Instead the matching rule stores each
match, its refinements and the classes the action reads, in a relation of its own, and
a rule in the `slotted-apply` ruleset joins that row with `Idx`, reads one refinement,
checks the conditions and acts, and a third rule in that ruleset deletes the row. The
schedule completes refinement-index generation between matching and applying, so a
step still means one round of every rule, with every stored alternative consumed.

**C14. Nodes are indexed by shape.** `node-shape` considers the symmetric readings
of a row's children and selects one canonical shape. The row is inserted once into
the shape index, together with its class and the renaming from the shape into that
class. A collision states an equation between the classes. The same shape walk also
finds self-symmetries, which enter the class's group after restriction to its slots.
Of two rows of one class with one shape, the greater reading is deleted. This
implements the reference's shape hashcons using `weak_shape` over
`get_group_compatible_variants`.

**C15. A renaming is spelled on its classes' slots.** Every `RenamesToLeader` row's
renaming has its domain within the leader's class slots and its image within the
follower's, and every element of `EclassGroup` within the class's own. Orientation
restricts a renaming as it enters, a later narrowing restates it, and the rules that
delete rows act only on restricted ones. An entry on a slot a class has dropped says nothing about the
class, but it makes two spellings of one edge two rows, and every rule that composes
renamings then multiplies the spellings.

**C16. A built node below the root is spelled canonically.** Its edges go through
`shape` and its edge into its parent is the renaming back to the frame, narrowed to the
slots the node leaves free. This is the one place the encoding writes something other
than what the rule says, and it changes no answer: the node is the same node, spelled
in the numbering every frame agrees on, so two rules that build it write one row and
reach one value. The root keeps the frame's spelling (C11).

# Against the reference

The side to match is the reference crate's multipattern matcher, `ref-multi` -- the
pattern language the encoding implements -- and the goal is the same e-graph: the same
classes, slots, groups, and nodes up to a verified isomorphism. `slotted/eval.py`
compares the final graphs and says `isomorphic`, `different`, or `inconclusive`.
It attempts witness search on every available graph pair, using compact interned
class and slot signatures and explicit search/node-variant work limits. Counts and
probe partitions cannot override an exact rejection or establish equality. With
counts enabled, class and node counts are also checked separately before witness
search. They remain visible even if search is inconclusive, and a count mismatch
rejects the comparison without trusting the isomorphism checker. Missing counts or
unverified `ref-multi` comparisons fail the command when both encoding and
`ref-multi` are selected; loading a saved report also requires equal counts as well
as a verified verdict. Each comparison records the encoding and reference observation
IDs. A merged report replacing either observation marks the old comparison inconclusive;
it cannot reuse an earlier witness verdict just because the counts still match. Workload
identity includes the rule count. Graph collection records why counts are unavailable,
including timeouts and symmetry-enumeration limits; unexpected reader errors propagate.
The JSONL is a versioned disposable cache, and old schemas require recomputation.
Goal outcome, elapsed seconds, and graph size have separate columns. Each side's
goal is checked independently, and any unsuccessful goal fails the command even
when the graphs are isomorphic. The nested matcher can miss a goal that the encoding
reaches; agreement with it is not required for correctness. Elapsed seconds measure
the whole run, including unsuccessful runs, rather than time to a successful goal.
Both Markdown and HTML reports start with a compact table in the paper's Table 1
layout: systems grouped under each workload, with budget, goal, elapsed seconds,
nodes, classes, and saturation. Budget means the configured round limit, not the
number of completed iterations. The full diagnostic table follows; `--long` changes
only that full table. Both views use the same observations and preserve failed goals
and missing results.
Three things had to
be made the same, each established on a minimal case the harness keeps:

- *Substitution picks the same term.* `beta` substitutes into one term of the body's
  class, and which term decides which rows the graph holds from then on. The encoding
  takes the smallest term, ties broken by a canonical spelling (`sort/slotted/subst.rs`,
  `cheapest`), from the e-graph as the round began, since `beta/apply` runs in one
  apply phase whose reads are that snapshot. The parsed terms and substitution results
  belong to that execution state and are shared by its workers and the two result
  primitives. A new phase starts with an empty cache, including after `push`/`pop`
  or an e-graph clone; constructor, class-slot, and layout changes are all observed.
  The crate's own methods read the graph at
  application time, after the round's earlier unions, and its default takes the node a
  class was created with -- history the encoding cannot replay. So the oracle harness
  substitutes as the encoding does: `slotted/xmulti`'s `SnapshotSubst` takes the
  smallest term per class at each round's start, the same tie-break over the same
  constructor names (`ctor` lines in the spec, from `eval.py`), and is the harness's
  default (`XMULTI_SUBST=syntactic` restores the crate's). Without it, ΣMMM's second
  phase ended with 71 classes against the
  reference's 75, eight reference classes split; with it the partitions agree.
- *One row per node.* The shape walk folds a row and its image under a symmetry of a
  child (*One row per shape per class*), as the reference's hashcons does. Before, the
  encoding kept both -- an extra `sum` row per such reading on MMM's first phase -- and
  `cheapest` could pick a spelling the reference never holds.
- *A redundant slot unifies, on both sides.* `let x = var(r) in var(a)` sits in the
  class of `var(a)` carrying `r`, which its class does not. The frame reads the slot as
  an occurrence like any other (C4), so on `binop f (var a) (var b)` the pattern
  `(Binop f (Let e1 $x e2) (Let e1 $x e3))` finds `e1` with the two lets' redundant
  slots read as one -- soundly, since the class's meaning does not depend on the slot.
  The multipattern matcher's `unify` and `final_refine` do the same. The crate's nested
  matcher, the one the paper's experiments ran, gives such a slot a fresh name on every
  use and finds no `e1`, which is why `ref-nested` holds fewer `sdql-let` rows than
  either. The encoding follows MultiPattern's treatment of redundant slots.

With the three in place, ΣMMM's and MMM's first and second phases have verified
isomorphism witnesses against `ref-multi`. The former `same rows` label was only a
probe/count diagnostic and could miss different symmetry groups; those records must
be recomputed. TTM's second phase remains unverified:
`ref-multi` did not finish it within the artifact's 300 s in the recorded evaluation.

**The nested performance baseline.** `eval.py` explicitly selects `snapshot` for
`ref-multi` and `syntactic` for `ref-nested`, overriding ambient `XMULTI_SUBST` on
both the timed and counting runs. The binary reports the selected policy and each
evaluation row records it. Syntactic substitution does not build our extraction
snapshots. Nested results are diagnostic; their counts and graph are not expected
to match the encoding, since both the matcher and substitution policy differ.

This follows the artifact at commit `83f2e5b`: the
[SDQL beta rule](https://github.com/memoryleak47/slotted-egraphs-artifact/blob/83f2e5b/sdql/slotted/src/rewrite.rs)
uses direct term substitution, and its `EGraph::new()` selects
[`SynExprSubst`](https://github.com/memoryleak47/slotted-egraphs-artifact/blob/83f2e5b/sdql/slotted/slotted-egraphs/src/egraph/mod.rs).
That method reconstructs the stored syntactic term; the library also offers
`ExtractionSubst`, which chooses a smallest AST, but the SDQL runner does not select
it. The SDQL runner separately extracts the final optimized program with `SdqlCost`.
The paper's egg/SDQL baseline uses
[`BetaExtractApplier`](https://github.com/memoryleak47/slotted-egraphs-artifact/blob/83f2e5b/sdql/baseline/src/sdqlsubstitute.rs)
on cached `beta_extract` expressions, so that side does use extraction-based substitution.
The array experiment uses explicit let-rewriting instead of direct substitution,
as stated in the paper's footnote 4. We retain the pinned modern reference revision
for both matchers, so this baseline reproduces the substitution choice, not the
entire historical implementation.

**Rounds.** The evaluation runs the paper's budget on every side; the reference stops
early when a round applies nothing new and reports that, and the encoding is asked
after its budget whether one more round changes table cardinalities. A timeout or
missing graph leaves equivalence inconclusive; it is never evidence of saturation
or graph equality.

# Where the pieces live

| path | what it is |
| --- | --- |
| `slotted/LANGUAGE.md` | the source language: every form and why it exists |
| `slotted/slotted-egglog.py` | the compiler — a program in that language to egglog |
| `slotted/slotted-encoder.py` | the encoding itself: the tables above, and rule compilation |
| `egglog/src/sort/slotted/` | matching frames, substitution, renaming and group algorithms, and their primitive registration |
| `slotted/tests/` | tests written in the source language |
| `slotted/xdiff/` | the differential harness against `memoryleak47/slotted-egraphs` |
| `slotted/xmulti/` | the reference oracle, pinned to an exact revision |
| `slotted/paper_fixtures.py` | the paper's ten SDQL workloads from the artifact: translation, Table 1's numbers, the generated tests |
| `slotted/eval.py` | collection and correctness checks for the paper's two case studies; `make slotted-eval` |
| `slotted/eval_report.py` | observation records, cache loading, and the summary/full tables; launches no benchmarks |
| `spot-check.py` | independent Array N=0 spot check: explicit reference multipatterns, direct live-row/leader counts, one timed run per side; imports no eval or differential-checking scripts |

Nothing here is hand-maintained egglog: the machinery is generated from the
constructors a program declares, so a worked example is a program you run
through `--desugar`, not a file to keep in step by hand.
