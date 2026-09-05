# Compiling user rules into the slotted encoding

Companion to these runnable files:

| file | what it is |
| --- | --- |
| `slotted/encoding/egraph-encoding-11.egg` | the machinery: union, congruence, redundancy, symmetry |
| `slotted/tests/user-rules.egg` | the tutorial: one shape of user rule per section — M1–M11 — each stated as prose plus the single rule a compiler emits, and nothing else. All eleven are a real rewrite, from `sdql_rules()` or the paper's §4.1 array language, and each is exactly what `slotted-encoder.py` emits for it: `slotted/check-tutorial.py` compares every one against the encoder's output and allows only a renaming of the variables. M6 and M9 are the same rule (`eta`) at two atom orders, since the lead is a compile-time choice. The shapes no rewrite produces on demand — a multi-rooted left-hand side, two mints in one match, a child wider than its class — are hand-built e-graphs in the fixture block of `slotted/tests/user-rules-tests.egg`, whose rules are still the encoder's output |
| `slotted/tests/user-rules-tests.egg` | the cases for it: it includes the tutorial, then adds the terms, schedules, assertions and counter-examples |
| `slotted/LANGUAGE.md` | the slotted language as a reference: every form it adds to egglog and why, including the two kinds of equality and the example that separates them |
| `slotted/slotted-egglog.py` | compiles a test written in the SLOTTED language — its own `(constructor ... :binder ...)` declarations, then terms, `rewrite`s and `(check (= a b))` — into a self-contained egglog program: the hand-written core, the machinery for exactly the constructors declared, and the compiled body. It includes no generated file, so nothing sits between a test and running it. Its `=` is COMPILED, not egglog's: `(RenamesToLeader f m l)` is `f = m*l`, and two terms are equal when ONE renaming reaches both from the leader -- Def. 6, two invocations agree when the renaming between them is a symmetry of the class. Landing in the same class by *some* renaming is weaker and is spelled `renaming-=`; the pair that separates them is two alpha-variants whose free slot is renamed, one class but not equal. `slotted/LANGUAGE.md` is the reference for the language |
| `slotted/slotted-encoder.py` | the recipe as code: the machinery emitter, the term encoding and the rule compiler, which every generator below goes through |
| `slotted/xdiff/xdiff.py` | differential tests against the reference implementation |
| `slotted/languages/sdql.egg` | the paper's `sdql` language and all 43 of its rewrite rules, in the SLOTTED language. `gen-sdql-rules.py` compiles them for the .egg tests and the differential harness, and `slotted-egglog.py` compiles the same file to run it; neither restates a rule |
| `slotted/languages/array.egg` | the same, for the paper's §4.1 array language and its 8 rules. `xarray.py` builds its rule objects from this file |
| `slotted/tests/paper/` | the reference crate's own suites, in the SLOTTED language and standalone, one file per test there so the two diff side by side: `var-xy-eq-yz`, `fgh-transitive-symmetry`, `enode-collisions` (3.4), `figure-3`, `redundancy-orbit` (3.5 step 1) and `two-redundant-slots` (Def. 8) |
| `slotted/tests/symmetry-tests.egg` | where a class's symmetry group comes from and what has to follow: closure, composition down a union chain, congruence to a parent, and matching a repeated pattern variable up to a symmetry |
| `slotted/tests/binder-tests.egg` | rules that reach under a binder, whose pattern IS a binder, and that introduce one with `:fresh` -- each paired with the shape that must not fire |
| `slotted/tests/redundancy-tests.egg` | redundancy from a rewrite rather than a union, and a match that only exists after one. Ends with the shape that still fails, written out |
| `slotted/tests/rewrite-tests.egg` | the project's original tests, ported off the pre-compiler encoded form |
| `target/slotted/slotted-array-rules.egg` | what those 8 compile to, self-checking |
| `slotted/xdiff/xarray.py` | the same 8 rules, differentially tested against the reference |

Semantics come from Schneider et al., *Slotted E-Graphs*, PLDI 2025
([PDF](https://steuwer.info/files/publications/2025/PLDI-Slotted-E-Graphs.pdf),
[code](https://github.com/memoryleak47/slotted-egraphs)) — mainly Definition 6
(when two invocations are equal), Definition 8 (which e-nodes an invocation
stands for), §3.5 (union) and §3.6 (matching).

A note on the numbers below: a `before | after` table measures one specific change at
the time it was made, so its suite totals are that day's, not today's. Current totals
live in the commit that last moved them. Claims about how the encoding *works* are kept
current; historical measurements are left as measured.

## Vocabulary

Only three terms are needed.

A **slot** is a variable name. An e-class is parameterised by the slots of the
terms it holds, so referring to one means saying what goes into each slot — an
**invocation**, written `m*c` for a class `c` and a renaming `m`. (The paper calls
this a *renamed id*; the Rust crate calls it an `AppliedId`.) A **renaming** is a
one-to-one map between slots.

Slot names are local. `(Var 0)`'s `$0` and some `f` node's `$0` are unrelated
names that happen to look alike, so relating one class's slots to another's always
means writing down a renaming.

Notation used below:

| | |
| --- | --- |
| `(compose a b)` | `b` first: `(compose a b)[x] = a[b[x]]` |
| `(App f m1 c1 m2 c2)` | the node `f(m1*c1, m2*c2)`; each `mi` maps its child's slots into the node's |
| `(RenamesToLeader a m b)` | `a = m*b` |
| `(RenamesToLeader c m c)` | `m` is a symmetry of `c` |
| `(find-mapping a… b…)` | the least `m` with `m ∘ bi = ai`; fails if no one-to-one `m` exists |

Note `compose` runs in the opposite order from `SlotMap::compose` in the crate.

Two facts about the machinery that matter later. A slotted e-class is **not** one
egglog e-class: nodes equal up to renaming are linked by `RenamesToLeader` and one
is deleted, so a slotted class is a set of `U` values sharing a leader. And every
`(Var v)` collapses to `[0↦v] * (Var 0)`, so the leaves are one class, not many.

## The model

**A rule variable is an invocation, not a class.** So a user variable `x`
compiles to two egglog variables: the class `X`, and a renaming `mx` carrying
`X`'s slots into the pattern's.

The pattern's slots are not invented. One atom is chosen as the **first atom**,
its matched node's slots *are* the pattern's, and its own renaming is therefore
the identity and never written down.

## Compiling a rule body

**Step 1 — flatten.** Rewrite the left-hand side as depth-1 atoms

```text
?v == (Op ?c1 ?c2)
```

one per e-node, every child a bare variable. This is `MultiPattern` in the crate,
and it is already the shape of an egglog rule body, which is what makes the rest
mechanical. `(f (g ?x) ?y)` becomes `?t == (f ?u ?y), ?u == (g ?x)`.

Flattening is not always meaning-preserving: a nested pattern is matched under one
renaming for the whole pattern, a flattened one gets a renaming per atom. A slot
written both under a binder and outside it therefore means different things in the
two forms, and the binder escapes. A flattener must reject or rename those.

**Step 2 — order the atoms so each one shares a variable with the ones before
it.** This is a correctness condition, not a heuristic. An atom sharing nothing
has no constraint on its renaming, so every slot it needs is *invented* — and an
invented slot cannot be revised later. If a following atom then shows that slot is
really one the pattern already named, the two disagree and the match is lost.
`connected_order` in `slotted-encoder.py` does the reordering; `C12` is the case that motivated
it. A body no ordering can connect has to invent slots, and there the gap is real.

**Step 3 — give each atom a renaming.** One rule:

> An atom's renaming is the least renaming, total on its node's slots, agreeing
> with **everything already known about that atom**: its root if an earlier atom
> bound it, every child an earlier atom bound, and every slot literal an earlier
> atom pinned. Collect them into a single `find-mapping-total`, whose avoid-set is
> every slot named so far.

It is tempting to read this as three separate cases — first atom, root known,
children known — and that reading caused three of the four bugs listed at the end.
`slotted/tests/user-rules.egg` had drifted back to it and has been brought into
line; the counter-example under `M4` in `slotted/tests/user-rules-tests.egg` is an
e-graph where the two readings visibly disagree, the short one computing an *empty*
renaming for a child that has a slot.
The cases are only *which* constraints happen to exist:

* nothing known — the atom is first; its renaming is the identity and it defines
  the pattern's slots;
* root known — join `(RenamesToLeader V symV V)` and constrain by
  `(compose mv symV)`;
* children known — constrain by `(compose mx sym)` against the stored edge, with a
  `(RenamesToLeader X sym X)` join per child.

An atom that knows several of these must use all of them.

**Step 4 — walk the children.** A child at stored edge `p` has candidate renaming
`(compose mp p)`. If its variable is new, that *is* its renaming. If it is already
bound, check the two agree.

## Checking that two occurrences agree

This is the whole of what a repeated variable costs. Definition 6: two invocations
of the same class are equal exactly when one renaming differs from the other by a
symmetry of that class. Both renamings are known by the time this runs, so the
symmetry it would need is *determined* — compute it and look it up:

```text
(= sym (compose (inverse mx) (compose mp p)))
(RenamesToLeader X sym X)
```

With all three arguments bound that is an index lookup, not a join. The
enumerate-and-compare spelling means the same thing but makes the planner produce
one row per symmetry and discard all but one:

```text
(RenamesToLeader X sym X)
(= (compose mp p) (compose mx sym))
```

The enumerate-and-compare form is what the encoder emits, so it is the one `M2`
shows — on sdql's `sub-identity`, `(- ?e ?e) => 0`, which is this shape. The lookup
form states the same condition and is what an optimiser would turn it into; both
are here because the reading matters more than the spelling.

Either spelling needs `mx` to be no wider than the class:

```text
(compose mx (ClassSlots X))
```

Composition truncates silently, and a redundant slot is stored as a *partial*
self-loop, so a short symmetry could match a renaming read off a wider node and be
accepted wrongly. Narrowing by `ClassSlots` rules that out at the source, and it is
what the encoder emits — one `compose` per use of a variable, unconditional (M8). An
earlier version guarded with `(= (map-length sym) (map-length mx))` instead, which
compares the two lengths after the fact rather than fixing the domain; the narrowing
subsumes it.

**Neither may be weakened to `(= (compose mp p) mx)`.** Equality of renamings is
strictly weaker than equality of invocations, and the difference shows: `M2(c)`
matches `(- ?e ?e)` against `(- a[$0,$1] a[$1,$0])` where `a` is symmetric. The two
occurrences *are* the same invocation, the symmetry-aware rule fires, and the naive
one does not. The machinery will not normalise the two edges to be equal either, so
this is not a case you can pre-process away.

## Symmetry joins: where they are needed

Matching in the paper considers every node an invocation stands for, including all
symmetry-permuted variants. The encoding stores one variant per orbit, so those
have to be regenerated. The claim is that regenerating them where occurrences are
checked suffices:

> Every occurrence of a variable after the first costs one symmetry lookup. The
> first occurrence costs nothing.

The first occurrence is free because binding `mx` pre-composed with a symmetry
just reparameterises every later constraint by it. The first atom needs no join,
because permuting its root relabels the pattern's slots, and the action is built
in pattern slots, so the result is an α-variant the machinery identifies anyway.
Variables used once need no join for the same reason.

### One symmetry per class, handed to the primitives

The intended shape, and the better one: join **one** `(RenamesToLeader C sym C)`
per e-class and use that `sym` everywhere that class's renaming is used, rather
than joining a fresh one at each site. The primitives then receive
`(compose mx sym)` and work out whether it fits — solving the constraint is what
decides, instead of the query enumerating candidates site by site.

Two consequences worth stating:

* **Fewer joins.** One per class, not one per use, and each is a small relation.
* **It makes a correctness fix affordable.** A variable bound as an atom's root
  gets `mp`, whose domain is the matched *node's* slots — but a variable's
  renaming must have its *class's* slots for a domain, and the two differ exactly
  when the node carries a redundant slot. Restricting it needs the live slot set,
  which is precisely what a symmetry's domain is: `(compose mp sym)`. With a
  per-class join that costs nothing extra.

Measured against a per-use scheme -- a fresh symmetry joined at each place one is needed --
it was indistinguishable: same answers, same firing count, same single known failure. Only
per-class is in the tree; keeping both meant carrying an alternative nothing exercised.

The scheme does **not** address the branching question above, and did not fix
`X1`: both are about redundancy, not symmetry.

**The stored set has to be closed, not just a set of generators**, or a lookup for
a composite element would fail and lose matches. It is: the machinery's
transitivity rule composes self-loops, because its guard has an `e1 = e3` escape.
`S1` pins this down — a class is given one 3-cycle, and the parent then holds it
at the identity beside it at the cycle's *square*, which is never unioned in. The
rule fires, so the lookup found the composite. `S1b` is the control: without the
3-cycle there is no match, so `S1` is not passing for some other reason.

The set is not quite a group, though: a redundant slot is recorded as a *partial*
self-loop, so it is an inverse monoid. That matters for the occurrence check —
if the computed symmetry came out short, because a composition truncated, it could
match one of those partial loops and be accepted wrongly. Hence the width guard
above. On a saturated e-graph the shrinking rule keeps self-loops at the live
slots and the question does not arise, but user rules share a ruleset with the
machinery and so can match mid-repair, which is exactly when it would. `S2` covers
a symmetry and a redundancy in play together.

## Actions

Each variable at a child position uses its renaming. New nodes are built in
pattern slots.

**`union` is only correct at the identity.** The paper's union takes invocations,
and whether it produces a redundancy, a new symmetry, or a class merge depends on
their renamings. egglog's `union` takes classes, i.e. only the case where both
renamings are the identity. A compiler cannot know that they are, so it does not
try: `slotted-encoder.py` emits `Equated` for every action, and so does every rule
in the tutorial. Build the node and assert the fact:

  ```text
  (let _hn (App2 "h" ma A mb B))
  (Equated _hn mp_root Root)
  ```

  Concluding `(union Root built)` instead is the encoder's `union-id` mutant. Where
  the action's root is the first atom's root and its class carries no redundant slot
  the two coincide, but nothing in the rule establishes that, and off the identity
  the union is a different and false claim.

  `Equated` is the machinery's orientation-free form: it states `_hn = mp_root * Root`
  without saying which of the two is the leader, and the machinery derives the oriented
  `RenamesToLeader` row from it, promoting it to a real union when the renaming turns out
  to be an identity.

  **Do not write `RenamesToLeader` from an action.** It carries an orientation — the
  leader is the smaller of the pair under `ordering-max` — and `union` rewrites a row's
  endpoints, so an orientation that was right when the row was written can be wrong
  afterwards. Such a row is deleted as stale, and the fact goes with it. An earlier
  version of this document said the machinery would "re-orient it"; nothing did, and a
  backwards row is what let transitivity and single parent disagree forever on the SDQL
  batax term.

**Getting this wrong is silent**, which is why it is stated twice. A plain
`(union root built)` asserts an equation whose renamings are both the identity.
When the root's renaming is not, the equation is simply false — it merges two
distinct pattern slots — and the e-graph absorbs it as a redundancy rather than
complaining. `C11` is the case: a root renaming of `{$0↦$3, $2↦$2}` drove
`(Var 0)` from one live slot to none, after which every edge was emptied and
`h(x,y)` collapsed with `h(x,x)`. Two things make it hard to spot: the built node
is *correct*, so inspecting it tells you nothing; and an edge-width check misses it
because the children's classes go slotless too and the widths agree again.

Restricting the built node to the root's slot space instead — composing each child
renaming through `inverse mp_root` — is also sound, but needs a totality guard and
then declines to fire on cases the fact-insert handles.

The same gap appears for plain input terms. A `U` value is a node, not an
invocation, so a bare leaf has nowhere to carry its slot: `(var $0)` and
`(var $2)` both encode as `(Var 0)`, and `union (var $0) (var $2)` — which makes
the variable class slotless in the reference, collapsing every `h(var, var)` —
becomes a no-op. Slots inside a compound term ride in the stored edges and
survive; only a top-level leaf loses them.

## Slots the constraints never reach

`find-mapping` returns the *least* renaming, so a node slot outside the
constraints gets no name, and dropping a slot leaves an edge narrower than its
child's slot set, which Definition 4 forbids. The paper's §3.6 handles this by
picking any fresh slot; the crate does it in `enodes_applied`, so it never has an
unnamed slot to drop.

A slot the constraints do not reach is MINTED, and that is not the end of the story:
a fresh name differs from everything, so minting decides the slot is not any slot
already in play. That is one reading of a choice; the others, where the slot IS one
already in use, are matches too, and they build different e-nodes.

The compiler makes that choice ONCE, after every atom has been read, with
`refine-namings` — [`M4`](#m4) below. Two slots may be merged unless the pattern itself
writes both of them, or they are two slots of the same node. The first would let a
`not-free` side condition hold by renaming its two slots together, which is capture; the
second would stop a renaming being one-to-one. This is `final_refine` in the reference,
and those two bounds are its `allows_directed_union` and `add_disjointness_constraint`.
The identity is element 0, so a program reaching only index 0 answers as one compiled
before this did.

Choosing per atom instead does not work, and it is worth saying why: offering every
naming for an atom makes the rule insensitive to how that atom's renaming was
constrained, and two of the three compiler mutants the corpus carries stopped being
detected. Deciding after the match keeps minting meaningful — and the pattern's own
slots are not all known until the last atom has been read, which is what the first bound
above needs.

`find-mapping-total` ports that: same constraints and same one-to-one check as
`find-mapping`, plus a fresh name for every domain slot left unnamed.

```text
(find-mapping-total avoid domain first… second…)
```

`domain`'s keys are the slots the result must cover, `avoid`'s slots are the ones
it may not reuse. Both are identity maps the caller already has: a node's slots are
`(map-union (map-image p1) (map-image p2))`.

**It picks the smallest unused slot.** This was once recorded here as load-bearing,
on the strength of a generated case whose node count climbed 16, 18, 30, 28, 38, 47,
50, 59 under an above-the-maximum policy while the reference saturated in two rounds.
**That no longer reproduces.** Re-measured on the current machinery, minting one above
the largest name mentioned locally settles just as well:

| above-the-local-maximum | result |
| --- | --- |
| curated | 33/33 agree, 0 unsaturated, 0 nondeterministic |
| generated | 250/250 agree, 0 unsaturated, 0 nondeterministic |
| slot names in play, rounds 5→80 | bounded, stable from 10 rounds on (max 2–3) |
| same, with the avoid-set not accumulated | 33/33, still settles |

The α-finder is what makes any deterministic policy converge: `h($5)` and `h($0)` are
α-equivalent, so minted names are merged back down to the canonical smallest form
rather than accumulating. Why the earlier case escalated is **not established** — it
predates the migration and single-parent fixes, both of which interfered with exactly
that canonicalization, but it cannot be reproduced now to confirm.

Smallest-unused is kept because names stay small, which keeps `ordering-max`
comparisons and printed output readable — not because the alternative diverges.

So: any deterministic choice is *sound*, because different choices give α-variants
the machinery identifies.

**The avoid-set must accumulate — for this policy.** The primitive is pure and sees
one atom at a time, so passing only the first atom's slots lets two inventing atoms
pick the same slot. Thread a running union of `(map-image mp)`; identity maps never
conflict under `map-union`, so the union is always defined. Checked by removing the
accumulation: `C7-redundant-distinct-vars` becomes order dependent and loses a match.

This is the one place the two policies genuinely differ. Smallest-unused *reuses* low
names, so it has to be told which are taken; minting above the local maximum is
self-avoiding, and passes 33/33 with no accumulation at all. So the avoid-set is the
price of keeping names small, not a requirement of minting as such.

The alternative, if you would rather not invent slots: guard every variable the
action uses with `(= (map-length (compose mp p)) (map-length p))`. Sound but
incomplete — `M3(b)` shows the rule declining to fire in the bad case and still
firing in the good one. Occurrence checks are self-guarding already, since a
dropped slot changes the domain and breaks the equation.

## The invariant rules are saturated between user-rule steps

The rules that maintain the encoding live in a `slotted` ruleset, and the schedule is

```lisp
(run-schedule (saturate (run slotted))                  ; before any user rule
              (repeat N (seq (run) (saturate (run slotted)))))
```

**Why saturate them, rather than run them alongside.** A user rule that matches a node
before that node's α- and slot-canonicalisation has finished sees a spelling which is about
to change — and matches again when it does. Interleaved in one ruleset the two never settle:
that is what `fuzz179` was, a period-3 orbit in which the user rules rebuilt α-variants as
fast as the machinery retired them.

**Why the user's side is finite.** User rules are not expected to terminate — equality
saturation generally does not — so they get a step count while the invariants get
`saturate`. Termination of a program is then a statement about the *machinery* only, which
is the property worth checking.

This is the shape egglog's own proof encoding uses for its maintenance rulesets:
`instrument_schedule` walks the user's schedule and rewrites every `Run` as
`(seq <that run> <rebuild>)`, where `rebuild` saturates the proof rulesets. Since `(run N)`
is `(repeat N (run))`, instrumenting it gives exactly the alternation above.

A file with no user rules of its own — `egraph-encoding-11.egg` and the per-language
files — only needs `(saturate (run slotted))`, which also reads better than the iteration
counts it replaced.

| | |
| --- | --- |
| generated cases reaching a fixpoint | **250/250**, from 249 |
| generated isomorphic | **249/250**, 0 differ, from 248/250 |
| curated | 44/44 differential, fixpoint, node counts, isomorphism |

Two consequences worth stating plainly.

**It removed a mutation's bite.** `wide-kids` — the compiled action not narrowing its
non-root variables by `ClassSlots` — is no longer caught, on 44 curated *or* 250 generated
cases. Not masked: observing inside a user step, before any repair, the action does not write
a wide edge at all. With the invariants saturated first, the renamings an action reads off a
node are already canonical, so that narrowing is now belt-and-braces where it used to be
load-bearing. It is kept, and the mutation is kept as a record, but it no longer
discriminates — recorded because a test that has stopped testing what it was written for is
worse than no test.

**One demo in the user-rules cases inverted.** `M8` asserted that a malformed edge
appears; under this schedule none does, so it now asserts the opposite and says why. The
alternative — contriving an unphased schedule to keep the old assertion alive — would have
preserved a test of a state the encoding no longer reaches.

## What the differential tests cover

`xdiff.py` builds a case, runs it through the reference (`xmulti`, which drives the
crate directly) and through a compiled egglog rule, and compares which probe terms
end up equal. Per case it checks five things:

1. **baseline** — with no rule at all both sides must already agree, so a
   difference is attributed to matching rather than to the machinery;
2. **agreement** — the compiled rule against the reference;
3. **fixpoint** — both sides must have settled. A case that hasn't means the two
   ran different amounts of work, so comparing them says nothing: the reference
   reports whether it saturated, and the encoding is rerun at twice the iterations
   and must agree. That doubles as a determinism check;
4. **order independence** — the answer must not change when the atoms are compiled
   in a *different* order, which moves which atom is first and hence every slot;
5. **slot-renaming invariance** — renaming every slot in the program must not
   change either side's answer. This is a per-side property needing no
   cross-system comparison, and it asks a different question from agreeing with
   the reference: a side can be consistently wrong and still invariant.

```text
./xdiff.py              the curated cases
./xdiff.py fuzz 250 7   250 random cases, seed 7
./xdiff.py show C11     dump one case: spec, both answers, compiled rule
./xdiff.py show 61 555  the same, for a random case
```

Touching the generator renumbers every random case, since they share one RNG
stream — so a failing index does not reproduce across a generator change. Copy an
interesting case into `curated()` before changing anything, which is where `C11`
and `C12` came from.

Current state — `./xdiff.py` and `./xdiff.py fuzz 250`:

| | curated | random |
| --- | --- | --- |
| cases agreeing | 44/44 | 250/250 |
| of which the rule fired | 34 | 65 |
| matching differences | 0 | 0 |
| order dependence | 0 | 0 |
| slot-renaming | 0 | 0 |
| machinery differences | 0 | 0 |
| excluded: timeout or unsettled | 0 | 0 |

The probe partition is only one projection of the e-graph, so four more comparisons run
beside it, each over the whole corpus:

```text
isomorphism.py     the two e-graphs are isomorphic -- classes, slots, symmetry
                   groups and nodes -- by constructing and checking a witness
mutations.py       each past bug, put back, still breaks the corpus by the amount
                   recorded for it
def4-edges.py      every edge's domain is *exactly* its child's slot set -- both
                   directions of Def. 4 in one comparison
nodecounts.py      e-nodes per operator, against the reference
fixpoint.py        each case reaches a fixpoint of the *rules*, not just of the
                   database, which `(run N)` cannot distinguish
follower-nodes.py  no e-node sits on a follower class
invariants.py      Def. 4 on every edge, and that no stored renaming is non-injective
```

## The paper's §4.1 array language, ported and compared

The headline efficiency result of the paper is a functional array language whose
`map`s are fused and fissioned (Listing 1, and the (A) → (B) transformation of §4.1).
Nothing had to be added to the encoding for it: the array language *is* the generic
string-headed encoding, with `lambda` and `let` as its two declared binders.

| Listing 1 | surface | encoding |
| --- | --- | --- |
| `Lam(Bind<RenamedId>)` | `(lam $x b)` | `(App2 "lambda" {0↦x} (Var 0) mb b)` |
| `App(RenamedId, RenamedId)` | `(app a b)` | `(App2 "app" ma a mb b)` |
| `Let(RenamedId, Bind<RenamedId>)` | `(let $x b e)` | `(App3 "let" {0↦x} (Var 0) mb b me e)` |
| `Var(Slot)` | `(var $x)` | an edge `{0↦x}` to the `(Var 0)` class |
| `Number(u32)` / `Symbol(Symbol)` | `7`, `map` | `(Num 7)`, `(Sym "map")` |

Only `let`'s columns are reordered: Listing 1 writes `(let ?e $x ?body)`, value first,
where the encoding — and the reference crate's own `tests/rise` and `tests/array` —
write `(let $x ?body ?e)`. Same constructor, and the binder is column 0 on this side
because that is where the generated binder rule looks for it.

Eight of the nine rules are ported: `eta`, `let-intro`, `let-unused`,
`let-var-same`, `let-app`, `let-lam-diff`, `map-fusion`, `map-fission`. `beta` is
left out because its right-hand side is `?body[(var $x) := ?e]`, and the oracle's
spec language cannot express substitution; the paper's own benchmarks use the
let-based rules instead (footnote 4).

`xarray.py` compiles each rule by the recipe above and compares it against the
reference crate's *own* `Rewrite::new_if`, so the reference sees the rule as one
nested pattern while the encoding sees it flattened into depth-1 atoms.

```text
./xarray.py            each rule firing, and each guard blocking      14/14 agree
./xarray.py vac        drop each guard: the answer must change         5/5 load-bearing
./xarray.py iso        whole-e-graph isomorphism, not just probes     14/14 (+ the one
                                                                     known difference)
./xarray.py fuzz 60    random array terms, two seeds                 60/60 and 59/59 agree
./xarray.py goal       (A) → (B), the paper's transformation           see below
./xarray.py egg        regenerate target/slotted/slotted-array-rules.egg
```

Flattening is safe for these eight even though it is not safe in general. The one
shape where the depth-1 form proves *more* than a nested pattern is the same slot
literal on two binders in different atoms (`B3` in `xdiff.py`): each atom looks its
own node up and gets its own name for that node's bound slot, so writing `$x` twice
constrains nothing. None of the eight does that. `let-var-same` writes `$x` twice but
both occurrences are children of one atom, so one `mp` pins both; `eta`'s second `$x`
is a *free* occurrence inside `?b`, which is a public slot of `?b`'s class and so is
reached through the root constraint.

Three things the port needed that the toy language never exercised:

* **A constant leaf in a child position.** `(app map ?f)` pins a child to the
  `(Sym "map")` class rather than to a pattern variable.
* **A slot the right-hand side binds but the left-hand side never named.**
  `map-fusion` writes `(lam $x …)` for an `$x` nowhere in its pattern. The
  reference writes a literal named slot; the encoding has to *mint* one, which is
  `find-mapping-total` over the accumulated avoid-set with a one-key domain.
* **Building a binder in an action.** A built `lam`'s bound slot is on the node but
  not on the class, so the parent's edge must not name it — `map-remove` on the
  identity map. Getting this wrong writes an edge that breaks Def. 4. `xdiff.py`'s
  own `build_rhs` had the same gap; no case there builds a binder, so nothing
  observed it.

### (A) → (B), measured

`./xarray.py goal 0 1`. "reaches" means (A) and (B) end in one e-class.

| program | reference | encoding |
| --- | --- | --- |
| 1-D, 2 functions | reaches, saturates | reaches |
| 2-D, 4 functions, N=0 extra params | reaches, 2.1s | reaches, saturates, 1.0s |
| 2-D, 4 functions, N=1 | reaches, 2.5s | reaches, saturates, 1.3s |
| 2-D, 4 functions, N=2 | reaches, 2.8s | reaches, saturates, 1.6s |
| 2-D, 4 functions, N=3 | reaches, 3.2s | reaches, saturates, 1.6s |
| the same, with `λf1…λf4.λm.` wrapped round it | reaches | > 30 min, see below |

`N` is the paper's difficulty knob: "by adding 2 parameters, we use `((f1 p1) p2)`
instead of `f1`". The functions and the matrix are free symbols in the rows above
rather than λ-bound at the top as Listing 1 writes them; that is the same rewriting
problem, and it is the last row that says why the distinction matters.

Neither side saturates in general — `map-fusion`/`map-fission` and `let-app` keep
producing work — so this is a *bounded* comparison. The reference gets 10 rounds and
the encoding 30 user steps with the invariants saturated between them, so "reaches"
means within that budget. The times are not a like-for-like cost comparison either:
`egglog` here is a debug build, and the encoding does the machinery's work in datalog
rather than in Rust. They are in the table only because they are the same order of
magnitude, which is worth knowing.

**Enclosing binders are what the encoding pays for, and the reference does not.**
Writing the *same* 2-D four-function program with binders around it, `k` of `λm`,
`λf4`, `λf3`, `λf2`, `λf1`:

| enclosing binders | 0 | 1 | 2 | 3 | 4 | 5 |
| --- | --- | --- | --- | --- | --- | --- |
| reference | 2.1s | 1.6s | 1.7s | 6.3s | 6.3s | 5.3s |
| encoding | 1.0s | > 10 min | not run | not run | not run | > 25 min |

Every reference entry reaches (A) = (B). The reference is flat across the whole row;
the encoding falls off a cliff at the *first* enclosing binder, which is too early for
"the problem got harder" to be the whole story, since the reference is doing the same
rewriting. The encoding entries marked `>` were stopped without a verdict, so they are
lower bounds and not "does not reach".

Two things it is *not*: no single rule is expensive on its own — each of the eight,
run alone on the one-binder program, finishes in 0.1s — and it is not the paper's own
difficulty knob, which the encoding tracks fine (the N=0…3 table above). So it is the
rule *set* interacting on a program with a binder around it. The suspected mechanism
is that every atom's renaming is solved by joining against a `RenamesToLeader`
self-loop of each variable's class, and a class with `k` slots can carry up to `k!` of
them, where the reference's `ematch_all` walks down from a class and never enumerates
them. That is a hypothesis: a leave-one-out over the eight rules was started and not
finished, so which rule and which join dominate is not isolated. It is a different
axis in any case from the paper's Figure 8, which counts e-nodes and memory.

### A language difference the array comparison found, since fixed

It showed up as a baseline disagreement, before any rule ran, and took two fixes.

`Bind` covers one column. `Let(Bind<body>, value)` hides the bound slot from the body
only, so in `let x = x in f1 x` the value's `x` is ambient and the class keeps that
slot. The generated binder rule used to strip the bound slot from the *whole* node, so
the class came out with no slots at all and two applications the reference keeps apart
became one class — 8 classes against 9:

```text
(app (let $0 (app f1 (var $0)) (var $0)) (var $0))
(app (let $0 (app f1 (var $0)) (var $0)) (var $1))
```

`:binder` now names the column a binder *covers* — the one after its slot, matching
`Bind<T>` around a single child — so a slot free in an uncovered column is not
stripped. That alone was not enough: with the strip blocked, the bound slot stayed in
the class's slot set and stopped being renameable, which separates two terms the
reference *identifies* — the opposite error. A colliding bound slot is therefore
renamed to a slot the node does not use before the strip applies. Both halves were
needed: `xarray.py iso` went 8-vs-9 classes, to 9-vs-9 but non-isomorphic, to 15/15.
`slotted/encoding/binder-scope.egg` is the pair of cases, and `xarray.py extra` the
comparison.

### Two discrepancies in the reference checkout, one now fixed upstream

Both in `slotted-egraphs/tests/array/mod.rs`, which looks stale next to
`tests/rise/`, whose language and rules are the paper's:

* `Lam(Slot, AppliedId)` — a *free* slot where Listing 1 and `tests/rise` both have
  `Lam(Bind<…>)`. A non-binding `lam`.
* `slot_free_in(slot, var)` returned `!…contains(slot)`, i.e. it computed "**not**
  free in". Every use in that file therefore had the opposite polarity to Listing 1:
  `eta` fired only when `$x` *is* free in `?f`, and so on. Measurably wrong: with
  Listing 1's polarity the reference rewrites (A) into (B); with that file's, it does
  not. **Fixed upstream** on PR #45, with a test that pins the direction — the file had
  none, which is how it survived. `tests/rise/rewrite.rs` writes its conditions inline
  and was never affected.

The `Lam` one is still worked around by targeting the paper's semantics, which is what
`tests/rise` implements and what `xmulti`'s `define_language!` declares.

## A soundness bug in the machinery: migration truncates edges

Found by the differential suite as `X1`/`X2`, and fixed. It is worth reading
because it is the *same* dropped-slot mistake as the fresh-slot section above,
one level down.

The migration rule rewrites a node into its leader's slot space:

```text
e2 = m*e1  and  e2 = f(m1*c1, m2*c2)   =>   e1 = f((m⁻¹∘m1)*c1, (m⁻¹∘m2)*c2)
```

`compose` keeps only the keys whose value lies in the left map's domain. So when
`m1` reaches outside `im(m)` — exactly when `e2` has a slot that is redundant in
`e1` — the rewritten edge **silently narrows**. In the minimal case `m = {$0↦$0}`
and `m1 = {$0↦$1}` compose to the *empty* map, and an empty edge to `(Var 0)`
asserts the variable class has no slots. Every `h(var, var)` then collapses.

The minimal reproducer is one term and one rule, no unions:

```text
term   h(v0, v1)
rule   ?c == (h ?a ?b)  =>  union ?a (h ?b ?c)
```

Two things made it hard to see. It is **child-position sensitive** — swapping the
action's two arguments makes it disappear, because the truncation only hits the
edge that reaches the dropped slot — and every visible symptom is downstream:
malformed self-loops appear (derived by transitivity closing a cycle), the
variable class loses its slot, and `h(x,y)` merges with `h(x,x)`. Deleting the
self-loops does not help, and neither does guarding transitivity.

Fixed by minting a name for the uncovered slot instead of dropping it: migration
composes through a renaming that is total on the node's slots, which is
`find-mapping-total` in `slotted/encoding/egraph-encoding-11.egg`. The alternative —
declining to migrate whenever an edge would narrow — was in the tree for a while and is
measured in the next section.

### What declining costs, measured

The complete alternative is to mint a name for the uncovered slot instead of
dropping it: extend the pullback to be total on the node's slots. Both are generated
from one source. It was selected by a `MIGRATION` knob for a while, which was better than
the copy of the whole machinery that preceded it -- by the time anyone looked at that copy it
had drifted to none of `ClassSlots`, `compose-total` or the current alpha-finder tie-break.
Only minting is in the tree now: it is the only mode that empties followers, so the knob was
carrying a branch nothing used.

Neither mode distinguishes itself on *what it proves*: curated 44/44, generated
250/250, node counts against the reference 44/44, either way. What used to separate
them was cost, and that has gone:

| | then | now |
| --- | --- | --- |
| App rows on `X2`, declining | 7 | 7 |
| App rows on `X2`, minting | **1224** | **7** |
| `X2` at `(run 200)`, minting | no fixpoint in 600s | settles, instantly |
| corpus e-node rows | — | **194 either way** |

The fan-out was never inherent to minting. It was α-variants multiplying, and both
sources of that have since been fixed — `ClassSlots` (Def. 4, below) and the
alpha-finder's tie-break. So the argument that decided this originally no longer
holds, and the choice comes down to which mode keeps the encoding's own invariants,
which is settled under "Do follower classes need self-loops at all?" below.

**Settled: minting, and the guard is gone.** No test distinguishes the two on what
gets proved, so the deciding argument is the one under "Do follower classes need
self-loops at all?" below: minting is the only mode that empties follower classes, and
declining leaves a node on a class no query can see. The fan-out that once argued
against minting is explained under "Why minting" — a consequence of keying a node by
its renamings, which the reference avoids by keying on a shape — and both of its
sources have since been fixed, so it no longer applies.

### The guard really is incomplete: the invariant is false

The question was whether this holds:

> every fact carried by a node on a self-loop-less class is also carried by a node
> on a self-looped one

If it did, the guard would be complete and "incomplete" would be the wrong word,
since a compiled rule only ever misses a node whose content it can reach anyway.

**It is false.** `X2`, under the guard, reaches a fixpoint holding two nodes that
no compiled rule can see and that are α-variants of nothing visible:

```
h( {1→1,2→2}·h( {1→1,2→2}·B, {0→2}·Var0 ),  {1→1,2→2}·B )
h( {1→1,2→2}·B,  {1→1,2→2}·h( {0→1}·Var0, {1→1,2→2}·B ) )
        where  B = h( {0→2}·Var0, {0→1}·Var0 )
```

`slotted/xdiff/stranded.py` reproduces this. It works in two steps:

1. Declare two observer relations *after* the machinery reaches a fixpoint, one
   joining `RenamesToLeader V s V` and one not, both keyed on the whole `App` row.
   The difference is exactly the set of rows a symmetry-joining rule cannot see.
   Counting relation rows during the run instead would answer a question about
   history, since rows outlive the `delete` in the migration rule; and reading
   `print-function` output instead would merge classes, since a class with no
   extractable term prints as `Unextractable`.
2. For each invisible row, search the visible ones for an α-variant — same operator,
   same children, edges equal under one injective renaming — with each edge first
   restricted to the slots its child actually has, because the machinery does not
   force an edge's domain to match its child and an unrestricted comparison reports
   false uniques.

| | stranded | of those, no visible α-variant |
| --- | --- | --- |
| `X1` guarded | 1 | 0 |
| `X2` guarded | 2 | **2** |
| `X2` minting | 0 | 0 |

Minting strands nothing, which attributes the stranding to the guard rather than to
anything else in the machinery.

**Why the earlier structural argument fails.** It went: every `App` row gets a
self-loop from the "everything must have a self-loop" rule, so a row only loses one
when single-parent deletes it, by which point its content is already related to the
leader. The gap is the last step. Single-parent deletes the self-loop, and nothing
re-derives it — that rule fires on a *new* `App` row, and the row is not new any
more. If migration was also declined, the leader never received the node. So the
relation `e2 = m·e1` is recorded while the node itself sits only on `e2`, reachable
in principle and unreachable by any rule that joins a self-loop.

**Not every decline strands something.** Declining means `compose (inverse m) m1`
lost a key, i.e. the child edge maps into slots outside the leader's frame. Two
kinds:

* **(a) the lost key is junk** — the child does not have that slot, so the entry
  meant nothing and dropping it would have been safe. This is `X1`'s only decline:
  `m1 = {0→0, 2→2}` into `Null`, which has no slots at all. Harmless, and the reason
  `X1`'s one stranded row *does* have a visible α-variant.
* **(b) the lost key is live** — the child genuinely uses it, so the class really has
  a slot its leader cannot name. This is `X2`, and it is the harmful kind.

The whole curated suite declines only 4 times: 1 on `X1` (kind a) and 3 on `X2`
(kind b). Aiming at kind (b) directly does *not* work: five cases built by unioning
a wider term with a narrower one, so the leader's frame is too small, all strand
nothing, because the redundancy path records a partial-identity self-loop that
widens the frame before migration is ever asked. `X2`'s kind-(b) declines arise
instead from the machinery's own churn on nested nodes, which is why they were hard
to construct on purpose.

**What this establishes.** There are reachable, stable states whose content no
compiled rule can reach. No case changes an *answer* — `X2` itself agrees with the
reference — so the defect is in what rules can see, not yet in what gets proved. But
"invisible to every query" is not a state the encoding should be allowed to reach,
so it is worth fixing on its own.

### The fix: don't delete a self-loop that a class still needs

The two-rule interaction reduces to four lines of machinery, with no user rule
involved — `Case 14` in `slotted/encoding/egraph-encoding-11.egg`:

```lisp
(let $B (App2 "h" (map-of 0 2) (Var 0) (map-of 0 1) (Var 0)))     ; h($2,$1), slots {1,2}
(let $N (App2 "h" (map-of 0 1) (Var 0) (map-of 1 1 2 2) $B))      ; h($1,B), slots {1,2}
(union $N (Var 2))          ; N's class is just $2, so slot 1 is redundant for it
(run 20)
```

At the fixpoint `$N` holds an `App` row and its only `RenamesToLeader` row is
`$N → {0→2} → (Var 0)`. No self-loop, so no query can see the node.

The instinct is to blame the guard on migration, but the cheaper culprit is
**single-parent**, whose `b = a` branch deletes a class's self-loop the moment the
class acquires a leader:

```lisp
(rule ((RenamesToLeader a m1 b) (RenamesToLeader a m2 c) (!= a c) ...)
      ((delete (RenamesToLeader a m1 b))
       (RenamesToLeader b (compose (inverse m1) m2) c)))
```

With `b = a` that deletes `RenamesToLeader a m1 a`. The edge it adds in exchange is
**already derivable**: transitivity turns the same two rows into
`a = (compose m1 m2)·c`, and a symmetry group is closed under inverse, so
`compose (inverse m1) m2` and `compose m1 m2` generate the same set. So that branch
contributes nothing but the deletion. One guard removes it:

```lisp
       (!= a b)
```

| | before | after |
| --- | --- | --- |
| `X1` stranded / of those unique | 1 / 0 | 1 / 0 |
| `X2` stranded / of those unique | 2 / **2** | **0 / 0** |
| curated differential | 31/31 | 31/31 |
| generated differential | 250/250 | 250/250 |
| curated `RenamesToLeader` rows | 183 | 199 (+9%) |
| curated `App2` rows | 144 | 143 |

So the cost is about 9% more union-find rows and slightly *fewer* e-nodes — `X2`
compresses to 7 `App` rows instead of 8, because a class that keeps its self-loop
can still be migrated into later.

`X1`'s one remaining stranded row is the harmless junk-edge kind and is stranded by
a *different* mechanism: the shrinking rule deleting a too-wide identity self-loop,
which is open question 2. It has a visible α-variant, so nothing is lost.

The guard was one branch of a `MIGRATION` knob; only minting is in the tree now.

### Do follower classes need self-loops at all?

They should not, and — with minting and an oriented migration — they do not: every
follower across the corpus is empty. A follower is supposed to be *emptied*: migration
moves each of its nodes into the leader's frame and deletes the original, so nothing is
left to match on and a self-loop would be dead weight. Getting there took the two fixes
below; what follows is the state each one was found from.

The exception is exactly where migration **declines**. Then the node stays on the
follower forever, and with no self-loop no compiled rule can see it. So the follower
self-loop is not a general requirement; it is the price of the guard. `X2` is the
case that shows it: 2 followers still hold a node at its fixpoint.

Which suggests the obvious alternative — mint instead of declining, so followers
really are emptied. Minting was originally rejected on cost, and that reason has
expired (above): both modes settle on `X2` at 7 rows and total 194 across the corpus.
Switching found one thing the guard had been hiding:

| | declining | minting |
| --- | --- | --- |
| curated | 44/44 | 44/44 |
| generated | 250/250 | 250/250 |
| node counts vs reference | 44/44 | 44/44 |
| corpus e-node rows | 194 | 194 |
| followers holding an e-node | 3 | **0 of 26** |
| wide edges, generated | 0 of 250 | **1 of 250** (`fuzz236`) — until fixed, then 0 |

Minting reached zero followers only once migration was also *oriented*; both fixes are
below.

`fuzz236` was a real defect, not a cost of minting: **the action narrowed only the
root by `ClassSlots`, not the other pattern variables.** A variable's renaming is read
off the matched node, so its domain is the *node's* slots; written into a built node as
a child edge, it can name a slot the child's class has since proven redundant. That is
a Def. 4 violation, `child-update` deletes the row, and the action rebuilds it next
iteration — a stable oscillation, which is why it survived to `(run 200)` rather than
being repaired. Narrowing every variable rather than just the root fixes it and
compresses `fuzz236` from 9 `App` rows to 6. It is now the `wide-kids` mutation.

Declining was masking it: with the node left behind, the class never reached the state
where its slot set had narrowed under a live edge.

**Minting is therefore the better mode, and it is the default.** One follower still
holds a node, and that one is *not* a declined migration — see below.

Which reopens the question this section asked: the follower self-loop was kept as "the
price of the guard", and the guard is no longer the default. It is still kept, because
the remaining case below is a class that holds a node on a non-leader `U` value and so
still needs to be addressable. Whether *that* one needs the self-loop is unmeasured.

### Migration has to be oriented

Switching to minting left one follower holding a node, in `MR1`. The cause was not the
α-finder picking a spelling, and the node was not stranded — **migration had no fixed
target and was moving it back and forth.**

`RenamesToLeader` holds *both* directions for a pair: `MR1` ends with

```text
(RenamesToLeader A            {0↔1} Unextractable)
(RenamesToLeader Unextractable {0↔1} A)
```

so migration's `(!= e1 e2)` was satisfied either way round. It moved the node onto one
value, deleted it from the other, and next round moved it straight back. The database is
a fixpoint — every table is size-stable from round 4 to round 200 — but the *rules* are
not, and `(run N)` cannot tell the difference because it stops after N rounds either
way. `(run-schedule (saturate (run)))` can: `MR1` was the only case in the corpus that
never terminated.

The fix is one atom. The encoding already fixes an orientation — the single-parent rule
points every edge at the `ordering-min` value — so migration follows it:

```lisp
(= e2 (ordering-max e1 e2))       ; toward the leader only
```

| | before | after |
| --- | --- | --- |
| followers holding an e-node, curated | 1 | **0 of 26** |
| curated cases that saturate | 43 of 44 | **44 of 44** |

Everything else is unchanged: curated 44/44, generated 250/250, node counts 44/44, row
counts identical case by case, mutation matrix unchanged.

**Zero on the curated corpus is not the property.** Measured over `fuzz 250` — which is
where the claim had never been tested — 3 cases ended with a follower holding a node, 5
nodes out of 93 followers. `follower-nodes.py fuzz 250` is that measurement, and it took
three changes to reach zero: orienting migration closed the curated cases and `MR1`'s
non-termination, orienting `child-update` took the generated ones from 5 nodes to 1, and
saturating the invariants between user steps closed the last. **Now 0 of 93 over 250
generated cases**, so the property holds where it is measured rather than only where it was
first checked.

Two things this cost before it was found:

* **A stable row count is not a fixpoint.** Every probe here reads the state after
  `(run N)`, which cannot see a rule that deletes what another rebuilds.
  `slotted/xdiff/saturates.py` now checks the corpus with `saturate`, and
  it is the only check that would have caught this.
* **"Has an edge to a different value" is not "is a follower".** Since the relation
  holds both directions, that test is true of the leader too, and the probe reported a
  follower holding a node when the node was on the leader. A follower is a value with a
  strictly *smaller* peer.

Where followers are empty, an isomorphism check may enumerate leaders only, and the empty
peer is what prints as `Unextractable` — a value whose `App` rows have all been deleted —
so there `Unextractable` marks the side with nothing on it rather than a problem. It is
not safe to *assume* it: three of 250 generated cases used to end with a follower holding a
node, so the isomorphism check detects and reports that rather than enumerating leaders and
quietly missing what they hold. It is zero across both corpora now, but the check does not
rely on that.

**Migrating the self-loop to the leader does not substitute for keeping it.** The old
single-parent rule already did that — `RenamesToLeader b (compose (inverse m1) m2) c`
carries the symmetry onto the parent edge, and transitivity derives the same set
independently, a symmetry group being closed under inverse. Nothing is lost from the
*information*. What is lost is being addressable: a rule reaches a class's symmetries
by joining `(RenamesToLeader v sym v)`, so a class holding a node and no self-loop
cannot be matched, and having its symmetry on the leader does not help because the
node is not on the leader. The guard moves the symmetry but not the node.

## Why minting, and why the reference gets away with it

### What forces a mint

An edge's domain must be its child's slot set. Migration rewrites a node's edges out
of its own class's frame and into the leader's, and the leader's frame may have no
slot to name one of them with — which is exactly what a *redundant* slot is. The edge
still needs a name for it, so one is invented.

`Case 14`'s e-graph is the smallest instance. `B = h($2,$1)` and `N = h($1, B)` both
have slots `{1,2}`; unioning `N` with `(Var 2)` makes `N`'s class the variable `$2`,
which has one slot, so slot 1 becomes redundant. The leader is `(Var 0)` reached by
`{0→2}`, whose image is `{2}`. Rewriting `N`'s second edge `{1→1, 2→2}` through that
frame sends 2 to the leader's slot 0 and leaves 1 with nothing:

| | `N`'s second edge, after migration |
| --- | --- |
| guarded | declines; the node stays as written, on a follower |
| minting | `{1→1, 2→0}` — 2 to the leader's real slot, 1 to an invented name |

Note that `(union $h (Null))` on its own does *not* force a mint: egglog's `union`
merges the two into one class, so there is no follower and migration never applies.
It takes a class related to its leader by a non-identity renaming.

### The reference mints too — with an ever-increasing counter

`compose_fresh` in `slotmap.rs` is the same operation, called from `union.rs` with the
comment *"if `sh` contains redundant slots, these won't be covered by `map`. Thus we
need compose_fresh."* It fills any uncovered key with `Slot::fresh()`, and
`Slot::fresh` is a global counter (`fresh_idx += 4`) that never reuses a name — the
above-the-maximum policy that made *this* encoding diverge.

It gets away with it because of how a class stores its nodes:

```rust
nodes: HashMap<L, ProvenSourceNode>     // keyed by canonical SHAPE
```

A node's identity is its shape; the minted slot lives in the *bijection*, which is the
value. Moving a node is `remove(sh)` then `insert(sh, new_bij)`, so a class holds at
most one entry per shape and a fresh name can never multiply nodes. The reference also
shrinks a class's slot set to the *intersection* on union (`cap` in `union_leaders`)
and restricts the symmetry group to it, so the class's frame only ever gets smaller.

Here an `App` row is keyed by the whole tuple, renamings included, so two α-variants
differing only in a minted name are two distinct rows. That used to fan out badly —
`X2` under minting once held 1224 rows that were largely the same structure at
different names —

```text
(App2 "h" {0→0,1→1} (App2 "h" {0→0} (Var 0) {0→1} (Var 0)) {0→0,1→1} (Var 0))
(App2 "h" {0→0,1→1} (App2 "h" {0→0} (Var 0) {0→1} (Var 0)) {0→0,2→1} (Var 0))
(App2 "h" {0→0,1→1} (App2 "h" {0→0} (Var 0) {0→1} (Var 0)) {0→0}     (Var 0))
```

— waiting on the α-finder to merge them. Three things had to be right before it
stopped:

* **Smallest-unused minting**, so each mint is deterministic and the set is finite.
  An ever-increasing counter, which is what the reference uses, is what made it never
  settle here.
* **`ClassSlots`**, so a class's slot set narrows once rather than being re-read from
  whichever self-loop a join happened to bind.
* **The α-finder's tie-break**, which was itself manufacturing variants.

With all three, `X2` settles at 7 rows either way and the corpus totals 189. So the
keying difference is real but no longer costly on anything measured: it needs the
α-finder to converge the variants, and it now does. What remains true is that a
reference-style *ever-increasing* counter cannot be copied — that is a property of the
minting policy, not of keying by shape-plus-renamings.

**Read the firing count before the agreement count.** A case whose rule never
fires says nothing about matching, and random patterns mostly do not fire, so the
harness always reports how many did. Getting that number up was most of the work
of making the sweep mean anything: it went 1/53 → 21/141 → 61/300 as the generator
learned to read patterns off terms that are actually in the e-graph.

Curated cases, and what each is for:

| | |
| --- | --- |
| `C1`–`C10` | repeated variables, chains, joins, symmetry, redundancy, three-atom bodies |
| `C11` | the action must not use `union` off the identity |
| `C12` | atoms must be compiled in a connected order |
| `C13` | the first atom must not be a binder |
| `C14` | the action's root may carry a non-identity renaming (replaces `C11`) |
| `P1`,`P2` | ported: a node's distinct slots may not be merged, with and without redundancy |
| `S1`,`S1b` | the stored symmetries are closed, so a lookup finds a composite element |
| `S2` | a symmetry and a redundancy in play at once |
| `B1`–`B4` | binders: chaining through one, α-equivalence, the same slot literal on two binders |
| `M1`,`M3` | shapes `slotted/tests/user-rules.egg` teaches that nothing else covered: a swapped action, and one shared variable across two operators |

`slotted/tests/user-rules.egg` is the readable form of this same recipe, so each of
its sections names the case above that covers its shape. Keep the
two in step — the hand-written file passing its own assertions only says it does
what it expects, and it had drifted to the three-case reading once already. One
shape there, `M9`, cannot be covered as the oracle stands: it puts a slot literal
in a non-binder child position, and the reference admits a slot there only via
`Bind` or as the whole of `Var(Slot)`, which is a unary atom the harness's
two-child format cannot express.

### Comparing more than the probe partition

A probe partition only sees what someone thought to probe. Counting e-nodes per
operator sees the whole e-graph, so a spurious node, a missing one, or a merge that
should not have happened shows up whether or not a probe was aimed at it.
`slotted/xdiff/nodecounts.py` does that: the oracle grows a `dump` line
that prints every class and node through `to_syntax` -- operator, children with their
slotmaps, slot literals -- and the encoding side counts `App{n}` rows by operator.

`var` and `null` are excluded: the reference holds a variable as a `var` *node* in its
own class while the encoding holds it as the nullary `(Var 0)` value, so counting them
would compare bookkeeping rather than content.

**41 of 43 curated cases agree on node counts. Two do not**, and neither was visible
to the probe check:

| case | reference | encoding |
| --- | --- | --- |
| `X1-migration-must-not-truncate` | `h`: 6 | `h`: 7 |
| `S1-symmetry-group-is-closed` | `f`: 1 | `f`: 2 |

`X1` is the stranded row already documented above. `S1` was new, and diagnosing it
gives a second, independent compression gap.

Its two `f` rows have *identical children* and differ only in the second edge, by a
rotation that is in the class's stored symmetry group -- both `k` and `f` do hold the
full cyclic group of three, so closure is not the problem. Their outputs are already
in one class, so `e1 == e2` in the alpha-finder and its tie-break guard decides the
case. Instrumenting the premise shows it matches six times, and of the instantiations
where the two spellings genuinely differ, `b1` is always the identity while `a1` is a
non-identity rotation:

```text
(a1 b1 a2 b2 m) = (c   e  e   c²  c )
                  (c²  e  c   c²  c²)
                  (e   e  c²  c²  e )   <- a1 = b1 and a2 = b2, so "same node"
```

The guard fires only when the composed spelling sorts *below* the stored one, and
composing with a symmetry here always sorts it above, so every instantiation declines.
Stable at 5 `App2` rows through 60 extra rounds, so this is a fixpoint and not pending
maintenance. Changing which spelling the `delete` targets -- the matched edges rather
than the composed ones -- does not help.

No equality is at stake, since the two rows are already one class: like the migration
guard, this leaves a node un-canonicalised rather than losing a fact.

**Fixed.** The tie-break was comparing the *composed* edges against the stored ones,
which mixes two different things -- and composing with a symmetry can raise the tuple
past every stored spelling, so no instantiation qualifies. Comparing stored against
stored is a total order on row spellings, so for two distinct rows exactly one
direction fires, which is all the guard was for. The `delete` then has to name the row
that was matched rather than its composed form, or it removes a row that may not
exist.

`S1` now agrees, so 42 of 43 cases match on node counts. Curated 43/43, generated
250/250, all eight egg files pass, and the mutation matrix is unchanged (`root-only` 11
cases, `union-id` 2, `unordered` 1, `slot-late` 1).

### The whole e-graph, not a projection of it

Node counts and the probe partition are both *projections*: two different e-graphs can
agree on either. `slotted/xdiff/isomorphism.py` compares the thing itself,
by constructing a witness — a bijection between the two sides' e-classes, and one
between each matched pair's slots, under which the node sets are equal. The witness is
then re-checked, so a pass is a proof; a failure to find one is reported as "none found"
rather than as a difference, and the search cap is named when it is hit.

The sizes are printed with the verdict, because a comparison that quietly matched nothing
would otherwise look the same as one that matched everything — an earlier version of the
follower handling here was dropping 16 e-classes, and the count is what showed it:

```text
curated      44/44  isomorphic   217 e-classes,  282 e-nodes,  226 symmetries
generated   250/250 isomorphic  1931 e-classes, 2557 e-nodes, 1931 symmetries
                    0 differ, 0 not comparable
```

Nothing differs and nothing is left undecided. Getting there took the two orientation fixes,
the phased schedule, and reading the encoding by class *identity* rather than by the term a
class renders as; this was 244/250 with 6 not comparable before them. Every case reaches a
fixpoint, so the database-fixpoint fallback below is unused.

Three things had to be handled rather than assumed.

**Slot names are unrelated.** The reference mints `$f0, $f1, …` from a global counter,
the encoding the smallest unused integer, so the per-class slot bijection is searched
for, not read off. Colour refinement narrows the candidates first; the sizes here make
exhaustive search cheap, and exhausting it is what makes a negative answer meaningful.

**A class's symmetry group is not in its node set.** `C4`'s commutative `k` class holds
*one* node and a swap; a class without the swap holds the same one node. So the group is
compared too — recovered from the reference by testing every permutation of a class's
slots with `eq` on two invocations, which is a group-membership test, and from the
encoding as the self-loops `(RenamesToLeader c p c)` whose `p` permutes the class's
slots.

**A node is only defined up to those groups.** The two sides need not store the same
representative: on `C4` the encoding's row is `k($1,$0)` where the reference's is
`k($0,$1)`. So node equality quantifies over the parent's group and each child's group —
the reference's "strong shape" — and over renamings of slots a node carries but its
class does not, which is α-equivalence for a binder's bound slot.

Two differences in *representation* are translated rather than compared, and both are
checked instead of trusted: the encoding spells the binder `lambda` and rides its bound
slot in a child edge to the variable class, where the reference has `lam` with a slot
literal, so the translation asserts that position really is the variable class; and the
machinery seeds `(Var 0)` and `(Null)` unconditionally, so the same two terms are added
to the reference rather than dropping classes from one side by a rule about which ones
"do not count".

It compares the two sides at the strongest fixpoint each can reach:
`(run-schedule (saturate (run)))` against the reference's own saturation loop. Where the
encoding has no fixpoint of its *rules* — see below — the state is taken at a fixpoint of
the *database* instead, established by two different round budgets producing the same
graph, which is the standard the partition comparison already uses. Those cases are
counted separately so the two are not conflated.

### `RenamesToLeader` cannot store its own orientation

The two sections above orient a *rule*. This one is about the relation: its orientation
is a function of value order, and `union` rewrites a row's endpoints, so a row that was
oriented when written can be backwards afterwards. Nothing put it back.

A backwards row is what lets transitivity and single parent disagree forever. On the
SDQL batax term the tables sat at 648 rows with `saturate` reporting progress, four
edges swapped every iteration, period two. Backwards rows by user step were 0 0 0 0 2 7,
and the machinery stopped saturating at step 6 — exactly where the seventh appeared.
`child-update`'s `(union node (Ctor …))` is the site: disable that family and the count
goes to zero. No rule *writes* a backwards row; every writer checks.

Repairing the row in place does not work, and this is the part worth remembering.
Transitivity has no orientation awareness, so it re-derives the backwards row as fast as
a repair flips it — measured, oscillating between 24 and 26 rows forever. The fix has to
be structural: `Equated` holds the fact with no orientation picked, three rules derive
`RenamesToLeader` from it always putting the smaller value in the leader column, and a
stale row is simply deleted, which is safe because the fact survives in `Equated`. With
one writer, the delete cannot fight anything.

Everything relating two *different* values writes `Equated` — transitivity, single
parent, `Var` normalisation, the alpha-finder, the binder strip, and every compiled user
action. Self-loops keep writing directly; there is no orientation to pick. Afterwards the
machinery saturates to step 11 on batax rather than step 5, with no derivation lost:
100/100 isomorphic at identical class, node and symmetry counts.

One deliberate consequence: a class's symmetry group now lives on the *leader* only,
where it used to be copied to every member. Followers hold no e-nodes once the machinery
has saturated, so the leader is where a query reaches it.

### Child-update needs the same orientation migration does

**Corrects two earlier accounts of this.** It was first reported as the binder rule
against single-parent, which cannot fire on a self-loop at all; then as an edge narrower
than its child, which it is not. Both are wrong. What follows is traced rather than
inferred.

Table *sizes* are stable but contents are not. Keyed on payload and renamings -- which
print structurally, unlike child values, which print by extraction and so change whenever a
class becomes unextractable -- `fuzz77`'s lambda row alternates every round, and so does
its child's slot set:

| | the lambda's 2nd edge | its child's `ClassSlots` | Def. 4 |
| --- | --- | --- | --- |
| run 120 | `{0→2}` | `{0}` | domain = child's slots ✓ |
| run 121 | `{2→2}` | `{2}` | domain = child's slots ✓ |

Both spellings are *well formed*. What alternates is which value of the child's slotted
class the edge points at: one names its slot `0`, the other names it `2`, and they are two
members of one slotted class. At each phase there is a `RenamesToLeader` edge from the
current child to the other one.

**So it is the same bug as migration's ping-pong, in a rule that never got the fix.**
`RenamesToLeader` holds both directions between two values of one class, and
`child-update` follows *any* edge:

```lisp
(rule ((RenamesToLeader c2 m c')
       (= node (App2 p1 m1 c1 m2 c2))
       ...)
      ((union node (App2 p1 m1 c1 (compose m2 m) c'))
       (delete (App2 p1 m1 c1 m2 c2))))
```

Nothing says which of `c2` and `c'` is more canonical, so it rewrites the pointer one way
and back, deleting and rebuilding the node row each round. The fix is the atom migration
already carries:

```lisp
(= c2 (ordering-max c2 c'))       ; toward the leader only
```

When the child's class is unchanged the atom holds trivially, so the self-symmetry case the
rule also handles is unaffected.

This is why the self-loop rule looked like the culprit: its one input table genuinely does
have a new row each round, which is all semi-naive needs to re-fire it. The pair below is
downstream of the node-row churn, not the cause, and **asking whether the self-loop rule is
needed at all was what exposed that** -- a rule cannot re-derive from an unchanged row, so
the row could not have been unchanged.

**The symmetry-finder had the same defect, and fixing it closes all but one case.**
`sym_out` is solved from a *node's* edges, so its domain is the node's slots, and a node
may carry slots its class does not depend on — so unrestricted it asserts a symmetry the
class does not have. The shrinking rule deletes that, the rule derives it again, and
neither wins. On `fuzz52` the visible symptom is a self-loop on a **slotless** class,
renaming `{1→1}` one round and `{0→0}` the next. Restricting on both sides by
`ClassSlots`, which only narrows, leaves nothing to shrink:

```lisp
(= cs (ClassSlots e)))
((RenamesToLeader e (compose cs (compose sym_out cs)) e))
```

| `fixpoint.py fuzz 250` | |
| --- | --- |
| before either orientation fix | 8 known failures |
| after orienting `child-update` | 245/250 |
| after restricting the symmetry-finder | **249/250** |

The self-loop rule was the obvious suspect and is **not** the cause: rewriting every
self-loop to derive from `ClassSlots` leaves all five failing, and `ClassSlots` is empty
for the class whose self-loop churns, so a self-loop naming slot 1 cannot come from it.
That experiment is what pointed at the symmetry-finder instead.

**The one that remained was not a maintenance-rule cycle, and the schedule is what fixed
it.** `fuzz179` has period *three*,
and both of its rules are self-referential:

```text
?x3 == h(?x1,?x2)   =>   ?x2 = h(?x3, ?x2)      the class becomes a node containing itself
?x3 == h(?x2,?x1)   =>   ?x3 = h(?x3, ?x3)      ... in both positions
```

Six rules fire on every round of the orbit, named from egglog's per-rule log
(`RUST_LOG=debug`) matched back against the rule texts:

| | |
| --- | --- |
| both compiled user rules | build a node containing the class being defined |
| migration | re-frames those nodes onto the leader |
| the self-loop rule, the symmetry-finder, `ClassSlots` | react to each new node |
| `encoding-11`'s "equal up to some identity renaming" merge | retires variants |

What churns are α-variants: same operator, same children, renamings differing by swapping
slot names `0` and `2`.

```text
run 120 -> 121   gone  h {2→2}/{2→2}
                 new   h {0→0}/{2→0}   h {0→2}/{0→2}   h {2→0}/{0→0}   h {2→0}/{2→0}
run 121 -> 122   gone  h {0→2}/{2→2}   h {2→0}/{2→0}   h {2→2}/{0→2}
                 new   h {2→2}/{2→2}
```

The mechanism is a loop through *spellings*, not through facts. An action builds a node
with whatever renamings the compiled rule solves for; the maintenance rules re-frame or
retire it, which changes rows; a changed row is a new row, so the user rule matches again
and builds the next spelling. Only slots `0` and `2` are ever in play, so the set of
spellings is finite and the state orbits instead of growing.

**The reference settles on the same input**, because a class stores
`nodes: HashMap<L, ProvenSourceNode>` keyed by canonical *shape*: building `h(x,x)` under
any slot naming hits the same key, the second build is a no-op, and nothing re-fires. Here
a row is keyed by the whole tuple, renamings included, so each spelling is a distinct row.
That is the divergence recorded under "growth, not a missing merge", and this is its
sharpest instance.

Worth being clear about severity: **no answer is wrong**. The partition agrees on this case,
and the isomorphism check finds 0 differences on all 248 comparable cases. What diverges is
termination, so it is a cost-and-schedule problem rather than a soundness one.

Two candidate fixes were on the table, and the second turned out to be enough:

* **An α-invariant key for rows**, which is what the reference has — a redesign of how
  nodes are stored, and still the deeper answer to the row-keying difference.
* **Phasing with rulesets**, which is what was done: saturating the invariants before any
  user rule fires means an action's build lands on an already-canonical row and creates
  nothing new, so the user rule does not re-fire on its own output. See "The invariant
  rules are saturated between user-rule steps" above. `fuzz179` now finishes and the
  generated corpus is 250/250.

### Downstream: a binder makes open question 2's pair permanent

Asking for `saturate` on the generated corpus turned up cases that never terminate,
and they are *not* the α-variant growth below: every table keeps the same *size* from 10
rounds to 240, and the database size oscillates by one row forever. Row *contents* do
change, which is the section above.

`RUST_LOG=debug` makes egglog name the rules that still match, which is quicker than
guessing at it:

```text
size 51, updated=true, top_matches=[... (rule ((RenamesToLeader (App2 'lambda' ...
size 50, updated=true, top_matches=[(rule ((RenamesToLeader a m1_o c) ... =7, ...
```

The cycle is **open question 2's own pair** — the self-loop rule against the shrinking
rule — and the binder rule is what makes it permanent. On `fuzz77` the lambda node is
`L = lambda {0→1}(Var 0) {2→2}K`, whose own slots are `{1,2}`:

| | derives | |
| --- | --- | --- |
| self-loop rule | `RenamesToLeader L {1→1,2→2} L` | the identity on the *node's* slots |
| binder rule | `RenamesToLeader L {2→2} L` | the same, bound slot `1` removed |

The shrinking rule then has `m1 = {1→1,2→2}` and `m = {2→2}`: `m` is idempotent,
`m2 = m·(m1·m) = {2→2} ≠ m1`, so it deletes the wide loop. Next round the self-loop rule
re-derives it — from a node row that has itself been re-created, per the section above.
`RenamesToLeader` flips 13 → 12 → 13 with period 2, forever, and `single-parent` is not
involved at all: its `(!= a b)` and `(!= a c)` guards stop it firing on a self-loop.

**This falsifies the convergence claim in open question 2.** That claim was measured on
five curated cases, where the too-wide loop is derived once and then gone. A binder is
different: the narrow loop is not a transient to be cleaned up, it is *permanently*
correct and permanently narrower than what the self-loop rule keeps re-deriving. So the
two rules sit in a stable disagreement rather than converging.

The lesson from migration applies unchanged — **a rule that both builds and deletes needs
an orientation that strictly decreases** — and here the fix would have to stop the
self-loop rule asserting the node's slots as the class's, which is the "do not derive a
class-level fact from a node" advice that question 2 already draws.

Bisecting by rule kind is worth distrusting here. Removing migration makes these cases
terminate, which looks like an accusation but is not one: removing it changes the state
the run ends in, and *that* state happens to be a rule fixpoint. Migration cannot fire at
the oscillating state at all — a faithful copy of its premise matches zero times. The
per-rule log is what actually identifies the pair, and the same caution applies to the
bisect that was run for migration.

**It is strictly sharper than the partition.** Put each known bug back and it fails on
more cases than the matching comparison does, and it is the only comparison against the
reference that saw `wide-kids` at all, which until then only an internal invariant caught.
The figures below are from *before* the schedule was phased; that change made `wide-kids`
benign, so it is now caught by nothing:

| | matching mismatches | non-isomorphic |
| --- | --- | --- |
| `root-only` | 11 | **12** |
| `union-id` | 2 | **4** |
| `slot-late` | 1 | **2** |
| `unordered` | 1 | 1 |
| `binder-1st` | 0 | 0 |
| `wide-kids` | 0 | **1** (0 since the schedule was phased) |

`binder-1st` remains caught only indirectly, by the order-independence check.

A comparison that always answers "isomorphic" would pass every corpus just as quietly,
so `isomorphism.py selftest` pins the three answers that matter on hand-built graphs,
with no egglog and no reference involved: a graph with every slot renamed must be
*accepted* and its witness must verify, and the two subtlest ways to differ — a class
missing one symmetry, and one edge moved onto another slot — must be *rejected*. The
second of those is rejected by exhausting the search, which is what makes a negative
answer worth anything.

### What "the same slotted class" means, settled by counting

A slotted class spans several `U` values, and which values are one class was not pinned down
-- two attempts at merging them for the isomorphism check failed in *opposite* directions,
one over-merging and one under-merging. Counting settles it, without needing to merge
anything:

    slotted classes  =  ClassSlots rows  -  values with a strictly smaller peer

Compared against the reference's class count, with "peer" read two ways:

| | reference | bijective links only | any link |
| --- | --- | --- | --- |
| `C13` | 9 | 10 | **9** |
| `NR1` | 4 | 4 | **4** |
| `fuzz42` / `fuzz79` / `fuzz140` | 9 / 7 / 9 | 10 / 8 / 10 | **9 / 7 / 9** |

So it is **any** `RenamesToLeader` link, partial ones included, and the count has to mark the
larger value whichever way round the row names the pair -- a link is not always stored both
ways, and marking only one side reported a class with no non-canonical members when it plainly
had a peer.

That reading is right because a
partial `m` in `a = m*b` is the redundancy relation, saying b's class does not depend on the
slots `m` drops, and the reference models that as one class with the smaller slot set rather
than as two classes. `class-count.py` is the check, at **44/44 curated and 250/250 generated**. `fuzz130` agrees
too, once both directions are marked: its apparent extra class was this check's own hole, not
the encoding's.

Two things follow. `NR1` counts correctly under either reading, so the over-merge my second
merge attempt showed there was its *frame translation* and not its criterion -- which is the
remaining work for `fuzz130`. And no case in either corpus has the encoding with *fewer*
classes than the reference, which is the direction that would mean merging two classes the
reference keeps apart -- invisible to the probe partition, since that only compares the terms
it was given.

### Def. 4 is checked exactly, in one comparison

The two halves used to be checked separately and partially: `check 6` looks for an edge
wider than an idempotent self-loop on its child, and the narrow half was recorded as "not
checkable this way" and left to `compose-total`. Both are one comparison against
`ClassSlots`, which is where a class's slots are held —

```lisp
(!= (map-domain m) (ClassSlots c))
```

— since `map-domain` and `ClassSlots` are both identity maps, so comparing them is set
equality. `slotted/xdiff/def4-edges.py` reports **0 over 44 curated and 250
generated cases**.

**This is what makes `wide-kids` benign rather than luckily undetected.** An action reads
renamings off a matched node, and narrowing them by `ClassSlots` is a no-op exactly when
those renamings already have the child's slots for their domain — which is what this checks,
and what the phased schedule guarantees by saturating the invariants before a user rule can
match. So the mutation is undetectable *because* of a property now checked on every case,
and if this check ever fires the mutation becomes live again. That is the honest form of
"this test no longer discriminates": a reason, mechanically monitored, rather than a gap.

That probe earned its keep immediately, by refuting a claim rather than confirming one. The
one case the isomorphism check cannot decide, `fuzz130`, appeared under an attempted fix to
have an edge whose domain was empty where the reference's was not — which would have been a
narrow violation and the first real difference found. It was not: the probe queries egglog
directly for `map-length m < map-length (ClassSlots child)` and reported zero, so the empty
edge was manufactured by the fix, not present in the encoding.

The mechanism was this file's own most-repeated warning. Translating a node into another
frame by composing with a map over the *class's* slots truncates any slot the node carries
that its class does not — which Def. 4 permits nodes to do — so the redundant slot is
silently dropped:

```text
u = {2→0}   the value's class slots to its representative's
m = {0→0}   an edge whose image is the node-local slot 0
compose(u, m) = {}          the slot is gone
```

**The merge is in the tree now, and the printed name was what blocked it.** Membership is any
`RenamesToLeader` link (settled above, and checked independently by `class-count.py`), but
while the merge keyed values by the term they printed as, several distinct classes printed as
`Unextractable`, collapsed into one value, joined components, and left *fewer* classes than the
reference:

| | classes printing `Unextractable` | merged result |
| --- | --- | --- |
| `X2` | 4 | 4 classes where the reference has 5 |
| `S1b` | 4 | 6 where the reference has 7 |
| `NR1` | 2 | 3 where the reference has 4 |
| `C13` | 1 | correct |

Only the cases with more than one such class came out wrong, which was the whole story --
`C13`, with one, was correct. Reading the serialized e-graph instead of the printed tables gives
each class an identity and the merge then works; see "Reading the encoding by identity, not by
rendering" above.

Two limits worth stating.

* A class with more than six slots is reported rather than enumerated, since the group
  is recovered by trying every permutation.
* The identity is added to every group before comparing, because a slotless class's
  identity is the empty permutation and the reference prints it as an empty field. So a
  *missing* identity self-loop is not what this check detects — that is a reachability
  question, and `stranded.py` is what asks it.

Either is counted as *not comparable*, separately from *differ*, so a limit of the tooling is
never presented as a finding about the encoding. Neither occurs on the corpus.

### Reading the encoding by identity, not by rendering

The encoding side used to be read from `print-function`, which renders a `U` value by
*extracting* a term for it — and a value whose rows have been deleted, or whose child's have,
has no term and prints as the single word `Unextractable`. Several distinct classes then share
that one name. That cost the comparison two things: the several `U` values of one slotted class
could not be merged into one class, so a case where they both held nodes was undecidable; and
three attempts at merging them all failed, each collapsing exactly the classes whose names had
collided.

`--to-json` names a class `{sort}-{canonical value}`, which is an *identity* rather than a
rendering, so the problem disappears. Everything needed is in that serialization: each row is a
node with an `op`, the `eclass` it belongs to, and `children` naming other nodes; renamings come
back as `map-of` nodes over `i64` nodes, so their contents are readable too.

With identities in hand the merge is straightforward — components of any `RenamesToLeader`
link, each member's contents carried into the representative's frame, and rows that then
coincide treated as one node, as in the reference, whose class keys its nodes by shape.

| | before | after |
| --- | --- | --- |
| generated isomorphic | 249/250, 1 not comparable | **250/250, 0 not comparable** |
| curated | 44/44 | 44/44 |
| mutation sensitivity | root-only 12, union-id 4, slot-late 2 | unchanged |

### The other divergence is growth, not a missing merge

`X1` looks like the same kind of gap -- one `h` node too many -- but it is not. Its
node count *grows* with the round budget: 7, 7, 7, then 9 at eighty extra rounds, and
identically so under the old tie-break, so this is neither caused nor cured by the
change above. `X1`'s rule builds a node equal to its own child, and the encoding makes
a new row per spelling where the reference keeps one entry per *shape*, so alpha-
variants accumulate faster than the alpha-finder retires them. The reference saturates
at six.

That is the same root cause as the minting fan-out: a row is keyed by its renamings, and
the reference's node key is a shape.

**The alpha-finder does keep pace, and that is measured.** An alpha-invariant key for rows
would remove the difference at the source, but it is not needed to match the reference: the
encoding ends with the same number of e-nodes per operator on **250 of 250** generated cases
and 44 of 44 curated, and the isomorphism check -- which compares node sets and needs equal
multiplicities -- finds **0 differences** on all 249 comparable generated cases. So no
surplus alpha-variant row survives to the fixpoint. What the keying difference costs is
transient rows during the run, not a different answer.

### An upstream crash, found while modelling the class slot set

Looking at how the reference holds a class's slots turned up a panic in it. Shrinking
a class whose symmetry group is non-trivial:

```text
term  (f (var $0) (var $1))
union (f (var $0) (var $1)) (f (var $1) (var $0))     ; the class becomes symmetric
union (f (var $0) (var $1)) (g (var $1) (var $1))     ; and then its slots shrink

SlotMap::index($f2): index missing!                   (group/mod.rs, build_ot)
```

Neither union alone does it; the symmetry and the shrink are both needed.

`restrict_proven` filters a permutation by its *keys*, so with `cap = {1}` the swap
`{0→1, 1→0}` becomes `{1→0}` -- which maps a surviving slot outside `cap`. That is not
a permutation of `cap`, and composing it later indexes a slot the map does not have.

The fix was already written in the same function and thrown away. `final_cap` removes
the orbit of every newly redundant slot, so no surviving slot can be moved out, but
`c.slots` and the generator restriction both took `cap` instead. Using `final_cap`
fixes the panic, and in the case above gives the right answer for a second reason:
`orbit(0) = {0,1}`, so both slots are redundant, which is what the comment on that loop
says should happen.

The reference's suite is unchanged by it -- 105 pass before and after, with the same
three pre-existing `redundancy_matching_bug` failures -- and our corpus still agrees
43/43.

The fix is part of PR #45 itself -- pushed to its head branch,
`oflatt-claude/slotted-egraphs:multipat-subst-canonicalisation` -- so the oracle and the
reference we claim to match are the same code, with no out-of-band patch to remember.
It carries `tests/fgh/shrink_with_symmetry`, which reproduces the panic without it.

That test asserts the surviving slot count is what it is, not that it is optimal. One
slot is redundant and the class is symmetric in the two, so a stronger shrink may be
justified -- and the class does come out with one slot, not none, so using `final_cap`
is not by itself the orbit-closure the discarded code was reaching for. Whether the slot
set should shrink further is a separate question from the crash, and this does not
settle it.

### Which slotted-egraphs is this compared against?

Upstream `main`, pinned to `b90adca` in `slotted/xmulti/Cargo.toml` --
a rev rather than a local checkout, so a CI runner can build the oracle. That is `main`
after PR #45 was merged, and two things in it matter.

The first is the fix PR #45 carried: `extend_subst` canonicalising the child
`AppliedId` through the slot union-find. The second is newer and costs us matches --
`final_refine`, which takes every slot pair e-matching left undecided and branches on
BOTH readings, once with the slots unified and once with them apart. The encoding has
no such branch: an unconstrained slot is minted, a fresh name differs from everything,
so it only ever takes the "apart" one. Moving to this base took the deep sweep from 17
divergences to 278, 229 of them ours, with nothing in the encoding changed -- the
oracle got sharper and showed a gap that was always there. `FINAL_REFINE_GAP` in
`slotted/xdiff/xdiff.py` pins the two curated cases that show it.

On PR #45's own contribution: `multipat.rs` is in `main` too, so the multipattern
matcher is not new; what that PR added was the one-line fix.
Without it a child bound after the matcher merges a freshened bound slot keeps the
pre-merge name -- surviving into the returned `Subst` only when the child binding is
the last thing to happen, so a single-atom pattern or the last child of the last atom.
For a binder that means the body comes back over a *fresh* slot instead of the bound
one, and the binding escapes.

Six of the curated cases can tell the two apart, and the encoding agrees with the
fixed one:

| case | fixed | buggy |
| --- | --- | --- |
| `U1` | `[0,1,2][3]` | `[0,1][2][3]` |
| `B3` | `[0,1][2]` | `[0,2][1]` |
| `CD1` | `[0,1,3][2]` | `[0,1,2,3]` |
| `CD2` | `[0][1,2][3]` | `[0,1,2][3]` |
| `CD3` | `[0,2][1][3]` | `[0][1][2][3]` |
| `CD4` | `[0,1][2][3]` | `[0][1][2][3]` |

All four conditional cases are sensitive, which follows from the symptom: a slot
condition asks about the body's slots, which is exactly what the bug corrupts. Under
the buggy version `notin` wrongly succeeds, so `CD1` and `CD2` over-fire, and `in`
wrongly fails, so `CD3` and `CD4` never fire at all.

`slotted/xdiff/oracle-diff.py` runs the corpus through two oracle
binaries and reports which cases separate them. Worth running whenever the reference
is bumped: a case that stops distinguishing them has lost coverage, and a new
disagreement is either a fix or a regression upstream.

### Multipattern matching is strictly stronger than single-pattern

Worth knowing before porting the paper's experiments, because those are written as
*nested single patterns* while this encoding matches the *flattened* form. The
reference's own property test is deliberately one-directional -- every equality the
nested form proves must also be proved by the flattened one, and "the converse is
deliberately not required: the depth-1 matcher sees through redundant slots that
`ematch_all` does not, which is the point of it".

Measured, rather than assumed. `slotted/xdiff/nested-vs-multi.py`
reconstructs a nested pattern from a case's atoms where they form a tree, runs the
reference both ways, and compares: **27 of the curated cases run both ways, and 3
differ** -- and in each the multipattern proves more, never less.

| case | multipattern | single nested |
| --- | --- | --- |
| `C5-redundant-same-node` | `[0,1][2]` | `[0][1][2]` |
| `C6-redundant-two-nodes` | `[0,1][2]` | `[0][1][2]` |
| `B3-same-slot-literal-two-binders` | `[0,1][2]` | `[0][1][2]` |

All three turn on a redundant slot or a slot literal, which is exactly the case the
upstream comment names. So a ported experiment can legitimately derive *more* than the
paper's original run did; that is the flattening being stronger, not a divergence to
fix. Whether it shows up on the paper's own rules is open until those cases exist --
they do create redundancy, through a `let` whose body ignores the bound variable.

Sixteen cases cannot be compared this way at all: a shared subterm (which is the whole
reason multipatterns exist), a side condition, an `=` action, or an action naming an
intermediate atom root, which nesting absorbs.

### Ported from the crate's own suite, and what is not

`P1` and `P2` are `regress::same_node_redundant_slots_stay_distinct` and
`live_slots_of_one_class_stay_distinct`. `B3` is
`known_bugs::lambda_bug_reaches_the_goal_under_multipat`.

Not ported, with the reason:

* **`?q == (var $s)` atoms** (`slot_literal_over_redundancy`, and the eta tests) —
  the encoding has no `var` *node* to match. `(Var 0)` is a leaf class and the slot
  lives in the parent's edge, so there is no atom to write.
* **`known_bugs::bug2` / `bug3`** — they need three rules interleaved to
  saturation, and the harness runs one rule per case.
* **`props.rs` slot-renaming invariance** — the generator does not shift every
  slot in a program yet. Worth adding.
* **`refine.rs`** — both sides are incomplete in the same way, so there is nothing
  to compare; the crate marks them `#[ignore]` for the same reason.
* **`flattening_is_not_faithful_for_a_sibling_slot_literal`** — it compares nested
  against flattened matching *inside* the crate, and the encoding has no nested
  matcher to compare against.

### Checking that the tests still test something

Each past bug can be put back with `XDIFF_BUGS=`, and the corpus is expected to
notice:

```text
XDIFF_BUGS=root-only  ./xdiff.py     an atom's renaming from its root alone
XDIFF_BUGS=slot-late  ./xdiff.py     a slot literal checked after the renaming
XDIFF_BUGS=unordered  ./xdiff.py     atoms compiled in the order written
XDIFF_BUGS=union-id   ./xdiff.py     the action unions classes, not invocations
```

**Coverage is a property, so `mutations.py` asserts it** rather than leaving it to be
inspected by hand. Each mutation must still break the corpus by a recorded amount — fewer
means the corpus has stopped testing something, more means a case newly disagrees — and the
script exits non-zero either way.

A mutation earns its place by failing there. Two were removed once they stopped
discriminating, rather than kept as decoration:

* `wide-kids`, which left only the action's root narrowed to its class's slots. The property
  it stood for is checked directly by `def4-edges.py`, and that check is what makes the
  mutation benign — so the check is the thing to keep.
* `binder-1st`, which let a binder fix the pattern's slot space. That one was mis-framed as
  empirical: `slots(pattern)` is the pattern's *free* slots and a bound slot is not free, so
  the restriction follows from what the terms mean. Nothing observes it because there is
  nothing to observe, not because coverage is missing.

Where each is caught:

| bug | caught by | how |
| --- | --- | --- |
| `root-only` | C3, C5, C6, C9, C10 (+6 more) | disagrees with the reference |
| `unordered` | C12, C13 | disagrees with the reference |
| `slot-late` | B3 | disagrees with the reference |
| `union-id` | C14 | disagrees with the reference |


`wide-kids` **no longer discriminates anywhere** — not the partition, not the node counts,
not the Def. 4 invariant, not the isomorphism check. Saturating the invariants between user
steps means the renamings an action reads off a node are already canonical, so omitting the
narrowing changes nothing to observe. It is kept as a record rather than as coverage; see
"The invariant rules are saturated between user-rule steps". Before that change it was
caught by the Def. 4 check directly and by the isomorphism check as a consequence, and it
needed minting -- rather than declining to migrate -- to be reachable at all.

Two things this was worth doing for.

**Coverage decays silently.** Changing minting to smallest-unused made `C11` — the
witness for the only unsoundness found — stop testing what it was written for,
because under the new policy its root renaming comes out as the identity, and at
the identity the right and wrong spellings agree. The same happened to `R2` in
`slotted/encoding/multipat-diff.egg`. For a while nothing anywhere caught `union-id`.
`C14` replaces `C11`, with the action rooted at a *child* variable so its renaming
is a stored edge rather than the identity.

That also exposed a blind spot in the generator: it only ever rooted an action at
an atom root, and those usually carry the identity, so the class-versus-invocation
distinction went unexercised. Rooting the action at any bound variable finds
witnesses in the first handful of cases.

**A mutant has to be faithful, or it measures nothing.** The first `root-only`
switch dropped the child constraint *and* the occurrence check that the original
bug still performed, which makes the rule more permissive rather than
under-constrained — so it looked as though nothing caught `root-only`, when in
fact eight cases do.

`binder-1st` is still caught only indirectly, by order-independence rather than by
disagreeing with the reference. A direct witness would be better.

### Not covered

* **Symmetry branching.** The reference's `unify` returns several states when two
  invocations differ in two or more slots and more than one pairing is legal,
  where a primitive returns one. `U1` builds the shape deliberately — two atoms
  over a node whose slots are both redundant, so each lookup freshens them
  independently — and both sides still agree. Two constructions tried, neither
  discriminates, so the question is *open, not settled*: the encoding may be fine
  here, or the observable may simply be too coarse to see it.
* **Other action shapes.** Two are now generated: building a node, and equating
  two variables (`E1`–`E3`), which is the union of two invocations egglog's own
  `union` cannot express. Nothing exercises a right-hand side deeper than one
  level, or the `Subst` form.
* **Cost.** The one performance problem found turned out to be the minting policy
  above, and no case in 250 now times out or fails to settle. That is not the same
  as knowing the encoding is fast: nothing here is a benchmark, the terms are tiny,
  and the machinery has known derive-and-delete pairs that do redundant work.

## Mistakes worth not repeating

Each of these was silent, and each cost a round of confusion.

**In the encoding**

* *`union` in an action off the identity renaming* — asserts a false equation,
  absorbed as a spurious redundancy. `C11`.
* *An atom's renaming solved from its root alone* — under-constrained as soon as a
  node carries a redundant slot.
* *Atoms compiled in the order written* — an unconnected atom invents slots it
  cannot revise, and loses matches. `C12`.
* *A slot literal checked after the renaming was solved* — same failure: two
  binders written with the same slot each invent their own, then cannot agree.
  Constrain with it, do not check against it.
* *Invented slots colliding across atoms* — the avoid-set has to accumulate.
* ***`compose` truncates, silently.*** It keeps only the keys whose value lies in
  the left map's domain, so every `(compose a b)` on an edge is a place a slot can
  disappear — and a narrowed edge asserts its child is slotless. This one mistake
  is behind the fresh-slot gap, the `M3` unsoundness, and the migration bug above.
  The lesson is not "avoid `compose`" — narrowing is correct for partial maps, and
  two rules depend on it. It is that **an `App` edge is the one place narrowing is
  always wrong**, so use `compose-total` there and let the primitive hold the
  invariant. Wherever you use plain `compose`, ask where the result lands.
* ***A deleted fact does not come back.*** If rule A derives a fact from a row and
  rule B deletes that fact, A will not re-derive it — semi-naive fires A on a *new*
  row, and the row is no longer new. So a maintenance rule that deletes another
  rule's output has permanently overridden it, not temporarily. This is the whole of
  `Case 14`, and it is the same shape as open question 2. Before writing a `delete`,
  ask which rule produced the thing and whether it could ever fire again.
* *Argument order.* The renaming comes *before* each child:
  `(App String Renaming U Renaming U)`, `(RenamesToLeader U Renaming U)`.
* *Child rewrite direction.* It is `(compose m1 m)`, not
  `(compose r_i (inverse R))`.
* *A variable reached two ways does not compile to `(= path_i path_j)`.* That is
  equality of renamings; it has to be the symmetry lookup above.
* *A head is not special.* A variable used as both a constructor head and a child
  is just a variable with two occurrences.

**In the test harness**

* *A slotted e-class is not an egglog e-class.* Grouping probes by egglog class is
  strictly finer and reports differences that are not there.
* *`eg.eq` is not class identity.* It compares invocations, so it depends on which
  slot names survive a redundancy.
* *A bare leaf at top level loses its slot.* This alone accounted for every
  apparent machinery difference: 13 of 200 before the fix, 0 after.
* *An operator can be named differently on the two sides.* The machinery's
  α-equivalence rule is written against the literal string `"lambda"`, so a rule
  compiled for `"lam"` silently matches nothing.
* *A regression case can stop being one.* Changing the minting policy left `C11`
  and `R2` passing whether or not the bug they were written for was present. Put
  the bug back and check the test fails — `XDIFF_BUGS=` exists for that.
* *And so can a mutant.* If the switch that puts a bug back does not reproduce
  what the bug actually did, the coverage it reports is fiction in either
  direction.
* *A generator's defaults are part of its coverage.* Rooting every action at an
  atom root meant the action's renaming was almost always the identity, so nothing
  exercised the difference between unioning classes and unioning invocations.
* ***A stable row count is not a fixpoint.*** Every probe here reads the state after
  `(run N)`, which stops after N rounds whether or not anything is still firing. Two
  rules deleting and rebuilding the same row leave every table size-stable — `MR1` was
  constant from round 4 to round 200 while never terminating. Only `saturate` separates
  them, which is `fixpoint.py`.
* *A probe over hand-picked cases measures those cases.* `fixpoint.py` checked five,
  and the one case that did not terminate was not among them. It now runs the corpus.
* *Read the relation's direction before reading its name.* `RenamesToLeader` holds
  both directions for a pair, so "has an edge to a different value" is true of the
  leader too. A probe built on that reported a follower holding a node when the node
  was on the leader; a follower is a value with a strictly *smaller* peer.

## Cost

Per rule, against a non-slotted encoding: one extra `Renaming` column per child
position per atom; one fully-bound `RenamesToLeader` *lookup* per repeated
occurrence; one `find-mapping-total` per atom, with a `RenamesToLeader` *join* per
variable it is constrained through. Only the joins fan out, and `RenamesToLeader`
is small — usually one self-loop per class.

## Where `compose` can lose a slot

`(compose a b)` keeps only the keys of `b` whose value lies in `a`'s domain, so
every composition is a place a slot can silently vanish. That is not a defect —
it is the composition of partial maps, and two things depend on it. Auditing each
site in the machinery, and checking on real cases which ones actually truncate:

| site | truncation | why it is or is not a problem |
| --- | --- | --- |
| idempotence tests — `(bool= (compose m m) m)`, and the shrinking rule | intended | truncation *is* the test: it is how a non-permutation is detected |
| child-update, `(compose m1 m)` | impossible | `m`'s image is inside `m1`'s domain by well-formedness |
| **migration**, `(compose (inverse m) m1)` | **observed** | **was unsound**: the narrowed edge is asserted as fact, claiming its child is slotless. Now `compose-total` |
| single-parent, `(compose (inverse m1) m2)` | possible, never observed | lands in a `RenamesToLeader` row, where a partial map is meaningful. 0 occurrences across the corpus |
| transitivity, `(compose m12 m23)` | observed on `X1` | same: narrowing through a partial self-loop says the slots are redundant, which is what a partial map means there |
| α-finder and symmetry-finder, `(compose m_o sym)` | observed on `X1` | feeds `find-mapping`, which requires equal key sets, so a narrowed map makes the rule *not fire*: incomplete, not unsound |
| `MISC`, `(compose m1 (inverse m2))` | possible | only feeds an idempotence test, so a truncation means no union: incomplete, not unsound |

The first reading of this table was "truncation is harmless where it makes a rule
decline, dangerous where the composed map is inserted as a fact". That is wrong:
single-parent and transitivity both insert composed maps and are fine. **What
matters is where the map lands:**

| landing site | may it narrow? | why |
| --- | --- | --- |
| an `App` **edge** (`m1`/`m2`) | **never** | Def. 4 requires `dom(m) = slots(child)`, so a narrowed edge misstates *the child* |
| a `RenamesToLeader` renaming | yes | a partial map is meaningful there — it is how a redundant slot is recorded |
| the input to a test | yes | failure just makes the rule decline |

Only the first line needs anything from the primitives, and only two sites produce
an edge from a composition: migration, and child-update where it cannot happen. So
migration uses `compose-total`, which refuses to drop a key, and the guard that
used to compare `map-length` by hand is gone — the invariant is stated once, in the
name of the primitive, instead of re-derived per site. A narrowing composition can
no longer reach an edge position by accident.

## Primitives

What the encoding relies on. All of these were already here, ported from
[`memoryleak47/egglog@slotted-encoding2`](https://github.com/memoryleak47/egglog/tree/slotted-encoding2)
and rewritten against this tree's `add_primitive!`, **except
`find-mapping-total`**, which is new:

* `egglog/src/sort/map.rs`
  * `map-union` — partial-map union, fails on a conflicting key.
  * `compose` — `(compose a b)[x] = a[b[x]]`; explicit partial maps, so a missing
    key means "no mapping", not "identity".
  * `compose-total` — the same composition, refusing to drop a key. For the one
    place narrowing is always wrong: a result that becomes an `App` edge.
  * `map-image`, `map-domain` — a renaming's two slot sets, as identity maps.
    Slot sets *are* identity renamings here, so these name what used to be spelled
    `(compose m (inverse m))` and `(compose (inverse m) m)`. The node-slots idiom
    `(find-mapping p1 p2 p1 p2)` becomes
    `(map-union (map-image p1) (map-image p2))`, which says what it is.
  * `inverse` (also `map-inverse`) — rejects a non-injective map, whose inverse is
    not meaningful. Measured: the machinery never builds one, so this only turns a
    silently wrong answer into a rule that does not fire.
  * `find-mapping` — variadic, taking the two tuples flat as `[first…, second…]`.
    Strict: a paired `(first[i], second[i])` must carry the same key set, and the
    result must come out functional and one-to-one. That one-to-one check is
    load-bearing — it is what keeps `k($50,$50)` and `k($50,$60)` apart.
  * `find-mapping-total` — as above, extended to be total on a domain, inventing
    slots for the keys the constraints leave unnamed. `Map i64 i64` only, since
    inventing a slot needs the space ordered and unbounded above.
* `egglog/src/lib.rs` — `bool=`.
* `egglog/src/sort/bool.rs` — `and` made variadic, like `or`.

The renaming primitives are registered only when the key and value sorts match,
and deliberately not reserved: reserving `compose` breaks
`egglog/tests/tricky-type-checking.egg`, which declares its own.

Not ported: `shape2` (no consumer here), `has_delta` (a stub), and the `Vec i64`
flavour of `find-mapping` (a different representation).

## Open questions

1. **Choice of first atom.** It must not be a binder (`C13`), and beyond that the
   choice decides how many atoms have to solve for a renaming. Probably pick the
   one with the most shared variables, or leave it to the query planner. Also
   unsettled: what to do when *every* atom is a binder — the compiler currently
   just takes the first, and no test forces the question.
2. **Are self-edges derived from nodes a problem?** Two machinery rules derive a
   class-level self-edge from a node's own edges. Under redundancy that states
   something false about the class, and although the shrinking rule deletes the
   too-wide identity, semi-naive never re-runs the derivation, so the saturated
   state is not a fixpoint of its own rules. It reproduces in eight lines:

   ```text
   (relation SymSeen (U Renaming))
   (rule ((RenamesToLeader c m c)) ((SymSeen c m)))

   (let $f (App2 "f" (map-insert (map-empty) 0 0) (Var 0)
                    (map-insert (map-empty) 1 1) (Var 1)))
   (union $f (Null))
   (run-schedule (saturate (run)))

   (check      (SymSeen (Null) (map-empty)))
   (fail (check (SymSeen (Null) m) (!= m (map-empty))))   ; fails
   ```

   **Measured, and there is no rule to fix.** The shrinking rule does narrow the
   too-wide identity away: with a narrow idempotent `m` beside a wide `m1`,
   `compose m (compose m1 m)` is the narrow one, so the rule deletes `m1`. In the
   eight-line case above the wide loop is derived and then gone. Under
   `run-schedule (saturate (run))` all 44 curated cases now reach a genuine fixpoint,
   `X1` included. `slotted/xdiff/fixpoint.py` is the check, and it runs
   the whole corpus — it used to check five hand-picked cases and so missed the one
   case that did not terminate.

   **It does not converge with a binder, and that was measured later.** The claim above
   that "the pair converges whenever the program does" came from five curated cases,
   where the wide loop is derived once and then gone. Four generated cases show
   otherwise: the binder rule's narrowed self-loop is not a transient, it is
   *permanently* correct and permanently narrower than the identity the self-loop rule
   keeps re-deriving from the node, so the two sit in a stable disagreement.
   `RenamesToLeader` flips by one row with period 2 forever while every table stays the
   same size. Worked through under "A binder makes open question 2's pair permanent"
   above.

   So the shape of the mistake stands, and is now known to bite: **do not derive a
   class-level fact from a node**, and prefer a merge that can only move one way over
   two rules that derive and delete against each other.

   The same warning also caught an unrelated instance — migration deleting a node
   from one value and rebuilding it on the other, in both directions, because
   `RenamesToLeader` is symmetric. See "Migration has to be oriented" above. The
   generalisation: **a rule that both builds and deletes needs an orientation that
   strictly decreases**, or it is only a fixpoint of the database and not of itself.
3. **Redundant slots in the pattern's slots.** The pattern's slots are the first
   atom's *node* slots, which may include slots the class has already made
   redundant. That falls out for free, but it means the pattern's slots are not
   always a subset of the class's live slots — check nothing downstream assumes
   otherwise.
4. **Stranded nodes.** Fixed for the single-parent mechanism (`Case 14`), but `X1`
   still strands one row via the shrinking rule deleting a too-wide identity
   self-loop — question 2 above. That row is harmless (it has a visible α-variant),
   so the open part is whether the shrinking rule can strand a row that does not.
   `slotted/xdiff/stranded.py` is the detector: it reports, per case, how
   many rows no symmetry-joining rule can see and how many of those are α-variants
   of nothing visible. Worth running after any change to the maintenance rules.

## Def. 4 is checked, and the encoding breaks it

The reference asserts this outright, in `check_internal_applied_id`:

```rust
// 2. It needs to have exactly the same slots as the underlying EClass.
assert_eq!(&app_id.m.keys(), &eg.classes[&app_id.id].slots);
```

An edge's domain is *exactly* its child class's slots -- not wider, not narrower --
while a *node* may carry more slots than its class (`real.slots().is_superset`), which
is what redundancy is. The encoding has no such assertion, and `check_case`'s sixth
check now supplies one: wide edges and non-injective renamings in the final state,
with `KNOWN_WIDE` recording the accepted violations so a *new* one still fails.

It is not a curiosity. **Ten of 150 generated cases violate it**, all wide edges, none
non-injective -- while every one of the 150 still agrees with the reference on the
partition. So this is invisible to the comparison the suite was built around.

What is established about it:

* Only the **action** creates a wide edge. Baseline runs -- the same e-graph with no
  rule -- are clean in every case checked. `child-update` composes, which can only
  narrow; `migration` uses `compose-total`, which preserves the domain.
* Both failing curated shapes use the atom **root** as an action operand, and a root's
  renaming carries the matched *node's* slots, which exceed its class's under
  redundancy. The compiler knows and narrows by composing with a class self-loop.
* That narrowing is only as good as the self-loops. Question 2 means a class can carry
  a self-loop derived from a node, wider than the class, and composing with *that* one
  narrows nothing.
* The end state is not a fixpoint of the machinery's own rules. `child-update`'s
  premise still matches the offending row, so the count is stable at one because
  creation and deletion balance, not because nothing is happening. `X1` shows the same
  as an oscillation, 1, 2, 2, 1.

**Fixed, by holding the slot set directly.** The gap was that a class's slot set was
only ever implied by self-loops, which are derived from nodes and so can over-state it,
and a rule got whichever one the join bound.

```text
(function ClassSlots (U) Renaming :merge (map-intersect old new))
```

One slot set per class, narrowing on merge and so only ever shrinking -- what `c.slots`
and `cap` are in the reference's `union_leaders`. Each node offers its own slots as an
upper bound, and the merge keeps what *every* node of the class has, so anything only
some of them carry is redundant. Deriving it from a node is safe here precisely because
the merge can only narrow, which is the difference from the self-loop rule. Two rules
carry a slot set along a `RenamesToLeader` edge in both directions, since a slotted
class spans several egglog classes.

The compiled action then restricts a root's renaming by `ClassSlots` rather than by a
symmetry, and every violation goes:

| | before | after |
| --- | --- | --- |
| wide edges, curated | 1 (`X1`, allowlisted) | **0**, allowlist empty |
| wide edges, generated | 10 of 150 | **0** of 250 |
| node counts vs the reference | 41 of 43 | **43 of 43** |

`X1`'s extra `h` node was the same cause and went with it. Partitions are unchanged --
43/43 curated and 250/250 generated -- and the mutation matrix still discriminates
(`root-only` 11 cases, `union-id` 2, `unordered` 1, `slot-late` 1).

`ClassSlots` restricted only the action's *root*, which left the same violation
reachable through the action's other variables; `wide-kids` and `C15` are that gap,
under "Do follower classes need self-loops at all?" above.

## Machine-checked invariants

Def. 4 — an edge's domain is exactly its child's slot set — used to be maintained by
discipline alone. `slotted/xdiff/invariants.py` checks the half that is
provable, plus the precondition `inverse` relies on:

* **An edge wider than its child.** An idempotent self-loop `s` on the child is a
  partial identity, so `child = s*child` and every slot outside `dom(s)` is
  redundant: the child's live slots are inside `dom(s)`. An idempotent self-loop
  with *fewer* keys than the edge therefore proves the edge names slots the child
  does not have. Looking only for narrower witnesses is what makes this immune to
  question 2's too-wide loops — an earlier version compared against an arbitrary
  self-loop and reported eight "bad edges" on `X1` that were all a correct `{0→0}`
  edge to `(Var 0)` sitting beside a bogus `{0→0, 2→2}` loop.
* **A stored renaming that is not injective**, which is what `inverse` needs and
  nothing checked. Zero across the corpus, so `inverse` being strict costs nothing.

The narrow direction is not checkable this way, and is what `compose-total` now
prevents where it was reachable.

Across the corpus: 0 non-injective renamings, and one wide edge, on `X1`. It is
built by the compiled action out of question 2's surviving too-wide loop, and it is
inert — the slots it names are redundant for that child, so `m*c = c` either way.
Both probes take a snapshot: they declare their rules in their own ruleset and run
only that, because a relation keeps an observation after the row that caused it is
deleted, which answers a question about history instead.
