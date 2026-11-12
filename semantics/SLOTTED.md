# Slotted semantics (phase 1) and the slotted pass (phase 2)

The slotted layer ports the "Slots and Binders" and "E-Matching" semantics of the paper's
slotted section onto the plain specification under `EgglogSemantics/Spec/`, without
changing it. The slotted pass compiles a slotted program to a plain `Program` over a primitive
evaluation layer; its correctness proposition relates `SEval` to `Target.Eval`. Phase 3
is the proof of that proposition, including the maintenance and matching simulations.

## What exists

| Part | Module |
| --- | --- |
| The specification, one blueprint node per displayed definition, rendered by the `slotted` blocks of `paper/semantics.tex` under `make -C semantics paper-check` | `Slotted/Spec/{Binders,Slots,Congruence,Match,Eval,Step}.lean` |
| The parser for the slotted `.egg` subset, one slotted program per check, and its corpus report (`difftest slotted-parse`, `make -C semantics lean-slotted-parse`) | `Slotted/Tests/Parse.lean`, `DiffTest.lean` |
| The specification evaluated over a finite slot universe and a finite term universe, with soundness of what it finds | `Slotted/Tests/Bounded.lean` |
| The paper's distribution example and the `tests/slotted/paper` phenomena as `#guard`s, and the conservative-extension test against the plain interpreter | `Slotted/Tests/Examples.lean` |
| The slotted closure contains the plain one under the empty signature | `Slotted/Proofs/Conservative.lean` |
| The bounded evaluator against the Rust reference on the `paper/` corpus files (`make -C semantics lean-slotted-difftest`) | `slotted-difftest.sh`, `difftest slotted-bounded` |
| The executable slotted pass, its primitive target and phase 3 premises | `Slotted/Encode.lean`, `Slotted/Encode/`, `Slotted/Target/` |
| Compiled corpus outcomes against Rust, and checked hand-written snapshots | `slotted-compile.sh`, `Slotted/Tests/Compile.lean`, `tests/slotted/` |

## Layering

Slots are ordinary terms: the slot `$s` is `Term.app "$s" []`, recognised by its head
(`Term.isSlot`); its name is spelled with the `$`. In queries and actions a written slot `$v`
is stored as `Expr.var "$v"`, with a deterministic query binding to the name `$v`.
Ordinary variables range over renamed representatives. A concrete slot, such as one a `let` binds, is the term
`Expr.app "$s" []`. No core type changes; the plain `Cong`, `Matches`, `Reach` and `Eval` are
untouched, and the slotted definitions live beside them in namespace `Egglog.Slotted`.

A slotted program (`Slotted.Program`) is a plain `Program` together with a binder signature
`Binders := FnName → List (Nat × Nat)`; the pair `(j, i)` is the paper's
`(j, i) ∈ bind(f)`: argument `j` is a binding position whose slot is bound in argument `i`.
A binding position is a field of the head: congruence replaces term children only.

## Definitions and their paper names

| Paper | Lean (namespace `Egglog.Slotted`) | Node |
| --- | --- | --- |
| `bind(f)`, binding positions, `B_i(t)` | `Binders`, `Binders.isBinding`, `Binders.bindingPositions`, `Binders.boundIn` | `def:slotted-binders` |
| slot `$s`, `slots(t)`, all slot names of a term | `Term.slot`, `Term.isSlot`, `slots`, `allSlots` | `def:slotted-slots` |
| renaming `m`: finite partial injection, `dom`, `img`, `m⁻¹`, `m ∘ m'`, `m|_A`, `id_A`, `m_s^r` | `Renaming`, `Renaming.WF`, `.dom`, `.img`, `.inv`, `.comp`, `.restrict`, `Renaming.id`, `.update`, `.Covers` | `def:slotted-renaming` |
| the action `m * t` with fresh bound names | `Renames bind m t t'` (a relation: every fresh choice is a result), `RenamesList`, `plans`, `childMap`, `Fresh` | `def:slotted-action` |
| α-equivalence | `AlphaStep`, `AlphaEq` | — |
| `Rename` rule; `∼_E` closed under renaming; slot terms reflexive; congruence on term children only | `SCong bind db`, `SCongArgs` | `def:slotted-congruence` |
| redundant slot; live free slots `FS(E, t)` | `Redundant`, `liveSlots` | — (defined in prose) |
| `reps'(E)`, `live'(E, X)` | `sreps` (least stored spelling under `SCong`), `reps'`, `subsumed'`, `SameRow'`, `live'` | `def:slotted-reps` |
| slotted `G ≡ G'` | `SameMeaning'` | — |
| `Query'`, `App'`, fixed literal pattern slots; `Free`, `NotFree`, `free-names-are`, `renaming-=` | `SExpr.Matches`, `SMatches`, `ValidEnv'`, `SQueryMatches`, `SQueryHolds`, `Builtin`, `RenamingEq` | `def:slotted-query` |
| slots used only in actions receive fresh names; the slotted round `Run'` | `freshVars`, `FreshSlots`, `evalActions'`, `SRunRules` | `def:slotted-round` |
| slotted schedules and outcomes | `SReach`, `SEval`, `Slotted.Program`, `Program.Eval` | — |

### The action `m * t`

`Renames bind m t t'` holds when `t'` is a result of `m * t`: a slot goes through `m`; a
literal stays; for an application the binding positions receive pairwise distinct fresh
names, fresh for all slot names of the term and for `dom(m) ∪ img(m)`, each covered child is
renamed by `m` updated at its bound names (`m_s^r = (m \ {$s}) ∪ [$s ↦ $r]`), and every
other child by `m`. The relation holds only when `slots(t) ⊆ dom(m)`. Different fresh
choices give different results, all α-equivalent; `SCong`'s `rename` rule takes any result
on each side, so α-equivalent spellings of an existing term are congruent, as the paper
states.

### Redundant slots

A free slot `s` of `t` is redundant in `E` when renaming it alone to a name fresh for `t`
gives a term congruent to `t`: `$x·0 ∼ 0` makes `$x` redundant. `liveSlots E t` is
`slots t` without its redundant slots: a slot is free in a term when renaming it changes
the term's class. This is the paper's `FS`, which `free`, `not-free` and `free-names-are`
inspect. The definition stays in Lean; the displayed congruence node shows only `Rename`,
while `Slot` and `Cong'` remain constructors of `SCong`.

### Pattern slots and fresh action slots

A literal pattern slot `$x` denotes the slot named `x`; no name-assignment step precedes
matching. `ValidEnv'` stores these constants as deterministic environment entries and
ranges ordinary variables over `reps'`. Thus the only branching is over renamed
representatives. A slot used only in actions receives, in `SRunRules`, a name absent
from every value of the match; every fresh choice is a result of the round.

## Executable checking (bounded)

`Slotted/Tests/Bounded.lean` fixes a finite list of slot names `S` and a finite term
universe `U`, the subterm closure of the stored terms closed under renaming over `S`
(`termUniverse`), and computes:

- `injections A S`, all injective assignments of keys to `S`; `renameAll bind S m t`, every
  result of `m * t` with fresh names from `S` (`renameAll_sound`: each is a `Renames`);
- `scong bind S U eqs`, the least partition (`Classes`) of the known terms closed under the
  `SCong` rules with renamings over `S`: slot terms are reflexive, children of known
  applications exist, same-head terms of `U` with congruent children merge, and every pair of
  a class's first member with a member is renamed under every injection of their free slots
  (`closure_sound`: two terms in one class are `SCong`-related; symmetry and transitivity are
  the partition's);
- from a closure: `sreps`, `reps'`, `live'`, `redundant` and `liveSlots`, `renamingEq`, the
  reference evaluators `exprB`/`patternB`/`validEnvB` of the match judgement, and a
  join-driven candidate generator (an application pattern is unified against the live terms,
  a bare variable ranges over `reps'`, a literal slot denotes itself) whose output is filtered by
  the reference evaluators;
- `round`, `exec`, `observe`: the slotted round under every fresh choice from `S`, schedules
  with fuel, and the outcome of a slotted program. A check is decided on the universe seeded
  with the instances of its expressions under every assignment.

What is bounded: a pair the closure does not relate, a slot it does not find redundant, and a
check it finds to fail are statements about the universe. `Examples.lean` says for each
assertion which kind it is. The distribution example uses five slot names: the two stored binders, the fixed literal
`$v` of the rule, and two names for the checked α-variant. The capture example includes its
fixed rule literal as well.

## Conservative extension

For a program without slots, under the empty binder signature and the empty slot universe,
the slotted evaluator and the plain interpreter agree on four small programs (a union, a
failing check, a saturation, a disequality guard) in `Examples.lean`. Of the theorem that
`SEval Binders.none` and `Eval` coincide on slot-free programs, the half that the slotted
closure contains the plain one is proved (`Slotted/Proofs/Conservative.lean`:
`scong_of_cong`, `mem_live'_of_mem_live`). The other half is stated in prose only: on a
slot-free store `Renames` is the identity and the `rename` rule adds nothing beyond the
reflexivity of slot terms, which no slot-free query can see, so `SCong` is `Cong` there,
`reps'` is `reps`, `live'` is `live`, and the match judgements coincide; its Lean proof is
left to phase 3, where a simulation may need `SCong Binders.none db a b ↔ Cong db a b`
for slot-free `db`.

## Parser subset

`Slotted/Tests/Parse.lean` reads `(sort …)`, `(datatype …)` and `(constructor … :binder …)`
declarations into a binder signature (binder indices count the non-payload columns and bind
in the child after the last of them), `(let x e)` as a substitution of the ground term (or
concrete slot) for later uses of `x`, top-level `(union a b)` and ground terms as runs of
empty-query rules, `(rewrite lhs rhs :when (…) :name "…")` and `(rule …)` as rules of the
default ruleset, `(run N)` as `N` rounds, `(check …)` and `(fail (check …))` as checks, the
predicates `=`, `!=`, `free`, `not-free`, `free-names-are`, `renaming-=`, `renaming-!=`, and
`(push)`/`(pop)` by saving and restoring the state. A file with several checks becomes one
program per check.

Skipped forms, with the reason: `subst` (a representative choice outside the semantics),
`extract` (output, not a check), `include` (external files), `__internal-*` checks,
`datatype*`, `function`, `relation`, `run-schedule`, `:ruleset`. On
`egglog-experimental/tests/slotted` the parser accepts 35 of 50 files with 205 checks,
including all six `paper/` files; the 15 skipped files are 9 `include`, 3 `subst`, 2
`__internal-holds`, and 1 `datatype*`. Three accepted files contain declarations only.

## Interfaces used by the pass and its correctness proposition

- `Slotted.Program` and `Program.Eval`/`SEval` as the source side of the pass's correctness
  statement, `SReach` for the schedule-level simulation, `SameMeaning'` for its fixpoints.
- `Renaming` with `comp`, `inv`, `restrict`, `id`, `update`, `Covers`, and `Renames`, the
  action, to state what the compiled renaming columns mean.
- `SCong`, `reps'`, `live'` and `SQueryMatches` to state the matching correspondence;
  `liveSlots` as the meaning of the compiled free-slot analysis `FS`.
- The parser, to read the slotted corpus for the pass's own tests, and the bounded evaluator
  as an oracle on small cases.
- Open: the conservative-extension theorem (above); completeness of the bounded closure on
  a universe, which the pass does not need since its executable path is the target
  interpreter on compiled programs.

# The slotted pass (phase 2)

Phase 2 compiles a slotted program, a plain `Program` with its binder signature, to a plain
program over the primitive target semantics and interpreter below, following the paper's
"Representation and Slotted Maintenance" and "E-Matching" subsections and the Rust compiler
under `egglog-experimental/src/slotted/`. The pass is `Slotted.compile`
(`Slotted/Encode.lean`); `Slotted.encode` is its total form and `Program.encode` applies it
to a `Slotted.Program`.

## Simplified maintenance

`RenamesTo(a,m,b)` means `a = m * b`: the finite partial injection `m` maps
`b`'s slots to `a`'s names. It has no ordering invariant. A term child is stored
as `(ρ,c)`, so terms differing only in names can share `c`. A self-equation
`RenamesTo(c,π,c)` is a symmetry. Closure, support analysis and replacements run
together in one saturation.

Write `N_g(s,ρ,c) = Sum(g,s,ρ,c)`, `A=FS(a)`, `B=FS(b)`, and
`trim(A,m,B) = id_A ∘ m ∘ id_B`. The general constructor rules use one map per
term child, literal payloads, and one field per binding position. In the paper's
rule syntax:

```text
FS(a,A) ⇒ RenamesTo(a,id_A,a)
RenamesTo(a,m,b) ⇒ RenamesTo(b,m⁻¹,a)
RenamesTo(a,m,b) ∧ RenamesTo(b,n,c) ⇒ RenamesTo(a,m∘n,c)

$0 ⇒ FS($0,{$0})
a = f(g,ρ̄,c̄,s̄) ⇒ FS(a, ⋃ᵢ (img(ρᵢ) ∖ Bᵢ))
FS(a,A) ∧ FS(a,B) ∧ C=A∩B ∧ C≠A
  ⇒ FS(a,C), subsume(FS(a,A))
RenamesTo(a,m,b) ∧ FS(a,A) ∧ FS(b,B)
  ⇒ FS(a,m[B]), FS(b,m⁻¹[A])
RenamesTo(a,m,b) ∧ FS(a,A) ∧ FS(b,B)
  ∧ n=trim(A,m,B) ∧ n≠m
  ⇒ RenamesTo(a,n,b), subsume(RenamesTo(a,m,b))

a=Mul(g,ρ₁,c₁,ρ₂,c₂) ∧ a'=Mul(g',η₁,c₁,η₂,c₂)
  ∧ RenamesTo(c₁,π₁,c₁) ∧ RenamesTo(c₂,π₂,c₂)
  ∧ m=align(ρ₁∘π₁∘η₁⁻¹,ρ₂∘π₂∘η₂⁻¹)
  ⇒ RenamesTo(a,m,a')

a=N_g(s,ρ,c) ∧ RenamesTo(a,m,b) ∧ FS(a,A) ∧ FS(b,B)
  ∧ b=min(a,b) ∧ b≠a ∧ n=trim(A,m,B)
  ∧ h=extend(n⁻¹,{s}∪img(ρ),B)
  ⇒ union(b,N_{g+1}(h(s),h∘ρ,c)), subsume(N_g(s,ρ,c))
a=N_g(s,ρ,c) ∧ RenamesTo(c,m,d) ∧ FS(c,C) ∧ FS(d,D)
  ∧ d=min(c,d) ∧ d≠c ∧ n=trim(C,m,D)
  ⇒ union(a,N_{g+1}(s,ρ∘n,d)), subsume(N_g(s,ρ,c))
a=N_g(s,ρ,c) ∧ FS(c,C) ∧ ρ'=ρ|_C ∧ ρ'≠ρ
  ⇒ union(a,N_{g+1}(s,ρ',c)), subsume(N_g(s,ρ,c))

a=f(g,t̄) ∧ a'=f(h,t̄) ∧ g<h
  ⇒ union(a,a'), subsume(f(g,t̄))
```

The `πᵢ` are the symmetries of the children, the self-equations
`RenamesTo(cᵢ,πᵢ,cᵢ)`, which `Trim` keeps as permutations of their free slots.
A binding position is a slot name stored in the node itself, so for the sum
`align` also receives `[t↦s]`; with `a=a'` the rule discovers a symmetry of the parent.

`align` is defined only for a consistent injective union. Partial composition
retains only entries where both steps are defined, so `ρᵢ∘πᵢ∘ηᵢ⁻¹` tolerates
`πᵢ` having a larger domain than either child map. Before collision or
migration, a binder shared with an outside occurrence is refreshed in its field
and in the child images it binds, using a name outside all the node's local
slots. An earlier shadowed binder is refreshed without changing the occurrences
bound by the later field. Both updates use the same generation and subsumption
form. All maintenance rules run in one saturation.

### Revision checklist: answers and evidence

- **Fresh binders.** The capture-avoiding semantic action chooses pairwise distinct
  names outside the term and `dom(m) ∪ img(m)`. This is local to that action, not
  a prohibition on coincidences with other independently matched terms. Action-only
  slots remain fresh for the entire match (`Run′` with `ν`). Uniform renaming
  plus separate alpha-equivalence is deferred; capture-avoiding `Renames` stays.
- **Free slots.** The intended support is `S(t)=⋂_{u∼t} slots(u)`; semantically
  `liveSlots` says that changing a free name changes the class. `FS` estimates
  that support from node images minus binders, intersects competing estimates,
  and transports through every equation in both directions. A self-equation is
  included: repeated transport and intersection remove a whole symmetry orbit
  when any member becomes redundant. No separate symmetry propagation rule is
  needed. The strict `C≠A` guard retires only a larger estimate; exchanging the
  two inputs retires the other estimate when necessary.
- **Identity.** Keep finite `id_A`, not a global identity. Its domain matters for
  `FS`, restriction, map comparison, and the executable value representation.
- **Shrinking maps.** Retire an equation only when `trim(A,m,B)≠m`, after writing
  its restriction. Transport fires on the same pre-state, so the removed entries
  have already contributed both support estimates. Self-equations use the same
  `Trim` rule, giving permutations of the current support at a fixpoint;
  `Restrict` cuts child maps to that support. Collide reads self-equations without
  support or permutation premises: every retained entry is a true equation, and
  every correspondence accepted by `align` gives a true equation of the parents.
  A collision blocked by stale entries is retried when maps shrink. Matching and
  orbit membership check permutations of the current support explicitly.
  The `redundancy-orbit` and `symmetry-with-redundancy` corpus files test this
  interaction.
- **Later unions and reversed edges.** Do not delete a fact because its endpoints
  change order. Inversion retains both directions; migration and child update
  choose the smaller endpoint when they fire. Unions cannot revive a removed slot,
  so map-size cleanup is different from deleting a direction that may be needed
  again. `hand/follower-later-leader.egg` tests the latter case.
- **Generations and Dedup.** Both remain. Replacing `g+1` by `g` makes both
  assertions of `paper/fgh-transitive-symmetry.egg` false: permanent subsumption
  hides the recreated `H` spelling. Removing only Dedup passes that file, but
  makes `binder-tests.egg` exceed the gate's 600-second limit; its nested-binder
  check #7, `(check (= a b))` at line 60, also exceeds a focused 30-second limit
  with the final matcher. Dedup retires duplicate
  spellings before their combinations overwhelm structural matching. This is an
  execution-limit blocker, not evidence of semantic divergence.
- **Arrow audit.** Migrate requires `b=min(a,b) ∧ b≠a`; Child requires
  `d=min(c,d) ∧ d≠c`. Closure, transport, and collision permit reflexive edges.
  Collide requires equal endpoints for each child self-equation and accepts
  untrimmed maps; matching and orbit membership additionally require a permutation
  of current `FS`.
  Restriction needs strict map change; Dedup needs strict generation order.
- **Unification terminology.** Use “unification map”: a possibly noninjective map
  on initially separate temporary names. Keep disequality cliques `C` and fixed
  pattern literals `P` as separate arguments of unification and refinement. A
  merge with a literal keeps that literal as representative; merging different
  literals fails. Node and class cliques prevent collapsing distinct slots of one
  term, while independent placeholders may alias. Action-only slots are not fixed
  pattern literals and are fresh after refinement.
- **Equality and disequality without a group collection.** Equality can join a
  self-equation and compare maps. Disequality cannot negate one selected symmetry:
  identity may distinguish two uses that a swap equates. Use finite
  membership witnesses `Orbit(c,π)` for every `π∈Perm(FS(c))`, unioning
  `Orbit(c,π)` with `Orbit(c,id)` precisely for self-equations. Comparing the witness
  for `μ₂⁻¹∘μ₁` against identity then decides nonmembership with ordinary target
  disequality. Different classes or images are separate branches. The implemented rules are:

  ```text
  FS(c,A) ∧ π∈Perm(A) ⇒ Orbit(c,π)
  RenamesTo(c,π,c) ∧ FS(c,A) ∧ π∈Perm(A)
    ⇒ union(Orbit(c,π),Orbit(c,id_A))
  ```

  Only witness terms are unioned, never primitive maps. There is no group
  collection or change to `Target.Eval`. Enumerating all permutations is finite
  but factorial in support size; this specification-oriented pass makes no
  scalability claim for large supports.
- **Presentation.** The main block shows the compact closure, support merge and
  transport, collision, and replacement rules. Constructor-specific refresh and
  the detailed executable membership encoding belong in these implementation
  notes; all generated rules remain reviewable in snapshots.
- **Proof checker.** Future slotted certificates need the same capture-avoiding
  renaming on both sides of a proved equation, with coverage and injection checks;
  alpha-equivalence is the identity renaming with different fresh binder choices.
  No checker extension or correctness proof is attempted here.


## The target extension

`Slotted/Target/` extends evaluation with canonical primitive values and reductions
under reserved `@` names. `Expr`, the plain specification, `Target.Eval` and the
existing theorems are unchanged. Values are sorted slot sets `@set`, functional
maps `@ren(@pair(s,t),…)`, map lists `@rens`, lists of disequality cliques `@sets`,
booleans and integer generations. A unification map may be noninjective; the
renamings carried by term edges are injective.

`Prim.norm?` reduces primitive applications bottom-up. `TExpr.Matches` reads
ordinary applications as live rows and evaluates primitive operands without
requiring stored rows. A computed variable, bound by `v=@op(…)` or `@mem(v,…)`,
is exempt from the representative requirement; other match variables are bound
to class representatives. Ordinary literals and tables still require live membership.
`@mem` enumerates a primitive list. Actions remain plain: queries compute their
operands before ordinary writes, unions and subsumptions. Thus `Database`, `Cong`,
`reps`, `live`, `evalActions` and `SameMeaning` are reused. `Target.Eval` and
`Target.Diverges` use the resulting target query relation. Without primitive
names, reduction is the identity; its conservativity is a phase 3 obligation.

`FS` uses the functional-dependency rule form of intersection merge shown above.
No merge feature or collected symmetry value is needed in the target.

### The primitive catalogue

Arguments are values; a primitive is stuck (`none`) off its domain.

| Primitive | Meaning |
| --- | --- |
| `@set(s…)`, `@ren(@pair(s,t)…)`, `@rens(m…)`, `@sets(A…)`, `@true()`, `@false()` | canonical value constructors |
| `@img(m)`, `@dom(m)` | image and domain |
| `@inv(m)`, `@comp(m,n)`, `@restrict(m,A)`, `@id(A)` | inverse, composition `s↦m(n(s))`, restriction, finite identity |
| `@apply(m,s)` | `m(s)`, stuck outside its domain |
| `@union(A,B)`, `@inter(A,B)`, `@diff(A,B)` | set operations |
| `@elem(s,A)`, `@isPerm(π,A)` | membership and permutation tests |
| `@perms(A)` | every permutation of the finite set `A` |
| `@align(m…)` | consistent injective union of maps |
| `@extend(m,S,B)` | injective extension to `S`, fresh outside `img(m)∪B` |
| `@mint(L)`, `@succ(g)` | least canonical name outside `L`; integer successor |
| `@fresh(S,U)` | injection of `S` into temporary names outside `U` |
| `@cliques(A…)` | separate distinctness constraints for each `A` |
| `@identity(A)` | initial unification map with singleton blocks |
| `@unify(U,m,n,C,P)`, `@unify1(U,s,t,C,P)` | merge required pairs, preserving cliques `C` and fixing every literal in `P` |
| `@refine(U,C,P,D)` | all valid coarsenings by merging blocks touched by `D` |
| `@anchor(q,ν)` | root coordinates: `q′(ν(s))=s`, fresh names for other blocks |

A unification map sends each name to its block representative. A block containing
one fixed literal uses that literal; a block cannot contain two different fixed
literals. Other blocks use their least member. Temporary names are `$@0,$@1,…`;
`anchor`, `extend` and `mint` choose canonical names `$0,$1,…`.

## The pass

| Module | Contents |
| --- | --- |
| `Target/Values.lean`, `Target/Prim.lean` | values, primitive reductions, unification and refinement |
| `Target/Spec.lean`, `Target/Interp.lean` | target semantics and executable interpreter |
| `Encode/Layout.lean` | constructor layouts and ground representation |
| `Encode/Maintenance.lean` | support, renaming closure, collision and replacement rules |
| `Encode/Query.lean` | flattening, binder normalization, unification, guards and actions |
| `Encode/Premises.lean`, `Encode.lean` | source premises, compilation, schedule, correctness proposition and fragment report |

**Representation.** A source constructor position is a child, a binding field or a
payload inferred from literal occurrences. A child becomes `(ρ,c)`, mapping its
class's slots to the parent's names. A binding field holds a slot, and a payload
holds its value. Every row starts with an integer generation. `repr($s)=$0`, with
edge `[$0↦$s]`; other nodes keep their source names, identity child edges and
generation zero. Terms with different names can share a child class.

**Maintenance.** `analysisRules`, `renamingRules` and `updateRulesAll` contain the
rules above. Each source round is followed by `saturate(run M)` over their union.
Closure uses no ordering; only Migrate and Child choose smaller destinations.
All updates union the replacement into its destination and subsume the old row.
Binder refresh and shadowing are constructor-specific:

```text
a=f_g(ρ̄,c̄,s̄) ∧ s_k∈img(ρ_u) ∧ u∉scope(k)
  ∧ (∀j≠k with scope(j)=scope(k), s_j≠s_k)
  ∧ w=mint(local(a)) ∧ h=id_{local(a)∖{s_k}}∪[s_k↦w]
  ⇒ union(a,f_{g+1}(ρ̄[k-covered↦h∘ρ],c̄,s̄[k↦w])), subsume(f_g(ρ̄,c̄,s̄))
a=f_g(ρ̄,c̄,s̄) ∧ k<j ∧ scope(k)=scope(j) ∧ s_k=s_j
  ∧ w=mint(local(a))
  ⇒ union(a,f_{g+1}(ρ̄,c̄,s̄[k↦w])), subsume(f_g(ρ̄,c̄,s̄))
```

The first rule changes the binder and covered edges; the second changes only the
earlier shadowed field. Scope tests are compile-time choices of generated rules.

**Matching.** Flatten to depth-one atoms, then:

1. Give each atom's local slots separate temporary names. Ground free names and
   written query slots remain literal names in `P`. Ground binders are normalized
   to fresh synthetic slots. Action-only slots get separate blocks outside refinement.
2. Build the identity unification map `U` and independent cliques `C` for each
   atom's distinct slots and for concrete free names versus ground binders.
   A repeated term variable selects `RenamesTo(c,π,c)` with `π∈Perm(FS(c))`,
   then unifies its two occurrences through that symmetry.
3. Unify literal occurrences with their own names. Every merge checks both `C`
   and `P`; distinct literals cannot merge even when `C` is empty. For example,
   `U={$@0↦$x,$x↦$x,$y↦$y}` aliases a temporary name with `$x` while fixing
   both literals. A rule about `Sub($x,$y)` cannot match `Sub($x,$x)`.
4. Refine all remaining alias choices among blocks reached by term variables,
   concrete slots and carried query slots. Independent placeholders may alias;
   the distinct slots of any one term may not. Anchor the result to the stored
   root's names, transporting literals and variable maps together for guards/actions.

`emitUnification` is the code name; the primitive signatures carry `U`, `C` and
`P` separately. Anchoring changes coordinates after matching, rather than making
literal names unification variables. `Free`, `NotFree` and `free-names-are` use
images of the anchored maps, hence the maintained `FS` support. `renaming-=`
compares classes. `=` selects a self-equation with `μ₁=μ₂∘π`. `!=` has three
branches: different classes; same class and different images; or same class and
images with `Orbit(c,μ₂⁻¹∘μ₁) != Orbit(c,id)`. With `k` disequalities this yields
`3^k` rules. A disjunctive check writes `@Goal()` after its schedule.

**Actions.** Build bottom-up at generation zero: a variable child is `(μ_v,c_v)`,
a literal slot is the leaf with its transported name, and a nested build has an
identity edge on its estimated free slots. A source equation is a plain union of
built terms, including a union with the anchored root. A different variable
invocation carries its map in a `RenamesTo` row. Action-only slots get fresh
names through anchoring, retaining `Run′`'s freshness policy.

**Rejections.** Unsupported forms include source `min`/`subsume`; reserved generated
names; inconsistent arities, binder scopes or payload roles; non-slot binders;
predicates inside terms; literals built or unioned as terms; mixed payload/term
comparisons; bare-slot roots/endpoints; unbound action variables; unkeyed queries;
and concrete action slots absent from the query's concrete names. Use an action-only
slot variable for a fresh name. Restricted-aliasing execution is explicitly rejected
after verifying its fixture with Rust's corresponding mode.

## Deviations from the paper and the reference

- **Generation and Dedup.** Permanent target subsumption requires new replacement
  keys; duplicate spellings require cleanup for the corpus gate. The exact blocking
  experiments are recorded above. Generations are wildcards in compiled patterns.
- **Retained directions.** Inversion keeps both endpoint directions. Native unions
  can reverse their order; only map shortening retires an equation.
- **Binder refresh and shadowing.** Explicit generated rules implement the paper's
  capture-avoidance requirement for arbitrary annotated constructors.
- **Structural ground matching.** Globals are flattened like other terms, so a
  retired spelling can still match through a live equivalent structure. Ground
  binders are normalized independently of free literal names.
- **Finite nonmembership witnesses.** `Orbit` and `@perms` implement negative
  symmetry membership in the unchanged target language. Equality reads self-equations
  directly. No separate symmetry relation, group collection or coset primitive exists.
- **One saturation and exhaustive matching.** There are no reference shape indexes,
  canonical invocation keys, stored-match tables or phased rebuild. Pairwise collision,
  symmetry enumeration and unrestricted refinement prioritize declarative clarity.
- **Payload inference and primitive layer.** The source is untyped. Inferred payload
  columns and canonical primitive values stand in for Rust declarations; snapshots
  target this extended interpreter rather than the unextended Rust binary.
- **Parser and policy boundary.** Numeric slots such as `$01` and `$+1` normalize to
  `$1`. Restricted aliasing remains outside this pass and is reported explicitly.

### Rule names and paper nodes

| Paper rule or operation | Lean declaration | Blueprint node |
| --- | --- | --- |
| Leaf, NodeFS, Intersect, Transport | `leafFSRule`, `nodeFSRule`, `intersectFSRule`, `transportFSRule` | `def:slotted-fs-rules` |
| Reflexivity, inverse, composition, map restriction | `reflexiveRule`, `inverseRule`, `composeRule`, `restrictRenamesRule` | `def:slotted-renames-rules` |
| Finite symmetry membership | `orbitSeedRule`, `orbitMemberRule` | implementation notes here |
| align; Collide | `Target.align`, `collideRule` | `def:slotted-align`, `def:slotted-collide` |
| Migrate, Child, Restrict | `migrateRule`, `childRule`, `restrictRule` | `def:slotted-term-updates` |
| Refresh, Shadow, Dedup | `refreshRule`, `shadowRule`, `dedupRule` | `def:slotted-term-updates` |
| One saturation between rounds | `rebuild`, `compileSchedule` | `def:slotted-rebuild` |
| Distribution, literals, unification, guards and actions | `compileRule`, `emitUnification`, `emitGuards`, `compileAction` | `def:slotted-compile-rule` |

## The correctness statement for phase 3

For `P` with binder signature `β`, `Pass.Premises P` and `compile β P.plain = .ok P′`,
`Slotted.Pass.Correct P` asks for

```
(∀ o : Result, Target.Eval Database.empty P′ o ↔ Slotted.SEval β Database.empty P.plain o) ∧
(Target.Diverges Database.empty P′.schedule ↔ Slotted.SDiverges β Database.empty P.plain.schedule)
```

`Encode/Premises.lean` defines the premises: `Binders.WF`; `WellBound` (in-range
annotations and slot literals or variables at binding positions); `PayloadConsistent`;
`Scoped` (query-bound head variables, except fresh action slots); and `Commutes` for every
source rule. `Commutes` says that a source round commutes up to `SameMeaning'` with a
bijective slot-name permutation fixing concrete constants and literal query slots.
`FixesConstants` includes query slots because they denote fixed names; action-only
slots remain fresh choices. This is the one adjusted premise; `Correct` is unchanged.
`NamePermutation`,
`renameTerm`, `renameDatabase` and `FixesConstants` define that statement; none mentions
the target or assumes its correctness. This premise's applicability is a phase 3 obligation.
Successful compilation checks namespace separation, arities, supported forms, keyed queries,
payload/term roles, source ordering exclusion and head scope.

The proof will relate target and source states by decoding classes through `RenamesTo` and `FS`,
using `reps'`, `live'`, `liveSlots` and `SQueryMatches` from phase 1. Generation is invisible
to decoding. `Correct` is a definition of a proposition; no proof is claimed, and
`ExtlogTheorems.lean` is unchanged. Interpreter adequacy, maintenance termination and
simulation, matching completeness, and conservativity of the target primitive layer remain
phase 3 work. `SDiverges` is the plain divergence definition over `SReach` and `SameMeaning'`.

## Composition with the congruence pass

The target is outside `Program.Fragment`, recorded by `fragmentReport` and printed for every
check and final program. Generated names violate `noAt`; maintenance takes `min` over class
variables inside saturation (`ordering`); primitive queries are neither keyed table reads
nor `min` (`queryEncodable`); variadic value/primitive heads violate `aritiesAgree`; and
integer generations alongside unions through class variables violate `noLitUnion`.
Every one of the 250 compiled asserted checks fails exactly these five clauses.
Of the 45 final programs, 29 fail the same five clauses. The other 16 have no constructor
occurrences (declaration-only files and states restored by `pop`) and fail only
`noAt`, `queryEncodable`: `binder-tests`, `carrier-name`, `datatype`, `egglog-surface`,
`lambda-binders`, `languages/{array,sdql,toy}`, `own-sort`, `proof-conditions`,
`proof-renaming-guards`, `rewrite-tests`, `sdql-binders`, `sdql-sum-sing`, `symmetry-tests`,
and `variable-names`. `headsScoped` holds throughout.
The exact per-program clauses remain in the gate output; this is not a claim that the
existing congruence correctness theorem applies to the slotted output.

## Execution and the gate

`Slotted/Target/Interp.lean` uses a hash-consed e-graph, union-find with congruence closure,
subsumption modulo congruent children, representatives by `Term.blt`, and a matcher joining
table atoms and computing primitive bindings in dependency order. `@mem` ranges over all
refinements. Row lookup recognizes unstored spellings with congruent children; ordinary
literals and table applications must still match live rows. Primitive computations can use
unstored constants. `Tests/Compile.lean` checks these boundaries and explicit rejections.

`slotted-compile.sh` first classifies every file, then confirms accepted files' assertions
against Rust in their required mode. It explicitly rejects the restricted-aliasing fixture.
For the remaining files, `difftest slotted-compile` compiles and executes every asserted check
and the final program, including files without checks and commands after the last check.
A reference failure, process error, timeout, exhausted saturation budget or disagreement fails
the gate. Explicit parser/compilation/policy rejections are counted separately.
`DIFFTEST_TIMEOUT` is a per-process limit (600 seconds by default); the interpreter budget is
256 passes per saturation. Neither limit constitutes evidence of semantic divergence.

`difftest slotted-trace <file> <case> [<index>|<substring>]` prints states after commands and
matches of query prefixes. `make lean-update-egg-snapshots LAKE="lake --no-cache"` writes the
hand-written compiled programs as `*.slotted.egg`, checked by `lean-slotted-egg-test` in
`lean-check`. Snapshots use the target's untyped term syntax and reserved primitive catalogue;
they are not standalone programs for the unextended Rust binary.

The eleven hand-written files cover alpha-equivalence, capture, distribution,
unification and fresh action slots, redundant slots, variable right-hand sides,
symmetries, a follower becoming leader, redundancy after symmetry, forbidden literal
collapse and a child update through a symmetric child. Their 47 checks plus the
unrestricted corpus's 203 give **250 agreements, zero disagreements**: 61 files,
46 parser-accepted, 45 compiled, 1 policy rejection, 15 parser rejections.
Collide's self-equation premises, without support, domain-equality or permutation
guards, pass this entire gate at the default 600-second and 256-pass limits.
All six `paper/` files (18 checks) and distribution (2 checks) agree. The gate uses
the supplied Rust binaries without rebuilding them.

### Per-file report

Corpus paths are relative to `egglog-experimental/tests/slotted/`; `hand/` denotes
`semantics/tests/slotted/`. Counts are asserted `check`/`fail` outcomes, not synthetic final
programs. Declaration-only files are compiled and executed with an empty final query.

| File | Checks | Status |
| --- | ---: | --- |
| `atom-identities.egg` | — | parser rejection: `include` |
| `bare-slot-union.egg` | 5 | compiled; all agree |
| `binder-scope.egg` | 4 | compiled; all agree |
| `binder-tests.egg` | 24 | compiled; all agree |
| `carrier-name.egg` | 3 | compiled; all agree |
| `coset-direction.egg` | — | parser rejection: `include` |
| `datatype.egg` | 7 | compiled; all agree |
| `egglog-surface.egg` | 18 | compiled; all agree |
| `lambda-binders.egg` | 8 | compiled; all agree |
| `languages/array-rules.egg` | — | parser rejection: `include` |
| `languages/array.egg` | 0 | compiled; declarations only |
| `languages/sdql-rules.egg` | — | parser rejection: `include` |
| `languages/sdql.egg` | 0 | compiled; declarations only |
| `languages/toy.egg` | 0 | compiled; declarations only |
| `multipattern.egg` | — | parser rejection: `subst` |
| `multiple-sorts.egg` | — | parser rejection: `datatype*` |
| `named-slots.egg` | 13 | compiled; all agree |
| `nested/binder-safe-matching.egg` | 2 | policy rejection: restricted aliasing (Rust verified) |
| `own-sort.egg` | 7 | compiled; all agree |
| `paper/enode-collisions.egg` | 4 | compiled; all agree |
| `paper/fgh-transitive-symmetry.egg` | 2 | compiled; all agree |
| `paper/figure-3.egg` | 3 | compiled; all agree |
| `paper/redundancy-orbit.egg` | 4 | compiled; all agree |
| `paper/two-redundant-slots.egg` | 3 | compiled; all agree |
| `paper/var-xy-eq-yz.egg` | 2 | compiled; all agree |
| `proof-child-freshness.egg` | 1 | compiled; all agree |
| `proof-conditions.egg` | 6 | compiled; all agree |
| `proof-group-restriction.egg` | 1 | compiled; all agree |
| `proof-node-symmetry.egg` | 1 | compiled; all agree |
| `proof-redundant-certificate.egg` | 1 | compiled; all agree |
| `proof-renaming-guards.egg` | 6 | compiled; all agree |
| `query-predicates.egg` | — | parser rejection: `__internal-holds` |
| `redundancy-tests.egg` | — | parser rejection: `__internal-holds` |
| `refinement-complete.egg` | — | parser rejection: `include` |
| `rewrite-tests.egg` | 6 | compiled; all agree |
| `rudi/bound-aliasing-rel-decoded.egg` | 2 | compiled; all agree |
| `rudi/bound-aliasing.egg` | 1 | compiled; all agree |
| `rudi/relation.egg` | 6 | compiled; all agree |
| `rudi/unify-redundant-and-symmetric-appid-decoded.egg` | 2 | compiled; all agree |
| `sdql-batax.egg` | — | parser rejection: `include` |
| `sdql-beta.egg` | — | parser rejection: `subst` |
| `sdql-binders.egg` | 22 | compiled; all agree |
| `sdql-paper-batax.egg` | — | parser rejection: `subst` |
| `sdql-paper-mmm.egg` | — | parser rejection: `include` |
| `sdql-rewrites.egg` | — | parser rejection: `include` |
| `sdql-sum-sing.egg` | 2 | compiled; all agree |
| `subst-refresh.egg` | — | parser rejection: `include` |
| `symmetry-tests.egg` | 27 | compiled; all agree |
| `symmetry-with-redundancy.egg` | 4 | compiled; all agree |
| `variable-names.egg` | 8 | compiled; all agree |
| `hand/alpha.egg` | 6 | compiled; all agree |
| `hand/capture.egg` | 4 | compiled; all agree |
| `hand/distribution.egg` | 2 | compiled; all agree |
| `hand/follower-later-leader.egg` | 4 | compiled; all agree |
| `hand/frames.egg` | 8 | compiled; all agree |
| `hand/literal-slot-collapse.egg` | 3 | compiled; all agree |
| `hand/redundant-after-symmetry.egg` | 5 | compiled; all agree |
| `hand/redundant.egg` | 4 | compiled; all agree |
| `hand/rewrite-variable.egg` | 4 | compiled; all agree |
| `hand/symmetric-child-update.egg` | 3 | compiled; all agree |
| `hand/symmetry.egg` | 4 | compiled; all agree |

### Validation

Run from `semantics/` with the supplied Rust binaries, `LEAN_NUM_THREADS=4`,
`RAYON_NUM_THREADS=1`, `CARGO_BUILD_JOBS=4`, and the shared `CARGO_TARGET_DIR`:

| Command | Exit | Result |
| --- | ---: | --- |
| `make lean-check LAKE="lake --no-cache"` | 0 | Whole library and hole audit; 116 congruence, 116 provenance and 104 resugaring cases; 29 existing snapshots; Rust certificate test; parser report; 11 slotted snapshots |
| `make lean-difftest` | 0 | 116 passed, 0 failed, 0 skipped |
| `make lean-compiled-difftest` | 0 | 116 passed, 0 failed |
| `make lean-slotted-difftest` | 0 | 18 paper checks agree, 0 disagree, 0 undecided |
| `make lean-slotted-compile` | 0 | 250 checks agree; file statuses above; 0 disagreements, 0 undecided, 0 execution errors |
| `make paper-check LAKE="lake --no-cache"` | 0 | Six-page PDF; slotted blocks visually inspected; no overfull boxes |
| `make lean-update-egg-snapshots LAKE="lake --no-cache"` | 0 | Eleven slotted snapshots; the 29 existing plain snapshots are unchanged |

No Python source was changed, so root `make nits` was not run. `paper-sync` was not run.
`ExtlogTheorems.lean`, the Rust subtrees and the restored `Cargo.lock` are unchanged.
