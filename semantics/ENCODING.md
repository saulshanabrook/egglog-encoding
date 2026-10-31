# Encoding passes

## Constructor-and-subsume encoding (October 2026)

The modelled language is untyped and has no declarations: applying any name to any
arguments builds a term, and a relation is a name whose applications are never nested
(`Spec/Syntax.lean`). It has no rulesets and no rule store either: a schedule is
`run R`, `saturate S`, or `S; S`, a run names the set of rules it fires, and a program is a
schedule and the single check that decides its outcome. The state is an e-graph
`G = (E, X)`: a set of equations `E`, whose reflexive facts record which terms exist, and a
set `X` of subsumed rows. egglog's named rulesets, `rule` commands and `run-schedule`
bodies are resolved by the parser, which expands a run of a ruleset into a run of the rules
registered in it so far; the emitter does the reverse with one ruleset per run. The
congruence compiler emits no merge function. Its one table, `@UF(key, parent)`, is a
relation, and every change to a row is a rule that subsumes the stale row and writes its
replacement. Two language features support this: a `subsume` action and a disequality
pattern `e ≠ e`. Source programs use neither (`Program.Fragment.monotone`).

### Semantics

- An action adds to the e-graph directly (`evalAction`, the paper's `G ⊕_σ h`): a build
  asserts `(⟦e⟧,⟦e⟧)`, a union `(⟦e₁⟧,⟦e₂⟧)`, and `subsume f(ē)` asserts the row `⟦f(ē)⟧`
  and marks it. A subsume names a row by its symbol and children, as egglog's
  `(subsume (f args))` does, so which spelling represents a child's class never decides
  which row is subsumed; egglog inserts a missing row it subsumes, and never un-subsumes
  a row.
- A round is the pre-state together with the union of every firing's result
  (`RunRules rs G = G ∪ ⋃{G ⊕_σ H | (Q ⇒ H) ∈ rs, G,σ ⊨ Q}`, `Database.sUnion`). Nothing is
  removed, so the firings commute and a head's actions can run in any order. The
  set-valued readings the proofs use (`Action.writes`, `RunWrites`, `RunMarks`) live in
  `Spec/Facts.lean`.
- Subsumption is modulo congruent children: the live terms are
  `live(E, X) = {t | t ~ t} \ {f(t̄) | f(s̄) ∈ X, s̄ ~ t̄}` (`Database.live`). This is
  egglog's behaviour, where a subsumed row stays subsumed when canonicalization merges it
  with another row (`combine_subsumed` takes the maximum).
- A query looks rows up and builds nothing (`Lookup`, the paper's `G,σ ⊢ e ⇝ t`): a
  variable denotes its binding, an application denotes its instance when that instance is
  live, and `min` picks the smaller operand. Every application in a pattern must therefore
  be live, as egglog joins over the non-subsumed rows of every table a pattern names.
- A saturation repeats its schedule until a pass changes neither congruence nor the live
  terms (`Database.SameMeaning`). Subsuming a live row is a change, as egglog's
  `saturate` counts a subsume-flag change.
- The final check sees subsumed rows, as egglog's `check` does (`check_facts` queries
  with `include_subsumed`), so `Eval` runs it against the final e-graph with subsumption
  forgotten (`Database.forgetSubsumed`). Rule queries never see them.
- A query variable is bound to a representative: the stored spelling of its class that is
  least in the term order (`Database.reps`, `ValidEnv`). This is egglog's one binding per
  e-class. Binding every stored spelling instead makes saturations diverge where egglog
  stops: a rule `(F x) ⇒ (G x)` whose outputs join the class of `x` would build a new
  spelling `G(G(…))` in every pass.
- `e₁ ≠ e₂` holds when both sides look up and are not congruent (`Matches.unequal`). In
  the union-free target this is structural inequality.
- The emitter declares generated tables as `relation`s, which egglog desugars to
  constructors with a fresh output sort, so `subsume` applies to them, and `print-size`
  counts subsumed rows, as the interpreter's `rowCount` does.

### Rules

Source terms are their own ids: the target holds every term the source built, as the key
of its union-find self-loop, and never equates two distinct terms. With `m = min b c` in
the model's term order (egglog: `ordering-min`), the generated maintenance rules are

| Origin | Query | Actions |
| --- | --- | --- |
| `compress` | `(@UF a b) (@UF b c) (≠ b c)` | `subsume (@UF a b)`, `(@UF a c)` |
| `collide` | `(@UF a b) (@UF a c) (= b (min b c)) (≠ b c)` | `subsume (@UF a c)`, `(@UF c b)` |
| `congruence f` | `(f ā) (f b̄) (@UF aᵢ rᵢ) (@UF bᵢ rᵢ)… (@UF (f ā) y) (@UF (f b̄) z) (= y (min y z)) (≠ y z)` | `(@UF z y)` |

Builds write the self-loop `(@UF t t)` for every subterm; a union writes `(@UF a m)` and
`(@UF b m)`. A self-loop written for a value that already has a parent is stale, and
`compress` with `a = b` subsumes it. The collision rule keeps the smaller parent, subsumes
the other edge, and links the larger parent under the smaller; a collision whose loser
already has a parent produces a collision one level up, so unions still meet at roots.
The congruence rule of a constructor matches two of its applications whose children have
the same parents and links the larger of their roots under the smaller; a nullary
constructor has one application and no rule. It fires only while the roots differ, and the
subsequent collision and compression make the two roots one.

A source `run R` compiles to the run of the compiled rules followed by a saturation of the
maintenance rules; `S; S` and `saturate S` compile structurally, so every pass of a
compiled saturation is one source pass in which each run is followed by a complete
rebuild, as in egglog's instrumented schedules. The rebuild after each run is what keeps a
pass clean: every round refires every source rule, and only a round without source rules
settles the maintenance rules. The final check is flattened like a query.

The disequality guards keep the rules from firing on canonical rows. Without the guard,
`compress` fires on a self-loop `(@UF m m)`, `(@UF m m)` and subsumes it, and `collide`
fires on the pair `(@UF a c)`, `(@UF a c)` and subsumes the canonical parent; subsumption
is permanent, so either would lose a row for good. With the guards no rule fires on a
canonical row, every rule's write is strictly more canonical than the row it subsumes, and
no rule subsumes a row it writes. A stale row is never needed again, because leaders only
move down the term order, so leaving it subsumed in the table is harmless.

A compiled query matches the terms themselves and joins the union-find in between. A
source application `f(e₁, …, eₙ)` becomes the atom `(f a₁ … aₙ)` over fresh child
variables and one edge `(@UF aᵢ xᵢ)` per child, where `xᵢ` is the child's id: a source
variable or literal is its own id, and a child that is itself an application is given a
fresh root variable `y` by the edge `(@UF (g b̄) y)` from its atom. At a rebuild fixpoint
every key has one live edge, to its root, so a source variable is bound to the
representative of its class and a source rule head already builds canonical spellings;
there is no leader query. An equality or disequality compares the ids of its two sides.

### Views as an optimization

The previous encoding kept one more table per constructor, `@fView(children…, id)`: the
application with the parents of its children as key and its own parent as output, which
is exactly the join a compiled query performs for it, materialized. Rules re-keyed a view
when a child gained a parent, moved its output when the application did, and detected a
congruence as two rows at one key; queries then joined views on ids alone and never read
the union-find. The paper presents the views as that optimization, the hashcons of an
e-graph written as rules; the compiler, the readers, the provenance and the proofs here
are about the view-free encoding.

### Fixpoints, informally

At a rebuild fixpoint no maintenance rule matches. `compress` not matching means every
parent is a root; `collide` not matching means every key has one parent; the congruence
rules not matching means two applications with the same child parents have the same root.
A stale row is subsumed in the round that matches it and is only rewritten from a strictly
staler row, so staleness is well founded and the fixpoint is reached; the formal argument
is part of the pending proof work.

### Provenance: a firing log

The provenance pass (`Provenance/Encode.lean`) adds one action to every rule: a row
`@prov:fire:<i>(x₁, …, xₙ)` that records a firing of rule `i`, the rule's position in
`Program.rules`, under the values of its query variables. No rule reads these rows, so the instrumented program builds exactly the data of
the original, round for round, subsumes the same rows, and settles when the original does.
The difftest checks this literally: the instrumented final state minus the log is the
original final state (`difftest provenance 64`).

Proofs are read off the log afterwards (`Provenance/Extract.lean`). A firing is justified
once every premise is established: a row premise by a proof of its instance, an equality
or disequality premise by a `subterm` proof from a row of the same firing carrying the side
in question. Passes over the log justify firings until none is left that can be, each data
row keeps the first proof found for it, and every returned proof is checked with
`Provenance.check`. Proof lifting (`Resugar/Lift.lean`) is unchanged in format: every
relational proof becomes a source proof that `SourceProof.check` and the Rust checker
accept.

The previous design, a proof column on every row with rules firing once per proof,
does not work with row replacement: a row re-derived with a new proof is a new row for one
round, and in that round it breeds further variants before a deduplication rule can retire
it, so instrumented saturations of two-premise rules never settled (the instrumented
`commutativity` case grew from 36 to 2936 rows in four rounds). The log keeps proof
identity out of the data entirely.

### Status

- Executable: `difftest congruence 64` passes all 101 corpus cases; `difftest provenance
  64` and `difftest resugar 64` pass all 101 in about three seconds each; the 14
  hand-written programs under `tests/` have `.congruence.egg`, `.provenance.egg` and
  `.proofs.txt` snapshots (`difftest egg 64`). `scripts/compiled-difftest.sh` runs the
  compiled programs in Rust egglog, with generated `@` names spelled `at_`, and compares
  a census of canonical e-nodes per constructor (an application joined with the live
  edges of its children, counted by the tuple of parents), which is independent of
  representative choice: 104 of 104 agree. `scripts/difftest.sh` (source
  programs, Lean against egglog) passes 101 of 101, and the Rust checker judges the 120
  exported source certificates like the Lean checker (`make lean-certificate-test`).
- Interpreter: `execRunRules` matches every rule against the pre-state, then applies
  every firing's writes and subsumptions, in sequence, which is their union. The
  relational runtime (`Congruence/Relational.lean`, structural identity only) agrees with
  the general interpreter on every case.
- Proofs: the specification-level proof modules and the certificate soundness proofs are
  ported to the declaration-free specification and then to subsumption
  (`PROOF-PORT-A.md` … `PROOF-PORT-G.md` record every statement change; `Proofs/Lookup.lean`
  bridges query lookup and evaluation, `Proofs/Subsume.lean` and
  `Proofs/InterpSubsume.lean` replace the deletion theory). `SourceProof.check_infers` and
  `Resugar.extractAll_infers` give checked and lifted certificates their meaning in the
  reached, saturated source state. The reference interpreter refines the specification
  up to `SameMeaning` for subsume-free programs (`exec_programStep`) and for union-free
  programs with subsumption, disequalities and `min` (`exec_programStep_noUnions`,
  `Congruence.exec_encode_programStep`), which is what the compiler emits; mixed
  union-and-subsume programs are not covered. Compiler correctness against the source,
  stated in `Congruence/Correctness.lean`, is established executably by the congruence
  gate; its Lean proof for this encoding is open. The proofs of the previous,
  merge-function encoding were deleted on 2026-10-30 (`PROOF-PORT-*.md` record the ports
  that preceded them).


## Current implementation

The Lean refactor separates congruence compilation, provenance instrumentation, and proof
lifting. The congruence pass is implemented in
[Congruence/Encode.lean](EgglogSemantics/Congruence/Encode.lean), provenance in
[Provenance/Encode.lean](EgglogSemantics/Provenance/Encode.lean), and lifting in
[Resugar/Lift.lean](EgglogSemantics/Resugar/Lift.lean).

## Congruence compilation

`Egglog.Congruence.encode : Program → Program` compiles constructor-source programs into
one explicit table:

| Table | Atom | Meaning |
| --- | --- | --- |
| `@UF` | `(@UF t parent)` | An explicit parent edge |

Structural constructor terms serve as ids and exist in the target as the keys of their
self-loops. Building `f(cs…)` builds its children and writes `(@UF (f cs…) (f cs…))`; it
needs no table lookup, temporary variable, proof term, or separate construction-history
relation.

`min` is the only computation in the fragment: the smaller of two terms in the model's
structural order, egglog's `ordering-min`. A source union writes an edge from each of the
two ids to the smaller one; the edge from the smaller id to itself is not a union-find
edge. A parent collision and a congruence keep the smaller root and write the same kind of
edge.

Maintenance rules compress paths, resolve parent collisions, and detect congruences
between applications whose children have the same parents. Rebuilding runs after each
source run.

`Congruence.compile` returns the program with rule origins. Source rules are tagged with
their original rule index; generated rules identify path compression, parent collision,
or the constructor whose congruence rule fired. These tags are for later resugaring and do
not affect execution.

The output has no built-in `union` in rule heads. It also needs no equality axioms from
the target runtime. `Relational.exec` uses structural identity and stored-value existence
for matching, and omits implicit congruence rebuilding. Source equality is represented by
ordinary union-find entries; target `(= x y)` is just an identity test with existence.

## Query traversal

Flattening visits conjuncts left to right. Within an application it recursively visits
children left to right, each reduced to its id, then emits the application over fresh
child variables and one union-find edge per child; a child that is an application gets a
fresh root variable through an edge from its atom. Within equality it visits the left
expression, then the right, each reduced to its id, then emits equality of the ids. Each
occurrence gets its own fresh variables, including repeated subexpressions. Variable
supplies are local to a rule; source names cannot use the generated `@` prefix.

For example, `(= (F (G x)) (H x))` becomes:

```text
(G @v0) (@UF @v0 x) (@UF (G @v0) @v1)
(F @v2) (@UF @v2 @v1) (@UF (F @v2) @v3)
(H @v4) (@UF @v4 x) (@UF (H @v4) @v5)
(= @v3 @v5)
```

Resugaring will receive the original query and repeat this traversal while consuming
premise proofs in order. No separate tree describing flattening is stored.

## Proof lifting

`Resugar.lift` checks a relational proof against the compiled program, then rebuilds it
recursively as a source proof tree. A UF row becomes an equality, and a value or an
application the target matched its reflexivity. Generated rules are recognized by their
origin tags: path compression is transitivity, a parent collision symmetry and
transitivity, and a congruence firing turns the second application into the first by
congruence on each child and chains the two roots through them. A source rule firing
names the original rule, restricts the substitution to the original query's variables,
and recovers its premises by walking the original query in the compiler's order
([Resugar/Query.lean](EgglogSemantics/Resugar/Query.lean)): an application's premise is
its matched atom with each child edge chained into the child's proof and pushed in by
congruence, an equation's the two sides' root edges chained through the equality. A subterm's existence comes from the derivation that introduced
it, never from a new `fiat`.

Each node is validated by `SourceProof.checkNode` as it is built, and the result is
checked again by `SourceProof.check`. `lift_sound` therefore inherits the source
checker's soundness: a lifted claim whose endpoints the source holds is a source
congruence.

`Resugar.Export` writes proofs as JSON certificates with the program as `.egg` source,
listing each tree's nodes in postorder with shared subtrees, and
[proof_certificate.rs](../egglog/src/proofs/proof_certificate.rs) replays them through
Rust egglog's proof checker. The fixtures in
[Resugar/Fixtures.lean](EgglogSemantics/Resugar/Fixtures.lean) pair lifted proofs with
hand-written proofs that both checkers must judge alike; their export is committed as
`egglog/tests/lean-certificates.json`, and `make lean-certificate-test` also exports and
checks the whole corpus.

## Validation

`make lean-check` builds the library, audits for proof holes, and runs the corpus gates.
The congruence gate compares every pair of held source terms against the compiled
program's reading, and checks that execution with and without equality reasoning agrees.
The provenance gate checks data preservation
and every retained row's extracted proof. The resugar gate lifts those proofs and checks
them against the original source program, and the certificate gate exports the same
proofs and checks them with Rust egglog. Failures, stuck executions, and
insufficient fuel fail the command. Out-of-domain cases are counted separately.

The corpus is the curated and generated programs in `DiffTest.lean` together with the
hand-written `.egg` programs under [`tests/`](tests), which `Program.ofEgg` parses. The
egg gate (`difftest egg`) checks each of those against its committed snapshots: the
congruence encoding in `<name>.congruence.egg`, the provenance encoding in
`<name>.provenance.egg`, and the lifted source proofs in `<name>.proofs.txt`.
`make lean-update-egg-snapshots` rewrites them after an intended change. A program that
unions a term with its own subterm does not saturate in the model, whose classes are sets
of explicit spellings, so the hand-written programs evaluate into separate constructors
instead.

From `semantics/`:

```sh
lake build difftest
.lake/build/bin/difftest congruence 64
.lake/build/bin/difftest congruence 64 both-2 rand-43 sat-hit
.lake/build/bin/difftest provenance 64
.lake/build/bin/difftest resugar 64
.lake/build/bin/difftest egg 64
.lake/build/bin/difftest export-certificates 64 /tmp/certificates.json
```

Executable regressions also check recursive traversal order, origin tags, rebuilding
necessity, and rejection of a rule firing whose constructor premise never existed.
