# Encoding passes

## Language and state

The modelled language is untyped and has no declarations: applying any name to any
arguments builds a term, and a relation is a name whose applications are never nested
(`Spec/Syntax.lean`). It has no rulesets and no rule store either: a schedule is
`run R`, `saturate S`, or `S; S`, a run names the set of rules it fires, and a program is a
schedule and the single check that decides its outcome. The state is an e-graph
`G = (E, X)`: a set of equations `E`, whose reflexive facts record which terms exist, and a
set `X` of subsumed rows. egglog's named rulesets, `rule` commands and `run-schedule`
bodies are resolved by the parser, which expands a run of a ruleset into a run of the rules
registered in it so far; the emitter does the reverse with one ruleset per run. The
congruence compiler emits no merge function. Its union-find table, `@UF(key, parent)`,
is a relation, and every change to an edge is a rule that subsumes the stale row and writes
its replacement. For sources containing `subsume`, each constructor also has a permanent
node relation and a subsumption marker relation. Two language features support this:
a `subsume` action and a disequality pattern `e ≠ e`. Source rules may subsume rows, and rules and the final check may test
disequalities. `Program.Fragment` requires names outside the generated `@` namespace,
encodable queries, scoped heads, consistent constructor arities and unions that cannot
receive literals. Minima over query variables are supported when the program has no
saturation; otherwise rules and the check are ordering-free.

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
  with another row.
- A query looks rows up and builds nothing (`Expr.Matches`, the paper's `G,σ ⊨ e`): a
  variable denotes its binding, an application denotes its instance when that instance is
  live, and `min` picks the smaller operand. Every application in a pattern must therefore
  be live, as egglog joins over the non-subsumed rows of every table a pattern names.
- A saturation repeats its schedule until a pass changes neither congruence nor the live
  terms (`Database.SameMeaning`). Subsuming a live row is a change, as egglog's
  `saturate` counts a subsume-flag change.
- The final check is an ordinary query over the live rows of the reached e-graph, with the
  semantics of a rule query (`Eval`). egglog's `check` currently also sees subsumed rows
  (`check_facts` queries with `include_subsumed`); the model diverges from it deliberately,
  and the reference interpreter's `observe` has a `checkIncludesSubsumed` mode that
  reproduces egglog's behaviour for differential testing.
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
of its union-find self-loop, and never equates two distinct terms. The default `encode P`
sets `Options.subsumption` to `!P.schedule.subsumeFreeB`.
Without source subsumption, builds write only self-loops, `Cong_f` reads `f(ā)` and
`f(b̄)` directly and joins `@UF(f(ā), y)` and `@UF(f(b̄), z)`, and maintenance contains
only Compress, Collide and constructor congruence. No node or marker relations are emitted.
This is the encoding displayed in the paper.

With source subsumption enabled and `m = min b c` in the model's term order
(egglog: `ordering-min`), the generated maintenance rules are

| Origin | Query | Actions |
| --- | --- | --- |
| `compress` | `(@UF a b) (@UF b c) (≠ b c)` | `subsume (@UF a b)`, `(@UF a c)` |
| `collide` | `(@UF a b) (@UF a c) (= b (min b c)) (≠ b c)` | `subsume (@UF a c)`, `(@UF c b)` |
| `congruence f` | `(@Node_f ā k) (@Node_f b̄ l) (@UF aᵢ rᵢ) (@UF bᵢ rᵢ)… (@UF k y) (@UF l z) (= y (min y z)) (≠ y z)` | `(@UF z y)` |
| `subsume f` | `(@Sub_f ā) (f b̄) (@UF aᵢ rᵢ) (@UF bᵢ rᵢ)…` | `subsume (f b̄)` |

Builds write the self-loop `(@UF t t)` for every subterm and the permanent row
`(@Node_f ā (f ā))` for every application. A union writes `(@UF a m)` and `(@UF b m)`.
A source `subsume (f ē)` first builds the expression, then subsumes the built spelling
`f(ā)` and writes `(@Sub_f ā)`. The marker keys on the children because a nested query
for the subsumed application could no longer read it. The subsumption maintenance rule
compares child leaders and hides each congruent spelling, including spellings built in
later runs. The node relation is never subsumed: congruence must still merge hidden
applications and propagate their equality to parents. A self-loop written for a value
that already has a parent is stale, and `compress` with `a = b` subsumes it. The collision
rule keeps the smaller parent, subsumes the other edge, and links the larger parent under
the smaller; a collision whose loser
already has a parent produces a collision one level up, so unions still meet at roots.
The congruence rule of a constructor matches two of its applications whose children have
the same parents and links the larger of their roots under the smaller. It fires only
while the roots differ, and the subsequent collision and compression make the two roots
one. A nullary constructor has one application and needs only its subsumption rule when
subsumption is enabled; plain mode generates no maintenance rule for it.

A source `run R` compiles to the run of the compiled rules followed by a saturation of the
maintenance rules; `S; S` and `saturate S` compile structurally, so every pass of a
compiled saturation is one source pass in which each run is followed by a complete
rebuild, as in egglog's instrumented schedules. The rebuild after each run is what keeps a
pass clean: every round refires every source rule, and only a round without source rules
settles the maintenance rules. The final check is flattened like a query.

The disequality guards keep the rules from firing on canonical rows. Without the guard,
`compress` fires on a self-loop `(@UF m m)`, `(@UF m m)` and subsumes it, and `collide`
fires on the pair `(@UF a c)`, `(@UF a c)` and subsumes the canonical parent; subsumption
is permanent, so either would lose a row for good. With the guards no union-find
maintenance rule fires on a canonical edge, and each replacement moves toward a smaller
parent. A stale row is never needed again, because leaders only move down the term order,
so leaving it subsumed in the table is harmless.

A compiled query matches the terms themselves and joins the union-find in between. A
source application `f(e₁, …, eₙ)` becomes the atom `(f a₁ … aₙ)` over fresh child
variables, one edge `(@UF aᵢ xᵢ)` per child, where `xᵢ` is the child's id, and the edge
`(@UF (f a₁ … aₙ) y)` to a fresh root `y`, the application's id; a source variable or
literal is its own id. At a rebuild fixpoint
every key has one live edge, to its root, so a source variable is bound to the
representative of its class and a source rule head already builds canonical spellings;
there is no leader query. An equality or disequality compares the ids of its two sides. A
`min` of query variables passes through flattening unchanged: its operands are roots,
which are the source representatives, so it chooses as the source does. A compiled head
writes the self-loops of both operands of a `min`, which are keys already.

### Views as an optimization

`Congruence.Options` selects the encoding and optimizations: `subsumption := true` can
explicitly retain permanent nodes even for a subsume-free source; `views := .naive` derives
a canonical node view `@fView(leaders…, leader)` from the terms and the union-find each rebuild round
and subsumes stale rows. `views := .indexed` writes a node's row with the node and indexes
its column values with `@HasChild(view row, column value)`. Maintenance joins this index
with union-find edges to update a row when a column gains a parent. With either view mode,
compiled queries read one view row per application, and congruence detection reads two rows
at one key. `phased := true` saturates the union-find rules before the term rules inside
each rebuild. `difftest congruence 64 --views=indexed --phased`
and `DIFFTEST_OPTIONS="--views=indexed --phased" semantics/compiled-difftest.sh` check
that the optimized compilations agree with the source and with egglog. `--subsumption`
forces node compilation for subsume-free cases in those same entrypoints; the default
corpus gates already exercise plain sources and sources that require subsumption. The
provenance and resugaring gates also rerun subsume-free sources with nodes explicitly
enabled, checking both encodings even within the checker's subsume-free fragment.

The views materialize the joins of compiled queries for programs without source
subsumption. `Options.forProgram` selects the explicit node-and-marker encoding when a
program subsumes rows, retaining the requested phasing. The paper presents views as an
optimization; the compiler correctness and proof-lifting theorems concern the compilation
without views.

### Fixpoints, informally

At a rebuild fixpoint no maintenance rule matches. `compress` not matching means every
parent is a root; `collide` not matching means every key has one parent; the congruence
rules not matching means two applications with the same child parents have the same root.
The subsumption rules not matching means every held application with children congruent
to a marker's is subsumed. A stale union-find row is subsumed in the round that matches it
and is only rewritten from a strictly staler row, so staleness is well founded and the
fixpoint is reached. The formal argument (`Proofs/Congruence/Fixpoint.lean`) counts the
rows and marks still missing from a finite universe of union-find pairs, source terms,
node rows and markers; a round that changes the state lowers that count, and a round that
changes nothing leaves the state canonical.

### Provenance: a firing log

The provenance pass (`Provenance/Encode.lean`) adds one action to every rule: a row
`@fire:<i>(x₁, …, xₙ)` that records a firing of rule `i`, the rule's position in
`Program.rules`, under the values of its query variables. No rule reads these rows, so the
instrumented program builds exactly the data of the original, round for round, and
subsumes the same rows. A saturation of the instrumented program may run additional
passes after the original settles, because a new log row is a change of the state, but those
passes write only log rows, which belong to a finite set, so they terminate. This is the
theorem `ExtlogTheorems.provenance_pass_correct` (`ExtlogTheorems.lean`, proved under
`Proofs/Provenance/`): for a union-free program whose names avoid the log prefix and
whose query and check variables are arguments of application patterns
(`Provenance.Instrumentable`, satisfied by the congruence compiler's output according to
`Provenance.encode_instrumentable`),
the instrumented program has the same outcomes and the same divergence, and erasing the
log from its final state (`Database.eraseLog`) gives the original's final state up to
meaning. The keyed-variable premise is what keeps a query from binding a variable to a
log row. The difftest checks the state clause literally: the instrumented final state
minus the log is the original final state (`difftest provenance 64`).

Proofs are read off the log afterwards (`Provenance/Log.lean`), in the one proof language
of `SourceProof/Format.lean`: a certificate for the compiled program is a rule node
`rule_i((t = t), σ; π̄)` stating the reflexivity of a row `t` the firing wrote, or of a
subterm of one, checked by the same checker as a source certificate (`Provenance.check` is
`SourceProof.checkIn` on a union-free program, returning the term). A logged firing is
justified once every equality premise has a proof, a row premise by the proof of its
instance and an equality by the proof of the common value, and every disequality holds; a
rule node carries one premise proof per equality pattern. `Provenance.reconstruct`
justifies the first available pending firing at each step, stopping when none can be
justified or its fuel is exhausted. `Provenance.proofs` supplies one fuel unit per logged
firing and returns `none` if any data row lacks a checked proof.
For programs in `SourceProof.Fragment`, proof lifting (`Resugar/Lift.lean`) turns each
such proof into a source proof that `SourceProof.check` and the Rust checker accept.
This checker fragment excludes subsumption. Node facts lift to reflexivity
of their recorded node; a subsumption maintenance firing adds no new equality. Exported
certificates omit repeated identical proofs, preserving the first occurrence.

The log keeps proof identity out of the data. The alternative, a proof column on every
row with rules firing once per proof, does not work with row replacement: a row re-derived
with a new proof is a new row for one round, and in that round it breeds further variants
faster than a deduplication rule retires them, so instrumented saturations of two-premise
rules need not settle.

## Correctness and execution

The paper's theorems are stated in [ExtlogTheorems.lean](ExtlogTheorems.lean).
`ExtlogTheorems.congruence_pass_correct` preserves outcomes and divergence for well-formed
source programs in the fragment. `ExtlogTheorems.passes_compose` gives the same guarantee
for the composition with provenance instrumentation. Their proofs are under
`Proofs/Congruence/` and `Proofs/Provenance/`.

### The fragment's boundary

`Program.Fragment` (`Source/Domain.lean`) admits disequality patterns in rule queries and in
the final check, subsumption in rule heads, and minima in the rules and the check of a
program without saturation; a `min` applies only to query variables and to such minima.
A disequality compares the ids of its two sides, and at a canonical compiled state every
live edge leads to a root, the
representative of a source class, so two ids differ exactly when the source values are not
congruent; rule queries and the final check are both read at such a state
(`Proofs/Congruence/QueryCorr.lean`, `Check.lean`). Each boundary is where the theorem
fails:

- A compiled saturation may run passes after the source has settled, at states with the
  meaning of the source fixpoint but with new spellings, and a new spelling can be the new
  representative of its class. A minimum compares representatives, so a rule that takes one
  can then build a term the source never builds, and a check that takes one can decide
  differently. With `(A)`, `(F (B))`, `(K (F (B)))` and
  `(M (F (AB)))` as facts, the saturation of `(rule ((F x)) ((F x)))`,
  `(rule ((A) (B)) ((union (A) (B))))` and `(rule ((K z) (M w)) ((H (min z w))))` stops in
  the source once `F(A())` is stored, before any rule binds `z` to it, whereas the compiled
  program runs one more pass and builds `H(F(A()))`. A program without saturation is
  simulated exactly, run by run (`Proofs/Congruence/Exact.lean`), and its rules and its
  check may take minima.
- A `min` over an application would be looked up by its spelling in a compiled query, and
  built by a compiled head whether or not it is chosen (`encodeBuildWith`), so the fragment
  admits `min` over variables only.

The proof checker and the lifting accept `SourceProof.Fragment`, the monotone,
ordering-free part of the fragment: a rule node's disequality is a syntactic test on the
substitution, which is not sound once the two terms become equal in the final e-graph, and
a minimum compares spellings, which the final representatives need not be. It excludes
subsumption as well: a previously matched row need not remain live.

The reference interpreter refines the specification up to `Database.SameMeaning` for
monotone, ordering-free programs (`exec_programStep`) and for union-free programs with
subsumption, disequalities and `min` (`exec_programStep_noUnions`). The latter includes
the compiler's output (`Congruence.exec_encode_programStep`); mixed union-and-subsume
programs are not covered, and neither are source programs whose rules test a disequality
or that take a `min`, which the corpus gates still execute. `execRunRules` matches every
rule against the pre-state, then applies the firings' writes and subsumptions.

`Congruence.compile` returns the compiled program with one origin per rule, in
`Program.rules` order. Origins identify a source rule by index, path compression, parent
collision, or a constructor's congruence or subsumption rule. Proof lifting uses these
tags; they do not affect execution.

The output has no `union` actions. `Relational.exec` executes it with structural equality
and stored-value existence, without implicit congruence rebuilding. The congruence gate
compares this interpreter with the general interpreter on the corpus; this executable
comparison is distinct from the mathematical compiler correctness theorem.

## Query traversal

Flattening visits conjuncts left to right. Within an application it recursively visits
children left to right, then emits the application over fresh child variables, one
union-find edge per child, and the edge to its fresh root, its id. Within equality it
visits the left expression, then the right, then emits equality of their ids. Each
occurrence gets its own fresh variables, including repeated subexpressions. Variable
supplies are local to a rule; source names cannot use the generated `@` prefix. The paper
shows the pass as inference rules, written as the `@[blueprint]` statements of the
compiler's definitions.

For example, `(= (F (G x)) (H x))` becomes:

```text
(G @v0) (@UF @v0 x) (@UF (G @v0) @v1)
(F @v2) (@UF @v2 @v1) (@UF (F @v2) @v3)
(H @v4) (@UF @v4 x) (@UF (H @v4) @v5)
(= @v3 @v5)
```

Resugaring receives the original query and repeats this traversal while consuming
premise proofs in order. No separate tree describing flattening is stored.

## Proof lifting

`Resugar.lift` checks a proof against the compiled program, then rebuilds it
recursively as a source proof tree. A UF row becomes an equality, and a value or an
application the target matched its reflexivity. Generated rules are recognized by their
origin tags: path compression is transitivity, a parent collision symmetry and
transitivity, and a congruence firing turns the second application into the first by
congruence on each child and chains the two roots through them. A source rule firing
names the original rule, restricts the substitution to the original query's variables,
and recovers its premises by walking the original query in the compiler's order
([Resugar/Query.lean](EgglogSemantics/Resugar/Query.lean)): an application's premise is
its matched atom with each child edge chained into the child's proof and pushed in by
congruence, made reflexive for a bare pattern (the paper's `e = e`), and an equation's the
two sides' root edges chained through the equality. Reconstruction reads the log in the
order it was written, so a term's existence is justified by a source firing whose facts
cover every subterm.

Each node is validated by `SourceProof.checkNode` as it is built, and the result is
checked again by `SourceProof.check`. `Resugar.lift_infers` gives a lifted claim a
source derivation when the source state is reached, well formed, and saturated for every
run in the program. `ExtlogTheorems.lifted_proofs_sound` states that lifted claims between
terms of the reached, saturated source e-graph hold there.

`Resugar.prove` is egglog's `prove`: a rule with the final check as its query and a fresh
nullary goal as its head runs after the schedule, the goal's row is proved like any other,
and the premises of that rule node are the proofs of the check's conjuncts, about the
original program. `difftest paper-proof <file.egg>` prints that proof in the paper's
notation, after `SourceProof.Proof.simplify` removes redundant reflexivity, transitivity,
congruence and symmetry steps. The simplified result is checked again.

`Resugar.Export` writes proofs as JSON certificates with the program as `.egg` source,
listing each tree's nodes in postorder with shared subtrees, and
[proof_certificate.rs](../egglog/src/proofs/proof_certificate.rs) replays them through
Rust egglog's proof checker. The fixtures in
[Resugar/Fixtures.lean](EgglogSemantics/Resugar/Fixtures.lean) pair lifted proofs with
hand-written proofs that both checkers must judge alike; their export is committed as
`egglog/tests/lean-certificates.json`, and `make -C semantics lean-certificate-test` also exports and
checks the whole corpus.

## Validation

`make -C semantics lean-check` builds the library, audits for proof holes, and runs the corpus gates.
The congruence gate compares every pair of held source terms against the compiled
program's reading, and checks that execution with and without equality reasoning agrees.
The provenance gate checks data preservation of terms, subsumption marks and check
outcomes, and every retained row's proof read off the log. The resugar gate lifts those
proofs and checks them against the original source program, and the certificate gate
exports the same proofs and checks them with Rust egglog. Failures, stuck executions, and
insufficient fuel fail the command. Out-of-domain cases are counted separately: a program
outside the compiler's fragment is skipped by every gate, and one outside the checker's
fragment, with subsumption, a disequality or a minimum, has its encodings checked but no lifted
proofs.

The corpus is the curated and generated programs in `DiffTest.lean` together with the
hand-written `.egg` programs under [`tests/`](tests), which `Program.ofEgg` parses; a
source `min` is written `ordering-min`, egglog's minimum on an eq-sort, and the difftest
scripts emit that spelling. The source difftest (`difftest.sh`) runs each corpus program in
egglog, comparing its row counts and asserting its final check with the outcome the
interpreter predicts in egglog's check semantics; on a program that subsumes no rows that
outcome is the model's as well. The egg gate (`difftest egg`) checks each of those against
its committed snapshots: the congruence encoding in `<name>.congruence.egg`, the provenance
encoding in `<name>.provenance.egg`, and, for a program in the checker's fragment, the
lifted source proofs in `<name>.proofs.txt`.
`make -C semantics lean-update-egg-snapshots` rewrites them after an intended change. A program that
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

## Slotted semantics

The slotted layer (`EgglogSemantics/Slotted/`, described in [SLOTTED.md](SLOTTED.md)) is a
specification beside the plain one, not an encoding: the slotted pass that compiles it to
plain egglog is phase 2. A slot `$s` is the nullary term `Term.app "$s" []`; a binder
signature `bind(f)` says which argument positions of `f` hold names bound in which children;
the congruence `SCong` adds the `Rename` rule, closing every known equation under every
partial injection of slots defined on both sides, with fresh bound names, so α-equivalent
spellings of an existing term are congruent and a slot an equation does not mention becomes
redundant. Matching binds variables to `reps'`, the representatives closed under renaming,
looks applications up in `live'`, interprets pattern slots as fixed names, and
interprets the free-name and renaming guards. A round fires every slotted match under every
choice of fresh names for the slots used only in actions.

`difftest slotted-parse` reports which files of `egglog-experimental/tests/slotted` the
slotted parser accepts, each as one program per check; `Slotted/Tests/Bounded.lean`
evaluates the specification over finite slot and term universes, soundly for the equalities
and redundancies it finds, and `Slotted/Tests/Examples.lean` runs the paper's example on it.

### Simulation with subsumption

`Rel subsumption src d` records that union-find keys are the stored source terms, every
application has a permanent node row when subsumption is enabled, and `Marker d f ā` holds
exactly for the source's subsumed spellings. In plain mode the source subsumption set is empty, so marker clauses are
vacuous and every held source application is live. A compiled mark either retires a stale
union-find edge with a smaller replacement, or hides a source application whose children are congruent to a marker's.
At `Canon d`, the converse holds too: every held application with such a marker is
subsumed. Hence compiled application reads agree with source live rows. The source round
correspondence transports marks by constructor and congruent children; maintenance keeps
markers and source meaning fixed. Its finite rank counts both stored rows and marks.

The hand-written subsumption corpus tests unions after subsumption, spellings built after
marking, congruence through hidden nodes, and saturation with unary and nullary marks.
`subsume-new-spelling` and `subsume-congruent-check` deliberately fail the model's live-row
check. The source egglog difftest predicts their successful checks using
`checkIncludesSubsumed := true` semantics. The compiled difftest's census is an ordinary
rule query and excludes subsumed constructor rows on both sides, even though raw
`print-size` includes them.
