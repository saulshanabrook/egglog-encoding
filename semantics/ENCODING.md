# Encoding passes

## Constructor-and-delete encoding (October 2026)

The modelled language is untyped and has no declarations: applying any name to any
arguments builds a term, and a relation is a name whose applications are never nested
(`Spec/Syntax.lean`). It has no rulesets and no rule store either: `run ρ̄` and
`saturate ρ̄` name the rules they fire, so the state is one set of equations, and a program
is a command sequence ending in the single check that decides its outcome. egglog's named
rulesets and `rule` commands are resolved by the parser, which expands a run of a ruleset
into a run of the rules registered in it so far; the emitter does the reverse with one
ruleset per command. The congruence compiler emits no merge function. Its tables
`@UF(key, parent)` and `@fView(children…, id)` are relations, and every change to a row is a
rule that deletes the stale row and writes its replacement. Two language features support
this: a `delete` action and a disequality pattern `e ≠ e`. Source programs use neither
(`Program.Fragment.monotone`).

### Semantics

- `delete e` writes no equation and erases the row `⟦e⟧`: `W_σ(delete e) = ∅` and
  `X_σ(delete e) = {⟦e⟧}` (`Action.write`, `Action.erase` in `Spec/Eval.lean`).
- A round collects the writes `W` and erasures `X` of every firing in the pre-state, then
  removes every spelling of an erased row and adds the writes:
  `RunRules ρ̄ E = (E ⊖ X) ∪ W`. `E ⊖ X` removes the reflexive assertion of every held
  `f(s̄)` with `s̄ ~ t̄` for some `f(t̄) ∈ X` and keeps the columns `s_i` existing
  (`Database.deleteRows`); deleting an absent row changes nothing. Deletions before
  writes mirrors egglog, whose table merge runs
  `do_delete` before `do_insert` (`core-relations/src/table/mod.rs`): a row that one firing
  deletes and another writes survives the round.
- `e₁ ≠ e₂` holds when both sides evaluate to existing terms that are not congruent
  (`Matches.unequal`). In the union-free target this is structural inequality.
- The sequential reading in `Spec/Sequential.lean` applies a delete in the current state;
  it agrees with the round for heads that neither assert an equation before a delete nor
  delete a row they also write. The proofs use delete-free heads.

### Rules

With `m = min b c` in the model's term order (egglog: `ordering-min`), the generated
maintenance rules are

| Origin | Query | Actions |
| --- | --- | --- |
| `compress` | `(@UF a b) (@UF b c) (≠ b c)` | `delete (@UF a b)`, `(@UF a c)` |
| `collide` | `(@UF a b) (@UF a c) (= b (min b c)) (≠ b c)` | `delete (@UF a c)`, `(@UF c b)` |
| `eclass f` | `(@fView cs e) (@UF e x) (≠ e x)` | `delete (@fView cs e)`, `(@fView cs x)` |
| `child f i` | `(@fView cs e) (@UF cᵢ x) (≠ cᵢ x)` | `delete (@fView cs e)`, `(@fView cs[i := x] e)` |
| `viewCollide f` | `(@fView cs y) (@fView cs z) (= y (min y z)) (≠ y z)` | `delete (@fView cs z)`, `(@UF z y)` |

Builds write `(@fView args (f args))` and the self-loop `(@UF t t)`; a union writes
`(@UF a m)` and `(@UF b m)`. A self-loop written for a value that already has a parent is
stale, and `compress` with `a = b` removes it. The two collision rules keep the smaller id,
delete the other row, and link the larger id under the smaller; a UF collision whose loser
already has a parent produces a collision one level up, so unions still meet at roots.
A source `run ρ̄` compiles to the run of the compiled rules followed by a saturation of the
maintenance rules; a source `saturate ρ̄` saturates the compiled rules together with the
maintenance rules, so rebuilding interleaves with every round, and is followed by the same
maintenance saturation. That trailing saturation is needed: every round refires every
source rule, so a source rule can rewrite a stale view row in the round that deletes it,
writes win, and the row survives until a round without source rules. The final check is
flattened like a query.

The disequality guards are necessary, not cosmetic. Because writes win over deletes, a rule
whose write equals one of its premises keeps that row alive against every other rule's
deletion. Without the guard, `compress` fires on a self-loop `(@UF m m)`, `(@UF m m)` and
rewrites it, so a displaced self-loop is immortal; and `collide` fires on the pair
`(@UF a c)`, `(@UF a c)` and rewrites the larger parent, so a displaced parent is immortal.
With the guards no rule fires on a canonical row, and every rule's write is strictly more
canonical than the row it deletes.

There is no leader query. Query variables are bound through view rows, whose children and
outputs are canonical at a rebuild fixpoint, so a source rule head already sees canonical
ids; the previous encoding needed leaders because stale keys stayed represented.

### Fixpoints, informally

At a rebuild fixpoint no maintenance rule matches. `compress` not matching means every
parent is a root; `collide` not matching means every key has one parent; the view rules
not matching means every view row has canonical children and output and no two rows share
a key. A stale row is deleted every round and is only rewritten from a strictly staler row,
so staleness is well founded and the fixpoint is reached; the formal argument is part of
the pending proof work.

### Provenance: a firing log

The provenance pass (`Provenance/Encode.lean`) adds one action to every rule: a row
`@prov:fire:<i>(x₁, …, xₙ)` that records a firing of rule `i`, the rule's position in
`Program.rules`, under the values of its query variables. No rule reads these rows, so the instrumented program builds exactly the data of
the original, round for round, deletes the same rows, and settles when the original does.
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
does not work with deletes: a row re-derived with a new proof is a new row for one round,
and in that round it breeds further variants before a deduplication rule can remove it, so
instrumented saturations of two-premise rules never settled (the instrumented
`commutativity` case grew from 36 to 2936 rows in four rounds). The log keeps proof
identity out of the data entirely.

### Status

- Executable: `difftest congruence 64` passes all 101 corpus cases; `difftest provenance
  64` and `difftest resugar 64` pass all 101 in about three seconds each; the 14
  hand-written programs under `tests/` have `.congruence.egg`, `.provenance.egg` and
  `.proofs.txt` snapshots (`difftest egg 64`). `scripts/compiled-difftest.sh` runs the
  compiled programs in Rust egglog, with generated `@` names spelled `at_`, and compares
  the view relations' row counts, which are the numbers of canonical e-nodes and
  independent of representative choice: 101 of 101 agree. `scripts/difftest.sh` (source
  programs, Lean against egglog) passes 101 of 101, and the Rust checker judges the 120
  exported source certificates like the Lean checker (`make lean-certificate-test`).
- Interpreter: `execRunRules` matches every rule against the pre-state, deletes every
  firing's rows, then unions every firing's writes. The relational runtime
  (`Congruence/Relational.lean`, structural identity only) agrees with the general
  interpreter on every case.
- Proofs: the specification-level proof modules and the certificate soundness proofs are
  ported to the declaration-free specification (`PROOF-PORT-A.md`, `PROOF-PORT-B.md`,
  `PROOF-PORT-C.md` record every statement change). `SourceProof.check_infers` and
  `Resugar.extractAll_infers` give checked and lifted certificates their meaning in the
  reached, saturated source state. The reference interpreter refines the specification
  up to `SameMeaning` for delete-free programs (`exec_programStep`) and for union-free
  programs with deletes, disequalities and `min` (`exec_programStep_noUnions`,
  `Congruence.exec_encode_programStep`), which is what the compiler emits; mixed
  union-and-delete programs are not covered. The compiler-correctness proofs under
  `Proofs/Congruence/` are about the previous, merge-function encoding and do not
  transfer; the paper displays the theorem (`Congruence.Correctness`) as a statement, and
  its proof for this encoding is open.

The sections below describe the previous, merge-function-based encoding and its proofs.


## Current compiler correctness: live tables and bounded source schedules

The mathematical specification stores value equations and reflexive function atoms
in one assertion set. Function entries are a derived view; declarations supply the
key/output split and merge policy. Expression matching has one rule. A merge consumes
two colliding atom assertions and installs the result, preserving column values and
merge-body effects. A run (`RunStep`) fires its rules and merges until no conflict
remains (`Database.conflicts` is empty). Saturation repeats runs until one leaves
congruence unchanged. Subterm existence is implicit, so redundant root assertions need
not make the raw stores equal.
The definitions have brief comments in `Spec/Database.lean`, `Spec/Match.lean`, and
`Spec/Step.lean`; `Spec/Sequential.lean` holds the step-by-step forms the proofs use.

The core specification and ordering/live-table lemmas build. New mathematical
proofs establish semantic equivalence of ordering-free source checks, current UF
root uniqueness, and termination of every generated merge schedule on finite
stores with the generated table shape. These are in `SameMeaning.lean`,
`SourceMeaning.lean`, `Congruence/LiveLeaders.lean`, and
`Congruence/LiveNormalization.lean` under `EgglogSemantics/Proofs`.

The conditional compiler-correctness port is now checked for these semantics.
`preservesObservations` in `AbstractComplete.lean` proves the original public contract:
well-formed supported programs agree on success versus failed checks whenever both
mathematical evaluations terminate. All representation, UF coverage, and rebuilding
invariants are derived from actual executions. The proof uses the source's inferred-fact
completion internally; neither the language nor the theorem uses an executable database.

`Tests.CongruenceCorrectness` constructs actual mathematical executions for a successful
nonempty check, a dynamically failed check, and a rule round that creates the checked
term. All satisfy `NoSaturate`; an empty-output compiler still violates the contract.
The focused build passes (1,080 jobs). The strengthened theorem's 111-module local
import closure contains no interpreter; its axiom audit uses only `propext`,
`Classical.choice`, and `Quot.sound`.

Termination preservation is now checked for sources satisfying `Program.NoSaturate`.
The source can use any finite number of `run` commands; each compiled action or run
finishes `saturate @rebuild`. Neither source `CongrOn` nor the language's scheduling
syntax changes. `LiveSaturation` proves finite-bound saturation despite destructive
row replacement, and `LiveRebuildTermination` proves maintenance has such a bound.
`AbstractTerminationComplete` composes these results into `preservesFiniteObservations`.

`Proofs/Source/Termination` derives source evaluation existence from well-formedness,
constructor-only declarations, and `NoSaturate`. Thus `evaluations_exist` gives actual
finite executions on both sides, and `observations_iff` equates their possible Boolean
success/failure observations. `preservesBehaviors` in `Proofs/Congruence/Correctness.lean`
now proves equivalence of success, failed checks, and divergence without evaluation premises.
`LiveProgramTermination` excludes every infinite compiled merge/rebuilding trace for
`NoSaturate` sources. These theorems and their non-vacuity examples use mathematical
databases only, with atomic rule rounds as in the specification.

Source saturation is deliberately outside this strengthened theorem. The optional
flattened encoding interleaves maintenance with source rules, whereas Rust recursively
inserts completed rebuilding after each scheduled run. `Tests.LeaderGrowth` records
the nested-head growth trace and proves that its program violates `NoSaturate`.
No nested schedules are needed for the paper's bounded source fragment.

`make -k lean-check lean-difftest` remains blocked on the older `SourceReads` and
interpreter proofs. These are outside the compiler theorem's import closure.
`make check`, retried with serial tests and CPU affinity, passes the nits and all
172 Python tests; Rust tests still encounter the host thread limit in explicit
multi-threaded cases. No generated snapshot replacements are accepted.


## Prior proof milestone and continuing scope

The completion claims in this section record the historical semantics at
`aac8168`. The current full Lean build remains blocked on the downstream proof
migration; the new foundational modules are checked separately. This section
must not be read as a completion claim for the current specification.

This is the working plan for PR #58. Mathematical congruence compiler correctness is
proved separately from the executable sanity checks:

- Add a top-level `check q`. It observes whether the complete query has a match, leaves
  the database unchanged on success, and stops the program on failure. Checks neither
  construct terms nor initiate a merge or rebuilding phase.
- Give finite evaluation the explicit results `Result.ok db` and `Result.checkFailed`.
  Failure short-circuits the suffix; divergence has no finite evaluation derivation.
- State congruence compiler correctness over mathematical `Database` states on both
  sides. For well-formed programs in the supported source fragment, every pair of
  terminating source/compiled evaluations must have the same success/failure observation.
  Establish query correspondence at command boundaries as the internal proof invariant.
- Interpreter correctness is outside the paper's obligations. Keep executable models
  and differential tests as sanity checks; do not route the paper theorem through
  `FDatabase` or an existential wrapper around executable target evaluation.
- **Termination preservation — proved.** Every finite source evaluation has a finite
  compiled evaluation, counting a failed check as termination. Together with outcome
  agreement, this removes the target-termination premise from finite observation
  preservation. Divergence preservation and termination of every schedule remain outside
  the theorem.

The strengthened mathematical theorem is `Egglog.Congruence.preservesFiniteObservations`
in
[AbstractTerminationComplete.lean](EgglogSemantics/Proofs/Congruence/AbstractTerminationComplete.lean)
and combines the original `PreservesTermination` contract with
`preservesObservations` from
[AbstractComplete.lean](EgglogSemantics/Proofs/Congruence/AbstractComplete.lean). Their
transitive imports contain no executable interpreter modules. The older executable
correspondence theorem remains available for the sanity checks.

The pipeline responsibilities are:

1. **Mathematical congruence correctness — proved.** The execution invariants and check
   correspondence establish conditional success/failure equivalence, and finite row
   bounds establish target execution existence for every finite source evaluation. The
   constructor-only source fragment (`Program.Fragment`) remains. The paper's completeness
   theorem ends here. The compiled target uses functions, but extending the theorem to
   arbitrary source merge functions is deferred.
2. **Implement a sound source proof checker.** Check explicit propositions against
   the original program, initially in the constructor-only source fragment.
   `Fiat` must be justified by original globals; it cannot
   introduce an arbitrary constructor or discharge an unproved rule premise.
   Congruence must preserve evidence that the enclosing application exists. Prove
   that accepted certificates imply their source propositions, including existence.
3. **Add a separate provenance pass.** Instrument the congruence-compiled program
   like Datalog provenance, extended to function entries and merges. Record evidence
   for global entries, rule firings, and merge-derived entries. Rule-created terms
   must have rule evidence, and merge-created entries must retain the evidence for
   both inputs and the merge computation. Do not hide these cases behind `Fiat`.
4. **Lift certificates back to the original program.** Recognize generated rebuilding
   rules by their origin tags and UF operations by the generated table name.
   Translate their justifications into source reflexivity, symmetry, transitivity,
   and anchored congruence, as appropriate. View collisions also require a source
   justification. For source rules, recover premises by walking the original query
   in exactly the compiler's recursive order, unflattening nested applications with
   congruence. Both algorithms receive the original query; there is no saved
   flattening tree. Validate that all generated names and maintenance rules have
   disappeared from the resulting source justification.
5. **Validate the whole pipeline.** Check the *same lifted certificates* with both
   Lean and Rust checkers. Running Rust's own encoder on the same inputs is useful
   comparison evidence, but does not establish this interoperability. Include
   negative tests for invented globals, missing existence premises, malformed rule
   substitutions, and incorrect equality endpoints, alongside positive tests for
   nested queries, repeated applications, rebuilding, UF chains, and function
   merges. Run the complete Lean, Python, and Rust validation suites.

The two compiler passes have separate responsibilities: congruence compilation
encodes rebuilding, union find, and query flattening without proof annotations;
provenance records how its resulting entries were derived. Proof lifting is a third
algorithm that interprets that provenance against the original source program.
The congruence output must contain no built-in unions and must execute without
implicit congruence or other equality axioms. Structural identity and existence
tests remain available. Provenance and lifting need soundness and validation;
they do not need their own completeness theorem for the paper.

This refactor targets the Lean model and encoding. Existing Rust certificate
formats and the Rust checker provide the interoperability target; rewriting the
Rust parser or runtime is outside the agreed scope. Source syntax has no lets,
and function entries use full table atoms such as `(LowerBound expr bound)` in
queries and evaluation. Function entries are not nested term values or union
operands. The constructor-only theorem scope does not remove functions from the
target or from provenance.

Stop and discuss an actual design blocker rather than weakening a theorem,
accepting unjustified proof premises, or silently broadening the source fragment.
Update the status below as each obligation is discharged. Intermediate commits
and pushes to the PR are authorized, including before the proofs are complete.

## Current implementation

The Lean refactor separates congruence compilation, provenance instrumentation, and proof
lifting. The congruence pass is implemented in
[Congruence/Encode.lean](EgglogSemantics/Congruence/Encode.lean), provenance in
[Provenance/Encode.lean](EgglogSemantics/Provenance/Encode.lean), and lifting in
[Resugar/Lift.lean](EgglogSemantics/Resugar/Lift.lean).

## Congruence compilation

`Egglog.Congruence.encode : Program → Program` compiles constructor-source programs into
explicit tables:

| Table | Atom | Meaning |
| --- | --- | --- |
| `@UF` | `(@UF t parent)` | An explicit parent edge |
| `@fView` | `(@fView children… id)` | The id of a source constructor application |

Each table has one output column. Structural constructor terms serve as ids. Building
`f(cs…)` builds its children and writes `(@fView cs… (f cs…))`; it needs no table lookup,
temporary variable, proof term, or separate construction-history relation.

`min` is the only computation in the fragment: the smaller of two terms in the model's
structural order, egglog's `ordering-min`. A source union writes an edge from each of the
two ids to the smaller one; the edge from the smaller id to itself is not a union-find
edge. Both UF and view collisions keep the smaller output and write the same two edges.
Their merge specifications explicitly bind singleton parameters `old` and `new`. All output columns determine
whether a row changed, so no special identity-column setting is needed.

Maintenance rules compress paths, propagate changed output ids through views, and re-key
child columns. Rebuilding runs after each source action and run. Copies of the maintenance
rules also join source saturation rulesets outside the paper's `NoSaturate` fragment;
those copies interleave maintenance without completing it between rounds.

`Congruence.compile` returns commands with rule origins. Source rules are tagged with
their original command index; generated rules identify path compression, output
propagation, or the particular constructor child being re-keyed. Copies in another
ruleset retain the same tag. `tableRole` recognizes UF and source-constructor views.
These tags are for later resugaring and do not affect execution.

The output has no built-in `union` in commands, rule heads, or merge bodies. It also
needs no equality axioms from the target runtime. `Relational.exec` uses structural
identity and stored-value existence for matching and function-key collisions, and omits
implicit congruence rebuilding. `encode_relational` proves that this execution produces
exactly the same result as the general interpreter. Source equality is represented by
ordinary UF and view entries; target `(= x y)` is just an identity test with existence.

## Checks and observable correctness

A top-level `check q` asks whether the entire query has a compatible existential
substitution:

```text
holds(D, q)  iff  ∃ σ. ValidQuerySubst(D, q, σ)
result      ::= ok(D) | checkFailed
```

The finite evaluation rules are:

```text
holds(D, q)     D ⊢ rest ⇓ r
───────────────────────────
D ⊢ check q; rest ⇓ r

¬ holds(D, q)
────────────────────────────────────
D ⊢ check q; rest ⇓ checkFailed
```

The first rule uses exactly the original database. Checks create no terms, export no
bindings, and perform no merge phase. The second rule has no premise about the suffix,
so failure terminates even before a divergent suffix. The empty query succeeds.
Divergence has no finite evaluation derivation; it is not `checkFailed`.

`Source/WellFormed.lean` supplies the static premise separately from `Program.Fragment`:
declarations are fresh and precede uses, applications have the declared arities, and
actions have bound variables and legal global union operands. A declared but absent
constructor remains a valid query and may cause a failed check. Rule unions may use query
variables under the fragment's existing literal restrictions.

The obligation in `Congruence/Correctness.lean` is:

```text
WellFormed(P) ∧ Fragment(P)
∧ ∅ ⊢ P ⇓ r ∧ ∅ ⊢ encode(P) ⇓ s
⇒ succeeded(r) = succeeded(s)
```

Both states are mathematical `Database` values. Neither `FDatabase` nor interpreter fuel
appears in this statement. `preservesObservations : PreservesObservations` is **proved in
Lean** by `Proofs/Congruence/AbstractComplete.lean`. The proof establishes all data and
metadata invariants along actual compiled executions, proves `CheckAgreement`, and then
applies the observation-composition theorem. It has no executable-state or interpreter
correctness dependency and no unproved invariant premise. The public well-formedness
premise is retained; the proof in fact needs only `Fragment` and the two finite evaluations.

`Proofs/Result.lean` proves that successful results coincide with `ProgramStep`, that a
failure is exactly a successful prefix followed by a false check, and that query
correspondence gives check-outcome agreement in both directions. Interpreter correctness
is outside the paper's obligations. The executable `observeM` and `Relational.observe`
return `some checkFailed` for a failed check and reserve `none` for an inconclusive run,
including exhausted fuel. Their regressions are sanity checks, not a replacement proof.

`PreservesTermination` is separately **proved**: a finite source evaluation implies
some finite compiled evaluation. It is not a consequence of conditional observation
agreement alone. `preservesFiniteObservations` combines the two results:

```text
WellFormed(P) ∧ Fragment(P) ∧ ∅ ⊢ P ⇓ r
⇒ ∃ s. ∅ ⊢ encode(P) ⇓ s ∧ succeeded(r) = succeeded(s).
```

Target termination is a conclusion, including when the source fails a check before an
unreachable suffix.

### Strength, non-vacuity, and comparison

The strengthened paper theorem is **preservation of finite success/failure observations**:
each finite source execution has a finite compiled execution with the same observation.
The original conditional theorem additionally covers every pair of finite source and
target evaluations. Neither assumes matching merge schedules or saturation round counts.
`checkFailed` is a defined observable result that must be preserved, not undefined
behavior that licenses arbitrary target behavior.

Non-vacuity requires actual evaluation witnesses as well as consistent static premises.
The mathematical examples in
[Tests/CongruenceCorrectness.lean](EgglogSemantics/Tests/CongruenceCorrectness.lean)
establish well-formedness, membership in the supported fragment, and finite evaluations
on both sides for these programs:

| Source program | Source and compiled result |
| --- | --- |
| Declare nullary `C`; construct `C()`; check `C()` | Success |
| Declare nullary `C`; check `C()` without constructing it | Check failure |

These witnesses rule out an empty supported domain or an impossible finite-target
premise. The general termination theorem separately establishes a finite compiled
evaluation for every finite source evaluation. The original conditional contract alone
admits an always-looping or always-stuck compiler, since it supplies no target evaluation
to compare. The strengthened theorem excludes that loophole: a terminating source failure
must have a finite compiled failure, and a terminating source success must have a finite
compiled success. It still does not constrain programs with no finite source evaluation.
Absence of an `Eval` derivation alone does not distinguish divergence from stuckness.

The internal result is stronger than the final Boolean observation: `boundary_prefix`
relates every pair of successful corresponding prefixes through sound target rows,
source-fact coverage, and completed rebuilding; `checkAgreement` consequently gives
equivalence of the source query and its flattening at each reached check. These results
require no execution of the remaining suffix. Termination preservation supplies a
compiled prefix whenever the source prefix has a finite execution. For the paper,
present check correspondence and finite target execution existence as the technical
lemmas yielding finite observation preservation.

Established compiler theorems make different choices about observations and exceptions:

| Theorem | Observations and guarantee | Explicit limits |
| --- | --- | --- |
| This congruence pass | Every finite source evaluation has a finite compiled evaluation with the same outcome; all paired finite outcomes agree | Existence of a terminating target run; no divergence preservation or guarantee for every schedule |
| CompCert | Successful compilation gives a backward simulation; target behaviors are justified by source behaviors, including termination, divergence, and I/O traces | Source undefined behavior permits behavior improvement; compilation can reject input |
| CakeML backend | Generated machine behavior follows source termination/divergence and FFI traces, or exits early at a resource limit | Source semantics excludes `Fail`; successful compilation and machine/environment setup; explicit resource-limit allowance |

CompCert's [compiler theorem](https://compcert.org/doc/html/compcert.driver.Compiler.html)
and [behavior definitions](https://compcert.org/doc/html/compcert.common.Behaviors.html)
include behaviors for divergence and getting stuck, and prove that every program has a
behavior. Consequently, when all source behaviors terminate without undefined behavior,
the target cannot satisfy refinement merely by diverging. Our termination theorem now
also excludes losing all finite target outcomes for a terminating source, but does not
provide CompCert's guarantees about every target behavior or about divergent sources.

The [CakeML backend paper](https://cakeml.org/jfp19.pdf), §2.3–2.4 and §10, explicitly
acknowledges that its resource-limit exception admits a compiler that always immediately
runs out of memory. Its theorem nevertheless constrains ordinary terminating and
diverging behavior, including traces. The comparison is therefore about the exact
permitted exceptions, not a claim that established compiler theorems have no loopholes.

The remaining distinction is between existence of a terminating target execution and
constraints on every target behavior. Arbitrarily stuttering schedules are possible in
the relational step semantics. Full behavioral refinement would also require a treatment
of divergence and stuckness, including programs having no finite source evaluation.

### Correctness proof

Write `C_P(A)` for the prelude of the **whole** program `P`, followed by the compiled
commands of its prefix `A`. Using the whole prelude matters: its declarations and copies
of maintenance rules depend on the complete program, including later saturation commands.
The internal statement needed at each check is

```text
P = A; check q; B
∅ ⊢ A ⇓ ok(S)       ∅ ⊢ C_P(A) ⇓ ok(T)
──────────────────────────────────────────
holds(S, q) iff holds(T, flatten(q)).
```

`CheckAgreement` in `Proofs/Congruence/Observation.lean` states exactly this property.
`observations_of_checkAgreement` proves the final success/failure theorem from it. The
prelude and the compiled blocks of non-check commands contain no checks, so a terminating
execution of any such block must succeed. Align the two executions one source command
at a time. At a check, query agreement implies that both pass or both fail. In the passing
case the databases remain unchanged and induction continues. In the failing case both
executions immediately return `checkFailed`; there is no premise about the remaining
program. If both reach the end, both return `ok`. This argument uses only the two given
finite executions. It does not construct a target execution or relate round counts.

The data proof supplying `CheckAgreement` uses the following boundary relation. A reading
`T ⊢ t ↝ i` is `ViewRepr T t i`: literals read as themselves; an application reads through
the view of its constructor after recursively reading its children.

- Every held source term has a target reading, and every nonreflexive asserted source
  equation has readings of its two endpoints joined by a UF edge in either direction.
- Every view row `View_f(cs, i)` has a held source witness `f(as)` with `as ≡_S cs` and
  `f(as) ≡_S i`. Every UF row `UF(a, b)` satisfies `a ≡_S b`.
- The target is rebuilt. Its equations are diagonal, its UF edges descend in the term
  order, and its generated declarations and maintenance rules are present. Source rules
  registered so far correspond exactly to their compiled rules.

The first two clauses express completeness and soundness. They do not require the raw
source and target term sets to be equal, or a particular choice of representative.

**Rebuilding lemma.** A finite, well-formed target at a generated-rule and merge fixed
point has canonical readings. A collision of two views at the same key joins their
outputs: the merge body writes both outputs to their minimum. The same reasoning joins
two outgoing UF edges. Path compression makes parent reachability transitive. Output
propagation and child rules transport view rows along these parent paths. All of these
facts follow from actual `RuleResults` and `MergeStep` instances; they are not additional
rewrites in the semantics.

Every id reaches a root. The proof uses the finite set of ids reachable in this database
and strict descent of nontrivial UF edges; it does **not** assume that the structural
order on all terms is well founded. Two reachable roots coincide because competing
paths join. Normalize each view's keys and output to roots. Structural induction on a
source term then shows that all its readings have the same root: corresponding child
readings normalize to equal keys, and the parent outputs join at that key. UF soundness
and literal isolation keep literal roots equal to their original literals.

This lemma is proved in `AbstractMaintenance.lean` and `AbstractRebuild.lean`.
`Proofs/Finite.lean` separately proves finiteness for every mathematical state reached
from empty by a finite successful prefix, including finite saturation derivations. A
round has finitely many matching substitutions because its rules, held terms, and query
variable lists are finite. Finite actions, merges, and sequences preserve finiteness.

**Query lemma.** At a boundary satisfying the relation, a source query has a complete
match iff its flattening has a complete target match. In the forward direction, choose
one canonical reading for each value of the source substitution. This single assignment
is shared by every occurrence of every query variable. Congruence transports a held
pattern witness to readings of the instantiated expressions. Even when matching
temporarily introduces query operands, those operands introduce only reflexive equations;
they cannot provide a new held witness. Traverse the original syntax in compiler order,
bind the fresh variable for each application to its reading, and satisfy the emitted
view atoms and equalities. Disjoint fresh-variable intervals and the reserved namespace
make these bindings compatible across the whole conjunction.

For the reverse direction, read the flattened view atoms back through the original
syntax. Sound view rows supply source existence and congruence. Because each source
variable occurs as a view key, its target value is a held source value; generated table
terms cannot be substituted for source values. Restrict the resulting assignment to
each pattern and join those substitutions. Groundedness preserves the existence
requirement at equality patterns. This is the proved `Abstract.Rebuilt.queryHolds_iff`
in `AbstractForward.lean`, using `AbstractQuery.lean`, `AbstractTransport.lean`, and
the reverse matching proof in `Match.lean`.

**Execution lemma (proved).** The prelude establishes the boundary relation
at empty source data, and paired successful executions of each source command and its
compiled block preserve it. The mathematical argument is by command cases:

- The prelude declares tables and registers maintenance rules without creating data.
  Source declarations are already installed there. Fresh declarations, consistent arities,
  and the reserved namespace give the required signatures without name collisions.
  Rule registration installs exactly the corresponding compiled rule. At a rebuilt
  boundary neither operation can add data through a further merge phase.
- Building an application writes its children before its view, with the structural
  application as its id. Induction on the expression gives readings for the source result
  and all newly built subterms. A union additionally writes both endpoint ids to their
  minimum, directly establishing the required joined readings. These rows are sound in
  the source action's post-state.
- A generated merge preserves soundness. Colliding views have source-congruent outputs
  by anchored congruence on their held witnesses; colliding UF edges have source-congruent
  outputs by transitivity. Their minimum is one of those outputs. Maintenance preserves
  soundness by transitivity and replacement of congruent children. All phases retain old
  rows, so existing readings and joined source equations persist. Minimum links descend,
  and compression preserves descent. Thus arbitrary intervening merge choices are allowed.
- For `run R`, use the query lemma in both directions on the pre-state. A compiled match
  gives a source match at the same source-valued ids, so its whole head is justified by a
  source firing in that round. Conversely, a source match gives a compiled match under
  the common canonical assignment. Induction over the head's expressions and actions
  represents every source contribution. Scoping, declared constructors, and the fragment's
  literal-union restriction ensure these whole source heads evaluate successfully.
  Unioning all contributions preserves both directions. Maintenance copies selected by
  `R` add nothing to the already rebuilt pre-state; the trailing rebuild reestablishes
  canonical readings after the new contributions.
- For `saturate R`, compare fixed points rather than rounds. To prove soundness, fix the
  final source state and induct over the given finite target derivation. Initial rows
  remain justified there; a compiled firing reads back to a source firing whose results
  are already included by the source fixed point. Merges and maintenance preserve those
  justifications. To prove completeness, fix the final target state. Copies of all
  maintenance rules in `R` make that state rebuilt. Induct over the given finite source
  derivation: represented premises give a compiled firing, and the target fixed point
  already contains its head. The query argument here is relative to the represented
  source intermediate state; soundness may be justified in the larger final source state.
  Thus different numbers of source and target rounds cause no problem. The trailing
  dedicated rebuild preserves the established relation.
- A successful check leaves both states unchanged. The query lemma also ensures that a
  failing check fails on both sides, as used in the observation proof above.

Induction over successful prefixes using this execution lemma establishes
`CheckAgreement`, which the observation theorem turns into `PreservesObservations`.
This composition is proved by `Boundary.step`, `Boundary.program`, `boundary_prefix`,
and `checkAgreement` in `AbstractComplete.lean`; the final theorem is
`preservesObservations : PreservesObservations`. `AbstractWidths.lean` derives declared
row widths and rule validity from the compiled program, while `AbstractMetadata.lean`
derives the signature, rule census, and diagonality from actual prefix execution.
`AbstractMerge.lean`, `AbstractMaintenanceSound.lean`, and
`AbstractMaintenanceDescent.lean` prove preservation for arbitrary merge choices and
maintenance firings. `AbstractGlobals.lean`, `AbstractSoundRounds.lean`, and
`AbstractRounds.lean` supply the command cases. No invariant is left as a public premise.

### Termination preservation proof

Finiteness of each reached database alone does not prove termination: a sequence of
finite databases can grow forever. The new argument supplies **one finite bound for all
reachable databases** in each compiled saturation.

`AbstractFiniteRows.lean` defines `SoundRows(S)`: view rows justified by an existing source
application at congruent children, and UF rows joining source-congruent values. When
`Terms(S)` is finite, these rows form a finite set. The held source applications determine
finitely many view names and arities, and every column comes from `Terms(S)`.

For dedicated rebuilding, all reachable target terms lie in
`Terms(T₀) ∪ SoundRows(S)`. Merges and maintenance rearrange held values without creating
new constructor values. `AbstractTermination.lean` proves this bound and constructs
finite completed merge and rebuild executions.

For source saturation, fix the source's finite final state `S*`. The existing soundness
proof justifies every finite target firing in `S*`, because `S*` already contains every
source rule contribution. Compiled source heads only write generated rows; any newly
constructed proper subterm is a source value. `AbstractRowWrites.lean` and
`AbstractSaturationTermination.lean` therefore bound every reachable target term by

```text
Terms(T₀) ∪ Terms(S*) ∪ SoundRows(S*).
```

`Proofs/FiniteSaturation.lean` chooses a reachable state with a maximal equation set inside
the finite bound. A rule round is always available with a reflexive merge phase, so it
cannot enlarge that state. Any subsequent merge is likewise reachable and cannot enlarge
it. Rules, declarations, and environment remain fixed, so the state is both rule-saturated
and merge-saturated. The maximizing state comes with an actual finite reachability
derivation; no assumption of a target fixed point or round bound is introduced.

`AbstractTerminationCommands.lean` constructs the prelude and ordinary command blocks,
then inducts over the finite source evaluation. A failed check ends this induction
immediately. `AbstractTerminationComplete.lean` closes the original `PreservesTermination`
contract and combines it with `preservesObservations`. The result uses neither an
interpreter bridge nor a well-founded order on all possible structural terms.

## Query traversal

Flattening visits conjuncts left to right. Within an application it recursively visits
children left to right, then emits the parent's view atom. Within equality it visits the
left expression, then the right, then emits equality of their resulting ids. Each
application occurrence gets one fresh variable, including repeated subexpressions.
Variable supplies are local to a rule; source names cannot use the generated `@` prefix.

For example, `(= (F (G x)) (H x))` becomes:

```text
(@GView x @v0)
(@FView @v0 @v1)
(@HView x @v2)
(= @v1 @v2)
```

Resugaring will receive the original query and repeat this traversal while consuming
premise proofs in order. No separate tree describing flattening is stored.

## Provenance instrumentation

`Provenance.encode` adds one proof output to each function. Proof constructors identify
the exact global command, rule action, or merge computation. Rule proofs carry the
substitution and ordered premises; merge proofs carry both input proofs. Their claims
are recovered by evaluating the original action or merge, without guessing endpoints.

Appending a proof output preserves the original merge parameter bindings. The pass
instruments actions and appends a result without renaming the original expressions; it
appends fresh `@prov:p0` and `@prov:p1` parameters for the two input proofs. The input
check requires distinct parameter names of the declared width and excludes the reserved
`@prov:` prefix, even for unused parameters. Scalar and tuple parameter spellings are
handled by the parser and emitter;
[`mergeEnv`](EgglogSemantics/Spec/Step.lean) defines the componentwise binding.

The pass accepts flat table queries and equality tests whose variables and existence
witnesses come from table premises. This covers the congruence compiler's output;
unanchored equality-only queries and constructor writes are outside its input
fragment. Function bodies and results may use `min` and
multiple output columns. Generated names use the reserved `@prov:` prefix.

Only original data columns determine merge conflicts. This also suppresses collisions
between distinct proofs of identical rows. A conflict records both inputs' proofs in
the result's proof, and body facts record the merge justification too. Proof metadata
therefore cannot trigger a data merge or cause an otherwise stable rule to accumulate
longer resident proofs.

Extraction decodes a proof constructor into a proof tree with explicit facts, then checks
it against the uninstrumented relational program, which has no `union`. Equality premises
use checked subterms of table facts as existence witnesses; no auxiliary existence
relation is needed. These are intermediate proofs, which lifting translates into source
proofs checked against the original program.

## Proof lifting

`Resugar.lift` checks a relational proof against the compiled program, then rebuilds it
recursively as a source proof tree. A view row `(@fView cs… id)` becomes the claim
`id = f(cs…)`, a UF row an equality, and a value its reflexivity. Global rows become
`fiat` nodes. Generated rules are recognized by their origin tags: path
compression is transitivity, output propagation symmetry and transitivity, and child
re-keying anchored congruence. A UF or view collision joins its two inputs the same way.
A source rule firing names the original command, restricts the substitution to the
original query's variables, and recovers its premises by walking the original query in
the compiler's order ([Resugar/Query.lean](EgglogSemantics/Resugar/Query.lean)),
consuming one flattened premise per application and equality and rebuilding nested
patterns with congruence. A subterm's existence comes from the derivation that introduced
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

## Proof status

The congruence pass has kernel-checked proofs for:

- Mathematical check correspondence and conditional success/failure agreement, with
  all representation invariants derived from actual executions
  (`Abstract.checkAgreement`, `preservesObservations`).
- Finite target execution existence and preservation of finite success/failure
  observations (`preservesTermination`, `preservesFiniteObservations`).
- Union-free output and equivalence with execution using structural identity only
  (`encode_unionFree`, `encode_relational`).
- Query flattening and matching in both directions (`sourceMatch_of_encodedQuery`,
  `encodedQuery_match_of_source`).
- Preservation of sound entries, descending UF edges, and the connection between
  retained entries and live rows through source actions, merges, and maintenance.
- Unique roots and normalized view readings at rebuilding fixed points
  (`Rebuilt.viewLeader`, `Rebuilt.viewsCover`).
- Source rule firings, aligned rounds, and saturation (`encodedRule_firing_reads`,
  `round_simulation`, `saturation_simulation`).
- Prelude initialization and global actions with interleaved merges and rebuilding
  (`prelude_state`, `global_cmd_simulation`).
- The executable reader and correspondence under explicit state invariants
  (`sameClassF_iff`, `Rebuilt.corresponds`).

**The mathematical execution proof is complete**, as described above. The earlier
executable-target theorem remains available for sanity checks:
[Complete.lean](EgglogSemantics/Proofs/Congruence/Complete.lean) proves
`Egglog.Congruence.encode_corresponds`:

```lean
Cong src a b ↔ SameClass target.toDatabase a b
```

Its premises are `P.Fragment`, a source execution from empty, successful compiled
execution, and membership of both endpoints in the source. `encode_corresponds_relational`
gives the same theorem for execution using structural matching and table operations only.
Termination is not asserted.

**Step 2 is complete for the agreed constructor source fragment.**
[SourceProof/Soundness.lean](EgglogSemantics/Proofs/SourceProof/Soundness.lean) proves
`check_supported` and `check_sound` for the executable checker. Accepted claims have
source existence witnesses for every subterm. For endpoints held by the source,
acceptance implies its original `Cong` relation. The source state must be reached by
the original program, well formed, and saturated for every ruleset. No proof is accepted
by assuming an unproved intermediate term exists.

**Step 3 is implemented.** [Provenance/Soundness.lean](EgglogSemantics/Proofs/Provenance/Soundness.lean)
proves that every accepted relational fact exists in a well-formed, reached state
saturated for the original relational program's rules and merges. The corpus gate
checks data preservation and every retained function entry's extracted proof.

**Steps 4 and 5 are implemented.** [Resugar/Soundness.lean](EgglogSemantics/Proofs/Resugar/Soundness.lean)
proves `lift_sound` for lifted proofs. Every retained row of every in-domain corpus
program lifts to a proof the source checker accepts, and Rust egglog's checker accepts
the same proofs and rejects the same hand-written counterexamples
(`make lean-certificate-test`).

Source merge proofs are deferred: equality can produce another spelling of one
stored function row without establishing a second input to its merge body. The
[Lean counterexample](EgglogSemantics/Proofs/SourceProof/Counterexamples.lean) records this. This does not
affect the constructor-only completeness theorem or the relational provenance pass.

The source fragment is defined once, as `Program.Fragment`: constructor declarations, no
`min` and no generated source names, consistent arities, supported queries, scoped and
declared heads, and no literal unions. A query fact is an application, as in egglog's
syntax; a bare variable or literal fact is outside it. The completeness theorem assumes it
and the source proof checker accepts only programs in it. Arbitrary source merge functions
remain outside its scope.
See [Source.lean](EgglogSemantics/Source/Domain.lean) for the exact conditions.

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
