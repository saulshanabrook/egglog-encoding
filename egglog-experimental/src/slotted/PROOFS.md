# Slotted proofs

`egglog-experimental --slotted --proofs source.egg` extracts and checks proofs
for supported equality checks in [slotted programs](LANGUAGE.md). Each proof uses
source terms, rewrites, and unions. The slotted checker verifies the lifted
proof against the source program before and after normalization.

The compiler emits a variant of the [slotted encoding](ENCODING.md) supported by
egglog's term/proof encoding. Slot lifting consumes unsimplified egglog proofs;
egglog's own proof checker and simplifier are skipped in this mode.

```text
source program → flattened program → encoded program
source proof   ← flattened proof   ← egglog proof
```

# Terms

A term is what the language writes: a constructor applied to children, a payload
literal, or a rigid `Var` name such as `$a`. Each carrier may declare one unary
variable constructor, for example `(V Var)` in `Math`; `(V $a)` is a `Math` term.
A binder column holds a `Var` name directly. Ordinary proof steps compare terms
syntactically: `(Lam $a (V $a))` and `(Lam $b (V $b))` are different terms.
Equivariance explicitly transports proofs between slot names. Alpha changes
bound names by scope. The claim checker infers how the requested terms are named
in the proof.

Printed proofs preserve source slot names in terms, substitutions, and renamings.
They use egglog's S-expression format, with `let` bindings for shared subproofs
and terms.
Internal slots without a source name print as `$v0`, `$v1`, …, skipping source names
and rule variables, even when they do not occur in the printed proof. The same
slot has one name throughout the proof, including permutation coordinates that
appear only in an equivariance step or the final witness. Numbered source slots
remain numbered.

Source axioms and rule instances retain their bound names. Lifting may give
binders distinct names to reconstruct encoded matches; explicit Alpha steps
justify those changes.

The checker derives each endpoint's type from constructor signatures and rigid
values. Both endpoints must have the same type, and a `Var` equality must be
reflexive. Neither propositions nor claims carry a sort annotation. An equality
between `(V $a)` and `(V $b)` cannot establish `$a = $b`, change a binder name,
or establish equality between another carrier's variable terms.

# Propositions

A proposition uses egglog's ordinary `Proposition`: an equality `t1 = t2`.
Any renaming has already been applied to the actual terms. Symmetry, transitivity
and congruence check exact term identities and carry no renaming state.

A renaming `m` is a finite bijection on slot names, the identity outside its
support. `rename(m, t)` recursively renames every slot occurrence, bound and free
alike, including binder declarations. Constructor heads and payloads are unchanged.
The explicit Equivariance rule applies this operation to both endpoints of a proof.

# Justifications

`SlottedProof` wraps ordinary egglog steps and adds `Rule(RuleProof)`, `Alpha`,
and `Equivariance`. Every stored step states an ordinary equality proposition;
equality dependencies use egglog's `ProofId` in the same slotted proof store.
Ordinary steps use egglog's justifications and printer.

A rule has `Vec<RulePremise>`: `Equality(ProofId)` or `RenamingEq { left, right }`.
RenamingEq is inline rule-premise evidence, with no proof ID or standalone
proposition. It cannot be a proof root or an operand of an equality step.

The slotted checker delegates ordinary equality steps and rule applications to
egglog's checker. It validates source axioms, sorts, fresh slots, Alpha, and
Equivariance locally. Source guards use primitive validators with the declared
binding scopes.

**Fiat.** `t = t` for a term the program built -- a slot, a payload literal, or a
subterm of a `let` or a `union` -- and `a = b` for a source `(union a b)`, in
either direction. Reflexivity is not assumed for terms the program never built.

**Rule.** Instantiate `(rewrite L R :name n :when (...))` by a substitution σ.
Pattern variables take terms of their declared sorts; slot literals take distinct
slots, as required by the [language](LANGUAGE.md#fresh-slots).

Premises are ordered: first a proof `t = L[σ]`, then evidence for the
`:when` facts in source order, after ordinary guard normalization. An equality
`(= a b)` requires a proof with endpoints `a[σ]` and `b[σ]` exactly. An Alpha step may establish the required spelling.
A constructor fact requires an existence proof ending at its instantiated term.
A `renaming-=` condition requires a `RenamingEq` premise. Other guards use egglog's
proof normal form: constructor operands are lifted to equality facts, followed
by the primitive call. For example, `(not-free s (F x))` requires a proof of
`(F x) = (F x)` and the ordinary result premise `(Fiat (= () ()))`. A guard
whose operands are variables or literals needs only the result premise. The
primitive validator checks the condition when the rule is checked.

Generated variables are reconstructed from the source rule and its substitution;
they do not appear in printed substitutions. Globals retain their bindings at
rule declaration.

RHS-only slot literals must be fresh for every other binding and the globals
in scope at the rule declaration. The conclusion is
`L[σ] = R[σ]`, its reverse, or reflexivity of a subterm of either side.

**RenamingEq premise.** Holds two ordinary equality proof references,
`left` and `right`. For `(renaming-= a b)`, they establish `a[σ] = ar` and
`b[σ] = br`. A primitive validator checks that a slot permutation takes `ar` to
an alpha-equivalent spelling of `br`. Mere existence does not establish this
relation. The printed form is:

```lisp
(RenamingEq (renaming-= a b) proof-of-a=ar proof-of-b=br)
```

Renaming equality is checked in its enclosing rule and cannot be used as an
ordinary equality proof.

Guards are evaluated on σ with the constructors' binding scopes. `free` tests
membership in the union of the listed terms' free slots; `not-free` tests absence
from that union. `free-names-are` requires exactly the listed free slots.
`(!= a b)` compares instantiated proof terms, following egglog's `!=` validation
convention, and rejects alpha-equivalent terms. `(renaming-!= a b)` additionally
rejects terms that differ only by a bijection of their free slots.

During checking, `(renaming-= a b)` becomes
`(= a ar)`, `(= b br)`, and `(renaming-= ar br)` with fresh witness variables.
The slotted rule proof is converted to an ordinary rule proof with expanded
premises. The ordinary checker verifies it against the expanded rule using the
supplied operand proofs and the primitive validator. The printed proof retains
one `RenamingEq` premise for the source condition.

**Sym.** From `a = b`, derive `b = a`.

**Alpha.** From `a = b`, derive `a = c` when `b` and `c` are alpha-equivalent.
The checker compares binding scopes and preserves free names, constructor heads,
and payloads. The premise establishes existence; Alpha cannot introduce an
arbitrary term without a proof. Its printed form is
`(Alpha (= a c) premise)`.

**Trans.** From `a = b` and `b = c`, derive `a = c`. The middle terms must
be syntactically identical. Endpoint typing prevents composition across sorts.

**Congr.** From `a = F(..., c, ...)` and `c = d`, derive `a = F(..., d, ...)`.
The selected child must match the child proof's left endpoint exactly; the
child proof's endpoints must have the column's declared type. No renaming is
performed by this rule.
The printed form is `(Congr (= lhs rhs) parent-proof child-proof index)`, where
`index` is the zero-based constructor argument position, including binder columns.

**Proj.** From `a = F(..., c, ...)`, derive `c = c`. The argument index must
exist, and the result has that argument's sort. This establishes existence of a
subterm without requiring a separate source axiom.

**Equivariance.** From `a = b`, derive `rename(m, a) = rename(m, b)` for a finite
slot permutation `m`. The checker recomputes both endpoints and checks their
types. This rule applies only the slotted theory's action on slots; it does not
rename payload values or constructor names.

# Claims

A printed claim is an instance of the source query. Query-local slots take the
names selected by the match; globals retain their concrete source names. For
example, after `(let p (F (V $a)))`, `(check (= p (F (V $b))))` can print a proof
of `(F (V $a)) = (F (V $a))`: the query match selects `$a` for `$b`.
This instantiation happens before constructing the equality and its renaming witness.

The checker infers a renaming witness `m` from the claim and its root proof. For
source terms `a` and `b`, the proof must have exactly the endpoints
`a = rename(m, b)`, after the usual binder refresh on the source terms. The
witness is returned by checking; it is not stored alongside the proof.

`(check (= a b))` additionally requires `m` to fix the free slots of `b`, or the
free slots of `a`. The latter is sufficient by equivariance with `m⁻¹` and
alpha-equivalence of bound names. `(check (renaming-= a b))` allows any witness,
but still checks the actual ordinary equality proof and its endpoints. The
source signatures determine the terms' types. Negative claims and other claim
forms are checked, not proved.

When the witness changes the spelling of `b`, the display wraps the proof in
`(Claim (= a (rename m b)) proof)`. A renaming prints as
`(renaming ($from $to) ...)`. The wrapper records a checked interpretation of the
root equality, not another inference rule. For example, alpha-renaming needs only:

```lisp
(Claim
  (= (Lam $a (V $a)) (rename (renaming ($a $b) ($b $a)) (Lam $b (V $b))))
  (Fiat (= (Lam $a (V $a)) (Lam $a (V $a)))))
```

# Normalization

The lifted proof is checked before and after simplification. The pass composes
adjacent equivariance and Alpha steps and removes reflexive congruence, symmetry,
transitivity, and double symmetry. Each reachable proof is simplified once.
Equivariance can remain around a compound derivation: distributing it across
shared premises could duplicate that derivation for every incoming renaming.

Source axioms and rule instances retain their provenance and substitutions.
A renamed source union still has a proof of the original union underneath it.
Slot names in the displayed proof reserve all source names and rule variables.

# The proof profile

`--slotted --proofs` compiles the same slotted graph operations into forms supported
by egglog's term/proof encoding. Generated machinery rules have stable names under
`slotted/`, so slot lifting can identify their derivations. User rules use their
source names, disambiguated when reused, with `/apply` and `/drain` on companion rules.

`group-coset-reps` returns a `Group`. Indexed reads use `group-elements`, sorted
by renaming content, so runtime reads and proof validation agree on each index.

The proof-compatible encoding represents these operations as follows:

- *Shape tables.* `_shape_F` becomes `_shape_class_F (key... back) <sort> :merge old`
  and `_shape_back_F (key...) Renaming :merge old`. The class lookup includes the
  selected back renaming, so rebuilding cannot pair values from different entries.
  `_shapeof_F` becomes `_shapeof_edges_F (...) Renamings :no-merge`, holding
  `[s1 .. sn, back]`, and `_shapeof_syms_F (...) Group :no-merge`.
- *Shape collisions.* The collision a merge block stated is a rule,
  `shape-collision`, in the shape phase: a row `c` whose memoized shape finds a
  stored pair `(c0, back0)` under its key other than its own `(c, back)` states
  `(ShapeEqual c (compose back (inverse back0)) c0)` -- a symmetry of `c` when only
  the renaming differs -- one run after the index write it reads. Since the dedup
  can fold a row in that run, before the collision rule sees it, the profile's dedup
  also states the symmetry between the two rows it compares as it deletes one.
  `Invocation` becomes `(relation Invocation_N (<sort> Renaming <sort>))`, written
  `(Invocation c name a)`, and `invocation-merge` unions two members under one name.
- *Merge behavior.* The `:no-merge` tables are `Unit`- or container-valued.
  Source-term extraction uses the same cost model and decoder in both modes.
- *Claims.* Supported equality checks compile to `slotted-prove` over the shared
  query compiler's facts. The command extracts an existence proof, reconstructs
  one shared substitution for every fact, and checks the instantiated equalities.
  Constructor-existence facts use reflexivity of the witnessed term.
  Other checks use the same
  queries without proof extraction. `--slotted-proof-checks` runs this encoding
  with ordinary checks for comparison.

**Retained programs.** `Compiler::compile_program` returns lowered commands with
resolved source programs and flattened rewrites. Each proof request captures the
source visible at its query, including declaration-scoped globals and original
`:when` conditions. Compiler state follows `push`/`pop` and successive inputs;
unnamed rewrites receive names unique across those inputs and scopes.
`CompiledProgram::run` executes the lowered commands and checks each extracted
proof against its retained source program.

The public `check_proof` and `check_claim` functions take a
`ResolvedSlottedProgram`, together with the proof store and root `ProofId`.
`check_claim` also takes the requested `Claim` and returns its inferred renaming
witness. Slot lifting and unflattening each return `(SlottedProofStore, ProofId)`.

The resolved program contains native `ResolvedNCommand`s and constructor binder positions.
`resolve_program` prepares it from source parsed with `egglog::ast::parse_sexps`:
supply the prefix visible at the query, with includes resolved from the working
directory. Rewrites become typed rules with their root fact, original conditions,
and union action; popped commands are removed. Nested terms and the distinction
between local variables and global references are preserved.
Guard primitives are registered with validators before rule resolution. Their
binding scopes include every constructor visible at the query, including those
declared after a rule. The ordinary checker uses the resolved calls' validators.

The checker derives its axiom and global context from the resolved commands.
The resolved program can be reused across proof stores; each store associates its
slot IDs with source spellings. Checking requires no encoded tables or lowering
metadata.

# Proof lifting

Flattening retains its native rules and generated pattern, class, reading, and
frame names. Proof requests retain the corresponding names for their compiled
queries. These mappings belong to lifting; the source checker does not consult
them. Source rule bodies are prepared in proof normal form when constructing the
checking context. Rule steps instantiate auxiliary bindings and expand their
`RenamingEq` premises against that prepared rule.

The pass in [`proofs/lift_slots`](proofs/lift_slots) produces proofs over those
flattened rewrites. A separate pass in [`flatten/unflatten.rs`](flatten/unflatten.rs)
replays the original rule's constructor traversal, consuming flattened atom and
global premises in the order that flattening produced them. Join ordering changes
the encoded match, but leaves this source premise order intact. Congruence expands
nested patterns; explicit Alpha steps restore their binder scopes. Each firing's
queues and occurrence proofs are temporary. There is no equality-graph search or
stored reconstruction recipe.

Slot lifting consumes source action and rule-head positions emitted during native
proof lifting. Shared lowering traversals identify the corresponding source
terms. Pattern occurrences carry support evidence through class congruences;
restricted constructed children retain ordinary equality proofs that justify
later renamings. Slot alignment uses those occurrences and the recorded frame
readings. Class-group operations replay the runtime's closure and reading
enumeration. These derivations follow the selected native proof and its premises,
without searching for alternative witnesses or certificates.

The pass replaces each flattened application with the original rewrite and its
original `:when` facts, and removes generated variables from substitutions. Slot
lifting proves existence of a head-built subterm by projection from the complete
rule result, preserving that occurrence for later passes. Unflattening preserves
every input step's exact endpoints, so ordinary equality steps replay directly.
The final checker uses only the original source program and the resulting proof.

Generated slots come from one supply that reserves all interned source slots, the input terms' slots,
encoded renaming coordinates, and names introduced during lifting. Negative
input slots are valid and are reserved too. A source union is stated using its
recorded terms, then transported to the decoded binder names by proof steps.

## Slot lifting

Slot lifting maps an egglog proof over the encoded program to a proof of the
flattened slotted program. Pattern expansion returns its proof,
variable bindings, and occurrences together; recursive rule applications have
their own bindings. The pass retains the shared proof arena, memoized
derivations, and fresh-slot supply across expansions. Its core is a denotation
`dec` from encoded terms to source terms:
`dec(F(m1, c1, ..., mk, ck)) = F(m̂1·dec(c1), ...)`, where
each edge is completed to a bijection by naming the child's redundant slots with
fresh names. A rigid name column is a singleton renaming: `dec(V({0→a}))` is
`(V $a)`. Binder columns use the same physical representation, with fresh bound
names when needed. They have no child eclass or group premise; shape operations
use the identity group for these columns. Every encoded fact then denotes an
ordinary proposition, and every maintenance rule firing has a fixed derivation.
The helper in [`proofs/coordinates.rs`](proofs/coordinates.rs) retains the encoded
edge coordinates needed by later reconstruction. Restating an edge in different
coordinates reuses the same ordinary proof; transporting its endpoints emits
Equivariance:

| encoded fact | proposition |
| --- | --- |
| egglog equality `a = b` | `dec(a) = dec(b)` |
| `RenamesToLeader a m b`, `Equated a m b`, `ShapeEqual a m b` | `dec(a) = rename(m̂, dec(b))` |
| `g` in `EclassGroup c`, `Reading c _ g` | `dec(c) = rename(ĝ, dec(c))` |
| `Invocation c n a` | `dec(a) = rename(n̂, dec(c))` |
| slot `r` of `c` outside `FreeVars c` | `dec(c) = rename(swap(r, r'), dec(c))` for fresh `r'` |

The last row is a *redundancy certificate*. It is derived on demand from the
derivation of the `FreeVars` row: the merge chain of intersections says which
`set` dropped the slot, and transport along an edge and group slot closure each
have a short Sym/Equivariance/Trans derivation.

`group-shrink` computes `group-close(group-restrict old-group slots)` and stages
it in `GroupReplace`; `group-restore` publishes the result. To prove a restricted
group element, slot lifting replays the runtime's closure and composes the
corresponding proofs for the original generators. The full equality
retains any action on redundant slots and must agree with the requested symmetry
on the surviving slots. `EclassGroup` merges use `set-union`, so each generator
keeps the proof from its contributing side. `GroupReplace` merges select `new`.
Omitted slots have separate redundancy certificates through the same derivation;
the completed permutation may still act on them. Invocation merges use those
certificates to reconcile the two completions of their shared partial name.

| rule firing | derivation |
| --- | --- |
| orient, restate on narrower slots | Change edge coordinates; use certificates for slots the restriction dropped |
| self-equation, self-edge into the group | the premise, respelled |
| group shrink and restore | compose the original symmetry proofs for a product on the surviving slots |
| transitivity | Trans of the first edge with the second |
| one leader per follower | Sym, Trans, Equivariance |
| migration | Sym of the edge, Equivariance by the total extension `R` |
| child update | Equivariance into the parent's names, then Congr with the child's edge |
| binder scope | Reframe the edge away from the bound slot; transport equality when needed |
| shape collision, node symmetries | Congr with transported child symmetries, then align edge coordinates |
| invocation naming | compose the edge with the symmetry `coset-min` chose |
| invocation merge | reconcile completions using support certificates, then Sym and Trans |
| user rewrite | Rule, with premises built from the atom rows by Congr and Equivariance |
| claim | the two terms' atom proofs, the class equality, and the `coset-same` symmetry |

# Running

The end-to-end demo snapshots show the source alongside its lifted, checked
proof: [a rewrite](../../tests/snapshots/slotted_proofs__demo_rewrite.snap),
[a nested rewrite with original conditions](../../tests/snapshots/slotted_proofs__demo_nested_conditions.snap),
[a renaming equality guard](../../tests/snapshots/slotted_proofs__demo_renaming_guard.snap),
[bound-slot renaming](../../tests/snapshots/slotted_proofs__demo_alpha_renaming.snap),
[scoped Alpha](../../tests/snapshots/slotted_proofs__demo_scoped_alpha.snap),
[congruence through a binder](../../tests/snapshots/slotted_proofs__demo_binder_congruence.snap),
[a redundant slot](../../tests/snapshots/slotted_proofs__demo_redundant_slot.snap),
and [fresh names avoiding source and rule variables](../../tests/snapshots/slotted_proofs__demo_fresh_names.snap).
They run with `make check` or
`cargo test -p egglog-experimental --test slotted_proofs demo_proof_snapshots`.

`egglog-experimental --slotted --proofs source.egg` prints proofs for checks
containing positive `=`, `renaming-=`, and constructor-existence facts. These may
use term and payload pattern variables, constructors, globals, and slots. All
facts in one check share a matched witness. Negation and other predicates use
ordinary checks. Extraction returns a source term without a proof. Substitution
is not supported in proof mode.

To replay lowered code, use
`egglog-experimental --slotted-encoded --proofs --slotted-source source.egg encoded.egg`.
The original source and matching mode must match the compilation that produced
the lowered commands. Include `--slotted-no-aliasing` if it was used for compilation.
From Rust, use `Compiler::compile_program` with
`Options { proof_mode: ProofMode::Prove, ..Default::default() }`, then call
`CompiledProgram::run` on `new_egraph_with_proofs()`. `run_encoded` checks replayed
commands against the same retained source programs. Serialized commands contain
proof request IDs; they do not contain their checking programs.
`cargo test --locked -p egglog-experimental --test slotted_proof_files` runs the
supported source corpus and frozen benchmark inputs through the Rust API.
For frozen differential fixtures it also observes equivalent probe pairs in an
ordinary execution and checks a source proof for every probe. Nested fixtures
use the no-aliasing matcher. These tests run in the normal workspace suite and
`make check`; they use committed inputs without Python orchestration or live
fixture generation.
Substitution fixtures are excluded from this proof suite.
`--slotted-proof-checks` runs the proof-compatible encoding with ordinary checks
for comparison.

The CLI accepts compiled inputs through egglog's `CliProgram` interface.
The core crate has no slotted commands, claim types, proof state, or CLI flags.
