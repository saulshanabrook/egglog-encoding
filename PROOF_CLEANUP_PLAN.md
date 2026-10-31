# Slotted proof cleanup plan

PR: https://github.com/saulshanabrook/egglog-encoding/pull/141

The source program is the authority for proofs. The intended result is an
understandable proof format, a small slotted checker that shares ordinary
checking with egglog, and minimal compilation metadata.

## Constraints

- Check the original slotted program, with rewrites desugared to rules and their
  original `:when` conditions in the body. Preserve nested expressions, binder
  semantics, declaration-scoped globals, sorts, and source names. Do not add
  generated matching conditions or replacement axioms to the source theory.
  Ordinary guards use egglog's proof normal form. Keep one dedicated RenamingEq
  premise for each renaming-= condition, expanding it only during checking.
- Do not change the normal proof checker's semantics. Refactoring and exposing
  existing checking code are allowed.
- Ordinary propositions are exact equalities. Equivariance applies a finite
  permutation to both endpoints of a checked equality.
- Alpha derives `a = c` from `a = b` when `b` and `c` are alpha-equivalent.
  Preserve the exact left endpoint, free names, binding scopes, constructor heads,
  payloads, and carrier sort. Require a premise establishing term existence.
- RHS-only slots are chosen by the proof. Validate freshness against all other
  bindings and captured globals; accept any fresh candidate. Do not generate
  trusted freshness facts or require a particular name.
- Keep the earlier Makefile, `supports_proofs`, and Group cleanups separate.
- Apply `.claude/skills/tidy-diff-docs/SKILL.md`; keep LANGUAGE.md focused on usage.

## Stages

1. **Establish the shared checker boundary.** Expose single-step checking without
   changing normal traversal, validation, or caching. Exercise ordinary rules
   with conditions, equivariance, Alpha, nested binders, fresh slots, captured
   globals, and multiple sorts. Report findings before changing source metadata.
2. **Retain the original program.** Keep native parsed source commands in
   execution order and preserve push/pop scope. Reconstruct flattened rules
   through the compiler's lowering. Remove source text from e-graph metadata
   tables; retain only necessary origin and generated-name mappings.
3. **Remove the parallel source representation.** Use egglog's Expr, Fact, Rule,
   and Command types and type resolution. Share constructor/binder information
   with the slotted frontend. Remove the remaining Condition/Rewrite/Rhs model.
4. **Extend the ordinary proof format.** Use an enum with `Ordinary(egglog::proof::Proof)`,
   `Rule(RuleProof)`, `Alpha`, and `Equivariance`. Rule premises are typed as
   `Equality(ProofId)` or `RenamingEq { left, right }`; every stored proof states
   an ordinary equality. Reuse ordinary propositions, justifications, IDs, and
   printing. Keep claims and the store in format.rs, the checker in its own file,
   and tests in separate files.
5. **Make renaming-guard evidence explicit.** Ordinary proof premises establish
   equalities to representatives; a slotted validator checks their permutation.
   Existence alone must never establish `renaming-=`.
6. **Separate checking from lifting.** Keep encoded row names, matching frames,
   generated variables, and flattening compensation out of the checker. Use
   explicit Alpha when bound spellings change; ordinary steps stay exact.
7. **Delete superseded paths and validate.** Preserve proof snapshots, minimized
   lifting regressions, supported benchmark coverage, and default proof fuzzing.
   Cover malformed permutations, capture, nonfresh slots, incorrect sorts,
   altered guards, scoped globals, and encoded replay. Run root `make check`.

## Checker boundary: implemented

- `ProofStore::check_step` takes a premise-checking callback. Ordinary traversal
  uses it with the same premise order and success-only cache as before.
- The production slotted checker delegates Sym, Trans, Congr, and Proj to this
  API. It retains carrier and well-formedness checks locally.
- Rule applications delegate to the ordinary checker. Ordinary guards use its
  fact-normalization routine and Unit-result premises. RenamingEq expands into
  operand equalities and a validated primitive call only during checking. Source
  scopes, sorts, and RHS freshness remain local.
- Alpha is implemented in the format, checker, printer, normalizer, and lifting.
  Source axioms retain their original binder spellings. Refreshed spellings are
  derived from those axioms using Alpha and ordinary proof steps.
- Rule premises match exactly; implicit alpha matching was removed. Lifting
  supplies Alpha steps where needed, including repeated names in nested scopes.
- Claim and ClaimKind live in format.rs. Source syntax uses egglog's
  S-expression reader; structural AST conversion preserves slotted identifiers.
- Source rules now use native type resolution, as described below.

### Ordinary guard normal form: implemented and validated

The only guard-specific premise is `RenamingEq { left, right }`. Its two
ordinary equality proofs establish `a = ar` and `b = br`; the primitive validator
compares `ar` and `br` modulo alpha-equivalence and a bijection of free slots.
RenamingEq evidence cannot be used as an ordinary equality.

Other guards use egglog's existing `proof_form_fact` normalization. Constructor
operands become equality facts with ordinary proofs; the guard's result premise
is the usual `Fiat (= () ())`. Variable/literal operands stay in the primitive
call. These guards may have more than one premise per original source line,
as explicitly accepted by the user. Do not add a generic primitive proof node.

Lifting and checking share this normalization. Generated constructor bindings
are reconstructed at their source spelling from the original rule and
substitution; no generated names or new metadata are serialized in the proof.
Keep source guards subject to the ordinary normal-form restrictions, rather
than complicating the checker to accept arbitrary primitive expressions.

Only during checking, expand RenamingEq into operand equality facts and a
primitive call on fresh witness variables, then delegate the complete Rule step
to `ProofStore::check_step`. Ordinary checker semantics are unchanged. The normal
fact-normalization routine is exposed without changing its behavior.

Validators use the complete constructor binding information, including later
declarations. Captured globals cannot be overridden. Generated variables avoid
all substitution and captured names. RHS slot freshness is checked against the
original substitution before guard normalization or representative expansion.

Root `make check` passed in an isolated worktree excluding the unrelated nested
checkout. It covered 295 Python tests, the full Rust workspace (including 101
experimental unit tests and 23 proof integration tests), 43 compatible slotted
proof fixtures, 31 runtime checks, 24 generated benchmark proofs, and seven
default proof-fuzz profiles (200 cases total). New regression coverage checks
nested guard operands, missing or altered evidence, and generated-name collisions.
Snapshots show both RenamingEq and ordinary expanded guard premises.

Claude Fable's read-only review found no correctness blockers. Its premise-count
diagnostic suggestion is applied. Keep ordinary primitive-result validation in
the native checker and avoid a new abstraction for the short fresh-prefix loops.

Final `make nits` and all 28 checker unit tests passed after the diagnostic and
documentation edits. Validation logs: `/tmp/slotted-renaming-eq-check.log`,
`/tmp/slotted-renaming-eq-final-nits.log`, and
`/tmp/slotted-renaming-eq-final-tests.log`. Review:
`/tmp/slotted-renaming-eq-fable-review.txt`.

## Typed rule premises: implemented and validated

`RulePremise` distinguishes an ordinary equality ID from inline RenamingEq
operand evidence. `SlottedProof::Rule(RuleProof)` holds these typed premises;
there is no standalone RenamingEq proof variant. The store converts native
Rule steps to typed equality premises, so every stored node states an ordinary
proposition. Checking no longer needs optional equality results or dynamic
rejection of guard evidence in equality steps.

The checker expands a slotted RuleProof to an ordinary rule proof and delegates
to the native single-step checker. Lifting, normalization, dependency traversal,
and rendering use the typed premises. Normalization keeps guard operands in
source coordinates. The ordinary proof types and checker are unchanged.

Tests retain malformed guard placement and operand validation, cover cycles
through either RenamingEq operand, and verify rule interning ignores substitution
insertion order. A transported-rule regression simplifies both guard operands
while preserving their source coordinates and substitution, then rechecks the
result. Printed proof snapshots are unchanged.

Independent read-only review found no correctness blocker; its diagnostic and
normalization-test suggestions are applied. Claude Fable was attempted first,
but its CLI session limit prevented this review. The fallback review is recorded
in `/tmp/slotted-typed-premises-review.txt`.

Root `make check` passed in an isolated checkout excluding the unrelated nested
repository: 295 Python tests, the full Rust workspace, 43 compatible slotted
proof fixtures, 31 runtime checks, 24 benchmark proof runs, and seven proof-fuzz
profiles (200 cases). After the review follow-ups, `make nits`, all 105
experimental unit tests, and all 23 proof integration tests passed. Snapshots
remain unchanged. Validation logs: `/tmp/slotted-typed-premises-check.log` and
`/tmp/slotted-typed-premises-final-checks.log`.

## Source cleanup: implemented

- Retain native source declaration, let, union, and rewrite commands through
  structural `slotted-source` records. No rule strings or flattened-rule JSON
  remain in e-graph tables. Source recording follows execution and push/pop scope.
- Reconstruct flattened native rewrites and generated names through the same
  compiler lowering used for encoding. Claims carry native expressions.
- Replay declarations incrementally so later carriers cannot change an earlier
  bare-slot union's sort or rule resolution. Share the frontend's constructor and
  binder model.
- Replace Condition/Rewrite/Rhs with native resolved Facts, union Actions, and
  Rules. A source rule retains only its native rule and captured globals.
- Resolve through egglog's typechecker with typed initial bindings for globals
  and RHS-only slots. Type inference receives the expected carrier/Unit context
  for plain facts; temporary constraints are removed before storing the rule.
- Preserve the slotted frontend's identifiers, including `_`, keyword-like
  variables, and `$`-prefixed payload variables. Resolve payload locals and
  captured globals separately when their spellings overlap.
- RenamingEq groups its two operand equality proofs. Other guards use ordinary
  normalized premises. The ordinary checker invokes their primitive validators.
- The format, claims, and witnesses are in format.rs; checking is in checker.rs.
  Encoded names and flattening compensation stay in lifting. Ordinary checker
  semantics remain unchanged.
- Production tests cover the former checker-adapter prototype; the duplicate
  test-only checker has been removed. LANGUAGE.md remains a usage reference.

## Previous-stage validation

The seven checker-adapter integration tests pass, including Alpha composed with
ordinary steps, malformed Alpha, equivariance, original `:when`, guards, and
captured globals. The production slotted corpus passes all 43 compatible files;
11 `subst` fixtures remain explicitly unsupported.

Independent read-only review found no semantic change in ordinary checking.
It caught a sort-name regression in the adapter, which is fixed and covered by
an end-to-end test. No soundness blocker remains in the reviewed checker boundary.

Root `make check` passed in an isolated worktree containing these changes, excluding
the unrelated nested checkout from Python discovery. Coverage includes 295 Python
tests, the full Rust workspace, 40 production proof unit tests, seven adapter
tests, the compatible slotted corpus, 31 runtime checks, 24 generated benchmark
proof runs, and all seven default proof-fuzz profiles (200 cases total). The final
sort-name regression also asserts that a proof is actually produced.

Validation logs: `/tmp/slotted-production-alpha-final-check.log` and
`/tmp/slotted-production-alpha-final-regression.log`.

## Source-cleanup validation

Root `make check` passed in an
isolated worktree matching the working files, excluding the unrelated nested
checkout from Python discovery. It covered formatting, linting, types, doc links,
295 Python tests, the full Rust workspace, all 23 production proof integration
tests, 43 compatible slotted proof fixtures, 31 runtime checks, 24 generated
benchmark proof runs, and all seven default proof-fuzz profiles (200 cases total).
Unsupported `subst` fixtures and incompatible no-aliasing benchmarks remain
explicit skips.

Regression coverage includes parsed/printed replay, original guards, declaration
scope, native variable names, constructor/guard name collisions, and attempts to
override captured globals. The full run caught a malformed `:when` diagnostic
regression; restoring the frontend's existing option validation fixed it.
Independent review found no remaining blocker in the source/checker boundary.

Validation log: `/tmp/slotted-native-proof-final-check.log`.

## Format correction: implemented and validated

The earlier completion report overstated format reuse: checking was shared, but
ordinary proof variants were still duplicated. That stage introduced an enum
wrapping the original `Proof`, with Alpha and Equivariance. The subsequent guard
node stage adds RenamingEq without introducing a separate equality type.

- Reuse `Proposition`, `ProofId`, ordinary justifications, dependency traversal,
  and printing. Ordinary checker semantics remain unchanged.
- Remove `SlottedPremise`; validate renaming guards using ordinary equality
  evidence and structural slot correspondence.
- Name the encoding pass `lift_slots`, retain `unflatten`, and name their shared
  coordinate bookkeeping `coordinates`. Proof lifting names the whole pipeline.
- Keep proof-module tests in separate files.

Root `make check` passed on this representation: 295 Python tests, the full Rust
workspace, 23 proof integration tests, 43 compatible source fixtures, 31 runtime
checks, 24 generated benchmark proofs, and seven proof-fuzz profiles (200 cases).
The isolated validation worktree matches the working files and excludes the
unrelated nested checkout from Python discovery.

Claude Fable reviewed the diff through the installed CLI and found no correctness
blocker. Its recommendations are applied: check all premise references before
dispatch, reject unsupported primitive guards, remove redundant helper and map
layers, and use consistent module visibility and test-file placement. New
checker-level cases cover binder scope and non-injective renaming guards. The
final `make nits slotted-proof-tests` run passed, as did all 95 experimental unit
tests and 23 proof integration tests after these refinements.

Validation logs: `/tmp/slotted-proof-wrapper-final-check.log`,
`/tmp/slotted-proof-wrapper-review-check.log`, and
`/tmp/slotted-proof-wrapper-review-unit.log`. Review:
`/tmp/slotted-proof-wrapper-fable-review.txt`.

`MalformedStep` now exposes structured error variants. Its regression checks
that invalid step construction reports the conflicting inputs without changing
the store. Root `make check` passed again, including all 96 experimental unit
tests. Validation log: `/tmp/slotted-malformed-step-check.log`.


## Rigid Var names

The source language uses a built-in rigid `Var` sort and requires one unary
variable constructor per equality sort, as requested. Terms use explicit
applications such as `(V $a)`; binders hold `Var` names directly. Equalities
between variable applications cannot equate names or cross carrier sorts.

The implementation covers declarations, matching, maintenance, substitution,
extraction, export, proof lifting, fixtures, generators, and documentation.
Proof claims and checker results carry no sort annotation; the checker returns
egglog's `Proposition` and verifies endpoint signatures. Ordinary checker
semantics remain unchanged. `subst` retains its existing proof restriction.

Regression tests cover cross-carrier equality, rigid binder fields after support
loss, concrete globals and fresh names, substitution capture avoidance, and
invalid declarations and layouts. Tests remain in separate files.

Claude Fable found no correctness blockers. Its cleanup suggestions removed
dead checks and redundant state, improved declaration diagnostics, and clarified
concrete global binders. The literal-name filter remains because the direct
source API also accepts ordinary Var locals, which may alias.

Root `make check` passed in an isolated checkout: 298 Python tests, the full
Rust workspace, 108 experimental unit tests, 23 proof integration tests, four
rigid-Var regressions, 43 compatible slotted fixtures, 31 runtime/differential
checks, 24 generated benchmark proofs, and all seven default proof-fuzz profiles.
The original reference goal root is preserved when tests insert a variable seed;
a regression covers that ordering. `subst` and incompatible no-aliasing workloads
retain their explicit skips.

Validation: `/tmp/var-sort-check-complete.log`. Review:
`/tmp/var-sort-fable-review.txt`.
