# Certificate proof port B

Completed the scoped port against the declaration-free specification. Existing
changes outside this scope predate the task, except for the individually copied
session A dependencies listed below. Validation uses the supplied launcher shim
and `lake build`; no root Makefile targets or network operations were run.

## Building

All **18 retained scoped modules** build:

- `Proofs/SourceProof/{Actions,Support,Ledger,Matching,Rules,Soundness,Counterexamples}`.
- `Proofs/Provenance/{Model,GeneratedEvaluation,Facts,Soundness,GeneratedClaim,
  GeneratedSoundness,Counterexamples}`.
- `Proofs/Resugar/Soundness`.
- `Tests/{SourceProof,SourceProofCorrectness,ProofPass}`.

`SourceProof.check_infers` establishes an accepted claim in a reached saturated
source model. `Provenance.extract_checked` checks every extracted relational
certificate against its associated term. `Resugar.extractAll_checked` and
`extractAll_infers` compose checked lifting with source soundness;
`certificates_checked` / `certificates_infers` also cover the public execution wrapper.

`Tests/ProofPass` executes the actual instrumented compilation with
`Relational.execProgram`, extracts four checked source proofs, finds the nontrivial
source union among their claims, and rejects extraction after erasing the firing
log. It proves the concrete source state is reached and saturated, then applies
`extractAll_infers` to every proof returned by that run. The nonempty extraction
and its contents are executable `#guard` regressions; the general and instantiated
soundness implications are kernel-checked theorems.

`Tests/SourceProofCorrectness` proves a concrete nonempty-query certificate
accepted by the checker, proves its source execution and saturation, and derives
both inferred and stored equality. `Tests/SourceProof` preserves malformed-proof,
missing-premise, substitution, congruence, nested-query and premise-order checks;
globals now use empty-query rules and runs, with adjusted command indices.
It additionally rejects source deletes, disequalities and inconsistent arities.

## Deleted

- `Proofs/Provenance/DistinctMerge.lean`: merge functions and merge provenance are gone.
- `Proofs/Provenance/Countermodel.lean`: self-merge rejection concerns removed certificates.
- `Proofs/Provenance/GeneratedContext.lean`: generated signatures and checker contexts are gone.
- `Proofs/Provenance/GeneratedMerges.lean`: generated merge bodies and live tables are gone.
- `Proofs/Provenance/GeneratedRules.lean`: the old live-table runtime and rule encoding are gone.
- `Proofs/Provenance/GeneratedWorld.lean`: the old live-table world and encoded signature are gone.
- `Tests/GeneratedProvenance.lean`: old merge/proof-column fixtures; log tests replace them in `ProofPass`.
- `Proofs/SourceProof/Context.lean`: its sole subject was the removed signature-collecting context.

`git rm` was attempted but cannot create the index lock in the read-only main
checkout's `.git/worktrees/extended-proofs2-port-B`. Files were removed from the
working tree instead. Staging these deletions remains an integration step; no
write to the main checkout or its Git metadata was attempted beyond `git rm`.

Generic provenance `Model`, `GeneratedEvaluation`, and `Facts` are retained for
their surviving rule/subterm and action/matching theorems. `GeneratedClaim` and
`GeneratedSoundness` are reduced to source-inference corollaries of checked lifting;
the old entry/world/signature/merge portions are removed.

## Copied from A

Exactly these **18 files** were copied from
`/home/oflatt/work/extended-proofs2-port-A/semantics/EgglogSemantics/Proofs/`:

`Syntax`, `Term`, `StoredCong`, `Database`, `Congruence`, `SemanticCong`, `Eval`,
`Operands`, `SameMeaning`, `Match`, `Query`, `Writes`, `SourceMeaning`, `EnvTransform`,
`Completion`, `Step`, `SourceModel`, `RuleStore`.

All build locally and were byte-identical to A at the final comparison. None was
edited here. Temporary dependency errors were resolved only by refreshing A's
files: `SourceMeaning:220` (in-progress syntax), `Step:153` (argument names), and
`SourceModel:86` (the saturation induction's database binder).

## Statement changes

- `SourceProof.check_supported`, `check_infers`, and `check_sound` **retain their
  premises and conclusions**: reached execution, `db.WF`, saturation for every
  ruleset, and successful `check P`; `check_sound` still requires held endpoints
  and concludes `StoredCong`. `check_infers` handles unstored congruent spellings.
  The meanings of `WF`, saturation and evaluation are those of the revised spec.
- `checkNode_supported`, `valid_supported`, `allValid_supported`, and
  `ruleFacts_supported` drop the removed context and context-soundness premises.
  Rule facts refer to `ruleFacts r σ premises`. Rule delete-freedom is derived from
  `sourceOk` / `Fragment.monotone` and preservation of the registered rule store;
  no additional external premise is needed.
- `sourceOk_ctors`, `valueOk_isValue`, and `valuesOk_isValue` are removed because
  constructor declarations and typed value checks no longer exist.
- Source `actionFacts_sound` / `actionsFacts_sound` take an explicit substitution
  rather than database signature/environment fields. Accepted source action facts
  imply delete-freedom (new helper lemmas), so sequence soundness has no new premise.
  `Claim.Holds`, support/completion and their surviving theorems are unchanged.
- `ledger`, `ledger_contained_completion`, `ledger_wf`, and `ledger_holds` drop the
  signature parameter. `ledger_sig` and `ledger_env` disappear with those fields.
- Source `premiseMatches_sound` and `premisesMatch_sound` drop signatures and reject
  `ne` by the checker definition. `querySubst_of_matches` uses held terms instead
  of typed values. `supportedValue_sound` is unchanged.
- `Provenance.Model` and its soundness theorems drop signature, atom-validity, and
  merge clauses, retaining rule-fact closure and subterm closure.
  `checkNode_sound_in_model` consumes the surviving `checkReason` predicate.
  `check_sound_and_atom_in_model` is subsumed by `check_sound_in_model`: there is
  no atom-validity check anymore.
- Relational single-action soundness takes an explicit substitution and covers
  deletes. Relational `actionsFacts_sound` adds `Actions.DeleteFree`: a later delete
  could otherwise remove an earlier fact. `actionsFacts_unionFree` drops signatures
  and includes deletes, which do not perform unions.
- Relational `premiseMatches_sound` / `premisesMatch_sound` cover `ne`, take support
  of the complete premise list, and require diagonal congruence
  (`∀ a b, Cong db a b → a = b`). Structural inequality alone would not imply
  semantic disequality in a union state. `supported_sound` is a new helper.
- `Provenance.extractRow_checked` becomes `extractEach_checked` / `extract_checked`,
  validating each returned proof against its associated term. `extract_sound`
  states their consequence for any explicit `Model P H`.
- The old unconditional generated-world `Provenance.check_sound` and
  `extractRow_sound` are replaced by the checked extraction/lifting pipeline.
  `Generated.check_claim_infers` and `check_uf_infers` now require successful
  `Resugar.lift`; `check_view_infers` also explicitly requires its `factClaim`
  mapping. They use well-formedness derived from the reached execution, and no
  longer need an explicit fragment or context parameter. Old `Fact`, generated
  `model`, `check_fact`, `Fact.value_infers`, `factClaim_infers`, and
  `entrySound_infers` disappear with the removed world/entry representation.
  This port does **not** claim that every accepted relational certificate lifts.
- `Resugar.lift_checked`, `lift_supported`, `lift_sound`, and `lift_infers` drop
  contexts; the remaining premises and conclusions are preserved.
  `extractAll_checked` / `extractAll_infers` replace entry/proof-column-based
  `extractRow_checked` / `extractRow_infers`, quantifying over every returned proof.
- `SourceProof.Counterexamples` keeps the congruent-but-unasserted spelling and
  unrelated-equality facts, removing only merge-specific setup and claims.
  `Provenance.Counterexamples` now demonstrates actual deletion: acceptance of
  a historical certificate does not assert current row membership.

## Semantic issues and blockers

No new spec/source/interpreter defect was found. Source monotonicity excludes
both disequality and deletion; general relational certificates may describe
historical rows. The relational matching and sequential-action premises above
are required by those distinctions.

No retained scoped module is failing. Root aggregators remain out of scope and
still import other unported/deleted modules. The only operational limitation is
the read-only Git index, which prevented staging the requested deletions.

## Root import changes

In `EgglogSemantics.lean`, remove these three existing direct imports:

- `EgglogSemantics.Tests.GeneratedProvenance`
- `EgglogSemantics.Proofs.Provenance.Countermodel`
- `EgglogSemantics.Proofs.Provenance.DistinctMerge`

If the root should continue exposing all retained certificate helper theorems,
add `Proofs.SourceProof.Ledger`, `Proofs.Provenance.Facts`, and
`Proofs.Provenance.GeneratedSoundness` (with the `EgglogSemantics.` prefix).
Their old indirect import paths changed with the redesign. All other deleted
modules had no direct import in either root aggregator. `EgglogPaper.lean` needs
no import change for this scope. Neither root file was edited.

## Validation

- Aggregate target list: `/tmp/proof-port-b-targets` (all 18 scoped modules).
- Aggregate build: `/tmp/proof-port-b-final.log`, successful (761 jobs).
- Main-theorem axiom audit: `/tmp/proof-port-b-audit.lean` and
  `/tmp/proof-port-b-audit.log`; all 26 theorems depend only on the standard
  `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or added axiom.
- No `sorry`, `axiom`, `native_decide`, or heartbeat increase in scoped files.
- Scoped `git diff --check` passes.
