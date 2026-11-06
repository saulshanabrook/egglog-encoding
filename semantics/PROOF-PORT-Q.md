# Task Q: unified proof language port

## Status

The initial focused build reproduced the broken subsume cases and the removed
relational checker dependencies. The launcher requires
`source /tmp/proof-port-env.sh` in this environment. The port is complete:
the full library, paper, and differential executable build succeeds, every paper
`assert_no_sorry` passes, and both differential gates pass.

## Statement changes

All names below are under `Egglog`.

- `SourceProof.premiseMatches_sound` and
  `SourceProof.premiseMatches_lookup_subterm` now require
  `p.monotoneB = true`.
- `SourceProof.premisesMatch_sound` and `SourceProof.premisesMatch_values` now
  require `∀ p ∈ q, p.monotoneB = true`.
- `SourceProof.ruleFacts_supported` derives these hypotheses from the source fragment; its
  statement is unchanged. It handles the added `disequalitiesSupported` conjunct.
- `SourceProof.actionFacts_sound` and `SourceProof.actionsFacts_sound` keep their
  statements. The subsume case produces no claims. A private
  `SourceProof.evalActions_retained` helper proves containment even for subsumes,
  which retain equations while marking rows, so previous claims remain true.
- `Resugar.lift_checked`, `lift_check_claim`, `lift_supported`, `lift_sound`, and
  `lift_infers` explicitly use `SourceProof.Proof` for their input parameter in
  place of `Provenance.Proof`; their other assumptions and conclusions are unchanged.
- Through the existing `Provenance` export, the unchanged spelling `Proof` now
  means `SourceProof.Proof` in `Provenance.extractEach_checked`,
  `Provenance.Generated.check_claim_infers`, `check_uf_infers`, and
  `check_term_infers`. `Provenance.extract_checked` likewise uses the existing
  `Facts` alias with unified proofs. No hypotheses or conclusions were changed.
- `SourceProof.check_supported` and `Resugar.lift_check_claim` now unfold
  `checkIn` as well as `check`; the theorem statements otherwise stay the same.
- All five certificate theorem names asserted in `EgglogPaper.lean` are retained
  with the required statements. The generated claim/soundness modules require no
  textual edits because the exported proof type already resolves correctly.

## Deletions

- `SourceProof.actionFacts_subsumeFree` and
  `SourceProof.actionsFacts_subsumeFree`: successful evaluation no longer implies
  the absence of subsumes.
- `Proofs/Provenance/Model.lean`: `Provenance.Model` (and its fields), private
  `option_true`, `checkNode_sound_in_model`, `valid_sound_in_model`,
  `allValid_sound_in_model`, and `check_sound_in_model`.
- `Proofs/Provenance/GeneratedEvaluation.lean`: under `Provenance.Generated`,
  `actionFacts_sound`, `actionsFacts_sound`, `supported_sound`,
  `premiseMatches_sound`, `premisesMatch_sound`, and `actionsFacts_unionFree`.
- `Proofs/Provenance/Facts.lean`: the `Provenance` exports of the four generated
  action/matching soundness theorems.
- `Provenance.extract_sound`, which required the removed abstract `Model`.
- The three deleted module imports from `EgglogSemantics.lean`, and the `Model`
  import from provenance soundness. No equivalent abstract compiled-checker
  soundness theorem is claimed; source inference goes through checked lifting.
  The removal of the separate `Provenance.Format` import was already present
  before this task; the only task edits to the umbrella module remove the three
  obsolete proof imports.

## Semantic findings

- The removed subsume-free lemmas are false with the new evaluator: an evaluable
  subsume returns `some []`.
- Syntactic disequality does not imply absence of semantic congruence. The old
  unrestricted matching soundness statements therefore cannot be preserved.
- A disequality's right-side variables need not occur in its left reflexive
  claim, so the unrestricted lookup/substitution-support lemmas also fail.
  The added monotonicity hypotheses exclude these cases and follow from
  `sourceOk`; they do not strengthen the paper's assumptions.
- Subsumption does not invalidate the action soundness statements: stored
  equations persist even when rows become unavailable to queries.

## Validation

- Focused build: PASS (`SourceProof.Soundness`, `Provenance.Soundness`,
  `Provenance.Counterexamples`, and `Resugar.Soundness`, under `Proofs`).
- `lake build EgglogSemantics EgglogPaper difftest`: PASS (1821 jobs).
  This includes the previously failing proof modules and all `assert_no_sorry`
  commands in the unchanged `EgglogPaper.lean`. Build log:
  `/tmp/proof-port-q-build.log`.
- After that build, `.lake/build/bin/difftest provenance 64`: PASS,
  **104 tested, 0 failures, 0 outside domain**. Log:
  `/tmp/proof-port-q-provenance.log`.
- After that build, `.lake/build/bin/difftest resugar 64`: PASS,
  **104 tested, 0 failures, 0 outside domain**. Log:
  `/tmp/proof-port-q-resugar.log`.
- `git diff --check`: PASS.
- No `sorry`, `axiom`, `native_decide`, or heartbeat overrides were added.
  Existing style warnings elsewhere in the build remain; edited proof modules
  produce no new warnings.

No network commands or `make check` are used. Edits are restricted to
the assigned proof modules, import removals, and this notes file. Pre-existing
implementation, test, paper, and script changes are left intact.
