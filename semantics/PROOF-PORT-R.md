# Task R: premise-matching proof port

## Scope and approach

The proof port is confined to `EgglogSemantics/Proofs/SourceProof/Matching.lean`
and this notes file. The existing draft of the matching proof port was reviewed
and validated; no further Lean changes were required. Pre-existing changes
outside this scope are left untouched.

The inlined checker consumes no claim for disequalities. The existing monotonicity
hypotheses exclude those patterns in these source proofs. A private
`premisesMatch_cons` lemma decomposes a successful monotone query head into one
claim, a successful singleton match, and a successful tail match. Both list
proofs use this decomposition.

## Statement changes

- `Egglog.SourceProof.premiseMatches_sound`: the hypothesis
  `premiseMatches σ p c = true` is replaced by
  `premisesMatch σ [p] [c] = true`. All other hypotheses and the conclusion are
  unchanged.
- `Egglog.SourceProof.premiseMatches_lookup_subterm`: the same replacement of the
  matching hypothesis; all other hypotheses and the conclusion are unchanged.
- Added private helper `premisesMatch_cons`: under `p.monotoneB = true`, a
  successful match of `p :: ps` against `cs` yields `c` and `cs'` with
  `cs = c :: cs'`, `premisesMatch σ [p] [c] = true`, and
  `premisesMatch σ ps cs' = true`.

The statements of `premisesMatch_sound`, `premisesMatch_values`, and
`Egglog.SourceProof.check_infers` are unchanged. No other existing theorem
statements are changed.

## Validation

Every shell first sources `/tmp/proof-port/env.sh` as instructed. No
network-dependent commands or `make check` are used.

- Passed: `lake --no-cache build EgglogSemantics.Proofs.SourceProof.Soundness`
  (845 jobs). This rebuilt `Matching`, `Rules`, and `Soundness` successfully.
- Passed: `lake --no-cache build EgglogSemantics EgglogPaper` (1101 jobs).
  `EgglogPaper` was rebuilt, and every `assert_no_sorry` passed, including
  `Egglog.SourceProof.check_infers` and the downstream provenance/resugaring
  results.

`Rules.lean` and `Soundness.lean` need no changes. No `sorry`, `axiom`,
`native_decide`, or heartbeat-limit increases were introduced. The scoped build
and full builds reported only existing warnings in unchanged code.

## Semantic assessment

No semantic issue identified in this scope. The support argument still relies on
monotonicity: it does not claim that a disequality test supplies a premise claim
or supports its substitution values.
