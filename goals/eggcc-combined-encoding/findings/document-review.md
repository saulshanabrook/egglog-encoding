# Independent document review

Reviewed the current goal/facts, explanation, reference and reproduction guide against the compact `consumer/oracle-final` checkpoint, witness rows, consumer outcomes and oracle rows. This was a read-only claim and comprehension review for collaborators who know egglog. No source review, build, test, experiment or official-gate verification was performed by this reviewer; those remain with the semantic and harness owners.

**Disposition: no blocking document finding.** The documents support the bounded richer-integration claim and keep official final gates explicitly pending. No acceptance conclusion is inferred from pending gates.

## Claim and comprehension checks

- `report.md:9-28` connects the existing `Function` expectation and `Arg`/body actual type to the real mismatch consumer. The internal malformed function is clearly distinguished from a valid source-level reproducer and from a new baseline bug.
- `report.md:32-46` gives one connected Int/Bool tag fact → pointer → inner `TCons` head → outer `TCons` tail → tuple → diagnostic path. The distinction between constructor-tag axioms and injectivity is explicit. The two-field constructor law uses a disjunction for disequality propagation, correctly distinguishing it from the conjunction in equal-output cancellation (`reference.md:18-27`).
- `report.md:50-71` shows the existing guard and the combined consumer rule, explains the unchanged diagnostic action, and states the manual recursive alternative's equivalent result. Constructor metadata and generic query reuse are the contribution; extra detection power and required cancellation are not claimed.
- `report.md:75-89` and `reference.md:39-45` accurately distinguish annotations removal from the tag-only QueryOff consumer. The retained witnesses confirm that QueryOff still has all five generic-query witnesses in both encodings, while its nested consumer outcome is `coverage-unknown`. AnnotationsOff retains the leaf witness and loses all four composite witnesses. Off, Manual and Combined all reach the existing type mismatch diagnostic on the same malformed fixture.
- `report.md:77-79` and `reference.md:60-62` make unknown/unsupported coverage a failure and separate inconsistent tag metadata from permitted refinement. Neither feature control is presented as successful acceptance of malformed IR.
- `report.md:91-95` accurately reports the compact evidence: 50 witness observations, ten internal consumer outcomes, nine oracle cases under two encodings and three complete modes, hence 54 rows. Every oracle row records checked real producers and the expected equal/mismatch outcome; no disagreement appears. Host/CLI claims are clearly a separate valid-program pipeline control, and their reuse is attributed to the checkpoint's identical-production-closure statement rather than silently presented as fresh final-source runs.
- `report.md:99-101` and `reference.md:64-66` preserve the finite normalized free-type boundary, explicitly avoid new-bug/optimization/speedup claims and leave other candidates as leads.

## Document roles

The Diátaxis separation works. `report.md` follows the compiler obligation, inference, comparison and interpretation without reproduction commands. `reference.md` gives the grammar, laws, modes, scheduling/boundary contract and evidence identities. `reproduction.md` owns environment setup, executable commands, output assertions and retained tooling failures. The short evidence summary in the explanation helps interpret the result and does not displace the connected example with an experiment ledger.

The pending-gate statements at `report.md:3`, `reference.md:3` and `reproduction.md:3` agree with the checkpoint status. They are deliberate provisional status, not a stale-placeholder finding in this review.

One bounded, nonblocking clarity improvement would help standalone readers: expand **NEE** and **EE** at their first occurrence (`report.md:91`, repeated in `reproduction.md:40`) or link those labels to their existing definition. The explanation identifies them as two assertion encodings but assumes the reader already knows the project-specific labels. No inference, claim or acceptance change is needed for that clarification.

## Reviewed identities

SHA-256 values bind the exact reviewed text and compact evidence. Raw evidence paths are relative to `benchmarks/local/eggcc-combined-encoding/`.

| File | SHA-256 |
| --- | --- |
| `goal.md` | `d81ef4424abb61086097f532f56bfa95fc983f4e41f5d875555c3b231eff893d` |
| `facts.md` | `3dc28ac857ae943453bf257e208ae0df1746fe5461ace6b1fdf55d31cdec8c93` |
| `report.md` | `431d0054b1b0691e830823f2d21a6fa45396cb68b3eeddead44e88b9df2917db` |
| `reference.md` | `49efb82d4fdc586970f7438d55f1e1b7f6a74bfb3516188be6c20cda7e93b6c6` |
| `reproduction.md` | `e8df4b9e32284d9a02b5205dbb3281d450631274fb21632a68e33b717785e8ed` |
| `consumer/oracle-final/checkpoint.json` | `227599b8ac493ecb60b012191d8d56b7ae90e602ad721992f8c00c8ec2a6b985` |
| `consumer/oracle-final/witnesses.json` | `180b80c7a11cf1698b16f3fd427ed26c80e347030bbd47f74d5025bcad5bfb55` |
| `consumer/oracle-final/consumer-outcomes.json` | `86fc68d77320a985d01e6cffda75becdadd29ac55cee1cb6f829520d6024c39d` |
| `consumer/oracle-final/oracle-results.json` | `df81c8775c45ef817c258c93d4e233eb25aa0d7ca0c183cf88dc0df63edf1c7d` |
