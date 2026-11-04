# Independent frozen-v2 observation evidence audit

**Consent to the first debug checkpoint's stated correctness/query-coverage claims; no blocking discrepancy found.** The retained evidence supports the seven source expectations, 37 CLI classifications, same-point MAX detector conflict, successful live/dead controls, before-seed unsupported rejection, matched seed construction and four initialized old/E1 replays. This is not a final release, corrected-source specificity, cost-admission or full-gate result. The distinct-point query-negative remains pending, as the checkpoint states.

I used only frozen artifacts, not the authorized changing compiler tree. No compiler/engine call, build, project import, project test or workload ran. Small standard-library scripts read/hash files, parse retained JSON/term text and independently check mathematical values and artifact consistency. Only this review file was written. This audit does not duplicate or upgrade the earlier six baseline bug reproductions.

## Identity and independent checks

All **587** files named in the review manifest's frozen-file map matched their recorded hashes at both audit reads. Frozen debug compiler SHA-256 is `8e8d8eb9e5ffcf8653d1e49f19540940458cd6e7c89f3d92b3f7c2851cad1488`; sibling Tiger is `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`. Every CLI row agrees with its command receipt, frozen input copy/hash, binary/Tiger identity, recorded exit and no-timeout status. The authoritative copied E1 five-file manifest, complete patch and final gate checkpoint agree; the four-file development engine diff is not treated as complete E1 source authority.

Bound artifact hashes:

| Artifact, relative to raw `compiler/observations/` | SHA-256 |
| --- | --- |
| `review-checkpoint/manifest.json` | `0755666072a36736a6ed43874cf67005327e20e0117362140c98e50197e8ccb2` |
| `review-checkpoint/diagnostics.json` | `11714afc96c7fe425323f5d15fa8622ca482d803132695bc066e49b2027d58af` |
| `review-checkpoint/summary.md` | `e10d62898d663a0a76e88745e5fb0c1c0ef8cc5883a234578ad78f8ea44a7824` |
| `development-v2/results.json` | `bc7f6a77b4415e69f21d6685bf2bd4a342215d8a800cd4be9e042d71c9f29424` |
| `initialized-replay/results.json` | `5e119bb8967fbc26d42e6465fa8cf89da564a740ad1372dc094badda607af036` |

## Expectations derived from actual frozen fixtures

I read the seven `runs/*-original/input.bril` copies. Each run's copied input hash matches its result/command provenance. MAX multiplication uses signed i64 wrap: `(2 * (2^63-1)) mod 2^64` represents **−2**, so `product < 0` is true. The small positive input produces 2 and false; zero/negative inputs never execute the positive branch. The contradictory fixture's x=1 takes the outer-positive and inner-nonnegative path, printing `1 < 2`; its multiplication branch is dead. Division is by nonzero two: x=−2 produces −1 and true, but is deliberately outside observer grammar.

| Case | Source output | Designated first-pass product-sign observations | Expected optimizer/observer outcome |
| --- | --- | --- | --- |
| MAX | `true\n` | 1, true | Off/CommonSeed complete with wrong `false\n`; Manual/Injective reject |
| one | `false\n` | 1, false | all four modes complete correctly |
| zero | empty string | 0 | all modes complete correctly |
| negative (−1) | empty string | 0 | all modes complete correctly |
| contradictory | `true\n` | 0 | all modes complete correctly; dead multiplication unobserved |
| unsupported-dead (1) | `true\n` | 0 | all modes complete correctly; Div arm unvisited |
| unsupported-live (−2) | `true\n` | no seeds permitted | Off completes correctly; all enabled modes reject domain before seeding |

All seven parse/interpreter invocations return exit 0 and non-null original/result strings equal to these independently derived expectations. Empty output is an actual string, not a null/missing interpretation.

## Actual CLI and detector evidence

The 37 command receipts independently classify as **7 source oracles, 24 complete optimization invocations, 3 expected observer rejections and 3 expected domain rejections**. No invocation timed out. The optimizer commands retain context/optimize/interp, explicit run-data/egraph outputs and the selected mode; the two query probes are separately flagged diagnostic invocations.

All 24 complete optimization invocations have non-null original/result fields, passes 0/1/2 in stderr, three native-input egraph snapshots and at least three reconstruction-schedule completion records. Enabled successes additionally have accepted audit and serialization-entry receipts for every pass. Outputs match the table, including the intentionally wrong MAX Off/CommonSeed result. This is evidence from the normal native pipeline, not an encoding-only replay. It does not convert those wrong-output runs into correctness passes.

MAX CommonSeed/Manual/Injective and the separate Injective-probe run all retain the same conflict **`(ObservationConflict 5 2 1 true false)`**. I checked its actual seed records and expressions, not merely its count:

- Point 1 has parent 0, selected branch true, argument type `TupleT([StateT, IntT, IntT, IntT])` and actual argument **`[StateV, 0, MAX, 2]`**.
- Seed 5 is the reached branch-local `LessThan(Mul(arg[2],arg[3]),arg[1])`, independently evaluating to true under that argument.
- Seed 2 is the same-context/type false literal at the **same point**, with false payload.

Manual and Injective exit 101 with their respective exact runtime error tails: manual conflicting feasible Bool observations versus `ObservedBool` unequal primitive argument 0. Both have `accepted:false` at `pre-serialization-observation-audit`, committed witness evidence, no serialization-entry file, no Tiger-input egraph snapshot, no later pass/reconstruction log and no normal run-data. The separate MAX probe has the same later detector rejection. These are actual observer failures at the intended boundary, not unsupported grammar, a parse error, the pre-pass query aborting, or an earlier existing-Const guard.

CommonSeed retains that exact conflict but accepts its empty audit, enters serialization and completes all three passes with source true/optimized false. Thus the additional literal/seed graph does not turn this example into an earlier top-level guard failure or eliminate the bad output. This supports the claimed extension in detector coverage, with the direct manual control's equivalent power explicitly retained.

Selected Div produces `domain-error.json` at `before-seeding`, with **zero emitted observation seeds** and the unsupported reachable binary-operator error in all three enabled modes. There is no observations/initialization receipt, egraph or normal run-data for those failures. They are domain exclusions, not semantic detector successes. Dead Div instead completes correctly.

## Seeds, region inputs and dead coverage independently reconstructed

I recomputed all **32** applicable CommonSeed-versus-Manual/Injective case/pass comparisons directly from frozen observations, initialization and source-schedule files. Points, actual region inputs, contexts, seed IDs/Expr terms/values, skipped records and counts match. Raw initialization bytes match after removing **only the exact one ObservedBool injectivity annotation** in Injective mode; raw source schedules match exactly. This verifies graph-input equivalence within the declared annotation difference rather than trusting `matched_seeds` booleans.

Across **54** retained pass observation records, I parsed the closed seed terms and independently evaluated **99 original pure Bool observations plus 198 literal seeds** using a small mathematical evaluator for the retained Arg/Const/Get/tuple/Mul/LessThan/Bool grammar. All 297 values agree. Leaf argument types/contexts match their point, literal type layouts match actual concrete point values, and 45 observed non-root point links independently satisfy their parent's If predicate and evaluated input transport. Every retained logical seed has the corresponding exact raw ObservationSeed action and Eval-result-only union.

For each of the three enabled modes, first-pass designated counts/values match the table. Zero/negative have two reached regions but only the root Bool observation, no product-sign seed and no Print visit; the unreachable product region supplies no record. The contradictory case has three reached regions, three pure Bool observations, one structural Print and no product-sign seed. The recorded skipped observations are zero throughout, and inspection of the actual expression seed set confirms the designated dead expressions are absent. These are host/source observation counts, not optimizer firing counts or runtime-cost measures.

## Full-host query probe and old/E1 initialized replay

The actual-host first-pass probe receipts report MAX known and fresh x=1 unknown, explicitly at `after-initialization-before-source-schedule`. Unknown is recorded normally; x=1 continues through the native pipeline. The matched old/new comparison is narrower: initialization-only replay, not an old-query compiler endpoint.

I verified each replay file is **exactly the retained actual-host initialization bytes plus its closed probe query**, with no optimizer source schedule appended. Old and E1 command receipts use the same file/argv tail, cwd, environment and timeout for that case; only executable identity changes. Frozen executable hashes match the recorded old `46f898796589e8585ecaf1499a9b9d7ee98d31fc45f64d2061c103795d62ecf2` and E1 `c5d2b867415eb5d68cb0e84898bd596c68f255238a05b433fdc4d339b0bb1d4a`.

| Replay | Input SHA-256 | Old unary | E1 |
| --- | --- | --- | --- |
| MAX | `e3cdcebb142d0f16aa7714a82b6c8e742b69e71e737d396e8e21969b820e3337` | exit 1, check unknown | exit 0, check known |
| one | `6c36f7643851b6f2ce6aeb2c4e999a352ddea731078d534ec17ff725be405608` | exit 1, check unknown | exit 1, check unknown |

All three exit-1 stderr files explicitly report **`Check failed:` for `known-disequal?`**, with no parse/type failure. MAX E1 has no ERROR entry. This supports the intended unmarked-binary coverage delta. It does not establish runtime inequality at every input or unique detector power. The otherwise witness-free distinct-point query-negative is still only prepared, not executed; accepting distinct-point audit tests does not fill that query gap.

## Scope retained

The checkpoint's conclusions are appropriately limited. The persistent invocation-directory fix, real two-rule corrected-source four-mode specificity, final release endpoint, restored-source root/DAG gates and repeated costs are not established by this audit. The known repeated-static-path collision still blocks cost admission for v2. Current frozen evidence is acceptable as the first debug full-host correctness/query checkpoint; future source/binary changes need their own bound receipts and delta review.
