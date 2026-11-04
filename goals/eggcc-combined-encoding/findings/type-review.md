# C6 source review: attempt 01

**Consent withheld pending one narrow consistency fix and its regression.** The main structural forward-disequality implementation matches the accepted finite contract. The blocker below concerns the fail-closed ablation/consistency boundary, not a newly discovered valid-source EggCC bug. This is a source review; no tests, builds, compiler workloads, project imports, or source edits were performed by this reviewer.

## Binding

Reviewed compiler: `/Users/saul/p/wt/eggcc/combined-encoding`, base `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`, new delta relative to the reconstructed final-original baseline. Frozen manifest: `benchmarks/local/eggcc-combined-encoding/consumer/attempt-01/source.json`, SHA `f062414aed6ab1164cccb0546e3e3b50c53df3e88e88169d8413b33d58aaacc6`; it names exactly nine changed files. Contract SHA: `f97fc8e07a20183d69f02051727abd49cc027092f2f5a337dd23559e81417273`.

```text
dag_in_context/src/lib.rs                    ed741bbbcc73fdadb947a3b90e2c6be780a7492e548b68ed6a068ce76c54f7cb
dag_in_context/src/structural_types.rs        3859787bd57656452e6268cb0434b86e3e76b4bf0c34bfdf075088118b7b80e2
dag_in_context/src/structural_types.egg       1fa5c0db118a3dfcafc4716a26bb36f414951ad8a6734d4db65596f469e98532
dag_in_context/src/structural_types_manual.egg 9628557850155592d35eb70c632314d627ee6d7f479c31e67435715ca4cdc408
dag_in_context/src/structural_types/tests.rs  443652ccd004321396d8d6a57551f9de3a4aed1a22c20bb7592d672c0d14ba4a
src/lib.rs                                   45c8263e3b3f9dc5552342da9679b57a80e66e22260a8768f7a9b121af845eaa
src/main.rs                                  c4236767dd0eff070f3d4f65ff3d15ca70e1b014659a5749f4ec745e8109eb39
src/structural_type_tests.rs                  e4e862e8b9161a05e9cd0d24a29a010c50fa97084d4c41c224295fdfdfc6da83
tests/encoding_combined/structural-types.bril  ac68ed9e9ae4ab19d6ffbb45675b08160aedc8284d4b9c494bfd3f9ef2d22a27
```

All nine were read at the frozen versions above. At the final source check, the eight non-DAG-test files still matched the manifest. The worker had added a new DAG regression while the focused run proceeded; the live test file then had SHA `69f557344405275203456fce6d1b367c613177087bd4aa8df631dd0fd0e9e122`. This review binds the frozen seven-test version, not that new test or a subsequent repaired snapshot. No implementation file had changed at the final check.

## Blocking source witness: collapsed tag distinction can be validated

There is no guard against a self-pair in `StructuralBaseTagDQ`, `StructuralListTagDQ`, or `StructuralTypeTagDQ`. In a QueryOff equal-ground fixture, deliberately unioning `IntT` with `BoolT` collapses the explicit leaf distinction. The root expected/actual types can remain the same TupleT value, whose pair is not a direct Base-versus-Tuple tag witness. The unchanged QueryOff consumer consequently need not derive `StructuralTypeMismatch`.

Yet [`structural_types.egg:58–59`](/Users/saul/p/wt/eggcc/combined-encoding/dag_in_context/src/structural_types.egg:58) records ground-equal coverage status 2, and [`structural_types.rs:92–115`](/Users/saul/p/wt/eggcc/combined-encoding/dag_in_context/src/structural_types.rs:92) accepts that status without checking the collapsed tag constraint. Thus the static predicted counterexample is:

```text
prepare QueryOff with expected = actual = ACTUAL
union(IntT, BoolT)
rerun preparation and the unchanged consumer
validate can report success despite the now-self tag disequality
```

This prediction was derived from source and was **not executed by this reviewer**. The worker independently acknowledged it and is preparing an explicit red regression before a narrow shared tag-self consistency guard. All three tag sorts need protection, including feature-removal modes. The guard should fail before successful validation and should remain distinct from the old raw mismatch panic; it does not change the valid fixed-input contribution comparison. Root accepted this as a blocker. The repaired guard/test delta needs a focused follow-up review.

## Source behavior otherwise consistent with the contract

- `structural_types.rs:19–37` marks only PointerT/Base/TupleT/TCons; Off and AnnotationsOff retain the original schema. Off type analysis and schedule return the exact original text. Default config is Off, and the CLI passes the selected mode to it. Ordinary scheduling and the old observer logic are preserved in the new delta.
- Shared preparation certifies finite structural ground forms, seeds the explicit tag inventory, and lowers actual `(disequal a b)` rule actions. Helpers, sentinels, and custom functions stay unmarked. Same-constructor parent mismatch is not directly seeded. Manual rules implement the same fieldwise laws; Combined uses the engine's marked forward structural search. This route exercises equality-sort propagation, not primitive payload panic, scheduled cancellation, or E1 reverse inference.
- The original ExpectType producers and panic action remain. Only its raw-ID predicate is replaced. The new `:naive` consume rule is inserted before each scheduled `error-checking` occurrence, after existing helper/type-analysis closure. This prevents the original independent guard from masking the feature probes. QueryOff consults the same-pair Type tag relation and retains the diagnostic action; it is not an action-deletion control.
- Coverage uses `(Expr, expected Type, actual Type)` keys, so an equal alternative cannot hide a different actual type. The separate `(Expr, expected Type)` presence table preserves expectations with no HasType producer. Status max permits legitimate late normalization to advance unsupported → supported → equal; host validation rejects unsupported/unknown/missing actual and zero obligations before actual graph serialization. `TmpType` has no ground rule. An equal unsupported-sentinel regression was missing in frozen attempt 01 and is among the worker's new checks.
- The primary fixture uses an actual Function and Arg, with matching input/Arg types and a second-slot Pointer(Int)/Pointer(Bool) output mismatch. It checks real ExpectType/HasType rows, then the existing diagnostic. The annotation and tag-only-query arms require absence of that mismatch plus coverage-unknown; their error-checking pass must not independently panic. The frozen tests include helper-equivalent normalization, direct cross-tag control, shape mismatches, unsupported/missing producer, late/multiple actual types and a missing-leaf-law negative. First three families cover NEE/EE; some later shape/coverage controls are NEE-only and must not be described as a full two-encoding cross-product.

The valid Bril host test exercises pointer-call source/result output `7` through the optimizer in all five modes with production non-weakly-linear configuration and a three-pass schedule. Source inspection establishes its intended setup, not actual native completion. The CLI unit test checks parsing/default selection; it is not a full CLI invocation. Live focused/host/CLI evidence and an independent finite Type oracle remain separate verification work. The implementation owner reports the original seven DAG tests passed, but their logs/results were not independently audited here.

## Narrow API question resolved without a new defect

The worker questioned whether `function_to_dag` would fail while formatting an unextractable unsupported key. Targeted current encoding source shows [`extract.rs:1009–1013`](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog/src/extract.rs:1009) substitutes `Unextractable`; output handling does likewise and returns Ok. An i64 status still determines the diagnostic. No source change is justified merely by that hypothesis. If raw status enumeration later becomes necessary, existing `EGraph::function_entries` (`egglog/src/lib.rs:1681–1689`) exposes `entry.output`, convertible with `value_to_base::<i64>`; no core API extension is required.

## Disposition

The frozen implementation is reviewable and its primary semantic path is sound under the finite free-type contract. It is not yet approved as the complete fail-closed profile because of the tag-collapse witness. Preserve attempt 01, record the actual regression separately from this static prediction, then review only the consistency guard/tests and any concrete test-driven fixes against a new checkpoint. Do not broaden the law, claim a new baseline bug, or treat this source review as evidence that the pending host/gate checks passed.

## Addendum — 2026-10-18 UTC: attempt 03 repair

**The attempt-01 blocker is closed; source consent for this bounded repaired profile.** This supersedes the earlier withholding for the tag-collapse issue only. Native-host results, broader oracle/evidence review and final gates remain separate; this addendum does not approve goal completion or any new coverage/bug/performance claim.

Frozen checkpoint: `consumer/attempt-03/source.json`, SHA `0bdc38d198668dde9ad8a7121be533a08215ad04a6320d5bf095ba38ee76a8dc`, timestamp `2026-10-18T05:09:12.510705+00:00`. All nine changed-file hashes matched the live frozen source at the review read. Only two files differ from attempt 01:

- `dag_in_context/src/structural_types.egg`: `45c211566cadf7c1505348bc9434d9fcb2ae9e467f7a203ce6c85c09d29c44ba`.
- `dag_in_context/src/structural_types/tests.rs`: `ea1b8bfb1cc50c83ccecf3697e963d0dbb5f68c9ea17908bd2f3e902742b7e7e`.

The repair adds three direct self-tag guards at `structural_types.egg:48–54`, in the already required `structural-type-consume` stage. A self-pair in the shared BaseType, TypeList or Type tag witness relation now panics with a dedicated `structural-type-inconsistent-tags` error. These guards run in all four enabled comparison modes before successful coverage validation. They do not depend on structural annotations or the query, do not restore the old raw-ID mismatch guard, and do not mask the meaningful feature ablations on their consistent fixed input.

The new test at `structural_types/tests.rs:241–272` deliberately collapses IntT/BoolT with an equal ACTUAL expectation and requires the dedicated consume-stage error in Manual, Combined, AnnotationsOff and QueryOff, under NEE and EE. This is eight mode/encoding combinations in one test. The same test separately constructs a Function/Arg whose expected and actual types are both TmpType and requires unsupported coverage in Combined under both encodings. The runtime corruption control directly covers the BaseType self-tag case; the analogous TypeList and Type guards were reviewed in source, rather than falsely counted as additional executed corruption cases.

The retained **attempt 02 red** is narrower than the original static prediction. Its command runs only `structural_type_corrupt_tag_union`, exits 101, and fails because consume returned Ok where the test expected a dedicated invariant error. The stderr shows Combined had already derived `StructuralTypeMismatch` through its query. Thus it establishes missing dedicated early invariant rejection; it does **not** demonstrate successful full compilation of a valid source or independently execute the predicted QueryOff validation escape. Attempt 03 retains that corruption setup and broadens its comparison loop from Combined to all four enabled modes. No exact-byte unchanged-test claim is made.

I inspected the actual attempt-03 command receipt, stdout and stderr: Rust 1.91.0/jobs4, release DAG-manifest `structural_type` filter, timeout 1200 seconds, exit 0. Stdout records **8 passed, 0 failed, 0 ignored, 74 filtered out**; the companion binary has zero matching tests and is not counted as extra coverage. The normalizer, nested consumer, fixed-input ablations and missing-law/producer tests remain in that successful target. I ran no commands that execute those tests myself.

Receipt hashes:

```text
attempt-02/source.json       677c1cd91ed15859afe1ec47892d925a80c25d5b6cb90194c03a72267b0ea06e
attempt-02/dag-tests.json    24bde5398ed6846f03d946c03538ba60053397dcea4169cfb32cd452709d3cb3
attempt-02/dag-tests.stdout  acd56767aa523a77a13f114c6e21534a12aea50fd312d139e5dc6bbaa37d3e69
attempt-02/dag-tests.stderr  7ea0bff6bbca85726be3e46538fd4aeb1ffe0825b90ed52bbd411384838359dc
attempt-03/dag-tests.json    a99c5eaccc0502e961a567244a304d8f7652216b944190c4d8c00023d3edf2b1
attempt-03/dag-tests.stdout  0547cf7a63b36a3d5a79856b36d270eba9fdf90ea7a1b2d6af7b67f66cc53520
attempt-03/dag-tests.stderr  f61195faa7c41f175e1282abd32a4ec6e1914665c96c8b678ab1cd677e24abb4
```

No remaining blocker was found in this narrow guard/test delta. The source contract is still the finite ground free-type profile, with mandatory normalization/consume/coverage order; this is not a guarantee for arbitrary corrupted cyclic type graphs or a new type unifier. Root's native-focused run was still separate work at this review boundary. Only this dated review addendum was written.

## Addendum — 2026-10-18 UTC: final production and fixed-case evidence

**Source and fixed-case joint-consumer consent.** Final production/test snapshot `consumer/final/source.json` SHA `3d2d6fe7fa559e15ec3fe877318389175b4a968477ebe9b0d9bf61a0a0834c98` and checkpoint SHA `cbf372014b05bcb65fec9724d20a9a1aa3e897a3ab3d0715967a473da2ad4747` were checked directly. At that read all nine live changed files matched. Relative to attempt 03, only witness-strengthening tests and rustfmt module declaration ordering changed; the three-line ordering diff in `lib.rs` changes no logic. The test file SHA was `82076381d147f84a66ed5741aea538b25c18e16566f7559ea5852046400b3191`, and final `lib.rs` SHA is `5104cb401934307b9b3ac51db4a9dd33ccbbce3e498af4edcc983a6170d76a96`.

I inspected the strengthened test source and verified that actual raw stderr JSON rows exactly equal archived `attempt-05/witnesses.json` (50 rows, SHA `180b80c7a11cf1698b16f3fd427ed26c80e347030bbd47f74d5025bcad5bfb55`) and `consumer-outcomes.json` (10 rows, SHA `86fc68d77320a985d01e6cffda75becdadd29ac55cee1cb6f829520d6024c39d`). Both encodings show this five-stage generic-query pattern, in order leaf/pointer/inner-list/outer-list/tuple:

```text
Off             unknown unknown unknown unknown unknown
Manual          known   known   known   known   known
Combined        known   known   known   known   known
AnnotationsOff  known   unknown unknown unknown unknown
QueryOff        known   known   known   known   known
```

The IntT/BoolT witness remains fixed in enabled modes. Removing annotations loses composite propagation. **QueryOff does not lose the generic graph witness**: its unchanged diagnostic consumer deliberately consults only direct Type tag evidence, so it fails to derive this nested mismatch despite the independently queryable full witness. That distinguishes query use by the actual consumer from query availability. Off/Manual/Combined reach the real fixed ExpectType panic; AnnotationsOff/QueryOff have no target mismatch row, run error checking without an independent raw panic, and return explicit coverage-unknown. All cases first verify actual Function→ExpectType and Arg→HasType producers. The manual consumer reads manual relations even though annotations and the diagnostic query remain inspectable in its graph. This establishes both mechanisms' role in the **same internal compiler obligation**, without equal-output cancellation, E1 reverse inference, primitive-wrapper panic, unique detection power, or a new valid-source bug.

The retained focused targets directly report 8 DAG tests, one host test spanning five modes, and one CLI parser test, all successful. Central contribution/normalization/corruption controls cover NEE/EE; some subsidiary shapes and coverage cases remain NEE-only. The host stderr contains 12 enabled-mode validation rows: Manual/Combined/AnnotationsOff/QueryOff each show passes 0/1/2 with 5/5/4 obligations; Off has no structural audit. The host test's normal source/result reference is `7\n`. The parser unit test is not counted as a full CLI invocation.

Actual CLI review is bound to `final/cli-controls/summary.json` SHA `c026f7160cc9b114094237cc6eb27e33800b1dcd6d8d6104034f96dcadaa9540`, release binary SHA `95c8d944cdc4fb816d3f65ea653feba07fffaae2fb4043507a1c47160f2b9082` (also recomputed from the selected executable), fixture SHA `ac68ed9e9ae4ab19d6ffbb45675b08160aedc8284d4b9c494bfd3f9ef2d22a27`, and the retained Tiger identity `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`. I read each of the ten primary optimize/emit command receipts, raw pass markers and run-data rather than accepting summary booleans alone. All five optimize calls exit 0, have source/result `7\n`, and complete passes 0/1/2. All five emit calls exit 0 through those passes and produce identical Bril bytes, SHA `22c8e7ba392254ba642cf3f97879934a5608b1a173a3c90c71a24d2984cd79af`. Emit-only interpretation fields are null, not extra output checks. Enabled optimize and emit calls record the same 5/5/4 obligation counts. The program allocates one valid cell, stores 7, returns that pointer through identity, reads/prints 7 and frees it; its expected output is independently clear from the program. Existing Off emits the same optimized code, so its ordinary load/call simplification is not a new encoding-enabled optimization.

The unmodified emitted-output reparse fails separately with `BadNumFuncArgs(0,1)` because of the printed empty ARGS marker. I verified each of the five retained normalized copies differs only by removal of exactly one `# ARGS: ` comment; those diagnostic parse/interpreter calls exit 0 and give `7\n`. They have no native passes and are **not** counted among the ten primary calls or as byte-exact raw emitted reparses. No compiler fix or new baseline-bug claim follows from that auxiliary failure.

The draft explanation/reference were reviewed for claim consistency. Two corrections were routed to root: the original panic is a fixed message rather than interpolated expected/actual types, and QueryOff must be described as a missing selected consumer witness despite an available full generic query. Full NEE/EE cross-product coverage must not be implied for every subsidiary case. Draft CLI/gate bookkeeping was explicitly pending and is not treated as a semantic defect. This is not final whole-dossier prose consent.

### Mandatory independent oracle still pending execution at this boundary

The earlier declared test expectations were not an executable independent Type oracle, so they did not by themselves satisfy that approved verification requirement. Root retained the gap and authorized a test-only addition. I inspected `consumer/oracle-final/oracle-test-only.patch` SHA `1fbdbdbf4f45af597510f15cdfcbad5142f25dad27fa329db59eb50a38f065cd`, bound to source manifest SHA `8165c4521d16ea4f5d1cffe66a08092962b55b8976f37c2b6a2553bfc5352738`. Only the DAG test file differs, now SHA `adbeb738313643e34f8a0060e52889638525f6e6df5b1a2de3d931afcd4c4b55`; production closure is unchanged.

Oracle source consent: derived Rust `schema::Type`/BaseType/Vec PartialEq supplies expected structural equality independently of both Egglog manual propagation and the engine query. `actual.to_string()==ACTUAL` binds the fixed graph input, and each expected Display form comes from the same Rust value used by the oracle. Every case checks the real producer rows, the exact target mismatch error or supported equality validation. The nine finite shapes across NEE/EE and Off/Manual/Combined should produce 54 rows: six equal and 48 mismatches. This is a bounded shape matrix, not arbitrary completeness evidence. **Its execution result and final official gates are still required and are not approved here.** No new tests, workloads, or builds were run by this reviewer; only retained evidence and the new oracle source were read.

## Final addendum — 2026-10-18 UTC: independent oracle passed

**Final semantic/source and actual joint-consumer consent; no remaining blocker in this review's scope.** The executable oracle requirement is now satisfied for its declared finite matrix. This closes the prior pending-oracle item, without approving the separately running official gates or final whole-dossier completion.

Authoritative checkpoint: `consumer/oracle-final/checkpoint.json`, SHA `227599b8ac493ecb60b012191d8d56b7ae90e602ad721992f8c00c8ec2a6b985`; source map SHA `8165c4521d16ea4f5d1cffe66a08092962b55b8976f37c2b6a2553bfc5352738`. I compared the complete final/oracle-final source maps: their only differing file is `dag_in_context/src/structural_types/tests.rs`. All nine changed-file hashes match the oracle-final live source at this final read. The production implementation, CLI, fixture and Tiger closure are unchanged, so the checkpoint explicitly reuses the previously reviewed host and CLI evidence; it does not claim those commands ran again after the test-only addition.

I inspected the actual oracle receipt, stdout/stderr and archived rows. The release DAG-manifest structural target exits 0 with **9 passed, 0 failed, 0 ignored, 74 filtered out**. The named independent-oracle test is listed and passes. `oracle-results.json`, SHA `df81c8775c45ef817c258c93d4e233eb25aa0d7ca0c183cf88dc0df63edf1c7d`, exactly matches the 54 JSON rows in raw stderr. I checked the full unique grid of nine cases × NEE/EE × Off/Manual/Combined, expected six equal and 48 mismatches, actual producer checks, and matching observed consumer outcomes. The printed canonical ground types agree with their independently derived equality classification. The model is Rust's derived free-tree/Vec equality, not either checker asking itself for an expected answer.

The refreshed 50 intermediate witness rows and ten consumer outcomes are byte-identical to the earlier independently checked artifacts, now emitted from the same oracle-final source. They preserve the fixed-leaf and QueryOff distinctions described above. Thus the evidence supports a richer **forward structural disequality integration through equality-sort fields into EggCC's actual ExpectType check**, with direct/manual equivalence and fixed-input feature controls. It does not establish a new valid-source bug, a newly enabled optimization, speedup, cancellation/reverse necessity, or exhaustive candidate search. Other candidate families may remain untested under the accepted positive integration route.

Additional exact receipts: `oracle-final/dag-tests.json` SHA `37a4a1d6f3f10c85b0bf900c86bdeca89c6e111d037db0cec3a0e4580f3e0bad`; stdout `d71b24eedbf253bf376fc6e4f7d02a345c04e15de54cf4d948a8268518d99560`; stderr `b85f11b33518aee9340b4416ab6a0ca3d393eb2a9afbbdeabc68d663295cebea`. The final oracle evidence covers its stated cases, not all possible type graphs or unsupported forms. No tests/builds/workloads were executed by this reviewer. Only this review file was amended.
