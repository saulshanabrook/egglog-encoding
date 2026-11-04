# Finite structural type contract

Actionable semantic contract for the first approved C6 slice, 2026-10-17. This is source-based design/review evidence, not a new execution result or an implementation review. Only this file was written; no builds, tests, compiler calls, project imports, runtime edits, or old-artifact changes were performed.

## Domain and interpretation

Use the existing three sorts with this **finite, fully known free-data** interpretation:

```text
B ::= IntT | BoolT | FloatT | StateT | PointerT(B)
L ::= TNil | TCons(B,L)
T ::= Base(B) | TupleT(L)
```

Each individual value is finite; pointer nesting and list length need not have a universal fixed maximum. Lists are flat lists of BaseType values, not nested tuple heads. `PointerT(B)` denotes an exact pointer **type description**, never a runtime address or nonalias certificate. Types do not contain Expr, context, execution state, or mutable analysis payloads. The free-data equality is structural equality, matching the Rust mirror's derived equality. See [`schema.egg:11–35`](/Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/schema.egg:11) and [`schema.rs:10–31`](/Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/schema.rs:10).

The supported replacement applies only to normalized `ExpectType`/`HasType` obligations whose expected and actual values have this interpretation. It assumes the normalizer and producer unions preserve that free-data meaning; it does not reinterpret arbitrary corrupted, cyclic, or contradictory type e-graphs as valid finite types. The consumer owner's recorded scan found only legitimate helper normalization on these surfaces; that is source evidence, not a theorem about arbitrary injected rules. A contradictory tagged type union is a contract violation, not a permissible type refinement.

## Exact laws

The four marked constructors may have these cancellation laws:

```text
PointerT(a)=PointerT(b)       ⇒ a=b
Base(a)=Base(b)               ⇒ a=b
TupleT(xs)=TupleT(ys)         ⇒ xs=ys
TCons(a,xs)=TCons(b,ys)       ⇒ a=b and xs=ys
```

They follow from the free-data interpretation. Their contrapositives justify forward disequality through any differing corresponding field. The first consumer needs **forward structural disequality through equality-sort children**; it does not need to run generated cancellation rules, primitive-mismatch panic rules, or remaining-child reverse inference. Only `PointerT`, `Base`, `TupleT`, and `TCons` should be annotated for this slice. The nullary leaves have no child cancellation to perform.

Injectivity does not imply cross-constructor disjointness. Supply these additional, explicit semantic tag laws, only within each same sort:

1. The six unordered pairs among `IntT`, `BoolT`, `FloatT`, `StateT` are disequal.
2. Each of those four leaves is disequal to every **present supported** `PointerT(b)`.
3. Every present supported `Base(b)` is disequal to every present supported `TupleT(xs)`.
4. `TNil` is disequal to every present supported `TCons(b,xs)`.

Symmetric use must be supported; no raw ID `!=` chooses these laws. Do not assert final same-constructor parent mismatches, all unequal IDs, or arbitrary Type pairs. Parent differences must be derived from the tag laws through the selected structural mechanisms. The seed inventory is finite over the present supported graph; it need not enumerate an infinite type universe.

For two consistent ground values, these tag laws plus same-constructor forward propagation are sufficient to find every structural inequality by induction on their finite trees. Conversely every resulting witness is a structural inequality. Equal normalized ground trees hash-cons/converge to the same class, and unequal ground trees remain distinct under the contract. Consequently the original normalized raw-ID mismatch guard and the complete structural checker have the **same outcomes on this domain**. This proves no new detector coverage or baseline bug; performance is unmeasured. This bounded statement excludes missing tag laws, unsupported forms, illegal unions, and incomplete normalization.

## Actual assertion API and shared preparation

The current extension supports `(disequal a b)` both as a top-level action and a rule-head action. It does not provide `assert-disequal` or require a new `mark-disequal` protocol. Declarations must be installed before rules mentioning their sorts/constructors. Source: [`disequality.rs:450–471`](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/disequality.rs:450); rule-head recognition/type inference and lowering at [661–688](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/disequality.rs:661). The pass installs the required NEE/EE support before the user rule. Both operands must have the same unionable equality sort.

A source-shaped seed rule is:

```lisp
; Schematic preparation relation name; no new parser/API syntax is proposed.
(rule ((= p (PointerT child)) (GroundBase child))
      ((disequal (IntT) p)) :ruleset structural-type-tags)
```

This is the justified IntT-versus-pointer tag law, not a test of whether current IDs differ. Repeat the finite inventory explicitly. Native primitive disequality is not used for these BaseType/Type/TypeList values. Do not rely on private `@disequality-*` names.

The implementation may materialize shared typed tag-witness relations first, then lower those same witnesses to `(disequal ...)` in query modes and to manual structural relations in Manual mode. That makes identical law inputs auditable. Manual propagation must recursively compare same-constructor fields using precisely the same tag inventory: Pointer pointees; Base payloads; Tuple lists; and TCons head **or** tail. It must not get an extra raw-ID or final-parent oracle. Query-off should consult only explicit/tag witnesses while leaving the final diagnostic action and domain fixed; it must not merely delete the panic action.

## Normalization, supported-domain recognition, and unsupported outcomes

Keep `TLConcat`, `TypeList-ith`, `TypeListRemoveAt`, and all other helper/custom functions unmarked. Their normalization is not injective. Preserve [`type_analysis.egg:4–25`](/Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/type_analysis.egg:4) and [`canonicalize.egg:122–131`](/Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/utility/canonicalize.egg:122). Get and Concat deliberately produce lazy helpers ([383–390](/Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/type_analysis.egg:383), [424–432](/Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/type_analysis.egg:424)). Seed no inequality from a helper application's temporary identity.

Positive, non-generative `GroundBase`, `GroundList`, and `GroundType` relations can certify the finite grammar: four leaves; present PointerT with ground child; TNil; present TCons with ground head/tail; present Base/TupleT with ground payload. This admits helper-equivalent classes after they contain the proper normalized structural form. Do not generate parent applications merely to establish groundness. An unground cycle does not acquire a certificate through recursive self-support. Certification relies on the free-data-preserving union invariant above; it is not a license to pick one convenient representative from an inconsistent class.

**Absence of a ground certificate is not a negative predicate or a passed check.** Use the smallest initial policy: host-side fail-closed coverage after normalization. For every actual `ExpectType(e,expected,msg)` row, require at least one `HasType(e,actual)` result; examine every actual type alternative. Classify each pair as:

- supported ground and committed equal: validated equal;
- supported ground and structurally known disequal: invoke the existing ExpectType mismatch diagnostic;
- supported ground but distinct without the selected checker witness: explicit coverage-unknown failure;
- unsupported or no actual type result: explicit unsupported/coverage failure.

This policy is an acceptable opt-in unsupported path, not a general type-unifier redesign. A future complement that retains the original check outside the supported domain is also possible, but must be implemented and tested explicitly. Positive ground rules alone do not implement that complement. An ablated checker ending in coverage-unknown is an expected **failure to validate**, not successful acceptance of malformed IR. Off retains the original guard and prologue behavior.

`TmpType` has no ground/tag rule. It is an intentional helper sentinel whose substitution exemption remains intact ([`subst.egg:46–56`](/Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/utility/subst.egg:46)); its presence elsewhere in a program must not be mislabeled a type mismatch. If it reaches an affected obligation, use the explicit unsupported/existing path. Rust `Unknown` is normally removed by argument annotation before e-graph entry; its printer emits `Unknown` for diagnostics, while `Symbolic` prints an Egglog variable ([`schema.rs:24–31`](/Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/schema.rs:24), [`to_egglog.rs:102–105`](/Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/to_egglog.rs:102)). Do not invent a production Unknown/Symbolic constructor to make a test pass. Unresolved forms are unsupported; a variable already instantiated to a justified ground value is that value, not an independent unknown witness.

## Schedule and actual consumer boundary

The target is only the existing ExpectType mismatch rule at [`type_analysis.egg:31–38`](/Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/type_analysis.egg:31). Keep its diagnostic and other error checks. Real Function rules produce the expectation ([565–572](/Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/type_analysis.egg:565)); Arg/Get/Single/Concat rules produce actual HasType values. Do not seed final ExpectType/HasType pairs merely to bypass those producers in the primary consumer fixture.

Preserve the helper/type-analysis ordering in [`schedule.rs:20–29`](/Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/schedule.rs:20). At each applicable error-check boundary: commit helper-normalized type-producer rows, close ground/tag preparation over present nodes, commit resulting assertions, then run the query-backed `:naive` consumer. Rerun when new type rows or tag facts appear. A host coverage audit must occur after the mismatch consumer had its opportunity and before serialization/extraction of an unvalidated graph; it cannot silently discard an expectation lacking HasType.

The query reads committed rows, creates no derived-pair storage, and does not schedule injectivity. This forward-only slice need not saturate `injectivity` to obtain its witness. If cancellation is separately exercised, schedule and label it. NEE/EE tag-seed consistency must be checked on normalizer controls; a seeded disjoint-tag union must produce a contract/contradiction failure rather than a successful type validation. `check-contradiction` succeeds when a contradiction **exists**; it is not a normal-consistency success test and does not run injectivity. No general joint-closure claim is made.

## Minimal connected fixture and fixed-input controls

Use a real internal Function/Arg term with:

```text
actual   = TupleT([IntT, PointerT(IntT),  StateT])
expected = TupleT([IntT, PointerT(BoolT), StateT])
body     = Arg(actual, InFunc("structural_type"))
function = Function("structural_type", actual, expected, body)
```

Brackets abbreviate TCons/TNil. The input type equals the Arg type, avoiding a separate argument-mismatch cause. The declared output differs at zero-based slot 1. Function→ExpectType and Arg→HasType create the target obligation. Required witness: IntT/BoolT tag law → PointerT pointee difference → second TCons head → outer TCons tail → TupleT → original diagnostic. This is an intentionally malformed **internal type-analysis fixture**, not a valid-source bug or generated-program runtime example.

Keep this exact source term, leaf/tag inventory, helper schedule and diagnostic action fixed across:

| Control | Required outcome on the nested fixture |
| --- | --- |
| Original raw check | Existing mismatch diagnostic after normalization. |
| Manual structural propagation | Same mismatch diagnostic with the declared structural witness. |
| Combined annotation/query | Same diagnostic reached through structural query; record intermediate/final witness presence. |
| Relevant annotations removed | No same-tag structural witness; coverage-unknown, with no independent original raw panic masking it. |
| Query reasoning replaced by tag-only lookup | Same fixed consumer action lacks its root witness; coverage-unknown. |

Also require equal nested types; head/tail/length and cross-tag mismatches; normalized append/index/remove equivalences; missing tag facts; late tag/type rows; unsupported sentinel/unresolved forms; and a deliberate disjoint-tag union failure. Test both assertion encodings. For annotation/query ablations, direct cross-tag pairs may still be detected; the chosen same-tag nested fixture is what distinguishes structural contribution. A missing-tag negative must remove all other independent witness paths, not assume one seed is uniquely necessary in a larger graph.

An independent ordinary finite Type-tree comparison supplies expected ground equality/difference; do not ask the same query/manual checker to compute its own oracle. Register actual consumer tests with nonzero discovery. Valid typed source controls must additionally reach the normal native pipeline with unchanged expected source/result output. Expected internal rejection/unknown/unsupported outcomes are separate from successful three-pass native runs. No new coverage, optimization, bug, or speedup follows solely from this integration.

## Source binding and disposition

Targeted source reads used the preserved `/Users/saul/p/wt/eggcc/encoding-impact` files referenced by consumer discovery, with no writes there. SHA-256: schema.egg `cbf82f3ddb22f60f364ee59e9ecf15ff2bd468f1d561ccb48e93e65a1fd0144b`; schema.rs `fba115bb773c536dbaeabf9be3870a571d503c2b13c25f96ef1372ee1ac61111`; type_analysis.egg `9924928fa7927189c36f0b65b1cd68d5914850b7fc9e6cfe00f118e39a7c81de`; canonicalize.egg `aa7b40cba93c9d51133df7e94fa15f5a4fa3ec1f897c4eb4780f632a4e582c52`; subst.egg `bdd3e00295d7bc8bb6aae674a63cb468e5bcab8b31aea0764e8c1c25ec0da45c`; schedule.rs `9fbdab5fb1b738e7e93cad0cc2924a2a440d725903354c5c81a62ccfb8ec10e0`. Actual assertion API was read in preserved encoding `disequality.rs`, SHA `8d56d53d87d0c21595b765f3aa6a9f7e3bc4752b4f87dfbcc651c108fe11bb3c`.

Approved plan SHA at this read: `943c66c5247dd7062bae02b5dcdd94dfc214562109fc93a9e4c382dc5e060fef`; accepted facts `3dc28ac857ae943453bf257e208ae0df1746fe5461ace6b1fdf55d31cdec8c93`; consumer discovery `40be1e13be3a73be120831877efb1e9a8bd6f3c40b5d8e9415492c452bd234b2`; encoding discovery `9526dbb9fee45c36f8114a93f883e857178e45259bb63f794d4b60fb445bc9a5`. Commands were `cat`/`nl`/`sed`, narrow `rg`, and SHA checks, with source API reads limited to the linked lowering ranges. No project module was imported or executed.

Consent for this minimal semantic contract, conditional on implementation enforcing its supported/unknown boundary and preserving all actual non-target checks. There is no identified mathematical falsifier for the finite free-data laws. A real source normalization equating disjoint tags, treating these structures as mutable approximations, silently accepting uncovered obligations, or masking feature ablations with another panic would reject the implementation or require a narrower contract before proceeding. Review the actual patch and evidence next; this note does not pre-approve them.
