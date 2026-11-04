# Structural type checking: reference

See [the explanation](report.md) for the connected example and [the semantic contract](findings/type-contract.md) for the full assumptions. Functional checks pass; official test/lint gates retain failures independently reproduced in the fresh pre-integration control.

## Supported types and laws

The supported domain is finite free type metadata:

```text
B ::= IntT | BoolT | FloatT | StateT | PointerT(B)
L ::= TNil | TCons(B,L)
T ::= Base(B) | TupleT(L)
```

`PointerT` describes a pointer's type; it makes no assertion about runtime addresses or aliasing. The injective constructors are `PointerT`, `Base`, `TupleT` and `TCons`. For example:

```text
PointerT(a) = PointerT(b) ⇒ a = b
TCons(a,xs) = TCons(b,ys) ⇒ a = b ∧ xs = ys
```

Their contrapositives give:

```text
a ≠ b ⇒ PointerT(a) ≠ PointerT(b)
(a ≠ b ∨ xs ≠ ys) ⇒ TCons(a,xs) ≠ TCons(b,ys)
```

Distinct constructor tags require separate axioms. The shared rules provide all six pairs of distinct base leaves, each base leaf versus a present ground `PointerT`, present ground `Base` versus `TupleT`, and `TNil` versus present ground `TCons`. No final same-constructor parent difference is asserted.

`TLConcat`, `TypeList-ith` and `TypeListRemoveAt` retain their existing normalization and are not marked injective. `TmpType` and unresolved/symbolic forms are outside the supported domain.

## Modes

The experimental compiler option is `--structural-types MODE`:

| Mode | ExpectType mismatch predicate |
| --- | --- |
| `off` | Existing normalized raw-ID inequality. Default. |
| `manual` | Constructor-specific structural mismatch relations over the shared type laws. |
| `combined` | `known-disequal?` with the four structural annotations. |
| `annotations-off` | The same query and laws, with the four annotations removed. |
| `query-off` | Explicit Type tag witnesses only, with the same domain and diagnostic action. |

The feature-removal modes are experiment controls. In `query-off`, the full structural query remains available for inspection, but the diagnostic consults only explicit Type tag witnesses. Failure of the selected check to validate an obligation is not successful type validation.

## Assertion representations

The engine supports a not-equal relation representation (`nee`, called NEE in test notes) and an equality embedding (`ee`, called EE). The first stores explicit unequal pairs in a per-sort relation; the query probes either orientation. The second embeds an assertion as `Eq_S(a,b) = F` in an auxiliary truth sort. These are storage choices for the same asserted distinctions, not injectivity-on/off controls. The central DAG comparisons test both; the actual CLI matrix uses the default `nee` representation. Full engine details are in [disequality.rs](/Users/saul/p/wt/egglog-encoding/eggcc-combined-encoding/egglog-experimental/src/disequality.rs).

## Consumer and schedule

The existing producer path is:

```text
Function(name,input,output,body) → ExpectType(body,output,message)
body type analysis             → HasType(body,actual)
```

In opt-in modes, the existing error rule consumes `StructuralTypeMismatch(expected,actual)` instead of `!= expected actual`. Its panic action is retained. Shared ground/tag preparation runs with the existing type helpers; a dedicated `:naive` consumer runs after committed helper closure and before error checking.

The combined predicate is `known-disequal? expected actual`. It reads committed disequality evidence and recursively uses constructor metadata. This forward propagation does not require running the `injectivity` cancellation ruleset and does not materialize every derived parent disequality pair.

Before native serialization/extraction, the host checks every expected/actual alternative. Supported equal types validate. A mismatch invokes the existing diagnostic. Unsupported values, missing actual types, or distinct types without a selected witness produce explicit coverage failures. Zero reached obligations also fails. The full rules and host boundary are in [structural_types.rs](/Users/saul/p/wt/eggcc/combined-encoding/dag_in_context/src/structural_types.rs), [shared preparation](/Users/saul/p/wt/eggcc/combined-encoding/dag_in_context/src/structural_types.egg) and [manual propagation](/Users/saul/p/wt/eggcc/combined-encoding/dag_in_context/src/structural_types_manual.egg).

The shared consumer also rejects any explicit tag distinction whose endpoints have been merged, before an equal obligation can count as validated. Such a union violates the free-type contract; it is a corruption test, not an allowed refinement.

## Scope

This is an opt-in comparison on finite, normalized, consistent free types. It does not establish a general symbolic type solver, constructor disjointness from injectivity alone, unrestricted scheduling completeness, a new compiler bug, or a performance improvement. For this domain, the original check and complete structural check should agree.

## Evidence identities

Raw paths below are relative to ignored `benchmarks/local/eggcc-combined-encoding/`. They are exact local evidence authorities, not benchmark measurements.

| Artifact | SHA-256 |
| --- | --- |
| `provenance/baseline-source.json` | `d4ebbe674bda0ba3fda19f7c8e8fdfd4f8974c056839651b9bea1ffe90bfebb1` |
| `consumer/oracle-final/source.json` | `8165c4521d16ea4f5d1cffe66a08092962b55b8976f37c2b6a2553bfc5352738` |
| `consumer/oracle-final/checkpoint.json` | `227599b8ac493ecb60b012191d8d56b7ae90e602ad721992f8c00c8ec2a6b985` |
| `consumer/oracle-final/oracle-results.json` | `df81c8775c45ef817c258c93d4e233eb25aa0d7ca0c183cf88dc0df63edf1c7d` |
| `consumer/final/cli-controls/summary.json` | `c026f7160cc9b114094237cc6eb27e33800b1dcd6d8d6104034f96dcadaa9540` |
| `final-gates/summary.json` | `b116e66101b0cd69c25ea53e7725e4b356c3fca3074999ef42c046c1192f1b69` |

The final test-only oracle addition leaves the production closure identical to the release build used for host/CLI controls. That executable is `95c8d944cdc4fb816d3f65ea653feba07fffaae2fb4043507a1c47160f2b9082`; its paired Tiger is `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`. Source archives and complete patches are adjacent to their source manifests. See [the consumer ledger](findings/consumer.md), [semantic review](findings/type-review.md) and [gate receipt](findings/gates.md).

Default-Off public prologue output is exactly 185,221 bytes in both roles, SHA `d5aacd0b84d58c0674b18188c43e25f30488c1920ae54142391508dfec9c76b7`. The final gate artifacts under `final-gates/` retain 26 selected snapshot trials for the 13 common pending bodies, all three matching strict lint sites, and the public-prologue export/dependency bindings. No snapshot was accepted and no lint allowance was used.
