# P1 Pack32: retain for one bounded actual integration

This is a source-backed implementation design, not an executed integration or a
payoff result. No compiler, test, native program, or timing command was run for
this design. The existing Pack32 source and screen captures are unchanged.

## Disposition and comparison with Parts32

**Parts32 does not supersede P1.** Its private graph starts with `x != y` and an
already imported `Low(x) = Low(y)`. Marked unary forward disequality and the
representation identities give unequal Pair outputs; ordinary reverse
congruence then consumes the imported equal low sibling. Removing injective
cancellation alone cannot falsify that chain: no equal applications of a marked
constructor have to produce a new child equality.

P1 instead starts from an equality of two binary packed outputs. Marked
cancellation produces `a=c` and `b=d`. These enable the originally described
reverse-congruence/transport chain. The same graph also permits comparing
`Pca(c,a)` with `Pcd(c,d)`, because the first seed identifies Pab=Pcd; their
syntactically equal high c gives a!=d, then cancelled a=c gives c!=d. Therefore
at least the cancelled child equality a=c is essential to the endpoint;
b=d is available but not individually necessary. The retained P1 fixture also
has changing bounded fields in its hot loop;
Parts32's exact low/high partition and opaque changing whole words do not prove
the bounded-field induction needed here.

| Property | Parts32 actual integration | P1 retained screen / proposed integration |
| --- | --- | --- |
| Semantic representation | Total unary word decomposition | Joint binary packing on two bounded fields |
| Initial dynamic equality | Low-child equality imported from a branch | Packed-output equality imported from a branch |
| Child equality produced by cancellation | None required | `a=c` required; `b=d` also available |
| Equal sibling used by reverse congruence | Imported low equality | Newly cancelled `c=a` |
| Marked forward step | Whole-word `Parts32` | Fixed translation `Shift7` |
| Extra host obligation | Exact partition constants and loop literal transport | Exact bounds initially and on every backedge |
| Existing native evidence | Actual generic integration changes code | Manual-only screen changes code |

Parts32 supplies reusable host scaffolding and evidence that the endpoint seam
works. It supplies neither an actual P1 import nor its cancellation knockout,
domain proof, native replay, or speed evidence. P1 remains
`retained_native_opportunity_pending_actual_encoding`. No broad impossibility,
completed payoff, or exhaustion conclusion follows from this design.

The later Affine/Route/Sort integrations also contain cancellation-to-reverse
chains, so a completed P1 would not establish unique generic expressive power.
They do not establish P1's guarded domain importer or dispose of this already
admitted bounded native opportunity. A terminal redundancy disposition would
need an explicit accepted change to the finite lead-resolution criterion; it
cannot be inferred from Parts32 alone.

## Exact semantic law and private graph

Let `B=2^32`, `U32={0,...,B-1}`, and `W64` be the 64-bit words with signed i64
interpretation. Define:

```
Pack32(a,b) = bits64(B*a+b),     a,b in U32
Shift7(a)  = bits64(a+7),       a in U32
```

`0 <= B*a+b < 2^64`; decoding its unsigned quotient/remainder by B uniquely
recovers `(a,b)`. Signed interpretation preserves bit equality. `Pack32` is
jointly injective on the stated domain, despite the source's wrapping Mul/Add.
`Shift7` is injective because wrapping addition by a fixed word is a bijection
on W64, hence injective on its U32 subset. The source's Bitand update is total
and always lands in U32. Do not mark unrestricted Add, Mul, or Bitand injective.

Use a separate equality sort `Field32` interpreted as U32. This prevents a
globally marked `Pack32(Word,Word)` declaration from silently asserting the
false unrestricted-i64 law. Source integer operands become Field32 opaque
values only after their domain certificates pass. Their packed and translated
outputs have sort `Word`. The fixed width and translation belong to distinct
constructor names; they are not arbitrary primitive parameters on a marked
constructor.

The smallest committed graph is the following. Bindings use the `pk32-` prefix
to avoid the inherited EE diagnostic global-name collision. Opaque A/B/C/D
constructors are unmarked and assert no distinction between the fields.

```lisp
(datatype Scope (ThisScope))
(datatype Field32)
(datatype Word)
(constructor A (Scope) Field32)
(constructor B (Scope) Field32)
(constructor C (Scope) Field32)
(constructor D (Scope) Field32)
(constructor Pack32 (Field32 Field32) Word :injective)
(constructor Shift7 (Field32) Word :injective)
(let pk32-a (A (ThisScope)))
(let pk32-b (B (ThisScope)))
(let pk32-c (C (ThisScope)))
(let pk32-d (D (ThisScope)))
(let pk32-ab (Pack32 pk32-a pk32-b))
(let pk32-cd (Pack32 pk32-c pk32-d))
(let pk32-ca (Pack32 pk32-c pk32-a))
(let pk32-tc (Shift7 pk32-c))
(let pk32-td (Shift7 pk32-d))
(union pk32-ab pk32-cd)
(disequal pk32-ca pk32-ab)
(run-schedule (saturate injectivity))
```

There are nine semantic application rows: four opaque leaves, three packed
applications, and two translated applications. The arithmetic source matching
is the representation bridge: `Add(Mul(a,4294967296),b)` becomes `Pack32(a,b)`
only after exact operand, constant, scope, type, and domain checks. No new
source arithmetic identity is inferred by the host. Extra Add/Mul private rows
or Parts32-style representation unions are unnecessary for this direct
semantic view; do not add an artificial identity stage simply to inherit a
control name.

Required observable chain:

```
Pack32(a,b)=Pack32(c,d)             source true-path seed
  => a=c and b=d                   marked binary cancellation
Pack32(c,a)!=Pack32(a,b)           source false-path seed
  => a!=b                         generic reverse, common high child c=a
  => c!=d                         canonical equality transport
  => Shift7(c)!=Shift7(d)          generic marked forward
  => exact contextual Eq=false    checked export and existing application
```

Witness `(a,b,c,d,n)=(1,2,1,2,1)` reaches the feasible target scope and returns
7. `(0,0,0,0,1)` takes the second equality branch and returns 5; distinct first
keys take the other branch and return 3. The existing byte-concatenation oracle
and boundary corpus remain independent semantic checks. These examples are
mathematical witnesses; they were not executed in this pass.

## Source seam and bounded importer

Reuse the archived Parts32 `eggcc/dag_in_context/src/lib.rs` initialization
bridge. Pinned U0 `dag_in_context/src/lib.rs:218-258` inlines and adds exact
contexts before serializing the immutable source program. The archived bridge
runs `scoped_reasoning::analyze(&program)` after loop-context serialization and
before the main graph schedule, then prints only the exact predicate unioned
with `Const(Bool(false), predicate.get_arg_type(), predicate.get_ctx())`.
Preserve its `--with-context` requirement and application knockout.

Replace only the Parts32-specific contents of `scoped_reasoning.rs` in a fresh
isolated P1 host. Retain `project`, tuple expansion, exact typed branch-input
transport, loop literal inference for base/mask/seven, independent finite
manual closure, read-only witness queries, NEE contradiction gate, boundary
receipts, and registered test structure. Do not copy its `Low/High` matcher or
its assumed `false word Eq -> true low Eq` context order.

P1 matcher, with conservative failure on every unsupported expression:

1. Find an integer target `Eq(Add(c,7),Add(d,7))` actually used by an `If`.
   Confirm a Boolean target type and integer operand types through `typecheck`.
2. Its exact scope must be `InIf(false, second_pred, second_input)` with
   `second_pred` an integer Eq of the recognized `Pack32(c,a)` and `Pack32(a,b)`
   expressions, allowing swapped Eq operands.
3. The second predicate's exact scope must be
   `InIf(true, first_pred, first_input)`, where the first predicate equates
   recognized `Pack32(a,b)` and `Pack32(c,d)`, allowing swapped Eq operands.
4. Translate all operands to one exact lexical loop root through each actual
   `InIf` input. Reuse the archived `translate(expr, root, expected, ...)`
   contract: verify `expr.get_ctx()==expected` before expansion; every Get must
   project the current scope's declared input and have the expected field type.
   Do not equate slot numbers from unrelated scopes or different iterations.
5. Match only Mul by literal B followed by Add of the low field, plus Add by
   literal 7 for both targets. Constants may follow proved same-index literal
   loop slots, exactly as in Parts32. An optional commuted-operand normalization
   is sound but should be added only if the actual source shape requires it.
6. Certify a,b,c,d as U32 at this loop root, as described below. Pack operands
   must be these exact translated bounded values, not merely four arbitrary
   fields with valid-looking metadata. Reject changed width/base/mask/shift,
   a missing bound, a different operand, wrong branch, wrong scope, wrong type,
   unresolved projection, or an inconsistent private assumption set.
7. Populate a fresh private graph per accepted target. Import exactly the two
   path seeds. Query and retain `a=c`, `b=d`, `a!=b`, `c!=d`, and the translated
   disequality separately. Export only the original target Eq=false when the
   final query is true and the contradiction check is negative. Unknown,
   unsupported, and Bottom all export nothing.

The U0 source gives this seam concrete semantics:
`add_context.rs:258-265` creates a fresh placeholder for each loop body and later
unites it with that exact InLoop, while `add_context.rs:270-279` constructs the
actual `InIf(bool,predicate,input)` contexts. A Rust-tree importer should bind
the loop by its actual `DoWhile(initial,body)` and `body.get_ctx()`, rather than
expecting an already cyclic `Assumption::InLoop` in the immutable tree.

### Four-field domain induction

Parts32 proves only literal passthrough invariants. P1 requires a small new
*domain* invariant, restricted to these fields, not a general interval solver:

* For each exact DoWhile input slot used as a/b/c/d, project its actual initial
  value. Follow enclosing If input projections. Under an actual true `valid`
  branch, flatten only the conjunction tree of Boolean And expressions. Check
  exact signed `GreaterEq(field,0)` and `LessThan(field,B)` leaves for that same
  lexical value. A literal already in U32 or a literal-mask Bitand also proves
  the initial domain. Reject unresolved Boolean slots, Or, false conjuncts, or
  missing leaves; no guessed association with variable names.
* Project body output `slot+1`, because output zero is the DoWhile predicate.
  Expand exact tuple construction and nested If inputs. At an If merge, the
  domain certificate must hold in **both** output branches. Accept a passthrough
  of an already certified loop field or `Bitand(any typed pure i64 value,M)`
  with a proved literal `0<=M<=0xffffffff`. The source's M is exactly
  `0xffffffff`. Do not treat arbitrary arithmetic as a bounds proof.
* These two checks justify induction: guarded initial values are in U32 and
  every backedge value is in U32. Record the initial bound leaves, exact input
  slot, loop/body context, output slot, mask literal provenance, and every
  branch certificate. Updated values stay opaque per iteration; never infer
  equality with their earlier values or with a similarly numbered slot.
* Keep the existing literal same-index invariants for B, mask, and 7 separate.
  A changed or moved constant slot invalidates its literal certificate. P1's
  integer Add/Mul/Bitand are pure, total, and wrapping according to pinned
  `interpreter.rs:238-246`; no pointer, state, free, allocation, call, division,
  or mutation is part of this fragment.

This is a bounded new analysis with an elementary proof obligation. If the
actual source boundary cannot expose its guarded initial tuple and masked
backedges with this structural traversal, allow one revision tied to the
captured source-shape falsifier. Close the importer lead if it then needs a
general path, range, recurrence, or loop-value analysis. Do not replace the
screen input to evade a failed P1 import.

## Fixed-input causal matrix and primitive-only null

All causal arms use byte-identical source, source scopes, domain certificates,
committed application rows, and original path seeds. Record graph/schema/seed
identities separately so an annotation change can be distinguished from a term
or seed deletion. Positive optimized arms must agree with the faithful manual
closure and the existing one-line source fold at the native endpoint.

| Mode | Single inference/application intervention | Required result |
| --- | --- | --- |
| U0 | Original admitted compiler | Retained target compare/select |
| off / B1 | Same dependency-retargeted host, analysis disabled | U0 code |
| seed-only | Complete traversal, graph, annotations and seeds; no inference/query/export | U0 code |
| primitive-only | Same populated graph and seeds; primitive comparisons only | No witness; U0 code |
| encoding | NEE generic saturation and final query | Child equalities, field and translated disequalities; optimized code |
| manual | Independent least fixed point on same finite rows/seeds | Same intermediate facts and code as Encoding |
| cancellation-off | Remove only Pack32's injective annotation | Neither cancelled equality; unknown target; U0 code |
| cancellation-rescue | cancellation-off plus only true intermediate `a=c` | b=d remains unknown; restored reverse/forward chain and optimized code |
| reverse-off | Use inherited `known-disequal-forward-only?` query | Cancelled equalities remain; no child/target disequality; U0 code |
| disequality-rescue | reverse-off plus true intermediate `c!=d` | Final marked forward step and optimized code |
| forward-off | Remove only Shift7's injective annotation | Cancelled equalities and `c!=d` remain; final target unknown; U0 code |
| query-off | Do not run final translated-child witness query | Prior private witnesses remain; U0 code |
| bridge-off | Retain final private witness, export nothing | U0 code |
| consumer-off | Retain witness/export receipt; suppress exact target union | U0 code |

The cancellation rescue deliberately inserts only a=c. The existing output
equality also identifies Pab=Pcd, so reverse comparison against Pcd supplies
a!=d and hence c!=d without needing b=d. This corrects the earlier design's
claim that both cancelled equalities were individually essential. The reverse
rescue inserts an actual intermediate field disequality, not a final
translated fact or a direct target fold. Never put rescue facts into the main
compiler graph.

Implement the null as an executed traversal over the same recorded source
applications and domain certificates. Compare every corresponding primitive
coefficient/width/translation/mask/bound field, recording the comparisons and
counts. On the positive it finds only equal B/B, 7/7, mask/mask, and matching
bounds. The marked semantic constructors have zero primitive children. The
null may retain dynamic source seeds in the graph, but runs no injectivity
saturation, equality-sort closure, `known-disequal?`, contradiction solver, or
manual closure and exports nothing. Assert byte-identical pre-inference graph,
seed, source, and certificate serializations to Encoding. This avoids the
rejected Parts32 pilot null that had removed its dynamic seeds.

As an explicit primitive-only countercheck, preserve the existing negative
graphs/metadata where possible: absent first equality and two unresolved
children, or missing a bound, permit actual 99 outputs. Bounds, B, and 7 alone
cannot justify a universal false target. A specialized multi-premise packing
rewrite is a fair manual implementation; do not claim unique logical power.

Run all existing positive rows and the three existing semantic-negative fixtures
without replacing or editing the originals. Add registered/fixture checks for
missing lower bound, missing low upper bound, changed/moved base or mask loop
slots, an unmasked field backedge, a swapped field binding, unrelated/sibling
contexts, absent context mode, missing packed disequality, wrong translation,
and two unresolved children. For a potentially unsound boundary, retain a
concrete feasible oracle witness when one exists; unsupported and infeasible
outcomes must stay distinct. Confirm EE/NEE agreement on the finite consistent
graphs, with the established binding-name prefix.

Do not identify a particular false-If rule as essential without its own causal
result. Parts32's rule knockout still optimized through extraction/LLVM. The
required downstream knockout is suppression of the exact target union.

## Endpoint, files, and exact next steps

The existing screen establishes a real remaining endpoint: in
`pack32-screen/inspection.json`, U0-emitted and source native functions each
retain five i64 equality comparisons and the 99 case; the exact manual fold has
four and no 99 case. The actual loop has changing fields. No new timing result
is inferred from those counts or captured diagnostic durations. First require
actual P1 Encoding/Manual native parity and knockout-to-U0 parity, using the
same admitted Tiger, runtime, LLVM18, O3_O3 backend, arguments, and one Rayon
thread. Only then design a prospectively frozen per-workload runtime or
end-to-end compilation experiment with independent confirmation. The current
source caps n at one million; do not silently widen it for timing or borrow
Parts32's samples/design as P1 evidence.

Implementation files in fresh isolated roots:

| File | Exact bounded change |
| --- | --- |
| `/private/tmp/eggcc-pack32-candidate/dag_in_context/src/scoped_reasoning.rs` | Replace Parts32 theory/matcher with Field32/Pack32/Shift7 graph, bounded domain induction, causal modes, receipts and registered tests |
| `/private/tmp/eggcc-pack32-candidate/dag_in_context/src/lib.rs` | Reuse archived source-boundary union and consumer-off bridge; remove Parts32-specific optional named-rule knockout |
| Both EggCC Cargo.toml / Cargo.lock files | Reuse archived dependency retarget with isolated encoding path; retain locked resolution |
| `/private/tmp/encoding-pack32-candidate/...` | Reuse exact archived engine delta including forward-only diagnostic query; no P1-specific engine feature |
| `pack32-integration/admit.py` | Reconstruct clean pinned sources from retained full archives; overlay archived final Parts32 files, retarget paths, verify input/overlay identities |
| `pack32-integration/run.py` | Reuse bounded capture helper with isolated paths and fresh durable command labels; pressure guard disabled |
| `pack32-integration/matrix.py` | Adapt Parts32 matrix to P1 positive/negative corpus and new mode names; require fresh output root |
| `pack32-integration/inspect_capture.py` | Assert scope/domain receipts, every intermediate/knockout/rescue, exact null identities, code/outputs and explicit validation status |

The live `/private/tmp/eggcc-parts32-candidate` and
`/private/tmp/encoding-parts32-candidate` paths no longer exist on this host.
Pinned U0 is a source archive extraction without `.git`; `git -C U0 archive`
and the old Parts32 `admit.py` therefore are not runnable setup recipes now.
Use these retained artifacts instead:

```
parts32-integration/eggcc-parts32-candidate.tar
parts32-integration/encoding-parts32-candidate.tar
parts32-integration/final-source.tar
parts32-integration/final-source-identities.json
parts32-integration/source-admission.json
```

The first two are complete pinned base archives; `final-source.tar` is the
reviewed overlay with `eggcc/` and `encoding/` member prefixes. The archived
base identities in `source-admission.json` are:

```
EggCC a0bbec127f83249074a46af3fd6f6126c90fe0fb
archive SHA256 7a886debd758e78d0e859a05bbac75084e7da9c4f4bd0d73321dcf6f5ad25c2a
encoding 392b6d6b48b5bc307a5b9c981c957fc0a09e23e5
archive SHA256 bf28b65f200123f5738326a069dad26d9d7004dd72ef89f9f4becd74f11cd82f
```

`admit.py` must verify these hashes, assert each new root is absent, extract
with Python tarfile `filter='data'`, and verify every final overlay member
against `archive_path`/sha256 rows before applying it. Then replace the literal
old encoding path in the two copied manifests with the new isolated path. Keep
both source archives and all existing captures untouched. Cargo build output
may be reused compatibly, but should point to an isolated writable target so
this task does not mutate another candidate's active outputs.

After implementing those named scripts/source deltas, the next exact commands
are the following; these are instructions for the parent, **not executed here**:

```sh
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/admit.py
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/run.py metadata-host cargo metadata --locked --no-deps
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/run.py build cargo build --release --locked
```

The capture helper runs from `/private/tmp/eggcc-pack32-candidate`, with
`EGGCC_ROOT` set there, LLVM18 environment and `RUSTUP_TOOLCHAIN=1.91.0`, finite
timeouts, and no inherited wrapper/RUSTFLAGS/snapshot acceptance variables.
Register the focused tests under the `pack32_` prefix in the existing dag unit
test module. Run the following in the isolated dag root with the same helper
environment and fresh capture labels, asserting a nonzero selected-test count:

```sh
cargo test --release --locked pack32_ -- --nocapture
```

Copy the built compiler and admitted Tiger into a new durable `bin/` directory,
bind exact binary/runtime/source hashes, then run the adapted matrix with
`PACK32_BINARY` and a new `PACK32_OUTPUT_ROOT`:

```sh
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/matrix.py positive
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/matrix.py negative
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/matrix.py loop-negative
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/matrix.py context-negative
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/inspect_capture.py
```

The first matrix emit is the actual-host importer falsifier. Capture accepted
and rejected source shapes before any revision. Close on no endpoint/code
difference, unsound/importer failure after the allowed revision, or a required
causal control that fails. A successful native matrix still does not pass the
payoff gate. Run full host `make test` and nits plus isolated encoding `make
check`; run this repository's required root `make check` if its source is
changed. Preserve and report real pending snapshot/lint failures rather than
accepting or waiving them. Only after these gates may P1 have a new frozen
performance design and actual endpoint observations.

This design writes no hypothesis ledger, active status, accepted facts, plan,
or shared EggCC source. The parent retains the decision to execute the bounded
probe and append its eventual disposition.
