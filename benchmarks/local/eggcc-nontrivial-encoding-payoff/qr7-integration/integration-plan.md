# Q1 QR7: bounded K7 integration design

Status: feasible as a bounded sidecar plus one memory-consumer bridge. This is
source/retained-graph analysis only. No compiler or engine was built or run,
no new benchmark observation was collected, and no shared source, ledger, or
goal document was changed. Actual optimizer reachability, emitted code, native
correctness, and payoff remain unverified.

## Smallest useful integration

Reuse the Parts32 initialization hook in `dag_in_context/src/lib.rs`, its exact
tuple projection and `If` input binding code, its structural slot-transport
algorithm, and its command-capture/matrix conventions. Replace its arithmetic
recognizer and private theory with K7. Add a query-local `Qr7MustAlias` relation
and a narrowly gated instance of the existing memory store-forward rewrite.
Do not introduce `NoAlias`, a general alias analysis, pointer injectivity, a
new scheduler phase, or a new engine feature.

The actual chain is:

```text
Q7(x) = Q7(y) and R7(x) = R7(y)   exact two nested true Eq assumptions
Pair(Q7(x),R7(x)) = Pair(Q7(y),R7(y))  ordinary congruence
K7(x) = K7(y)                    checked representation identities
x = y                           generic marked K7 cancellation
Addr(p,x) = Addr(p,y)            ordinary congruence, same allocation term
Qr7MustAlias(local-write-addr, local-load-addr)
                                 exact If/unchanged-loop transport and bridge
Get(load,0) = write-val; Get(load,1) = write
                                 existing store-forward transformation
```

Keep both index equality and pointer equality inside the private graph. Export
only the exact relation row for the matched local write/load addresses. A new
small bridge must consume that relation using the same value/state unions as
U0's store-forward rule. This is an added bounded consumer bridge; it must not
be described as execution of U0's untouched same-address rule.

Directly unioning the local pointer classes is a tempting smaller patch, but
would also expose their equality during extraction. LLVM could consume that
change even with EggCC store forwarding disabled, defeating a clean downstream
consumer knockout. The relation bridge isolates the intended consumer and
keeps branch-local value equalities out of the main graph.

## Sound law and admission

For signed i64 `v`, define `q=trunc(v/7)` and `r=v-7*q`. The product `7*q` lies
between `v` and zero, so it is representable; the remainder is in `[-6,6]`.
Exact reconstruction `v=7*q+r` proves K7 injective on all signed i64 words.
Divisor 7 is nonzero and excludes the signed MIN/-1 exceptional case. The
fixture's actual address domain is the smaller `0 <= x,y < 64`.

The recognizer must check integer operand/result types, exact divisor 7 on
both sides of both quotient/remainder constructions, exact `Sub(v,Mul(Div(v,7),7))`
shape (allowing only the two multiplication operand orders), and actual
same-root operand binding through each enclosing `If` input tuple. Q7 and R7
are unmarked. K7 alone is marked. `Pair` and `Addr` need only congruence.

Both Eq assumptions must be true on the lexical path to the allocation/loop;
neither sibling branch nor an unrelated scope supplies a seed. The host must
find the enclosing `If`/`DoWhile` nodes by lexical constructor traversal, not a
shortest arbitrary path through `ContextOf` or cyclic analysis rows. The
feasible witness is the retained `x=y=12,n=8` input. Refuse export on a private
contradiction or engine error; persist those outcomes explicitly.

For the first integration, require a shared `Get(Alloc(...),0)` base of
`PointerT(IntT)`, 64 live cells, the valid-input guard, unchanged pointer
expressions, no free/call/escape before the selected adjacent write/load, and
the expected final free outside the loop. The memory pattern must be exactly
`Load(load_addr, Write(write_addr,write_val,state))`. The key law establishes
equal offsets, and same-base congruence establishes equal pointers. No claim
that arbitrary PtrAdd is injective is required.

Establish bounds from the actual true entry predicate by recursively flattening
only Boolean `And`, then matching `GreaterEq(x,0)`, `LessThan(x,64)`, and the
corresponding y predicates after exact input localization. Match n's 0/limit
predicates for the endpoint contract. Do not assume interval analysis has
decomposed the conjunction. For lifetime admission, walk the typed state chain
from allocation through the initial sentinel store and the loop's carried state;
admit only the observed write/load grammar and final post-loop free. Reject a
call, early free, unknown effect, or escaped allocation rather than extending
the first fragment's effect model.

## Exact retained graph seam

The following IDs belong only to
`../qr7-screen/egraphs/tiger_egraph_0001.json`, SHA-256
`5bb9f38ca657697007cd210d7f97c57c18a789f139ea614ca598dede6bf20e08`.
They are diagnostic witnesses, never constants to put in the compiler.

| Stage | x side | y side | Exact binding |
|---|---|---|---|
| Quotient predicate `Expr-191` | `Expr-188=Div(186,187)` | `Expr-190=Div(189,187)` | Common divisor `Expr-187=7`, predicate under valid scope `Assumption-184`. |
| True quotient scope `Assumption-217` | input slot 4 `186` -> local `219`; quotient slot 8 `188` -> `220` | input slot 3 `189` -> `224`; quotient slot 6 `190` -> `225` | Input `Expr-212`, local Arg `Expr-218`; divisor slot 7 `187` -> `221`. |
| Remainder predicate `Expr-228` | `Expr-223=Sub(219,Mul(220,221))` | `Expr-227=Sub(224,Mul(225,221))` | Both products and both remainder rows are committed. |
| True key scope `Assumption-247` | input slot 4 `219` -> local `267` | input slot 3 `224` -> local `254` | Input `Expr-243`, local Arg `Expr-248`. |
| Same allocation | `Expr-268=PtrAdd(253,267)` | `Expr-255=PtrAdd(253,254)` | `Expr-253=Get(Alloc class 252,0)`. |
| Loop `Assumption-287` | input slot 6 `268` -> loop Arg slot 6 `303` -> output slot 7 `303` | input slot 5 `255` -> loop Arg slot 5 `301` -> output slot 6 `301` | Input `Expr-278`, Arg `Expr-288`, body output `Expr-403`; both pointers pass through unchanged. |
| Hot true If `Assumption-313` | input slot 6 `303` -> local `316` | input slot 5 `301` -> local `315` | Its input is exactly the loop Arg `Expr-288`; local Arg `Expr-314`. |
| Consumer | write `Expr-319=Write(316,317,318)` | load `Expr-320=Load(315,319)` | Loaded value `Expr-324`; loaded state `Expr-321`; replacement value `Expr-317`. |

The exact bridge row is `Qr7MustAlias(Expr-316,Expr-315)`. The consumer unions
`Expr-324` with `Expr-317`, and `Expr-321` with `Expr-319`. These relational joins
show a concrete prospective rule instance; they do not establish that the new
rule has executed or that extraction will select its result.

## Required extensions to the reused scaffold

1. The archived Parts32 `transport` uses `Scalar(Unknown)` for every Bop.
   QR7 has tuple-valued `Load`, so a subsequent `Get` would fail and abort the
   whole loop-body transport. Use `TreeProgram::typecheck()`'s `TypeCache` to
   create the correct unknown scalar/tuple shape for unsupported operators.
   A load contributes two unknown fields; writes and arithmetic contribute
   scalar unknowns. Unknown values must never be treated as fresh equal terms.
2. Retain arbitrary typed same-index passthrough witnesses, including pointers,
   instead of Parts32's `Invariant { index, value: i64 }` constant-only result.
   For each required loop slot i, demand output i+1 is exactly input `Slot(i)`
   through BOTH arms of every nested If. A changed, swapped, or unsupported
   slot remains unknown. Both pointer invariants are necessary.
3. Build a lexical loop-owner map from each visited `DoWhile(initial,body)`.
   At the initialization hook, the Rust AST body context is an `InFunc`
   placeholder such as `" loop_ctx_0"`; `add_context.rs:245-266` creates the
   real InLoop later through context unions. Do not require an already-present
   `Assumption::InLoop` in the AST, parse placeholder names, or treat them as
   globally reusable identities. Use the actual binder and `body.get_ctx()`.
4. Extend the pure expression recognizer with Quotient, Product, and Remainder
   shapes plus explicit expected-context checks. Resolve only exact declared
   tuple projections through nested If inputs. A slot number alone is never
   an equality across scopes. Do not infer a loop input from its position
   without the passthrough proof.
5. Return exact `(write_addr,load_addr)` RcExpr pairs plus receipts. In
   `build_program`, print them using the existing TreeToEgglog/term cache after
   `get_unions_with_sharing` and before function types are emitted. Append
   `(Qr7MustAlias a b)` to initialization. Never append `(union a b)`.

These are bounded adaptations of existing scaffolding. They are not present
in Parts32 unchanged, and success must not be assumed from that prior study.

## Minimal files to change in a new isolated candidate

- `Cargo.toml`, `Cargo.lock`, `dag_in_context/Cargo.toml`, and
  `dag_in_context/Cargo.lock`: reuse the admitted selected-engine dependency
  shape, retargeting only the isolated path. B1 uses the same dependency.
- `dag_in_context/src/scoped_qr7.rs`: recognizer, typed transport, finite
  private graph, independent manual closure, controls, receipts, registered
  mechanism/transport tests. No unrelated sidecar remains enabled.
- `dag_in_context/src/lib.rs`: module declaration and initialization hook.
  Seed `Qr7ForwardEnabled()` except in `consumer-off` mode.
- `dag_in_context/src/optimizations/mem_simple.egg`: declare
  `Qr7MustAlias(Expr,Expr)` and `Qr7ForwardEnabled()`, then add the bridge:

```lisp
(rule ((Qr7ForwardEnabled)
       (Qr7MustAlias write-addr load-addr)
       (= write (Top (Write) write-addr write-val state))
       (= load (Bop (Load) load-addr write)))
      ((union (Get load 0) write-val)
       (union (Get load 1) write)
       (DidMemOptimization "QR7 must-alias store forward"))
      :ruleset mem-simple)
```

Keep U0's original same-address rule unchanged. Only this bridge consumes the
sidecar relation; no new propagation rules or broad main-graph equalities are
needed. The ordinary `helpers()` schedule already saturates `mem-simple` at
`schedule.rs:96`, so initialization is early enough for the existing schedule.
Regenerate the theory at every build_program boundary from that boundary's
current typed AST; never cache scope IDs or reuse facts across snapshots.

The private graph pre-materializes two opaque scoped Word leaves, Q7/R7 rows,
K7 rows, Pair rows, a shared Region term, and Addr rows. It imports two checked
representation unions and the two dynamic component equality seeds. Record
Pair/K7 equality before cancellation, child/Addr equality after saturation,
contradiction status, exact local exports, and consumer event rows. Query
existing globals only; do not grow the graph to manufacture a witness.

## Fixed-input controls and null

All mechanism controls use byte-identical source, schedule, graph rows, dynamic
seeds, native backend, and arguments, except for the named inference/edge.

| Arm | Required result |
|---|---|
| U0 / B1(off) | U0 uses admitted original engine; B1 uses selected engine and integration disabled; match baseline output/code. |
| SeedOnly | Same host traversal/materialization/seeds, no inference/query/export; baseline code. |
| Encoding | Pair and K7 outputs equal, x/y equal, Addr equal, exact relation exported, bridge event recorded. |
| Manual | Independent finite congruence + marked-injectivity closure over the same rows/seeds; same exports/emitted/native code as Encoding. |
| cancellation-off | Only K7's annotation disabled; equal Pair/K7 outputs remain, x/Addr equality absent, no export. |
| identity-off | Remove only K7-to-Pair representation unions; paired component seeds remain, no x/Addr equality or export. |
| x-rescue | With cancellation disabled, inject the captured private x=y intermediate; Addr equality/export/consumer return. |
| key-rescue | With representation unions disabled, inject captured K7 output equality; cancellation/export/consumer return. |
| query-off | Same inferred graph, final Addr equality query not run; no export. |
| transport-off | Private result remains true; required pointer loop transport disabled; no local relation exported. |
| bridge-off | Private and transport receipts remain true; relation row withheld; no bridge event. |
| consumer-off | Exact Qr7MustAlias row remains; Qr7ForwardEnabled absent; no bridge event/value-state unions. |
| PrimitiveOnly | Same finite rows/seeds and primitive slots; inspect only primitive fields; no equality-sort inference/query/export. |

The null can see the common primitive 7 and bounds/size literals. K7 has only
one equality-sort Word child; Pair has two equality-sort Word children. There
is no conflicting primitive child that emits the final fact, and the common
divisor does not decide equality of dynamic x/y. Keep all branch seeds; do not
turn this into a weaker no-seeds control. A hand-written multi-rule key
theorem can equal the encoding's logical power; that is allowed and must be
the fair comparator, without claiming unique expressiveness.

Semantic negatives: reuse `omit-quotient-v2.bril`, `omit-remainder-v2.bril`,
and `different-divisor.bril` unchanged from the screen, including their
initialized sentinel. Each witness must remain `-24\n`, never `28\n`. Add
registered shape negatives for wrong context/type/root, unknown/zero/negative
divisor (rejected before evaluation), one changed pointer slot, one changed
inner If arm, swapped pointer slots, different allocation base, and absent
context. Near-boundary positive indices are 0 and 63; n is 0,1,8,1024. Native
semantic negatives should use valid initialized programs, not malformed IR.

## Exact next actions and command shapes

The live `/private/tmp/eggcc-parts32-candidate` no longer exists. Reconstruct
fresh QR7 roots from the retained complete base archives, then reuse selected
files from `parts32-integration/final-source.tar`; do not copy a live prior
checkout or replay the old write-candidate.py script unchanged. These commands
have NOT been run by this analysis:

```sh
cd /Users/saul/p/egglog-encoding
mkdir /private/tmp/eggcc-qr7-candidate /private/tmp/encoding-qr7-candidate
tar -xf benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/eggcc-parts32-candidate.tar -C /private/tmp/eggcc-qr7-candidate
tar -xf benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/encoding-parts32-candidate.tar -C /private/tmp/encoding-qr7-candidate
tar -xOf benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/final-source.tar eggcc/dag_in_context/src/scoped_reasoning.rs
```

Before compilation, author `qr7-integration/admit.py`, `write-candidate.py`,
`run.py`, and `matrix.py` by adapting the retained scaffolds. Admission must
verify the two base-archive hashes in `parts32-integration/source-admission.json`,
the fresh U0 commit, both lockfiles, selected dependency/engine deltas, runtime,
and exact inputs. The engine archive is revision
`392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`; U0 is
`a0bbec127f83249074a46af3fd6f6126c90fe0fb`. No new engine changes are needed
for K7 injectivity. Preserve admitted generic deltas if reusing that exact
engine cohort; do not quietly change the selected engine between arms.

The first commands after those new scripts have been authored are:

```sh
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/admit.py
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/write-candidate.py
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/run.py mechanism-tests \
  cargo test --offline --locked --manifest-path /private/tmp/eggcc-qr7-candidate/dag_in_context/Cargo.toml scoped_qr7 -- --nocapture
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/run.py release-candidate \
  cargo build --offline --locked --release --bin eggcc
```

The adapted runner's cwd is `/private/tmp/eggcc-qr7-candidate`; it sets the
environment below, captures numeric failures, and uses a finite build timeout.
Its freeze step copies the just-built eggcc and its build-generated Tiger into
`qr7-integration/bin/`, hashing both. Do not substitute the admission Tiger
without checking source/build identity. Admission starts from U0 source;
read the archived Parts32 sidecar and hook for reuse rather than overwriting
the new lib.rs wholesale with the Parts32 implementation.

The first actual-host probe must use the unchanged source and capture a fresh
receipt directory, egraphs, sidecar receipts, interpretation, and emitted Bril:

```sh
EGGCC_ROOT=/private/tmp/eggcc-qr7-candidate EGGCC_SCOPED_MODE=encoding EGGCC_SCOPED_EVIDENCE=/tmp/qr7-fresh/evidence \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/bin/eggcc \
  --with-context --run-mode optimize --interp \
  --egraph-out-dir /tmp/qr7-fresh/egraphs --run-data-out /tmp/qr7-fresh/optimize.json \
  benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-screen/source.bril
```

Use the future capture runner for this argv so stdout/stderr, actual environment,
identities, exit/timeout and errors are durable. Follow the existing environment:
LLVM 18, single Rayon thread, pinned Rust 1.91.0, finite compiler/native timeouts
(180s/30s), memory-pressure blocking disabled. Build one candidate binary and
Tiger; use runtime from admission. First verify nonzero registered focused
test counts; then run the causal/semantic matrix. After those pass, run engine
`make check` and EggCC's root `make test` plus its required lint/format checks,
retaining unrelated failures/snapshots rather than accepting them.

Lower each emitted arm independently with admitted U0 and its same runtime:

```sh
benchmarks/local/eggcc-nontrivial-encoding-payoff/admission/bin/eggcc \
  --with-context --run-mode llvm --optimize-egglog false \
  --optimize-bril-llvm O3_O3 -o /tmp/qr7-fresh/native/program \
  --llvm-output-dir /tmp/qr7-fresh/native/program.ll \
  --run-data-out /tmp/qr7-fresh/native/lower.json /tmp/qr7-fresh/optimized.bril
```

The initial falsifier is the exported relation/event plus disappearance of
the source hot load in Encoding/Manual, with baseline retained by the fixed
input knockouts. If the recognizer/transport fails, the one allowed revision
must be justified by a concrete captured seam, with original evidence kept.
Do not redesign scope/alias infrastructure to rescue an unsupported case.

## Endpoint and stop condition

The baseline's executed C `main` already has zero memory loads after LLVM
inlining. Its remaining endpoint is a vectorized reduction with two cyclic
basic-block components. The matched early-forward manual source has an acyclic
closed arithmetic sum. Inspect both `main` and exported Bril `_main`, and
compare actual-entry CFG/assembly using `qr7-screen/entry-inspection.py` as the
reference; a removed exported load alone does not pass the endpoint gate.

Only after mechanism/correctness/native gates pass should a separately reviewed
prospective timing design compare U0, B1, SeedOnly, Manual, and Encoding. Use
dynamic `(12,12,10000000)` and exact output `49999995000000\n`, include process
startup/argument parsing/allocation/computation/printing, and retain each
per-workload repeated observation plus an independent confirmation session.
The old six-pair manual pilot sizes an opportunity only. It supplies no actual
integration measurement, no engine overhead estimate, and no acceptance claim.

Close Q1's payoff if the bounded integration cannot reach the bridge, if its
valid negatives export, if Manual is not matched fairly, or if its actual
native entry fails to reproduce a measurable early-forward advantage. A new
relation, successful proof chain, or changed IR alone does not achieve the
goal. Q1 is injectivity-only; it must not be advertised as requiring disequality.
