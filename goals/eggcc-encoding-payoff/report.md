# How injectivity and disequality remove work in EggCC

This study found nontrivial EggCC uses for generic equality-sort reasoning.
QR7 is the strongest substantive-consumer injectivity-only result: cancellation
of a lossless quotient/remainder key derives an exact local must-alias relation,
which an added bounded store-forwarding bridge consumes. The resulting
phase-ordering change removes the loop from the actual process entry. In an
independent 112-cycle confirmation, programs built with the sidecar active use
about 44.9% less elapsed time than programs from the pinned untouched compiler
on the fixed hot workload, including fresh process startup.

Parts32 remains the strongest combined injectivity-and-disequality result. It
uses marked forward disequality, representation equality, and sibling-guarded
reverse disequality together to remove a redundant comparison from generated
hot loops. Across three constructed workloads and two independent
prospectively balanced sessions, programs built with the sidecar active use
about 7.5% to 8.6% less elapsed time than programs from the pinned untouched
compiler. Every required timing gate passes for both studies, with exact
outputs and their respective placebo checks.

The results are deliberately narrow: fixed constructed Bril programs on Apple
Silicon, not an EggCC-suite estimate or a compiler-time claim. Faithful manual
closures derive the same results and match the winning emitted code and native
instructions, so the generic encoding has no claimed monopoly on these results.
The evidence shows that reusable generic steps can feed actual EggCC consumers
and change measured generated-program runtime. QR7 establishes no disequality
contribution; Parts32 establishes the combined mechanism.

Same-mask is an independent, smaller replication rather than an earlier stage
of Parts32. It uses unmarked reverse congruence and one marked translation to
remove a different comparison, producing about 1.9% less elapsed time in its
own 32-cycle campaign. Parts32 supplies the stronger causal example and the
larger separately measured effect; their observations are never pooled.

This document is an explanation for a reader who knows egglog but has not seen
the experiments. It follows each result from source facts through private
inference and the compiler boundary to generated code and timing. Reproduction
commands and immutable artifact identities remain in the linked experiment
guides and the [reference](reference.md).

## The mathematical rules

For equality-sort values, `(disequal a b)` asserts a symmetric constraint. In
the not-equal-relation representation, called NEE here, one ordered pair of
canonicalized endpoints is stored and reads probe both orientations;
structurally derived pairs are not stored. Three logical implications matter
here.

**Injective cancellation.** For a marked constructor `F`, equal applications
have equal equality-sort children:

```text
F(a1,...,an) = F(b1,...,bn)  =>  ai = bi
```

Primitive fields are checked directly. If equal marked applications have
unequal primitive fields, the scheduled `injectivity` rule executes a panic;
primitive disequality is not stored.

**Forward disequality through a marked constructor.** The contrapositive of
cancellation lets any unequal child separate the parents:

```text
ai != bi  =>  F(a1,...,ai,...,an) != F(b1,...,bi,...,bn)
```

This is valid only when `F` is injective over the complete marked input tuple.

**Reverse disequality with equal siblings.** Ordinary congruence gives a useful
rule even when the constructor itself is unmarked:

```text
G(a1,...,ai,...,an) != G(b1,...,bi,...,bn)
and aj = bj for every j != i
  => ai != bi
```

The equal-sibling condition matters. From `G(a,b) != G(c,d)` alone we know only
`a != c OR b != d`; neither child disequality follows individually. When all
but one pair are equal, the remaining pair must differ.

The generated cancellation and primitive-panic rules run only when the
`injectivity` ruleset is explicitly scheduled. The separate
`known-disequal?` predicate performs a finite read-only search over committed
applications and asserted disequalities, following marked-forward and
equal-sibling reverse edges without saturation. It creates no applications,
unions, or persistent derived-pair rows; an undefined result means unknown. For
primitive children it compares values immediately. Containers are outside the
encoding. Contradiction normalization is a separate disequality schedule and
does not run `injectivity`.

## How derived facts reach generated code

The source programs are unchanged between each baseline and Encoding arm. Each
experiment runs through EggCC's ordinary compilation pipeline. For each
admitted source context, the sidecar builds a fresh private equality-sort graph
and adds analysis terms for arithmetic already present in the source. QR7 runs
the scheduled cancellation rules and checks the resulting private equality;
Parts32 asks the read-only disequality predicate over the committed graph. In
both cases, the Rust recognizer maps the successful private result back to
EggCC expressions it had already matched. The sidecar runs while EggCC is
writing the egglog program, so the exported fact is written beside the
program's own terms: QR7 adds one `Qr7MustAlias` row over the source address
expressions, while Parts32 adds one union between the source `Eq` term and a
`false` constant with the same type and branch context. Both are asserted by
the initialization rule before any optimization ruleset runs. The timing
campaigns measure the resulting native programs.

`K7` and `Parts32` therefore do not become Bril or runtime operations. They are
compile-time analysis constructors. The connection to performance has five
separate stages:

| Case | Facts read from the source path | Fact derived in the private graph | Fact exported to EggCC | Emitted-code change | Generated-runtime result |
| --- | --- | --- | --- | --- | ---: |
| QR7 | `q(x)=q(y)`, `r(x)=r(y)` | `x=y`, then `Addr(region,x)=Addr(region,y)` | `Qr7MustAlias(write_addr,load_addr)` | `load(pj)` becomes the just-stored `count` | 44.9% less elapsed time |
| Parts32 | `x!=y`, `low(x)=low(y)` | `high(x)!=high(y)` | `Eq(high(x),high(y))=false` | high-part calculation, comparison, and `99` arm disappear | 7.5%–8.6% less elapsed time |

The implementation has three layers, and only the first is reusable:

| Layer | What it is | What it knows |
| --- | --- | --- |
| Reusable engine | `:injective`, generated cancellation and primitive-panic rules, the `injectivity` schedule, and read-only `known-disequal?` search with marked-forward and equal-sibling reverse edges | constructor schemas, committed rows, unions, and asserted disequalities; no arithmetic |
| Case-specific sidecar | an exact source recognizer; a fresh private graph with opaque words, a marked constructor and its `Pair` representation invariant, imported path facts, and one narrow export | the arithmetic law that justifies the mark, and which source expressions the private terms represent |
| Bounded EggCC consumer | QR7 adds a `Qr7MustAlias` store-forwarding rule in `mem-simple`; Parts32 adds no downstream rule, so existing constant-predicate consumers act on the exported `Eq=false` union | ordinary EggCC relations, unions, and rewrites |

Both sidecars have the same shape. Each introduces one private unary
constructor over the opaque source word, marks only that constructor, and
unions each application with an unmarked `Pair` of the component terms that
the source branch predicates compare. Together, the marked unary wrapper and
the representation union encode the host-checked claim that the component
tuple uniquely determines the word.

The cases consume the mark differently. QR7 needs the positive fact `x=y`, so
it runs the generated cancellation rule in the `injectivity` schedule and
reads the resulting equality. Parts32 starts from `x!=y` and needs the negative
fact `high(x)!=high(y)`. A union cannot add a disequality, so Parts32 asks the
read-only `known-disequal?` search instead. That search uses the same mark as a
forward edge and ordinary congruence as a sibling-guarded reverse edge. The
reverse edge lets the equal low halves select the high halves as the pair that
must differ.

The next two sections follow those stages one at a time. In each case, the
domain-specific code recognizes and exports a narrowly scoped fact; the
injectivity and disequality steps in the middle are generic.

The arm names recur in the evidence. **U0** is the pinned untouched compiler.
**Off** in QR7 and **B1** in Parts32 use the same retargeted engine dependency
as Encoding, but the sidecar is disabled at entry and constructs no private
graph; this separates the inference from the dependency change. **SeedOnly**
populates the same private graph and seeds,
including ordinary e-graph rebuilding, but skips scheduled cancellation or the
read-only query, the Manual closure, and export. **PrimitiveOnly** preserves the
same private terms and seeds but permits no equality-sort inference. The marked
`K7` and `Parts32` constructors have no primitive fields, so this control has no
result and exports nothing.
**Manual** computes the same finite closure directly, while **Encoding** uses
the generic engine.

## QR7: injectivity reaches store forwarding

### The optimization opportunity

The [QR7 source fixture](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/fixtures/source.bril)
checks two integer arguments before entering a store/load loop. In simplified
form, the relevant path is:

```text
qx = trunc(x / 7);  qy = trunc(y / 7)
if qx == qy {
    rx = x - 7*qx;  ry = y - 7*qy
    if rx == ry {
        pi = p + x;  pj = p + y
        for count in 0..n {
            store(pi, count)
            value = load(pj)
            sum = sum + value
        }
    }
}
```

Store forwarding needs `pi=pj`. The two guards contain enough information:
for any signed i64 `v`, let `q(v)=trunc(v/7)`, `r(v)=v-7*q(v)`, and
`K7(v)=(q(v),r(v))`. Exact reconstruction
`v=7*q(v)+r(v)` makes the full key injective. Quotient or remainder alone is
not injective. Division by positive seven is total for signed i64, and the
product `7*q(v)` is representable. In the tested compiler, congruence can carry
equal inputs to equal outputs, but no applicable rule reconstructs a word from
its quotient and remainder by seven. The two address terms therefore remain in
different e-classes when same-address store forwarding looks for a shared one.

### What the experiment adds

The [QR7 sidecar](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/scoped_qr7.rs)
recognizes this exact quotient/remainder shape, the enclosing true branches,
bounded indices into one live 64-cell allocation, and unchanged loop slots. It
then creates the following schematic sidecar model in a fresh graph. Here `x`,
`y`, and `region` name private opaque terms created for the matched source
values and allocation:

```text
(constructor Q7 (Word i64) Word)
(constructor R7 (Word i64) Word)
(constructor K7 (Word) Key :injective)
(constructor Pair (Word Word) Key)
(constructor Addr (Region Word) Pointer)

; Facts imported from the two true branch guards.
(union (Q7 x 7) (Q7 y 7))
(union (R7 x 7) (R7 y 7))

; Private representation of the lossless key.
(union (K7 x) (Pair (Q7 x 7) (R7 x 7)))
(union (K7 y) (Pair (Q7 y 7) (R7 y 7)))

(let addrx (Addr region x))
(let addry (Addr region y))

(run-schedule (saturate injectivity))
```

This is schematic egglog with the same constructors and unions as the captured
program. Only `K7` is marked. The host justifies that annotation from exact
reconstruction; the generic engine does not discover the arithmetic
injectivity fact. `Q7`, `R7`, `Pair`, and `Addr` remain unmarked.

Two compiler-boundary additions connect the derived private fact to EggCC. The
host exports an exact `Qr7MustAlias(write_addr,load_addr)` relation, and the
[added `mem-simple` bridge](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/eggcc-candidate-r1.patch)
uses that relation only for a load whose state is the immediately preceding
write. It performs the same loaded-value and state unions as ordinary
same-address store forwarding. The result does not rely on the untouched
same-address rule learning this new relation by itself.

The distinction is visible in the rule shapes. The existing rule uses one
address variable for both operations, so the two addresses must already be in
the same main-graph e-class. The added rule uses separate `write_addr` and
`load_addr` variables plus the scoped `Qr7MustAlias` premise:

```text
existing: Write(addr, value, state); Load(addr, write)
added:    Qr7MustAlias(write_addr, load_addr);
          Write(write_addr, value, state); Load(load_addr, write)
```

### How the equality is derived

| Step | New fact | Why it follows |
| ---: | --- | --- |
| 1 | `Q7(x)=Q7(y)` and `R7(x)=R7(y)` | the two enclosing branches are true; EggCC's context labels record each predicate and direction, and the recognizer imports those path facts |
| 2 | `Pair(Q7(x),R7(x)) = Pair(Q7(y),R7(y))` | ordinary congruence |
| 3 | `K7(x)=K7(y)` | each `K7` application is unioned with its `Pair` representation |
| 4 | `x=y` | the generated cancellation rule for marked `K7` |
| 5 | `Addr(region,x)=Addr(region,y)` | ordinary congruence with the same region |
| 6 | `Qr7MustAlias(write_addr,load_addr)` | the final private equality check confirms `Addr(region,x)=Addr(region,y)`; the recognizer returns the source write and load addresses it had already matched to those private offsets, and the host emits the relation |

Step 4 is the inference contributed by injectivity. Conceptually, the
annotation generates this rule in the explicit `injectivity` schedule:

```text
K7(x) = K7(y)  =>  x = y
```

The captured graph makes the boundary especially visible. Before running that
schedule, `Pair` equality and `K7` equality are already true, while word and
address equality are false. After the schedule, all four are true. No
disequality fact or `known-disequal?` query contributes to QR7.

### How the derived equality changes the program

The must-alias bridge changes the retained optimized Bril at the load site as
follows. Variable names are simplified here; the complete
[baseline](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/final-r1/matrix/positive/u0/optimized.bril)
and [Encoding](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/final-r1/matrix/positive/encoding/optimized.bril)
files are retained.

```text
Untouched EggCC                  With Qr7MustAlias

store(pi, count)                store(pi, count)
value = load(pj)                sum = sum + count
sum = sum + value
```

The exported fact changes the program before lowering: EggCC replaces the
loop's `load(pj)` contribution with `count`, exposing `sum += count`. The
baseline emitted Bril still contains the load because EggCC has not connected
the quotient/remainder guards to address equality. During later optimization,
the remainder guard becomes an explicit `x==y` branch; on the loop path LLVM
uses that dynamic equality to remove the memory operations and vectorize the
summation. In the Encoding program the memory-independent recurrence is visible
earlier, and LLVM replaces the loop with a closed-form sum. The native
difference is therefore a remaining vector/scalar loop versus no loop, not a
load-count difference at process entry.

| Observed endpoint | Untouched U0 | Encoding |
| --- | ---: | ---: |
| Optimized Bril loop value | `load(pj)` | `count` |
| Actual process-entry instructions | 91 | 55 |
| Internal backward branches | 2 | 0 |
| Hot elapsed time, normalized to U0 | 1.00000 | 0.55055 |

Thus the measured 44.9% reduction follows this chain:

```text
marked K7 cancellation
  -> x=y
  -> equal write/load addresses
  -> early store forwarding in EggCC
  -> explicit arithmetic recurrence in emitted Bril
  -> loop-free native process entry
  -> less generated-program runtime
```

This is a phase-ordering result. The evidence does not assign the final native
change to a particular LLVM pass. Although whole-executable hashes differ,
emitted-Bril hashes and process-entry instruction hashes are identical within
the baseline group and within the winning Encoding/Manual group.

### Why the improvement is attributed to this chain

The controls stop or restore the inference chain at specific boundaries:

| Control | Last relevant fact | Emitted/native result |
| --- | --- | --- |
| representation identities removed | equal component `Pair` values | baseline |
| `K7` injective mark removed | equal `K7` values, but no `x=y` | baseline |
| exact key-equality rescue | `K7(x)=K7(y)` supplied directly | optimized |
| exact `x=y` rescue | word equality supplied directly | optimized |
| address query or export bridge removed | derived address fact cannot reach EggCC | baseline |
| consumer disabled | `Qr7MustAlias` survives, store forwarding does not run | baseline |
| faithful Manual closure | same finite closure without the generic engine | identical optimized code |

SeedOnly and PrimitiveOnly also stay at baseline. `K7` has no primitive fields,
so comparing its primitive metadata cannot establish equality of the two dynamic
words. The `transport-off` label suppresses export at the bridge gate while
transport computation still runs; it is an export-gate placebo rather than a
direct transport ablation.

The prospectively frozen runtime design uses all 14 arms in a balanced Williams
schedule. A 14-cycle screen is followed by an independent 112-cycle
confirmation, with complete 14-cycle blocks as bootstrap units. Each measured
row times ten serial fresh processes; the hot input executes ten million loop
iterations and prints exactly `49999995000000`. The confirmation contains
3,136 measured rows across the hot input and a separately reported zero-trip
control.

| Confirmation comparison | Paired median ratio | Complete-block bootstrap 95% |
| --- | ---: | ---: |
| Encoding / U0 | 0.55055 | [0.54710, 0.55750] |
| Encoding / Off | 0.55028 | [0.54417, 0.55228] |
| Encoding / SeedOnly | 0.55210 | [0.54940, 0.55442] |
| Encoding / PrimitiveOnly | 0.55338 | [0.54958, 0.55707] |
| Manual / U0 | 0.55741 | [0.55377, 0.55986] |

All five primary hot comparisons pass the frozen upper-95%-below-0.99 gate.
The zero-trip control has no speedup requirement; its Encoding/U0 ratio is
0.98926 with interval [0.98367, 1.00033]. Compiler and lowering time are
excluded. The retained correctness matrix contains 37 compiler cases and 177
native checks, including omitted quotient/remainder premises, a changed
divisor, a changed loop pointer, and missing context.

The [causal inspection](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/final-r1/inspection.json),
[actual-binary inspection](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/actual-binary-inspection-r1.json),
and [independent runtime verification](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/timing-r1/independent-verification.json)
are the result authorities. Their frozen source identities and exact fields are
listed in the [reference](reference.md#qr7-authorities-and-records).

## Parts32: injectivity and disequality remove a comparison

### The optimization opportunity

The [Parts32 source fixture](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/fixtures/source.bril)
contains this branch inside a loop:

```text
for count in 0..n {
    if x == y {
        score = 5
    } else {
        if low(x) == low(y) {
            if high(x) == high(y) { score = 99 }
            else                  { score = 7 }
        } else {
            score = 3
        }
    }
    sum = sum + score
    x = x + 4294967297
    y = y + 8589934593
}
```

For any signed i64 word `x`, define

```text
low(x)     = x & 0xffffffff
high(x)    = (x - low(x)) / 2^32
Parts32(x) = (low(x), high(x))
```

The subtraction is representable and exactly divisible, so `Parts32` is a
lossless representation. On the nested path, the complete words differ while
their low parts agree. Their high parts must therefore differ, making the
`score=99` arm unreachable. Untouched EggCC records those branch directions but
has no rule that supplies the 32-bit partition invariant connecting the whole
word to its low and high parts. Without that invariant, congruence alone cannot
derive the high-half result, so the compiler retains the high-part calculation,
comparison, and branch.

### What the experiment adds

The source program does not construct `Parts32`. The
[Parts32 sidecar](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/eggcc-final.patch)
introduces it only in a fresh compile-time graph to model the existing
`bitand`, subtraction, and division expressions. Schematically, the graph is:

```text
(constructor Low (Word i64) Word)
(constructor High (Word i64 i64) Word)
(constructor Parts32 (Word) Parts :injective)
(constructor Pair (Word Word) Parts)

(disequal x y) ; imported from the outer false branch
(union (Low x 4294967295) (Low y 4294967295)) ; inner true branch

(union (Parts32 x) (Pair (Low x 4294967295) (High x 4294967295 4294967296)))
(union (Parts32 y) (Pair (Low y 4294967295) (High y 4294967295 4294967296)))
```

Only unary `Parts32` is marked. `Pair`, `Low`, and `High` are unmarked. The
mask and divisor are primitive metadata on the unmarked constructors; comparing
those constants cannot establish the disequality between the dynamic words or
their high parts.

After populating this graph, the retained harness runs `injectivity` and then
issues read-only `known-disequal?` queries for the word, representation, pair,
and high-part pairs. The schedule can add equality unions, but it does not
derive or store this disequality chain; here the `Parts32` annotation matters
because the later query reads its marked-constructor metadata when traversing
the forward implication. If the synthetic `hx`/`hy` query succeeds, the
recognizer returns the exact source `Eq` predicate whose operands it had already
matched to those high terms. The host then unions that predicate with a
context-matched Boolean `false` in EggCC's graph. The private seeds,
representation terms, and intermediate endpoint pairs never enter EggCC's main
graph.

Unlike QR7, Parts32 adds no constructor-specific downstream optimization rule.
Once the exact contextual equality is false, existing constant-predicate
consumers remove the unreachable arm; the evidence does not identify one of
them as the exclusive consumer.

### How the disequality is derived

| Step | Entailed proposition | Why it follows |
| ---: | --- | --- |
| 1 | `x!=y` | the outer `x==y` branch is false |
| 2 | `Parts32(x)!=Parts32(y)` | forward disequality through marked `Parts32`, the contrapositive of injectivity |
| 3 | `Pair(low(x),high(x)) != Pair(low(y),high(y))` | the two representation identities |
| 4 | `high(x)!=high(y)` | reverse disequality through unmarked `Pair`, using `low(x)=low(y)` |
| 5 | `Eq(high(x),high(y))=false` | the scoped query result is applied to the exact source predicate |

Injectivity contributes step 2. Disequality reasoning contributes step 4. The
equal-low premise is what makes the reverse step definite: from unequal pairs
alone, either child could differ; once the low children are equal, the high
children must be the unequal pair. Both mechanisms are needed for this
inference.

Logically, the derivation above flows from `x!=y` to `high(x)!=high(y)`.
Operationally, the query searches backward from the high-child goal. It uses
the equal low siblings to move to the two `Pair` results. Because each
representation union places the corresponding `Pair(...)` and `Parts32(...)`
results in the same e-class, the resulting parent goal can be matched against
the `Parts32` rows. The search then uses the mark to reduce the goal to the
child pair `x`, `y`, where it meets the asserted `x!=y`. `known-disequal?`
itself inserts no derived disequality pair. The
experiment's wrapper rules retain private zero-argument success markers
(`WordKnown`, `PartsKnown`, `PairKnown`, and `HighKnown`) for diagnostics; those
rows carry no endpoints and are never exported.

### How the derived disequality changes the program

The retained optimized Bril shows the missing link between the private
inference and native performance. In simplified form:

```text
Untouched EggCC                       With high(x) != high(y)

hx = (x - low(x)) / 2^32             score = 7
hy = (y - low(y)) / 2^32
target = hx == hy
if target { score = 99 }
else       { score = 7 }
```

The complete [baseline](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/final-reviewed/matrix/positive/u0/optimized.bril)
and [Encoding](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/final-reviewed/matrix/positive/encoding/optimized.bril)
files show that the high calculations, comparison, `99` block, and associated
control-flow plumbing all disappear. The emitted file falls from 209 to 155
lines and from six to five Bril branch instructions. In the inspected native entry, the
baseline retains the scalar `99`/`7` target shape and has no vector i64
operations; Encoding removes that target shape and contains vector i64
operations. The timing result measures this complete code change rather than
attributing the effect to one LLVM pass.

```text
marked Parts32 forward disequality
  -> unequal complete representations
  -> equal-low reverse disequality
  -> high(x)!=high(y)
  -> target equality is false in EggCC
  -> dead high-part computation and branch disappear
  -> a vectorized native loop
  -> less generated-program runtime
```

### Why both mechanisms and the compiler boundary matter

The causal arms isolate successive inference boundaries:

| Disabled or restored piece | Last relevant fact | Emitted/native result |
| --- | --- | --- |
| forward `Parts32` mark removed | `x!=y` and equal lows | baseline |
| representation identities removed | `Parts32(x)!=Parts32(y)` | baseline |
| equal-sibling reverse search removed | unequal `Pair` values | baseline |
| final high query or export bridge removed | derived fact remains private | baseline |
| application of `Eq=false` disabled | exported disequality result survives | baseline |
| exact `high(x)!=high(y)` rescue | final needed fact supplied directly | optimized |
| full generic Encoding or faithful Manual closure | complete chain | identical optimized code |

Disabling one named non-weakly-linear false-`If` rule does not restore baseline;
another existing consumer, later extraction, or the backend can use the
constant predicate. The evidence therefore identifies the contextual
`Eq=false` application as essential without claiming one exclusive downstream
rewrite.

The actual-host integration follows typed loop-input projections and rejects
changed masks or divisors, missing path facts, changed loop slots, unrelated
contexts, and unsupported expressions. The retained matrix performs 200 native
checks plus emitted/source interpreter checks. U0, B1, and SeedOnly have
identical emitted and native entry code; Manual and Encoding also match each
other. The implemented generic derivation is a multi-stage closure over dynamic words
and representation children, rather than a primitive-field contradiction or
Boolean endpoint check. An equivalent specialized rule could encode the result
directly; the faithful Manual arm confirms that the generic encoding has no
unique logical power.

The generated-runtime campaign measures immutable native programs, including
process startup, over 90 balanced cycles per independent session. Every
observation contains 32 fresh processes and one million loop iterations per
process. Each complete session retains 1,350 measured rows, 45 warmups, and
eight passing process checks. The frozen acceptance comparison succeeds in all
six workload/session cells:

| Workload | Session | Encoding / U0 | Complete-block bootstrap 95% |
| --- | ---: | ---: | ---: |
| equal-low-positive | 1 | 0.92426 | [0.92354, 0.92549] |
| signed-min-boundary | 1 | 0.92431 | [0.92220, 0.92466] |
| signed-max-crossing | 1 | 0.92504 | [0.92404, 0.92843] |
| equal-low-positive | 2 | 0.91952 | [0.91526, 0.92272] |
| signed-min-boundary | 2 | 0.91492 | [0.91242, 0.91724] |
| signed-max-crossing | 2 | 0.91398 | [0.91143, 0.91670] |

Manual/U0 and Encoding/B1 also satisfy the frozen upper-bound threshold in
every cell. The B1/U0, SeedOnly/B1, and Encoding/Manual placebo validity check
passes, and the verifier reports no consistent greater-than-one-percent
directional placebo shift. These per-session results are not pooled. The
complete mechanism, raw evidence, and independent verification are in the
[Parts32 report](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/report.md).

## A smaller same-mask replication

The source contains this shape inside a loop:

```text
if ((x & m) == (y & m)) {
    delta = 3;
} else {
    if ((x + 7) == (y + 7)) delta = 99;
    else delta = 7;
}
```

On the outer false branch, `(x & m) != (y & m)`. Because both expressions use
the same dynamic `m`, reverse disequality gives `x != y`. Addition by the fixed
word `7` is a bijection modulo `2^64`, so a marked `Shift7` constructor carries
that fact forward:

```text
Mask(x,m) != Mask(y,m)
  => x != y
  => Shift7(x) != Shift7(y)
  => Eq(x+7,y+7) = false
```

`Mask` is intentionally unmarked: bitwise-and is not injective. The first step
uses only congruence contraposition and the equal mask sibling. `Shift7` is
marked because a fixed wrapping translation is injective. `x`, `y`, and `m`
are opaque equality-sort values; no primitive field comparison can establish
the conclusion.

EggCC runs this query in a fresh private e-graph tied to the exact branch and
source projections. It exports only the target contextual Boolean equality as
false. The branch-local `x != y` fact never enters EggCC's global graph. This
scope boundary prevents a fact from escaping into a sibling branch or surviving
after later global equality collapse.

Before the sidecar inference, LLVM retains a comparison and conditional
selection in the hot native loop. After the target equality is set to false,
the `99` arm, comparison, and selection disappear. The baseline loop has 12
instructions; Manual and Encoding have the same 10-instruction loop. Code shape
is causal evidence, while the repeated process measurements establish the
runtime effect.

The controls isolate both generic steps and the compiler boundary:

| Treatment | Private result | Native result |
| --- | --- | --- |
| U0, B1, SeedOnly | no derived target | baseline |
| reverse step disabled | parent disequality only | baseline |
| exact `x!=y` rescue | target disequality restored | optimized |
| `Shift7` annotation removed | `x!=y`, no target | baseline |
| exact target rescue | target disequality restored | optimized |
| query, bridge, or main-graph application disabled | internal facts retained as applicable | baseline |
| primitive-only treatment | no dynamic disequality path | baseline |
| faithful Manual and generic Encoding | same target fact | byte-identical optimized code |

The final application knockout is the downstream-consumer test. It retains all
private query results and the exported false value, but withholds the single union
into EggCC's graph; native code returns to baseline. Disabling only the named
non-weakly-linear false-`If` rewrite does not restore baseline. The interval
false-`If` rule remains enabled, and later extraction or the backend can also
consume the constant predicate; this ablation does not identify which alternate
consumer acted. The necessary boundary is therefore the target Boolean
application, not one specific downstream rewrite.

The frozen confirmation runs 200 million loop iterations per observation.
Ratios pair arms within each balanced cycle, and the confidence interval
bootstraps complete cycles with a fixed seed.

| Comparison | Paired median ratio | Bootstrap 95% interval |
| --- | ---: | ---: |
| Encoding / U0 | 0.98084 | [0.98042, 0.98164] |
| Manual / U0 | 0.98087 | [0.98004, 0.98230] |
| B1 / U0 | 1.00034 | [0.99860, 1.00183] |
| Encoding / Manual | 0.99964 | [0.99847, 1.00088] |

The identical-code placebo comparisons contain one, while both implementations
that remove the comparison show the same improvement. Native layout was not
independently controlled, so the study cannot assign the entire effect to
dynamic instruction count rather than the resulting layout. The complete
experiment and raw evidence are in the [same-mask report](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/candidate-same-mask/report.md).

## Supporting actual-host examples

Three further integrations show that the same closure applies beyond bit masks
and word decomposition:

- **Affine** cancels an invertible two-word affine key, uses an equal sibling to
  isolate disequality through unmarked wrapping addition, and carries it through
  marked multiplication by an odd word. It changes native code but has no
  timing result.
- **Route** cancels a tagged pair built from a common dynamic selector, then
  uses unmarked Add reverse disequality and marked odd-multiply forward
  disequality. Its intermediate rescues and causal knockouts behave as
  predicted.
- **Sort** cancels `(smin(a,b), smax(a,b), orientation)`, retaining the bit that
  makes sorting reversible, before the same reverse/forward tail. Its two
  intermediate rescues behave as predicted.

These are mechanism replications, not additional performance claims. Their
test counts and validation boundaries remain in the
[Route](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/route-integration/report.md),
[Sort](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/sort-integration/report.md),
and [Affine](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/affine-integration/report.md)
reports.

## What the search did not find

The earlier `ObservedBool(true) = ObservedBool(false)` findings detected two
real wrapping-interval bugs, but they are excluded here. One direct primitive
Boolean-conflict rule can reproduce them; disequality is unnecessary.

The bounded current EggCC corpus contains no exact quotient/remainder or packed
word equality consumer beyond the constructed examples. Ordinary tuple equality
already exposes projections through existing `Get`/`Concat` rules. Static
allocation IDs are primitive and fail the exclusion. This finite search does
not establish that no other EggCC use exists.

The Pack32 lead proposed cancelling a bounded binary packing, isolating one
unequal component with an equal sibling, propagating the result through a fixed
shift, and applying an exact false equality in a masked loop. Its actual
compiler probe rejected every query conservatively, exported nothing, and
produced identical emitted and native code in every treatment. It supplies no
native change or timing result. Route already exercises the same generic chain,
while Parts32 supplies the timed consumer. This does not refute the packing
invariant or show that another importer could not succeed. The
[Pack32 report](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/report.md)
holds the treatment counts and rejection details.

The same-region `NoAlias` lead reached an actual compiler implementation but
exported nothing. After one permitted revision, every positive treatment still
rejected its auxiliary rows conservatively, so emitted and native code stayed
identical and no timing was justified. This exhausts the bounded attempt budget
without refuting the scoped `NoAlias` law or ruling out a different design. The
[A1 attempt report](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-integration/actual-r0/report.md)
holds the test counts and rejected cases.

## Final validation

The repository-required root
[`make check`](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/root-make-check-r4/receipt.json)
passes. The detailed records for the frozen compilers, repository test runs, r2
cleanup, and matrix reproduction live in the
[reference](reference.md#source-identities-and-validation-boundaries) and the
linked r2 summaries. Two points matter for this explanation: the retained
timing samples measure the r1 compiler's native programs, and the r2 cleanup
changed only the QR7 sidecar file without changing behavior or creating a new
timing claim. No snapshot was accepted.

## Limits of the result

The integrations are experimental source-boundary analyses, not merge-ready
EggCC features. They use fresh private e-graphs so branch assumptions cannot
pollute the main graph, and they export only exact derived target predicates or
consumer relations.
The rules require total sound constructor laws, supported equality-sort
children, committed applications, and equal siblings for reverse disequality.
Unsupported fields and ambiguous multi-child differences stay unknown.

No compiler bug is claimed from these integrations. QR7 is the strongest
substantive-consumer injectivity-only result, with verified runtime payoff for
one fixed hot input. Parts32 remains the strongest combined
injectivity-and-disequality result, with per-workload effects in two independent
sessions. Same-mask is a smaller qualifying replication. Route, Sort, and
Affine show additional compiler opportunity and causal use of the encoding
without performance claims. Pack32 and the same-region alias attempt are bounded
negative results. They do not weaken either qualifying runtime result and do not
establish that their underlying laws are impossible to integrate differently.

Exact source, dependency, input, binary, command, output, and timing identities
remain in the ignored durable evidence tree.
