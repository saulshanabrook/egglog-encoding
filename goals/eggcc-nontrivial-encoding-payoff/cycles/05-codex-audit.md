# Cycle 05 Codex source audit

**No new bounded source-backed candidate survives this pass.** Parts32 remains
the strongest pending payoff because its conclusion depends on a dynamic
equality-sort disequality, a marked lossless representation, an unmarked pair,
an equal sibling, and reverse disequality before the existing compiler can
remove the target comparison. Same-mask already supplies a qualifying
constructed generated-runtime result. Affine, Route, and Sort independently
show that the generic closure reaches EggCC's emitted and native code, but they
remain unmeasured supporting cases.

This was a read-only pass over pinned EggCC U0
`a0bbec127f83249074a46af3fd6f6126c90fe0fb`, reconstructed from the retained
Git object. The reconstructed archive has the previously recorded SHA-256
`7a886debd758e78d0e859a05bbac75084e7da9c4f4bd0d73321dcf6f5ad25c2a`
and contains 771 files. The pass reread the five completed integrations, the
append-only hypothesis ledger, the corpus census, and the relevant U0 operator,
tuple, interval, and memory rules. It did not compile, execute, time, or edit
EggCC.

## Current-result audit

| Candidate | Generic equality-sort chain | Endpoint status | Simple primitive-conflict exclusion |
| --- | --- | --- | --- |
| Parts32 | `x!=y -> Parts32(x)!=Parts32(y) -> Pair(low(x),high(x))!=Pair(low(y),high(y))`, then equal low siblings isolate `high(x)!=high(y)` | Actual compiler/native causal gate passes; frozen two-session confirmation remains pending | Passes. Fixed mask/divisor metadata cannot decide any dynamic child fact, and the same-graph primitive-only treatment restores U0 code. |
| Same-mask | Unequal `Mask(x,m)` parents plus the common equality-sort mask imply `x!=y`; marked `Shift7` propagates the result | Prospectively measured constructed runtime improvement of about 2%; specialized contextual code can reproduce it | Passes the literal primitive-conflict exclusion, although it establishes no unique logical power. |
| Affine | Marked key cancellation gives two child equalities; an equal Add sibling isolates a disequality; marked odd multiplication propagates it | Actual compiler/native code changes; no timing; candidate-specific lint failures remain | Passes. Matrix coefficients are primitive metadata, but they do not decide the dynamic child relations. |
| Route | Marked tagged-route cancellation, unmarked Add reverse disequality, marked odd-multiply forward disequality | Actual compiler/native code changes and two intermediate rescues; no timing | Passes. The dynamic selector and routed payload equalities are essential. |
| Sort | Marked `(min,max,orientation)` cancellation, unmarked Add reverse disequality, marked odd-multiply forward disequality | Actual compiler/native code changes and two intermediate rescues; no timing | Passes. Primitive tag values alone cannot recover the dynamic inputs. |

In every case the final bridge is deliberately narrow: it exports only the
exact contextual integer `Eq` as false. That bridge is a real consumer of the
derived disequality, while extraction and LLVM may remove the branch even when
EggCC's named false-`If` rewrite is disabled. Therefore the application/bridge
knockouts are the causal endpoint; the false-`If` rule alone is not claimed as
essential.

## Fresh source screen

The finite expression vocabulary is visible in
`dag_in_context/src/schema.egg:84-148`: scalar operators, `Select`, static
`Get`, `Alloc`, calls, and flat tuple constructors. The Rust front and back
doors cover these same scalar and control operators in
`src/rvsdg/to_dag.rs:218-325` and `src/rvsdg/from_dag.rs:140-374`. Within that
bounded vocabulary, the remaining attractive directions close as follows.

### Ordinary tuples do not supply a new cancellation consumer

U0 already pushes static `Get` through `Concat` and unions each projected
element in `dag_in_context/src/utility/util.egg:58-105`. It also normalizes
subtuples and concatenations in
`dag_in_context/src/utility/canonicalize.egg:41-106`. Ordinary equality of
constructed tuples therefore already exposes the component equalities that a
new injectivity annotation would provide. Disequality plus all-but-one equal
siblings can still add a fact, as Parts32 demonstrates, but the retained census
found no exact current-corpus tuple guard with a blocked consumer. Inventing a
new reversible tuple merely restates Parts32, Affine, Route, or Sort.

### Select and signed min/max are now covered by Route and Sort

EggCC creates `Select` from small pure `If` outputs in
`dag_in_context/src/optimizations/select.egg:5-23` and creates signed min, max,
and select forms from exact conditional outputs in
`dag_in_context/src/optimizations/switch_rewrites.egg:4-62`. Route exercises a
lossless dynamic selector representation, while Sort exercises the lossless
`(smin,smax,orientation)` representation. Longer routing or sorting networks
reuse the same laws and exact Boolean consumer; no distinct producer or blocked
consumer was found. They are composition controls, not new candidate families.

### The existing memory payoff still lacks a qualifying producer

The concrete memory consumer is strong: `NoAlias` lets EggCC commute a write
past a load at `dag_in_context/src/optimizations/mem_simple.egg:70-81`, after
which exact-address store forwarding applies at lines 106-113. Current
`NoAlias` producers use interval signs around pointer additions at lines 20-58.
The underlying pointee domain stores primitive allocation IDs with offset
intervals (`dag_in_context/src/optimizations/memory.egg:25-36`). Distinct static
allocation IDs therefore fail the primitive-only exclusion. The source pass
found no branch-local dynamic equality-sort producer that can be transported
to two live pointers without adding general lifetime, path, and mutation
analysis. That is beyond this goal's bounded integration allowance.

### More arithmetic wrappers do not create a new endpoint

Wrapping `Add`, `Sub`, and `Mul` are explicit in
`dag_in_context/src/interpreter.rs:232-247`; the existing candidates already
exercise fixed translations, odd multiplication, affine reconstruction, and a
lossless quotient/remainder-style partition. XOR-like or alternate odd-affine
wrappers would be sound for selected fixed siblings, but this pass found no
new U0 or corpus guard and no consumer distinct from the exact false-`Eq`
endpoint. Trying arbitrary coefficients would extend a constructed family
without testing a new EggCC opportunity.

Float encodings remain ineligible without a separate NaN and signed-zero
semantics. Effect/state constructors are not injective in prior state: a write
overwrites information, calls may have effects, and loads depend on state.
Making those candidates sound would require a new effect or heap model rather
than a bounded encoding bridge.

## Disposition and stop boundary

This pass adds no new hypothesis row because it found no new valid
law/producer/consumer chain. It does not close three earlier admitted leads:

- Q1 QR7 must-alias still needs the bounded K7 cancellation integration and
  exact local pointer-equality export proposed by its retained screen.
- P1 Pack32 still needs either an actual sidecar integration or an explicit
  evidence-backed supersession by Parts32. The shared word-decomposition theme
  alone is not a terminal disposition.
- A1 same-region `NoAlias` still needs its one guarded loop-invariant transport
  and one-shot bridge, or a concrete falsifier showing that transport cannot be
  bounded soundly.

Same-mask is a measured success; Parts32 is awaiting its already frozen
measurement; Affine, Route, and Sort are supporting actual-host results; and
the ordinary-tuple, corpus-key, and fresh-region searches are closed at their
recorded falsifiers. The bounded source search cannot claim exhaustion until
Q1, P1, and A1 receive append-only terminal ledger rows.

The required independent Claude Fable pass was attempted against the same
pinned source, but the local CLI reported `Not logged in`; that operational
failure is retained separately and is not treated as a source audit or a
negative result. If authentication becomes available, Fable should challenge
this exact stop boundary. A proposal qualifies for another implementation only
if it names a source-backed producer and blocked consumer that are materially
different from the five completed cases and do not require a general alias,
effect, path, or IR redesign.
