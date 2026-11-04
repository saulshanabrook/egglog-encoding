# Source validation of the second Claude Fable pass

This note validates the proposals in [`02-fable-audit.md`](02-fable-audit.md)
against pinned EggCC source `a0bbec127f83249074a46af3fd6f6126c90fe0fb`
and retained executable evidence. The Fable prompt described the experiment before
the frozen timing batch and before the final causal controls existed. Its statements
that timing and negative receipts were absent were accurate for that prompt snapshot,
but they are no longer current experiment facts.

## Same-mask audit

The semantic audit is confirmed. The candidate translates expressions in their exact
parent or child contexts, uses opaque equality-sort leaves, keeps `Mask` unmarked,
marks only fixed wrapping translations as injective, and exports only the queried
child-context Boolean fact. Existing EggCC false-`If` rules consume that exported
fact. The candidate therefore implements the valid chain

```text
Mask(x,m) != Mask(y,m) and m = m
  => x != y
  => Shift_k(x) != Shift_k(y)
  => Eq(Shift_k(x), Shift_k(y)) = false.
```

Fable's materiality objection is narrower than the accepted goal criterion. A
special contextual rule can implement this exact chain, and the faithful manual arm
does so; the result therefore has no unique logical power. It is still eligible
under the accepted facts because the decisive relations are between equality-sort
children, the derivation crosses the unmarked `Mask` and marked `Shift_k`
constructors, and it cannot be reproduced by comparing only primitive fields. The
final report must state both facts rather than claim that the encoding is the only
possible implementation.

The following measurement concerns were resolved after the Fable snapshot:

- Encoding and Manual emit identical optimized Bril and entry assembly. U0 and B1
  likewise match.
- The 32-cycle frozen confirmation retained all samples and passed its declared
  threshold; independent replay checked all hashes and outputs.
- Seven compiler-level semantic negatives now have retained receipts.
- The final causal pass adds the reverse-step knockout, exact-child rescue,
  target-fact rescue, consumer knockout, and primitive-only null that were missing
  from the audited snapshot.

Two limitations remain valid. The literal-invariance analysis exists because the
sidecar models each fixed translation as unary; a sibling-guarded binary
cancellation law could avoid that analysis. The measured result is one constructed
Apple Silicon hot loop, and the small instruction deletion also changes loop
alignment, so it is evidence for this endpoint rather than a suite-wide estimate.
Compiler-time measurements remain a separate diagnostic.

## New and retained hypotheses

### H1: sibling-guarded Add/Sub cancellation

The law `x != y and k = k' => x+k != y+k'` is sound for wrapping i64 addition and
subtraction by a common sibling. It would admit the current nonliteral-shift negative
and remove the loop-literal analysis. This is an engine-completeness improvement in
the already measured same-mask payoff family, not an additional payoff. It is
deferred unless a distinct EggCC consumer appears.

### H2: arithmetic Parts32

This is source-backed and remains eligible. The checked decomposition
`Parts32(x) = (x & 0xffffffff, (x - (x & 0xffffffff)) / 2^32)` is lossless for signed
i64 values. The retained native screen shows that U0 and LLVM keep the target test,
while the faithful manual fold removes it. An isolated actual-encoding integration
is therefore the next decisive experiment.

### H3: live-cell NoAlias

This is source-backed but remains beyond the bounded integration presently proved.
The existing `mem-simple` consumer can use `NoAlias`, and the private graph can derive
the required dynamic index disequality. A sound bridge still needs a checked live-cell
representation and guarded loop transport. Keep this as a stronger consumer
opportunity, not a demonstrated result.

## Nonqualifying bug probes

- `rec_to_loop.egg` records multiplicative identity `1` but places literal `0` in
  the transformed false arm. The source mismatch is real. A valid recursive
  factorial-at-zero probe nevertheless produced `1` before and after U0 optimization,
  so this input did not trigger an incorrect rewrite. No EggCC bug has been
  established, and the probe would not satisfy the encoding requirement in any case.
- `hackers_delight.egg` rewrites the second result to `n / (n & -n)`. The signed-min
  observation is mathematically plausible, but no executable mismatch has been
  established. It is unrelated to the injectivity/disequality mechanism and is not
  admitted for this goal.
- `select.egg` may replace a pure `If` result with `Select`; `purity_analysis.egg`
  labels integer division pure, and the DAG interpreter evaluates `Select` lazily.
  Whether the native lowering may eagerly evaluate a zero-divisor arm depends on
  EggCC's source semantics. This is a separate semantic question and is not admitted
  as an encoding hypothesis.

## Disposition

The validated pass contributes one deferred completeness improvement, confirms the
two retained nontrivial families, and supplies three ordinary bug probes that cannot
satisfy this goal's mechanism gate. It does not overturn the same-mask result, and it
does not add a new qualifying payoff by itself. Continued source ideation should seek
a distinct equality-sort consumer; arithmetic Parts32 remains the cheapest active
test.
