# MISAAL literal-width and lookahead policy

Fresh family preparation enables
`"literal_width_guard": "positive-literal-halving-v1"` only for
`misaal-x86-tensor_shr`, `misaal-x86-conv_nn`, `misaal-x86-mul`, and
`misaal-x86-softmax`. It publishes new request files,
merges and verifies the two source pins below, and requires the runtime publisher
to retain that policy. Existing requests and native products remain unchanged.
Other cases retain their existing policy; a manually supplied request without
the field keeps the original behavior. Unit tests alone establish no source
completion.

The same publisher sets `HYDRIDE_DISTRIBUTE_LOOK_AHEAD=1` only for
`misaal-x86-mul`, `misaal-x86-softmax`, and `misaal-x86-l2norm`. Thus `mul` and
`softmax` receive both changes; `l2norm` receives lookahead without the width
guard. Each case records its policy alongside the original and published
request hashes. Existing source/native pins, cache branches, and unrelated
environment entries are preserved. An existing lookahead value other than the
string `"1"` is a conflict, even when the source's presence check would enable
it. Runtime publication must retain the explicit option before settings are
published. This is a named reproduction configuration change from the original
x86 recipe, not a claim that the original default succeeded.

The retained c098 x86 `tensor_shr` acquisition fails in the original Egglog
backend when the signed widening-multiply axiom divides `isize=0` by `iprec=0`.
The successful observational trace under
`benchmarks/local/artifact-audit-20260924/misaal/zero-width-probe/` establishes the
preceding steps: an x86 pattern introduces `(LIT "1" 1)`, the literal-cast axiom
creates `(LIT "1" 0)`, and cast-to-widening-multiply creates the zero denominator.
`conv_nn` retains the same failure at its first invocation. These are old source
attempts, not current-revision source-completion evidence.

The current 44ff source retains both unconditional literal-halving axioms at
`targets/halide/axioms.egg:50–60`. Both require `:when ((> prec 1))`: every positive
result of the existing integer halving remains available, including 2→1 and
8→4; the undefined zero-width result is excluded. Rosette's bitvector type
requires a positive size. This changes the domain of those two rules only. It
does not establish the correctness of their existing value/sign behavior.

## Source and capture contract

The request must name the contract, revision
`44ff893445d664cd87f52b08a138260ed2015ba8`, and both source hashes:

| Source | SHA-256 |
| --- | --- |
| `targets/halide/axioms.egg` | `5c710032858d34440ad94979c8788bb96967d1d71e93e55f3ea2bad2184ab4c1` |
| `lib/compiler/EggLogCompiler.py` | `87a96401b12291e184cf7eb65efe1f481bccd6faac514c56aef0502f1cc7c479` |

`guard_literal_width` verifies these files and the loaded source initializer's
code, globals, defaults, and class closure. It refuses prior initializer
wrappers. It preserves the original axioms and a guarded copy under the child
attempt's `literal-width-guard/`; the expected full guarded-file hash is
`e9d5c2f49af2c58df6e15f84372c79c0a1c9b92f1f0edbd285d5b92941d77e5f`.

The temporary initializer calls the original initializer and redirects only
`self.axioms_file`. The actual source's normal, swizzle, and swizzle-movement
emitters all read that field. Context exit restores the class initializer and
surviving instances, including after failures. Prepared source files remain
unchanged.

The capture hook executes the actual emitted guarded input and retains it in
`call.raw`. It verifies both evidence files before launch, rejects original,
duplicate, or unexpectedly omitted axioms, and preserves the original source's
explicit `skip_axioms` behavior. An invocation-local counterpart under
`literal-width-guard/` replaces only the guarded axioms with original bytes; it
is labelled `executed: false` and `reconstructed`. It is not an observation of
an entire unmodified parent run: previous source feedback may already differ.
Keeping this counterpart outside the actual `invocation-*.egg` directory also
preserves capture numbering and recovery membership checks.

## Validation before enabling a request

The Python tests exercise the actual retained initializer and three emitter
bodies with unrelated imports stubbed. They verify exactly two inserted guards,
preserved RHS forms and width preconditions, source/default/closure/wrapper
mutation rejection, restoration, and the actual capture boundary with a fake
backend. They do not execute Egglog, LLVM, Racket, or native generators.

The coordinator must run the following native gates before treating the repair
as validated:

1. Derive original and guarded diagnostic programs from the pinned source's two
   literal casts, four widening-multiply rules, and two cast-to-widen rules.
   Keep both signed and unsigned constructors/rules. Use `(LIT "1" 1)` for the
   retained failure boundary and `(LIT "0" 2)` / `(LIT "0" 8)` as positive
   controls. Zero avoids implying a nonzero one-bit signed literal extends like
   an unsigned value.
2. After eight rounds, query for the positive literal/cast equalities at 2→1,
   8→4, 4→2, and 2→1. Use `(fail (check ...))` existence queries for zero-width
   literals, zero-input-width casts, and zero-input-width widening multiply.
   Do not insert those invalid nodes with `let`. All guarded gates must pass;
   original controls must reproduce the zero-division failure.
3. Under the existing monitored source-acquisition entrypoint, run fresh
   `tensor_shr` and `conv_nn` parents with the opt-in request identity. Check
   complete source/LLVM feedback and ordinary replay of every actual backend
   selection. Preserve an unaffected passing source/replay canary. A passing
   prefix or changed extraction alone is insufficient.

Before these runs, refresh any runtime/adapter seals affected by the changed
helper hashes. Preserve old requests and failed attempts. Neither the native
controls nor historical requests are changed by fresh request publication.

On 2026-09-25, all six reduced native gates passed under the pinned original
backend. The original width-1, width-2 and width-8 programs fail specifically
on integer 0/0; all three guarded programs pass their positive equalities and
absence checks. Evidence is in
`benchmarks/local/reproduction/diagnostics/misaal-literal-width-gates-0001/attempt-0002/result.json`.
The first diagnostic attempt expected different error wording; its original
0/0 failure remains preserved. These reduced gates do not establish complete
source-parent or ordinary-replay success.

The first current-revision `tensor_shr` parent with this guard reached a
successful backend invocation, then failed the separate LLVM completion audit:
`llvm.hydride._mm512_srav_epi16_dsl` remained unlowered. The 503-second source
attempt is retained in
`benchmarks/local/reproduction/diagnostics/misaal-tensor-shr-literal-guard-0001.json`.
That attempt confirms progress past the division failure and remains failed.

On 2026-09-25, fresh complete parents passed after the separately documented
x86 selector literal-radix repair was also applied: `tensor_shr` completed its
one backend session in 34.407 seconds, and `conv_nn` completed all six sessions
in 119.217 seconds. Standalone ordinary replay passed for every session. The
hash-bound summary is
`benchmarks/local/reproduction/diagnostics/misaal-x86-selector-publication-0001/attempt-0001/complete-canaries-summary.json`:
`tensor_shr` capture `42d8d3bc…` / validation `81256603…`, and `conv_nn` capture
`af639f33…` / validation `676e1c06…`. These results supported the initial two-case default
publication policy together with the pinned fresh selector preparation; they
are not evidence that the width guard alone repairs the later LLVM failure.
The public family `--stage prepare` path publishes this configuration from
tracked code, without using those historical diagnostic files as inputs.

## Validated lookahead configuration

The source option `HYDRIDE_DISTRIBUTE_LOOK_AHEAD=1` has independent justification
for x86 `mul`, `softmax`, and `l2norm`. The upstream ARM Makefile sets it at lines
84 and 125; the x86 recipe at line 73 does not. `DistributeVec.h:67–76,95–104`
checks environment-variable presence: even an empty value or `"0"` enables it.
Use explicit `"1"` in a new request's environment and record the configuration
delta; absence is the off setting.

Retained old-revision probes generated Python for `mul` and `softmax` when this
was the sole changed option; those probes remain partial evidence. Earlier
`l2norm` failures left unsupported 1024-bit operands after unsplit casts, no
source compiler output, and a later LLVM link requesting that missing output.

On 2026-09-25, the current `l2norm` parent with explicit lookahead completed all
three sessions in 62.349 seconds and passed standalone ordinary validation,
without the width guard. The same lookahead-only configuration for `mul` and
`softmax` still failed on the observed zero-width 0/0 operation. These distinct
outcomes are retained in
`benchmarks/local/reproduction/diagnostics/misaal-x86-selector-publication-0001/attempt-0001/lookahead-summary.json`;
`l2norm` capture is `ac586238…`, validation `847d5e4c…`.

Fresh `mul` and `softmax` requests then added the same pinned width guard while
retaining explicit lookahead and the repaired selector. Both completed source
optimization and standalone ordinary replay: `mul` passed all five sessions in
83.052 seconds (`b183d72f…` / `be7a02c9…`), and `softmax` passed all eight in
121.373 seconds (`5727e44d…` / `9271b8e8…`). The hash-bound capture and validation
references are in
`benchmarks/local/reproduction/diagnostics/misaal-lookahead-width-canaries-0001/complete-summary.json`.
The originals, including failed lookahead-only attempts, remain unchanged.

These full-parent results justify the exact four width-guard cases and three
lookahead cases named above. Fresh public preparation derives the new requests
from tracked policy and pinned source; it does not consume these ignored
historical summaries. Other x86 workloads and ARM/HVX policies are unchanged.
