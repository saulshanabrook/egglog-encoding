# All three total lossless keys survive the U0/LLVM backend screen

The three constructed hypotheses in [cycle 03](../cycles/03-hypothesis-refresh.md) retain removable native work on pinned U0. No generic encoding integration, compiler change, workload timing, or new compiler bug is claimed. The first acyclic full-chain fixture worked for every family; no hypothesis revision was needed.

Durable evidence is in [`lossless-key-screens/20261019-three-total-keys`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/lossless-key-screens/20261019-three-total-keys). The successful run is `execution-02`; [`backend-summary.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/lossless-key-screens/20261019-three-total-keys/execution-02/backend-summary.json) is the machine-readable result. Every external command has a write-once argv/environment/input-hash/exit/timeout receipt and full stdout/stderr. [`artifacts.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/lossless-key-screens/20261019-three-total-keys/artifacts.json) hashes the retained evidence.

## What was compared

Each small Bril program takes dynamic signed i64 inputs `a,b,c,d,z,w`. Routing also takes dynamic `q,r`, with `p=(q<r)`. It tests every key field with nested integer-Eq guards, then tests the common tail:

```text
all Key fields equal:
    if c+z == a+w: print 5
    else:
        if 3*z == 3*w: print 99
        else: print 7
different Key: print 3
```

Arithmetic wraps modulo 2^64. The faithful manual comparator changes exactly `br target .unexpected .expected` to `jmp .expected`; all key fields, key guards, dynamic inputs, the Add guard, and target expressions remain in its source. The manual proof first reconstructs both input components from the equal key, substitutes `a=c` into the Add disequality, and then uses the invertibility of multiplication by 3. It does not remove the whole guard computation or replace the workload with its sampled answer.

Four roles were checked: original source, U0-emitted source, manual source, and manual source emitted through U0. Each role was interpreted and lowered with the same LLVM 18 `O3_O3` path. The primary backend comparison is therefore **U0-emitted versus manual-U0-emitted**, with both receiving the same EggCC and LLVM pipeline. Raw-source native checks provide an additional differential control.

| Family | U0 `icmp eq i64` / LLVM conditional branches | Manual through U0 | ARM64 application instructions, U0 → manual | Final dynamic target compare / `99` computation |
| --- | --- | --- | --- | --- |
| Two-word affine `(a+2b,2a+3b)` | 4 / 3 | 3 / 2 | 25 → 22 | Present → absent |
| Paired routing with common dynamic selector | 4 / 2 | 3 / 0 | 22 → 19 | Present → absent |
| Signed min/max with integer orientation tag | 4 / 2 | 3 / 0 | 29 → 25 | Present → absent |

The LLVM counts refer to `@_main`. They are not machine branch counts: the ARM64 backend if-converts the application entries. All three U0 application entries still execute `cmp x4,x5`, load `99`, and select between `99` and `7`; the exact manual fold removes that comparison and value computation. The executable `main` entry also retains `99` only in baseline roles. Thus this is an actual native code difference, rather than a source-name, serialized-IR, or debug-output difference. Complete LLVM, disassembly, and extracted application and executable entry bodies are retained under each role's `*-native/` directory.

## Correctness and law boundaries

There were 40 positive input rows: 10 affine, 20 routing, and 10 sorting. Routing exercises both selector outcomes for every row. Rows include the feasible positive `(a,b,c,d,z,w)=(1,2,1,2,3,4)`, equal-tail and unequal-key paths, equal pairs, ascending and descending pairs, signed MIN/MAX, and wrapping boundary cases. Every row produced the independent oracle's exact stdout in all four native and interpreter roles: 160 native and 160 interpreted output checks.

An independent Python model reconstructs the original pair from each key. It exhaustively checks all 87,376 signed pairs across word widths 2 through 8 and checks 4,145 64-bit pairs, including all selected edge-pair combinations and deterministic random pairs:

- Affine reconstruction uses `a=2v-3u` and `b=2u-v` modulo the word width. Its determinant is -1, a unit modulo 2^64; no bounds are assumed.
- Routing reconstructs the pair with the retained selector. The source uses the identical dynamic selector expression on both sides. The untagged map with independently varying selectors is not annotated as jointly injective.
- Sorting reconstructs `(min,max)` for tag 1 and `(max,min)` for tag 0. Equal inputs are valid; signed MIN/MAX require no subtraction or absolute value.

The 15 nearby semantic negatives each pass source and U0-emitted interpretation and native execution with stdout `99`. Their deliberately invalid target folds each return `7` under both interpretation and native execution. This adds 45 native and 45 interpreted checks:

| Family | Guard/law mutation and concrete counterexample |
| --- | --- |
| Affine | First component only: `(a,b,c,d)=(0,1,2,0)`; second component only: `(0,2,3,0)`; singular map `(a+2b,2a+4b)` with `(0,1,2,0)`. Each uses `z=w=0`. |
| Routing | First routed output only with `p=false`, `(a,b,c,d)=(0,1,2,1)`; second output only with `p=true`, the same pair; different selectors without a common tag, swapped payloads `(0,1,1,0)`. Each uses `z=w=0`. |
| Sorting | No orientation tag with `(1,2,2,1)`; omit minimum with `(0,2,1,2)`; omit maximum with `(2,0,3,0)`. Each uses `z=w=0`. |
| All three | Take the true Add-equality branch with equal keys and `z=w=0`; or replace `Mul3` by noninjective `Mul2` with equal keys, `z=0,w=MIN`. |

The total is **205 passing native output checks and 205 passing interpreter output checks**, from 549 successful bounded commands, with no timeout. The positive program sources remain unchanged by these separately stored negative fixtures. All command elapsed values are operational receipts, not performance evidence.

## Nonprimitive mechanism assessment

All three families pass **nonprimitive eligibility** for the proposed mechanism. They do not yet demonstrate that mechanism through the actual encoding integration. The intended private equality-sort closure is:

```text
Key(a,b)=Key(c,d)
  => a=c, b=d                              marked-key cancellation
Add(c,z)!=Add(a,w), a=c
  => z!=w                                  unmarked Add reverse congruence
  => Mul3(z)!=Mul3(w)                       marked forward disequality
  => the exact contextual target Eq=false   existing false-If consumer
```

The key coefficients, selector identity, or tag literals cannot determine the dynamic equality `a=c` or disequality `z!=w`. Without key cancellation, the Add comparison has two unresolved equality-sort children, so reverse congruence cannot select `z,w`. Without the Add-result disequality, equal keys alone do not imply `z!=w`: the equal-tail positive controls return `5`. Without the odd-multiplier law, the `Mul2` negative returns `99`. Each omitted field/tag negative demonstrates why that key law needs its complete dynamic evidence. This is a chain through distinct semantic constructors with a consumed equality-sort component equality, rather than a primitive `true`/`false` conflict detector.

A faithful dynamic manual closure can derive the same result; no unique logical power is claimed. A one-rule primitive-field mismatch shortcut cannot implement this semantic chain on the same symbolic terms and primitive metadata. The remaining admission work is actual expression import, exact-scope generic closure and consumer export, retained intermediate facts, fixed-input knockout/rescue controls, downstream-consumer knockout, and the same-graph primitive-only null. None was implemented in this screen.

The families remain constructed triggers. The Fibonacci update, Select canary, and conditional-swap benchmark discussed in cycle 03 are source support and near matches, not demonstrated corpus applications. The backend gate alone does not establish a generated-runtime benefit: a later hot driver must consume fresh dynamic tuples and retain the whole guarded computation, followed by a frozen matched measurement design.

## Sources, harness correction, and reproduction

U0 is `a0bbec127f83249074a46af3fd6f6126c90fe0fb` at `/private/tmp/eggcc-nontrivial-encoding-payoff-u0`; the admitted `eggcc` SHA-256 is `d86869982413d4561cf713cc769c96eb1c9bfefe46fa459a2692c53a7aa93cf0`. The successful run checked all 771 pinned source hashes before and after and found no change. Before/after manifests also match the binary, runtime, Cargo files, LLVM tools and driver identities. The backend is Homebrew clang 18.1.8 on ARM64 Darwin 25.6.0. Memory-pressure blocking is disabled and subprocesses use 30- or 180-second timeouts.

The initial driver assumed the CLI's advertised positional interpretation arguments were used. In this pinned source, [`src/main.rs:143`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/main.rs:143) constructs `prog_with_args` from `file.read_program()` and never consumes `args.bril_args`; interpretation instead reads the file's `# ARGS` header. The second input therefore reproduced the first header's answer and tripped the harness oracle. The failed assertion, original commands and `attempt-01-driver.py` are retained outside `execution-02`. The corrected driver writes a separate immutable Bril copy with the exact header for each interpreter check. This is an input-harness correction, not a hypothesis revision or qualifying bug claim.

Inspect `run.py` for the complete fixture generators, independent oracles and exact public CLI calls. It refuses to reuse the existing `execution-02` directory. For a fresh reproduction, copy the driver into a new empty evidence directory under `lossless-key-screens/` at the same depth, then run it; it resolves the admitted binaries from that directory's study ancestor. `summarize.py` verifies its receipts and extracts the backend result. The retained command recipes are, in shape:

```bash
eggcc --with-context --run-mode optimize --run-data-out emit.json source.bril > u0-emitted.bril
eggcc --with-context --run-mode parse --interp --run-data-out check.json exact-input-header.bril
eggcc --with-context --run-mode llvm --optimize-egglog false \
  --optimize-bril-llvm O3_O3 -o program --llvm-output-dir program.ll \
  --run-data-out lower.json u0-emitted.bril
program 1 2 1 2 3 4
llvm-objdump --disassemble --no-show-raw-insn program
```

No source integration or repository test suite was required for this evidence-only screen. No ledger/status, existing finding, other agent directory, compiler source, commit, push, or PR was changed.
