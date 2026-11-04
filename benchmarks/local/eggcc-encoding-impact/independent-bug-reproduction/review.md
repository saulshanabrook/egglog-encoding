# Independent minimized arithmetic bug gate

Supported: the preserved original EggCC baseline miscompiles a valid wrapping-i64 program. An independently derived oracle and six fresh complete compiler invocations establish the wrong output on the MAX input and correct output on a nearby control. This is a baseline correctness finding, with no encoding-benefit or performance claim.

The coordinator authorized this deliberate independent final-gate repetition after the compiler owner froze `compiler/arithmetic-screen/localization/{manifest.json,results.json}`. No compiler-owner `run.py` was imported or reused. The small independent checker is `reproduce.py`; its command was:

```sh
# cwd /Users/saul/p/egglog-encoding
/Users/saul/.local/share/uv/python/cpython-3.13-macos-aarch64-none/bin/python3.13 -I -B benchmarks/local/eggcc-encoding-impact/independent-bug-reproduction/reproduce.py --output /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/independent-bug-reproduction/capture-01
```

`capture-01/results.json` and each run's `receipt.json`, `run-data.json`, stdout, stderr and three native Tiger input snapshots are retained. `verification.json` independently rehashes the recorded inputs, binaries, Tiger, checker, peer receipts/artifacts and new output artifacts after all six runs. Every recorded hash still matches. These interpreted and instrumented correctness invocations are not timing observations; internal durations in CLI JSON must not enter performance figures.

## Independent expectation and valid input

Both fixtures contain the same program body. For positive `x`, it computes `product = mul x 2`, then prints whether `product < 0`; the other branch simply returns. There are no annotations, injected equalities, memory operations, division, uninitialized reads or new optimization rules. `9223372036854775807` fits signed i64. The pinned Bril interpreter at `06117c089c2d235ff8d040bb3d0cfd1e2a1c4880`, `brilirs/src/interp.rs:350–353`, reads i64 operands and explicitly calls `wrapping_mul`.

The oracle used Python integers plus signed reduction, independently of compiler outputs or the peer manifest's expected fields:

```text
signed_wrap_i64(v) = ((v + 2^63) mod 2^64) - 2^63
x = 2^63 - 1: x*2 = 2^64 - 2; signed_wrap_i64(x*2) = -2; print true
x = 1:        x*2 = 2;        signed_wrap_i64(x*2) =  2; print false
```

The required violated invariant is preservation of observable printed output for defined Bril operations. A positive operand and positive multiplier do not imply a nonnegative signed wrapping product. The MAX source must print `true`; replacing its in-branch answer with `false` changes behavior. Header argument variants are actual `# ARGS:` fixtures, with no unused trailing CLI argument assumption.

## Fresh full-compiler outcomes

Every invocation used cwd `/Users/saul/p/wt/eggcc/encoding-impact`, `--with-context --run-mode optimize --interp`, a fresh output receipt/egraph directory, and the frozen peer environment (`RAYON_NUM_THREADS=1`, `RUST_LOG=info`). Prototype explicitly used `--exact-local-addresses off`. The ordinary production CLI retains default parallel schedule/all passes and non_weakly_linear=true. Each run had a 60-second timeout, exited 0 without signal/timeout, logged exactly passes 0/1/2, and wrote three nonempty native extraction input snapshots.

| Fixture | Frozen endpoint | Source output | Optimized output | Conclusion |
| --- | --- | --- | --- | --- |
| mul-minimal-max | Original A | true | false | Wrong output |
| mul-minimal-max | Engine-retarget B | true | false | Wrong output |
| mul-minimal-max | Final prototype, feature off | true | false | Wrong output |
| mul-minimal-one | Original A | false | false | Passing control |
| mul-minimal-one | Engine-retarget B | false | false | Passing control |
| mul-minimal-one | Final prototype, feature off | false | false | Passing control |

Both interpreter fields were non-null strings in all six fresh receipts. Source results match the independent arithmetic oracle; stdout from each optimized invocation is the corresponding false result. The MAX discrepancy is a successful compiler invocation producing an incorrect optimized program, not merely a panic, timeout, missing field or equality-checking harness failure. The reviewed stable A emitted Bril also replaces the in-branch comparison with `const false`, consistent with the fresh reconstructed-program result. Its peer receipt/input/artifact hashes are checked in `verification.json`, with retained copies under `supporting-source/`; this is supporting source evidence, not a seventh fresh compiler invocation.

## Bound evidence

Stable peer manifest SHA256: `8f0e4167de8026cf6a01a324859627aa7d2534d33fd2076f06834f3f0f45e7d7`; peer results index: `e675b8d39e314ef5839fbdbd0c218ccb506ecbf1863adf40ea0d36ce84d4f2aa`. Both were copied into the capture and remained unchanged through all runs. Relevant peer artifact hashes were checked before and after reproduction.

Input MAX SHA256: `f6624abf3e6018b7e6d2d5e410afff2f95822965515361b644cfc61ba8fd31eb`; control: `b8bc31ef18ebefd6f25057439e277569a931b2ec769295cbf590aef14550bf9c`. Originals remain under the new compiler's `tests/encoding_impact/arithmetic/`; retained copies are in `capture-01/inputs/`.

Frozen compiler hashes: A `e062c92bbcb9a8f05caed3cc10ec013c126a1d1f528e57f3b797bf6c3004912d`; B `6c30c8cb28768f3c461666b0370ff5c249fe6ba1f8f58a1a1d6c78e2df3e638f`; final prototype `d44a89c2f752aff60b2691d9e055f23e54215fc9dfa74a0db8e956afc713162e`. Their sibling Tigers all match `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`. Exact binary paths, effective environment and argv are retained per run, with source and executable provenance unchanged before/after.

## Attribution and limits

The original A witness supports a genuine bug in the selected preserved baseline, before the engine retarget, new remaining-child query change or experimental local-address feature. B and prototype-off show persistence across those historical endpoints. This gate did not require new injectivity/disequality functionality and establishes no encoding-specific detection or repair contribution. Describe it as an ancillary baseline compiler bug found during the encoding search unless separate evidence later establishes a sound encoding contribution.

This independent gate establishes complete optimization/extraction/reconstruction plus Bril source/optimized execution. It performs no LLVM lowering or generated-machine-code execution, contains no speed measurement and evaluates no fix. It does not test upstream main, no-context/sequential/ILP configurations or all integer inputs. The minimized case is newly derived evidence, not an existing production workload. The compiler owner's pass 0/ruleset localization is separate evidence; this reviewer did not duplicate that scan and does not infer the exact faulty rule solely from matching wrong outputs. A repair requires its own focused regression and final source gates.

The scientific-method-debugging skill was used for the independent oracle, falsifiable MAX/control predictions and retained bounded replay. No source, frozen compiler, runtime or earlier study artifact was changed.
