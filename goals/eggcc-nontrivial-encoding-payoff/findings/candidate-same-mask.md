# Same-mask: a measured scoped disequality chain

The [complete explanation and evidence](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/candidate-same-mask/report.md) connects one source fragment to its encoding, causal controls, final native code, timing, limits, and validation.

In the false branch of `(x & m) == (y & m)`, ordinary congruence gives `x != y`; fixed wrapping translation injectivity then gives `x+7 != y+7`. A fresh private graph imports only that exact branch's parent disequality, uses unmarked `Mask` and marked unary `Shift7`, and exports only the proved target Boolean equality as false. Reverse-step and annotation knockouts lose the result; exact intermediate rescues restore it. A final application knockout retains all private witnesses but withholds the main-graph union, restoring baseline code. Primitive-only detection finds no witness.

On the constructed hot Bril loop, Encoding/U0 paired runtime median is 0.98084, bootstrap 95% [0.98042, 0.98164], across 32 balanced four-arm cycles. B1/U0 and Encoding/Manual placebo intervals contain 1; U0/B1 emissions and native entry code match, and Manual/Encoding emissions and entry code match. This passes the prospectively frozen <0.99 upper-bound gate for this microbenchmark. It is not a new compiler bug or a suite-wide speedup. Loop layout is an uncontrolled confound, and a specialized contextual rewrite could implement this fixed law directly.

A separate ten-cycle five-arm compile diagnostic includes private graph construction/translation. Encoding/B1 paired median is 1.02094, interval [0.95841, 1.03721], so no total-overhead conclusion is supported at that precision.

The engine's full Make check passes. EggCC library/integration/DAG bodies pass (31/2,421/68), but full integration gates are not green: 13 snapshots exactly match the historical dependency-retarget failures, strict Clippy retains three baseline sites, and the added hook has a rustfmt layout delta. No snapshots or failures are waived. The selected timed source and all earlier/diagnostic artifacts are preserved.
