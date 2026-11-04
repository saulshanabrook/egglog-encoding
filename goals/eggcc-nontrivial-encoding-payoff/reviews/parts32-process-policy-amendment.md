# Parts32 process-admission amendment

Policy v2 is fixed prospectively before any accepted preflight or timing sample.
Known compiler/benchmark executable names and prefixes still reject a checkpoint
at every utilization. Every other nonexempt process rejects at **CPU >=75%**.
Only the collector and its inventory subprocess are exempt; no GUI executable
has a special exemption. Both `timing.py` and the independent `verify-timing.py`
enforce the same versioned policy.

The retained first rejection,
[`timing-preflight-rejected-1792434879825091000.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/timing-preflight-rejected-1792434879825091000.json),
shows WindowServer at 16.7%, iTerm2 at 49.6%, and an unrelated protobuf test at
98.4%. A subsequent sanitized check reported the test had ended while the GUI
processes remained at 28.6% and 48.2%. The initial 10% rule therefore classified
persistent GUI activity as competing computation. The fixed 75% threshold is a
coarse near-full-core blocker with margin above those GUI observations and below
the observed test. It is an operational rule, not a statistically calibrated
noise threshold or a claim that lesser load is harmless. The original rejected
artifact remains unchanged, SHA-256
`2f07377c98d30c53197682d0c1ef8feccefe4eaf117d936f6279f5461519841e`.

This correction changes process admission only. The frozen design remains
SHA-256 `c646d77e41334fd252a4e951245068f771afbbb41e44cd828e30edd58b0f6367`:
workloads, arm identities, schedules, sessions, timer boundary, estimator,
resampling, and acceptance gates are unchanged. A new preflight must bind the
revised script hashes. No accepted preflight or timing output exists at this
amendment's validation.

The synthetic check
[`check-process-policy.py`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/check-process-policy.py)
passes 41 cases without running `ps` or native programs: every known name/prefix
at 0%, both PID exemptions, unknown-process thresholds including 74.9%/75.0%,
the retained rejection with and without protobuf, and the later GUI values.
Forged passing records are independently rejected by the verifier. Syntax checks,
all 23 frozen source/compiler/archive/arm bindings, and all 17 source-manifest
identities pass. Script hashes and detailed evidence are retained in
[`process-policy-static-validation.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/process-policy-static-validation.json).

During the first synthetic-check setup, local `inspect.py` shadowed Python's
standard-library `inspect` through `unittest.mock`. Its top-level code regenerated
65 existing derived extracts, diffs, and `inspection.json` from retained data;
it performed no compilation, native execution, preflight, or timing. No hashes
were captured immediately before that import, and these derived files have no
entries in `artifact-identities.json`, so their before/after byte identity cannot
be established. They remain in place; their post-incident hashes are in the
validation receipt. All frozen artifacts still match their pre-existing hashes.
The check now excludes its directory from module search before importing
`unittest.mock`; both ordinary and isolated (`python3 -I`) invocation pass.

The host remains shared. Several unknown processes below 75%, short-lived work
between checkpoints, or other resource contention can escape this rule. The
measurement owner must keep competing work out of the collection window;
balanced/reversed order, two required sessions, and code-identical placebo gates
remain the controls for residual noise. This amendment includes no preflight or
performance sampling.
