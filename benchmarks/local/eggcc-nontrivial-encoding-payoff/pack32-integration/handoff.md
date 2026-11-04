# P1 implementation staged; execution deferred

The bounded implementation is present in fresh isolated roots
`/private/tmp/eggcc-pack32-candidate` and
`/private/tmp/encoding-pack32-candidate`. Reconstruction and staging have
already run. Do not rerun the one-shot `admit.py` or `stage.py` on these roots.
The original sources, captures, source archives, ledgers, and dirty primary
workspace files were preserved.

No Cargo command, compiler, engine CLI, native program, test, oracle, matrix,
inspection, or timing campaign has been executed for P1. Only source archive
verification/extraction, source staging, Python `ast.parse`, and direct
single-file Rust formatting/parsing were performed. Rustfmt passed for the
sidecar and staged library. Python syntax passed for all five scripts. These
checks establish syntax, not Rust type correctness or an admitted source query.

## Implemented source and controls

`scoped_reasoning.rs` is the durable copy of the source staged in the isolated
EggCC host. `stage.py` removes the inherited optional Parts32 named-rule
knockout from `lib.rs`, preserves the exact Eq=false application and its
consumer-off control, and copies the P1 sidecar. The encoding source is the
verified Parts32 final overlay, including `known-disequal-forward-only?`, with
no new engine feature or engine source delta for Pack32.

The P1 theory uses bounded equality-sort `Field32` children and `Word` outputs,
with marked `Pack32(Field32,Field32)` and `Shift7(Field32)`. The independent
manual closure includes every committed constructor application and original
seed. The matcher verifies exact nested true packed equality, false packed
equality, and translated target, transporting typed projections through their
actual branch inputs. It imports no local field equality into EggCC's graph.

Literal constants use the retained structural same-slot proof. A separate
domain induction proves guarded/literal/masked initial U32 fields and every
backedge, supporting only bounded slots, literal masks, and exact both-branch
tuple transport. The current iteration remains opaque. The first actual-host
probe must determine whether the unchanged retained source has this supported
shape; no revision has been spent on a runtime/importer falsifier yet.

Modes are `off`, `seed-only`, `primitive-only`, `cancellation-off`,
`cancellation-rescue`, `reverse-off`, `disequality-rescue`, `forward-off`,
`query-off`, `manual`, `encoding`, `bridge-off`, and `consumer-off`.
Cancellation rescue supplies only the true intermediate a=c, leaving b=d
unknown with Pack32 cancellation disabled;
disequality rescue supplies the true intermediate c!=d with reverse disabled.
The primitive null retains the exact graph and original dynamic seeds, runs
only recorded source metadata comparisons, and performs no equality-sort
inference, contradiction query, saturation, or export.

The first packed-output equality also makes Pab=Pcd, so reverse congruence may
compare Pca(c,a) with Pcd(c,d), derive a!=d from their syntactically common c,
then consume cancelled a=c to obtain c!=d. This is an alternate valid path in
the identical committed graph. Therefore the endpoint needs a cancelled child
equality, but the available b=d equality is not individually essential. The
single-equality rescue makes this distinction observable.

Eight `pack32_` registered tests cover the generic causal graph, independent
manual closure, missing seeds/two unresolved children, unrestricted-domain
collisions, typed/sibling transport, initial/backedge boundaries, both initial
guard bounds, and EE/NEE consistency. None has been run.

`matrix.py` retains the existing positive corpus and original three semantic
negatives, adds six semantic negatives, four loop negatives, and absent-context
mode, and interprets each original and emitted fixture before native checks.
Its independent source oracle uses byte concatenation inside the admitted
domain and explicit wrapping semantics for weakened laws. It is defined but
unexecuted. Every command capture and phase refuses to overwrite existing
evidence. `inspect_capture.py` asserts intermediate facts, both rescues, null identities,
native parity/difference, exact outputs, and negative boundaries; it cannot
establish full validation or performance.

`implementation-manifest.json` binds the durable source/scripts, archive
admission, staged host sources, and selected engine overlay. The source-only
delta from reviewed Parts32 is in `pack32-versus-parts32.patch`.

## Deferred commands

Wait until the parent permits compiler/CPU work after the Parts32 campaign.
Use a new output directory and the capture environment; it selects Rust 1.91,
LLVM18, one Rayon thread, four Cargo jobs, finite bounds, an isolated target,
and disabled memory-pressure/snapshot-acceptance variables.

From `/Users/saul/p/egglog-encoding`:

```sh
export PACK32_OUTPUT_ROOT=/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/probe-01
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/run.py metadata-host cargo metadata --locked --no-deps
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/run.py --cwd /private/tmp/encoding-pack32-candidate metadata-engine cargo metadata --locked --no-deps
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/run.py --cwd /private/tmp/eggcc-pack32-candidate/dag_in_context focused-tests cargo test --release --locked pack32_ -- --nocapture
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/run.py build cargo build --release --locked
```

Assert the focused command selects eight registered tests. A syntax-only pass
does not waive a compile, lint, or behavioral failure.

After a successful build, copy the new compiler and the unchanged admitted
Tiger beside it; no candidate binary is present yet:

```sh
python3 - <<'PY'
from pathlib import Path
import shutil
base = Path('/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration')
out = base / 'bin'
out.mkdir()
shutil.copy2('/private/tmp/encoding-pack32-candidate/target/release/eggcc', out / 'eggcc')
shutil.copy2(base.parent / 'admission/bin/tiger', out / 'tiger')
PY
export PACK32_BINARY=/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/bin/eggcc
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/matrix.py positive
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/matrix.py negative
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/matrix.py loop-negative
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/matrix.py context-negative
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/inspect_capture.py
```

The first Encoding emit is the actual-host importer falsifier. Inspect its
boundary receipts before a revision. The script currently starts with U0/B1 and
the nulls; those runs are correctness controls, not a timing campaign. If no
actual query is admitted, use the retained rejected source shape to justify at
most one bounded importer revision; do not change the original source fixture.
If the original graph's producer/consumer is absent, the domain proof needs a
general analysis, the target native code remains, or a causal requirement
fails, preserve the failure and close the relevant lead.

After causal/native success, complete validation with fresh capture labels:

```sh
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/run.py --timeout 3600 host-test make test
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/run.py --timeout 3600 host-nits make nits
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/run.py --cwd /private/tmp/encoding-pack32-candidate engine-git-root git init --quiet
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/run.py --cwd /private/tmp/encoding-pack32-candidate --timeout 3600 engine-check make check
```

The isolated encoding archive has no `.git`; the empty local metadata above is
only for Python repository-root discovery and creates no commit. Its `make
check` may also need the same local Python/cache setup documented by Parts32;
retain any real setup failure. Host pending snapshots and warnings remain
unaccepted. The original workspace's source was not changed, so its full suite
has not been invoked during this source-only handoff.

There is no known source-implementation blocker. Rust type correctness, the
actual source shape, generic reasoning results, all new oracle rows, native
parity, and full validation remain unverified by the explicit execution
restriction. No timing design or performance claim is attached to this staged
implementation.
