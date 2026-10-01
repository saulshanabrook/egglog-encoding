# Paper artifact workloads

These are self-contained Egglog programs materialized from research artifacts.
They live here except for DialEgg's dynamic-cost workload, which requires the
experimental harness. Each file retains its source extraction or an intentional
correctness check and is expected to
complete in less than one minute. The checked-in files are the test and
benchmark inputs; external toolchains are needed only to reproduce them.

| Fixture | Upstream workload | License |
| --- | --- | --- |
| `misaal-hvx-dot-product.egg` | MISAAL `test_hvx_dot_prod.egg` at `c098f0f289d03f0c58db1ef85d9b4ff7eef9dec4` | Apache-2.0 |
| `churchroad-wide-multiply.egg` | Churchroad paper's 16-by-32-bit multiply at `9f82ca23b273a5a500cc6a1ca60b30d3c33c5721` | MIT, copyright Gus Henry Smith |
| `egglog-experimental/tests/papers/dialegg-nmm40.egg` | DialEgg generated NMM-40 `nmm.ops.egg` at `4d0d522e98c15becdc5e7d711348cb0891ff0d44` | Apache-2.0 |
| `speq-preserved-reference-suite.egg` | Four matching SpEQ REV workloads from artifact record `10963236` and LLEQ `00bd6254b3832d94558b7c38a394ea03d01a2763` | CC-BY-4.0, creator Avery Laird |

The choices favor meaningful representative workloads that stay bounded for
default use.
MISAAL has only one committed complete generated workload. Churchroad's paper
contains one end-to-end running example, the wide multiply used here. The file
replays that example's Egglog mapping phase, bounded to 17 iterations of the
paper's saturating schedule. Seventeen cycles measured about 0.9 seconds in
normal release mode on the calibration machine, while 18 measured about 1.6
seconds; timings are machine-dependent. `debruijnify` is required by
Churchroad's separate module-enumeration rules, but the paper driver does not
invoke those rules in this flow. DialEgg's NMM-40 input is the medium published scaling case: unlike
NMM-20 it runs for hundreds of milliseconds, while avoiding NMM-80's
multi-second, multi-gigabyte proof run. The SpEQ file groups the four preserved
REV programs that still reach the artifact's verified GEMV or histogram
reference rules: TACO-Gen, CSparse, NPB IS, and Parboil.

The Apache-2.0 text is in `LICENSE-Apache-2.0`. Churchroad's MIT license and
copyright notice are in `LICENSE-Churchroad-MIT`. The SpEQ fixture's header
contains the CC-BY-4.0 attribution and change notice. Every provenance header
records its original source, input digest, adaptations, and reproduction path.

## Reproduction

Clone the Git sources at their recorded revisions:

```bash
git clone https://github.com/RafaeNoor/MISAAL.git /tmp/MISAAL
git -C /tmp/MISAAL checkout c098f0f289d03f0c58db1ef85d9b4ff7eef9dec4

git clone https://github.com/gussmith23/churchroad.git /tmp/churchroad
git -C /tmp/churchroad checkout 9f82ca23b273a5a500cc6a1ca60b30d3c33c5721

git clone https://github.com/AzizZayed/dialegg-cgo-artifact.git /tmp/dialegg
git -C /tmp/dialegg checkout 4d0d522e98c15becdc5e7d711348cb0891ff0d44

git clone https://github.com/avery-laird/lleq.git /tmp/lleq
git -C /tmp/lleq checkout 00bd6254b3832d94558b7c38a394ea03d01a2763
```

MISAAL can then be regenerated directly:

```bash
uv run python scripts/paper_benchmarks/materialize.py misaal \
  --checkout /tmp/MISAAL \
  --output egglog/tests/papers/misaal-hvx-dot-product.egg \
  --check

```

For Churchroad, build the exact Yosys revision named by
`dependencies.sh`, then build the repository's Yosys plugin in the same build
environment. One source-build sequence is:

```bash
git clone https://github.com/YosysHQ/yosys.git /tmp/yosys
git -C /tmp/yosys checkout f8d4d7128cf72456cc03b0738a8651ac5dbe52e1
make -C /tmp/yosys config-clang
make -C /tmp/yosys -j8 ENABLE_ABC=0

CPLUS_INCLUDE_PATH=/tmp/yosys /tmp/yosys/yosys-config --build \
  /tmp/churchroad.so /tmp/churchroad/yosys-plugin/churchroad.cc

uv run python scripts/paper_benchmarks/materialize.py churchroad-wide-multiply \
  --checkout /tmp/churchroad \
  --yosys /tmp/yosys/yosys \
  --plugin /tmp/churchroad.so \
  --output egglog/tests/papers/churchroad-wide-multiply.egg \
  --check
```

Follow Yosys's README to install its platform-specific build dependencies.
The materializer verifies the Yosys commit reported by the executable and the
exact output of `write_churchroad` before applying current-syntax adaptations.

For DialEgg, follow its README to build `egg-opt`, then materialize the
artifact's NMM-40 scaling case:

```bash
cd /tmp/dialegg
./build/egg-opt --mlir-disable-threading --eq-sat \
  bench/nmm/40mm.mlir -egg bench/nmm/nmm.egg -o /tmp/dialegg-nmm40.mlir
cd -

uv run python scripts/paper_benchmarks/materialize.py dialegg-nmm --size 40 \
  --checkout /tmp/dialegg \
  --generated /tmp/dialegg/bench/nmm/nmm.ops.egg \
  --output egglog-experimental/tests/papers/dialegg-nmm40.egg \
  --check
```

The artifact pass writes `nmm.ops.egg` before trying its bundled paper-era
Egglog executable. That final playback can fail on recent syntax; the generated
file is nevertheless complete, and the materializer performs the required
current-syntax conversion before checking it in.

The materializer verifies the committed upstream inputs by SHA-256 and fails
closed if they drift. Current-syntax changes are deliberately mechanical:
explicit constructors, `$`-prefixed globals, and materialized includes.
Original extraction requests are retained. Proof-testing and proof-extraction
modes also produce equality proofs for their actual returned results.

### SpEQ native recording

Download artifact record `10963236`, verify the archive MD5 is
`813c94e4c12a3466909849f38b6ac1fe`, and extract `lleq-artifact/parseIR.py`,
`lleq-artifact/run_benchmark.py`, and the four reference inputs
`analysis/{gemm_ref,gemv,gemv_sink_perm,histogram}.ll` under `/tmp/speq`.
The archive is 6.26 GB. LLEQ's pinned `REVTest.cpp` retains the exact custom-LLVM
outputs for the selected programs.

Create an isolated recorder environment and regenerate the fixture:

```bash
uv venv --python 3.12 /tmp/speq-recorder
uv pip install --python /tmp/speq-recorder/bin/python \
  egglog==13.2.0 lark==1.1.7 z3-solver==4.12.2.0 'setuptools<81'

/tmp/speq-recorder/bin/python scripts/paper_benchmarks/record_speq.py \
  --artifact /tmp/speq/lleq-artifact \
  --rev-tests /tmp/lleq/llvm/unittests/Transforms/REV/REVTest.cpp \
  --lleq /tmp/lleq \
  --llvm-config /path/to/llvm-17/bin/llvm-config \
  --preserved-reference-suite \
  --output egglog/tests/papers/speq-preserved-reference-suite.egg \
  --check
```

The recorder builds the pinned REV analysis as a temporary LLVM plugin,
verifies the generated reference FIR, applies only the fail-closed API port
needed by egglog-python 13.2, and sets `save_egglog_string=True`. It registers
the reference rules from `run_benchmark.py`, runs each original 5 transform / 1
expand / 3 transform schedule, and reads `as_egglog_string`. No
command-processing instrumentation is used. It deterministically inlines the
recorder's temporary DAG lets. Replay retains native extractions in their
original scopes; reference-kernel checks during acquisition remain separate
from the timed workload.
