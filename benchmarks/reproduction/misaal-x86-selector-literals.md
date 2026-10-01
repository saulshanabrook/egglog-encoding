# MISAAL x86 selector literal repair

This is a source-backed candidate, not a successful native reproduction. Native
selector gates and new complete source-parent captures remain required.

The retained `tensor_shr` call selects 32-bit arithmetic right shift in 16 lanes.
Its generic name `_mm512_srav_epi16_dsl` covers several lane widths; parameters
select `_mm512_srav_epi32_wrapper`. Fourteen constant guards must match. Thirteen
match; argument 4 is the one-bit value 1, but the generated guard requires 177.
`RoseX86LegalizerGen.py:75–80` removes `#`, prefixes `0`, and always parses base 16:
`(bv #b1 1)` becomes hexadecimal `0b1`, or decimal 177. Common
`Legalizer.cpp:276–330` correctly reports actual `0x01` versus expected `0xb1`.
The correct wrapper and AVX512 shift intrinsic already exist. This mismatch is
independent of the host CPU; the diagnostic never executes target instructions.

The failed `conv_nn` lowering has the same cause in all 18 residual calls:
three 512-bit, four 256-bit, and eleven 128-bit SRAV32 calls. Its 68 required LLVM
functions are present, and none returns direct undef/poison. This is a selector
failure after selected results exist, not successful source-parent completion.
The lowering audit must continue to reject it.

Pinned source: MISAAL `44ff893445d664cd87f52b08a138260ed2015ba8`, Hydride
`beb825327fc946d65032e96f7cde9acf3d24c13e`. The new materializer verifies the
entire original selector, generator, and semantics-table hashes. It validates
all 2,025 emitted cases and 24,536 guards against their source entries, then
changes only 1,951 binary-literal guards in 1,349 cases:

| Source literal | Old integer | Correct integer | Guards |
|---|---:|---:|---:|
| `#b1` | 177 | 1 | 1,577 |
| `#b0` | 176 | 0 | 350 |
| `#b11` | 2,833 | 3 | 6 |
| `#b10` | 2,832 | 2 | 6 |
| `#b01` | 2,817 | 1 | 6 |
| `#b00` | 2,816 | 0 | 6 |

No other selector bytes change in this repair: names, branch order, permutations,
actions, hex constants, and all 265 scalar `-1` guards remain intact. The generator
embeds the same tested radix/width decoder, so regeneration retains the repair.
Bitvector values use their stated width, including two's-complement negative
values; plain signed scalar parameters remain signed. This matches vendored
Rosette `bitvector.rkt`'s `sfinitize`/`ufinitize` at lines104–130. Malformed tokens
and unsupported widths fail explicitly. Source changes or ambiguous cases also
fail before any source file is patched.

Fresh preparation calls this repair before the existing wide-integer,
SIMD-mode, and missing-return repairs. `Preparation.patch` retains original/new
hashes and exact patches; `legalizer-literal-derivation.json` binds each changed
guard to its source literal, helper hash, and coverage counts. New requests also
pin the generator and semantics table. The new helper must be included in the
coordinator's preparation identity. Existing prepared source trees, libraries,
requests, and failed receipts must not be changed.

The small tracked tests compile the actual original Python generator class
without external import/main execution and exercise its real SRAV and two-bit
extract cases. They also test width/radix/signed behavior, malformed tokens,
source/guard drift, fresh-only materialization, and ordering of existing repairs.
These are data-only tests; they do not establish native lowering correctness.

## Required root-owned gates

The separately sealed ignored package `misaal-x86-selector-gate-0001` contains
an original-source snapshot, the exact retained tensor input plus source wrapper
bodies, source-derived 128/256-bit fixtures, and Boolean/width negative controls.
Its driver builds a new complete selector plugin under a fresh output directory
with the existing guarded `Preparation` runner (one build job,5 GiB RSS,10 GiB disk
reserve). It checks the old plugin remains unlowered, the fixed plugin selects
the precise expected wrapper for each positive, and both deliberately wrong
selectors remain unlowered. All emitted modules must pass LLVM verification.
It then applies the new plugin to the complete retained tensor/convolution
linked inputs and requires the unchanged audit for all 1/68 requested functions.
The guard stops the sequence on a resource or compiler failure. Source/plugin/
tool hashes and request/result logs are retained; no settings are published.

After those gates pass, use the normal MISAAL preparation recipe in a new
immutable attempt, followed by new `tensor_shr` and `conv_nn` complete source
captures and ordinary replay. For a standalone fresh x86 dependency rebuild:

```sh
.venv/bin/python -m scripts.reproduction_prepare_misaal \
  --storage benchmarks/local/reproduction/preparation/misaal-x86-literals-v1 \
  --backend /absolute/path/to/the/recorded/original/egglog
```

This builds fresh source and library outputs; it is not the historical
`--repair-wide-literals` continuation. The combined public preparation stage
must then produce the per-case requests and sealed Racket prerequisites. Keep
source timeout, pattern-cache transitions, rule/schedule/cost behavior, and the
original selected-output/LLVM audits unchanged. Passing only the reduced gate
does not admit a corpus workload.

Evidence origins: `stages/misaal-x86-tensor_shr/complete/89071253…/attempt-0001`
and `stages/misaal-x86-conv_nn/complete/db3d430e…/attempt-0001`, under
`benchmarks/local/reproduction`; exact paths and hashes are in the ignored gate
manifest. Its LLVM/source identity is an auditable diagnostic snapshot, not a
claim of hermetic system-toolchain reproduction or full LLVM equivalence.
