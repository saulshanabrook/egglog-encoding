# MISAAL HVX source-pin review repair

Only these implementation/test files are modified:

- `scripts/reproduction_prepare_misaal_hvx.py`
- `tests/test_reproduction_prepare_misaal_hvx.py`

Fresh live baselines are retained under `.baseline/hvx-source-pins/` and the exact
handoff diff is `MISAAL-HVX-SOURCE-PINS.patch`.

## Finding and repair

The x86 seed did not pin either newly consumed HVX source file, and
`verified_request` does not validate directory identities. Merely recording their
current hashes allowed an edited ordinary argument permutation or generator body
outside the patch anchors to be accepted as the pinned 44ff/beb recipe.

`inspect_hvx_inputs` now checks both original full-file SHA-256 pins before parsing
semantics, copying/patching the generator, or executing any preparation step:

- MISAAL `44ff893445d664cd87f52b08a138260ed2015ba8`,
  `lib/sema/hexsemantics_new.py`:
  `eef4d1fcb30db190dc1947a55040203c33aff16e7262d52b36e26fe1cc0c0b75`.
- Hydride `beb825327fc946d65032e96f7cde9acf3d24c13e`,
  `codegen-generator/tools/low-level-codegen/InstSelectors/hexagon/RoseHexLegalizerGen.py`:
  `659d800eef85fa85877e8181d0b75e804b144a829245aed28604a5a1b8034494`.

Both constants were checked against `git show REV:path` and the actual acquired
source bytes; current inputs match. The tests mutate an ordinary permutation and
non-anchor generator code, require an explicit pinned-source failure, and confirm
no step, selector receipt or case request is emitted. Existing fixture-only width
validation still exercises its own semantic gate with an explicitly repinned
synthetic fixture.

## Validation and remaining boundary

All **10 focused HVX preparation tests** pass. Ruff check/format and Mypy pass for
the two changed files. The mirror implementation was loaded explicitly with the
current live, unchanged support modules/test fixtures because those newer HVX/ARM
dependencies are absent from this older isolated mirror. No supporting source was
edited. All native operations in the tests are mocked; no native build, selector
job, LLVM lowering or target execution ran.

The independent read-only review found no additional concat lowering blocker.
The actual source defines 2x16-bit and 4x8-bit repeated concatenation, and the
emitted zero-extend/shift/or construction matches it. The fixed-vector/i32 shape
checks agree with the inspected Rosette lifter/code generator; the common mapping
accessor retains legalized-child replacements. Required LLVM12 APIs exist in the
installed headers. Original ordinary intrinsic mapping remains in place except
the declared binary-literal parsing repair. Receipt/library/hash and absent-wrapper
contracts fail closed; actual source hashes are retained.

This is source/model evidence only. A guarded native build, concat2/4 lowering
fixtures (including invalid shapes), full original HVX parent completion, returned
LLVM audit, and standalone ordinary/strict validation remain separate gates.
