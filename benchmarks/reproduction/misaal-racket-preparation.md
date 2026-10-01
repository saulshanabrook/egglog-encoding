# Isolated MISAAL Racket preparation

The family coordinator prepares native generators, then calls
`prepare_source_runtime` to download the pinned Z3 archive, install isolated
Racket packages, run source API diagnostics, seal the runtime, and publish new
capture requests. Existing native products are reused when adding a runtime to
an already prepared request set. Source optimization and ordinary replay are
separate steps; a prepared request is not a reproduced workload.

The raw package-preparation command below records that the pinned MISAAL source
emits five arguments to parameter synthesis while its Racket function accepts
four. Its historical artifacts remain
`source-api-blocked`, `promoted: false`, and `workflow_ready: false`, even when all
dependency diagnostics behave as expected. The complete recipe separately tests
the documented restoration of the paper revision's four-argument ABI. It uses
both source-emitted method variants and the exact captured `ki4k2nlc.rkt` fixture,
with unchanged five-argument variants retained as negative controls.

The normal fresh-family entrypoint is:

```sh
uv run --locked python -m scripts.suite_reproduction --family misaal --stage prepare
```

The coordinator owns the shared lock throughout preparation. Any download,
package, solver, or ABI-gate failure preserves its receipt and prevents request
publication. A safety stop prevents subsequent work. Runtime seals bind source
and compiled packages, installation files, executable identities, diagnostic
evidence, and the required environment. Capture checks the seal before and after
the full source run; cache identities include the same files and code trees.

## Run contract

Run the raw package diagnostic from the repository root while no other reproduction job
owns `benchmarks/local/reproduction/stages/.heavy-job.lock`. The public command
acquires that lock itself. Every acquisition/native child uses the existing
process-group guard with a 5 GiB RSS ceiling, normal memory pressure, a 10 GiB disk
reserve, and a 600-second timeout. Steps run serially and any unexpected failure
stops the attempt, retaining its evidence.

```sh
misaal_prepared=benchmarks/local/reproduction/stages/misaal-prerequisites/prepare/de24509065a91a0011099031af73b866aad56a8f4ccd70149684696c620846b1/attempt-0001
.venv/bin/python -m scripts.reproduction_prepare_misaal_racket prepare \
  --output benchmarks/local/reproduction/diagnostics/misaal-racket-preparation-0001 \
  --request "$misaal_prepared/requests/misaal-hexagon-blur3x3.json" \
  --z3-archive benchmarks/local/reproduction/downloads/misaal-racket/z3-4.8.8-aarch64-osx-13.3.1.zip \
  --captured-script benchmarks/reproduction/fixtures/misaal-parameter/ki4k2nlc.rkt \
  --captured-sha256 32d0edbfbd86bdde0ba6b47af8eebd260f1421af79dcbb223923015f389a8521
```

Repeat `--request` for additional requests sharing the same pinned source
checkout. Output must be a fresh path under `benchmarks/local/reproduction`.
Internal `_acquire` and `_observe` modes are guard-owned child hooks; do not invoke
them independently. The tracked fixture preserves the actual captured source
bytes and their provenance; no historical capture directory is needed.

## Pins, bounds, and isolation

The module pins MISAAL `44ff893445d664cd87f52b08a138260ed2015ba8`, Hydride
`beb825327fc946d65032e96f7cde9acf3d24c13e`, and the exact Git trees for their MISAAL,
Hydride, and vendored Rosette packages. Generic catalog Rosette is not used.
Additional packages are `custom-load` commit
`142b32a0381d271f4bc6efbbcf3d306a0ee55566` and `rfc6455` commit
`e3a87e914e25841a6e1bb996aa001aeb178284bf` from their official catalog sources.
The `rfc6455` source is the leastfixedpoint Git service, not the old GitHub mirror.

Acquisition reconstructs each pinned Git tree from its recursive inventory, then
verifies every downloaded blob's Git SHA-1 and records SHA-256. Unsupported modes,
symlinks, submodules, incomplete/paginated inventories, unsafe paths, changed
blobs, and off-origin redirects fail closed. Bounds are 2 MiB per tree response,
4 MiB per source file, 32 MiB per package, and 1,600 tree entries per package.
Sources are fetched sequentially; no repository-wide source archive is needed.

The already acquired Apple Silicon Z3 4.8.8 archive is exactly 8,002,399 bytes,
SHA-256 `c53f9513283ce96ffd442fa134e48c1c67e4de486953f965a3b61a407144a255`.
It must contain only the 20,730,655-byte regular `z3` file. The executable hash is
recorded after extraction. Racket and raco use the reviewed arm64 Racket 9.2
installation and exact executable hashes; changed executables are refused.

Every Racket command receives an otherwise empty environment with attempt-owned
`PLTUSERHOME`, `PLTADDONDIR`, and `TMPDIR`; explicit `HYDRIDE_ROOT`; the selected
solver; and a controlled PATH. Package installation uses `--copy --no-setup
--deps fail --scope user --batch`. This prevents ambient user package reuse,
automatic catalog dependency resolution, global installation, and Rosette's
automatic solver download. Missing standard Racket packages are explicit
blockers. Installation package/checksum listings are retained in command logs.
Resolved package copies and each pinned source file are checked after import.

The complete acquired sources are scanned before native execution for process
group/session changes and foreign-process interfaces. Any such text match is a
review stop, including matches in examples/docs: this conservative result may
require a narrower reviewed source decision. The scan is not a semantic proof.
The selected Rosette solver launcher also has an exact SHA-256 pin. Separate
runtime evidence must observe the actual Racket and pinned Z3 child in the same
guarded process group. A custodian setting is not treated as group containment.

## Evidence and candidate format

`runtime.json` separates four diagnostic gates:

1. Full active `rosette`, `hydride`, and `misaal` imports, module/package paths,
   exact copied source bytes, and effective group setting.
2. A genuine eight-bit solver query whose model is checked, with a live
   Racket/Z3 PGID observation before the solver is released. A bounded `/bin/ps`
   snapshot checks the actual held Racket process and its descendants, including
   the exact selected solver path; no additional Python package is needed. Every
   diagnostic outcome releases the held smoke so its own `solver-shutdown` runs.
   Cleanup then checks that the observed children and selected solver disappear;
   no stale numeric process-group signals are sent. Missing or failed drain
   evidence remains a failed attempt and cannot produce a candidate.
3. A small genuine four-argument invocation of the original MISAAL optimizer,
   followed by interpreting its selected expression against every source test.
4. The unchanged captured five-argument script, required to fail specifically
   with the expected four-versus-five arity mismatch. Other failures do not pass
   this negative gate.

Source tree manifests, complete source-scan findings, raw scripts,
request/result/log files, solver identity, and `pgids.json` remain under the
attempt. Failures preserve whatever evidence has actually completed; imports
alone cannot stand in for solver or source-operation evidence.

Successful prerequisite diagnostics produce `candidates/*.candidate.json`,
whose outer object contains the original request path/hash, runtime path/hash,
blocked status, and a nested `candidate_request`. Nesting deliberately prevents
the candidate artifact from satisfying the existing execution-request schema.
The original request bytes and native product identities remain unchanged.
No `settings.json` or promoted capture request is written.

The nested request adds these integration fields:

- `racket`: exact `/Applications/Racket v9.2/bin/racket` spelling;
- `racket_sha256`: reviewed executable identity;
- `racket_group_containment`: `misaal-racket-lease-v1`;
- `source_hashes["lib/utils/DSLInstructionUtils.py"]`: the exact reviewed Python
  detached launcher identity;
- `racket_runtime`: blocked runtime receipt path/hash/status;
- isolated Racket/solver environment values and a PATH resolving that exact
  Racket executable, while retaining the existing native request's PATH suffix.
- `environment_unset` retains previous exclusions and removes inherited
  `PLTCOLLECTS` and `PLTCONFIGDIR` overrides.

`prepare_source_runtime` uses `reproduction_misaal_abi_gate.run_gates`, then
`reproduction_misaal_runtime.seal_runtime` and `augment_requests`. The latter
preserves every original native executable and source identity in fresh request
files. The source adapter enforces the runtime and detached-process lease
contracts. Old blocked candidates and failed attempts remain unchanged.

An optional archived preparer path identifies the exact source that produced an
older runtime receipt. It must match that receipt's hash; the archive is read as
evidence and never executed. This lets a lock or publication refactor reuse
successful package diagnostics without pretending that the new code ran them.

## Implementation validation

The accompanying tests execute no network acquisition, Racket, solver, package
installation, or native compilation. They check Git identity/path rejection,
download and archive bounds, detachment review stops, immutable candidate
augmentation, required evidence separation, native-input tampering, observed
group failures, and preservation of guard stops. Passing them establishes the
Python orchestration contract only; root's guarded diagnostics must establish
actual source/package/solver compatibility. Guarded native diagnostics have
passed the package imports, solver model and cleanup checks, original
four-argument synthesis, and the emitted-script and captured-script ABI gates.
The sealed runtime also passed a complete x86 `blur3x3` source optimization and
ordinary replay. These results establish the tested case; they do not establish
completion of the remaining family.

The fresh complete runtime recipe also passed at
`benchmarks/local/reproduction/prerequisites/misaal-fresh-runtime-0001/`:
pinned acquisition, isolated installation, all fifteen package/solver steps,
both source-interface gate groups, sealing, and publication of 102 requests.
The original native generators were reused at their recorded identities.
The outer `result.json` records this preparation success; the raw `runtime.json`
continues to describe the original unadapted interface mismatch. Actual parent
optimization and ordinary replay remain separate requirements for every case.

The inspected ordinary compilation path selects Z3, including parameter
synthesis through Rosette's default solver. Boolector is required only by
explicit backend selections or the optional property-discovery fallback in
`RepairRelavancePostProcess`; the normal pattern modules load retained property
JSON instead. The current gates do not establish Boolector availability, and
importing its Racket module alone does not exercise that solver.
