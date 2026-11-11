# Eggcc / Churchroad complete capture slice

Implemented only in this mirror. No builds, native generation, replay executions,
containers, catalog changes, or live source-tree edits were performed.

## Owned handoff files

- `scripts/suite_capture_eggcc_churchroad.py`
- `scripts/eggcc_churchroad_complete.py` (new, family-specific native patches and output witnesses)
- `tests/test_suite_capture_eggcc_churchroad.py`

Legacy prefix capture remains the default. `--complete` adds complete native
optimization, `--case` is repeatable, and `--checkout`/`--binary` support separately
prepared pinned or repaired native toolchains. `--from-capture` cannot promote old
prefixes into complete captures. Complete-mode latest receipts have a separate name.

Coordinator entry point:

```python
capture_complete(family, cases, destination, checkout, binary, engine,
                 timeout_sec=300, max_evidence_bytes=128 * 1024**2)
```

`destination` must be a fresh attempt directory. Each case record contains
`source_completion` with process status, parent marker, observed final outputs and
hashes; `raw_invocations`/`raw_events`; ordered `sessions`, roots and output-check
contracts; current ordinary validation; `workloads`; and `status`/`reason`.
Only `status == "reproduced"` admits the workload. Native success alone is not
admission. Replay identities and native binary/source identities are retained.
The coordinator should halt on `resource_stop`, process safety outcomes, or
session-validation safety outcomes. This adapter also stops its local case loop.

New native/build/replay calls use `require_guard=True`, a 10-GiB disk reserve, and
the authorized warning-pressure diagnostic setting. Event materialization has an
explicit 128-MiB input-byte budget; larger captures stop with retained evidence
and require reviewed headroom or streaming work. This byte budget is not a claim
that arbitrary large graph materialization has been memory-profiled.

## What is captured

Eggcc observes every actual optimizer pass/batch, Tiger's original selected node
IDs/child choices, the fresh Tiger reconstruction egraph, actual Function outputs,
native typecheck completion, and final optimized program. The witness binds the
exact shared initialization term to the selected term; it does not merely check
that some Function with the same name exists. Original metadata erased by Tiger's
`DumT`/`DumC` printer is recovered only from original graph nodes, with child-eclass
consistency checks. Unknown transformations fail closed. All expected passes and
all batch roots are required.

Churchroad observes original engine calls/includes, Yosys inputs/results, native
spec and port-binding selections, Lakeroad inputs/results, reinsertion, all final
output-port aliases and final emitted Verilog. It preserves one persistent graph.
Mapping-snapshot checks precede synthesis updates, even though the host obtains
some selections later from that retained snapshot. Only the exact pinned,
unscheduled `enumerate-modules` declaration file may be omitted; any other reached
command referring to that ruleset blocks the ordinary replay. Selected results
are anchored to actual input terms or IsPort rows, without witness insertions.

Source patches are retained as reproducible diffs and fail on changed source
boundaries. Complete preparation uses separate `target/benchmark-acquisition/*-complete*`
build/source directories. Original source archives, manifests, patches, resulting
Cargo locks and build receipts stay in the durable preparation evidence directory.

## Checks completed

- 17 focused Python tests pass, covering exact input/output equality, shared/cyclic
  queries, missing provenance, incomplete parents/passes, actual reconstruction
  outputs, persistent Churchroad state, aliases, active extensions, feedback and
  complete-mode guard/receipt behavior.
- Ruff lint/format and mypy pass for the three owned Python files.
- CLI help renders with the new complete/case/override interfaces.
- Guarded patch-anchor checks succeeded against the local Eggcc pin and freshly
  read Churchroad pinned `main.rs`, `lib.rs`, and `Cargo.toml`. These are source-text
  checks, not native compilation. Churchroad rewrites four main engine callsites
  and eighteen library/docs/test callsites; the only remaining direct library
  engine call is the observer's real delegate.

## First real canary after root integration / heavy-slot approval

Run from the live root after integrating the owned files, not from this mirror's
symlinked build paths. Internal calls already use the shared guard; do not wrap
the whole adapter in a second process-group guard.

```sh
uv run --locked python -m scripts.suite_capture_eggcc_churchroad eggcc --complete --prepare-only
uv run --locked python -m scripts.suite_capture_eggcc_churchroad eggcc --complete --case eggcc-fact --timeout-sec 300
```

This is a small real paper source with main/fact roots, so it exercises native
multi-root extraction and all passes. A successful canary requires native compiler
completion and current ordinary checks for every optimization/reconstruction
session; zero successful runs are claimed by this slice.

Graph-changing configurations use `case['native_options']`: DP is default; ILP
uses `--tiger-ilp` (optionally `--ilp-solver cbc`); Fenwick's profile treatments use
`--with-context` and `--with-context --no-hacker-rules`. Sequential schedules and
explicit ablations are also supported. Native `--time-ilp` does not replace DP's
feedback result. Interpreter, early-pass cutoff, restricted-function and alternate
run-mode overrides are rejected in complete mode.

## Actual remaining runtime gates

- Compile the instrumented native code and run the first Eggcc canary. The native
  Rust/C++ patches have not yet been compiler-checked.
- Confirm Tiger's projected original-node identities across real regionalization
  and large/context-heavy cases; then expand configurations and population.
- Churchroad still needs a real Lakeroad/Racket/Rosette/solver environment and its
  native driver/plugin build. Preparation currently retains the native build and
  serde_json lock changes but does not install Lakeroad. No simulation is enabled.
- Port the existing macOS-specific LLVM/Yosys preparation commands if the selected
  acquisition environment is Linux/OrbStack; overrides permit a separately built
  toolchain. This slice does not claim container portability.
- Validate the real Churchroad event flow, selected-node representation, and
  current CLI compatibility on `simple_mul`, then `wide_mul`. Any failed gate
  retains the full native evidence and remains outside reproduced totals.


## Admission-fix follow-up

See `ADMISSION-FIXES.md` and `admission-fixes.patch` for the latest five-fix handoff.
143 focused lightweight tests, Ruff and mypy pass. No heavy jobs ran in this slice.
The next authorized domain slice is portable Churchroad prerequisite preparation;
`CHURCHROAD-ENV.md` retains the source-pinned recipe.

## Runnable Churchroad preparation slice

Added only `scripts/reproduction_prepare_churchroad.py` and its focused test file.
`CHURCHROAD-PREP-HANDOFF.md` gives the exact guarded command, settings/canary
integration and remaining native gates. Eleven protocol tests, Ruff and mypy pass;
the CLI help renders. A separate read-only review found no concrete blocker.
No dependency installation, compilation, synthesis, capture or other native run
was executed. Root must release the centralized heavy slot before the first run.

## Native Churchroad preflight and Ninja repair

Live churchroad-attempt-0001 stopped before any child command: missing Ninja. Racket/other required executables were present. Heavy slot released to root for DialEgg diagnostics. Proposed isolated fix pins ninja==1.13.0 beside meson==1.2.0, retains wheel hashes and version receipt, removes host Ninja requirement. Bitwuzla pinned CaDiCaL/Kissat/SymFPU builds use Meson; no CMake requirement established, so none added. 12 mocked protocol tests, Ruff check/format and mypy pass. Patch CHURCHROAD-NINJA.patch, awaiting integration/regrant for fresh attempt.

## Native Churchroad attempt 0002 and Racket repair

Isolated Ninja/Rust/source acquisition succeeded; Bitwuzla built all 194 steps and installed. Rosette/yaml installed and setup completed. Lakeroad compile failed on duplicate unused `others ...` bindings in architecture-description.rkt module+ test lines1072/1077 under Racket9.2. Upstream current main retains the same pattern. Official Racket docs identify this as a 9.1.0.9 change to non-linear ellipsis matching (https://docs.racket-lang.org/reference/match.html#%28part._.Non-linear_.Patterns_and_.Ellipses%29). Narrow source patch renames only outer unused binding to other-outputs; synthesis definitions unchanged. Original/patch/result hashes retained by preparer. Independent read-only agent review agrees.13 protocol tests + Ruff/mypy pass; actual pinned source anchor/diff checked, but repaired native compile awaits heavy slot. CHURCHROAD-RACKET.patch for root integration; CHURCHROAD-OBSERVED-LAKEROAD.patch is the exact one-line generated native source diff. Attempt0002 remains immutable; slot released and reassigned to MISAAL.

## SpEQ prerequisite recipe slice

Added only scripts/reproduction_prepare_speq.py, tests/test_reproduction_prepare_speq.py and SPEQ-PREP-HANDOFF.md. No native/solver/compiler/archive/package command ran. 17 mocked/in-memory tests, Ruff/mypy and public help pass. Exact LLVM17.0.6 existing toolchain plus unmodified REV sparse export at 00bd6254…; private Python3.11.11 + egglog13.2.0/lark1.1.7/z3-solver4.12.2.0 hashes/frozen wheels; all four reference FIR hashes as runtime gates. New allowlisted full-stream acquisition includes root Dockerfile and full MD5 completion, no shared adapter modification. Existing historical source reuse intentionally blocks on missing verified Dockerfile. Two paper inputs remain missing, eight parents remain separately unrun. Root owns next heavy-slot authorization/integration.

Final SpEQ draft: 18 tests after adding mixed clang/LLVM version rejection. Private uv-managed Python required. Independent source review found no concrete blocker in archive/checksum admission, guarded helper descendant cleanup, four FIR gates or runtime identity closure. All native acquisition/build gates remain unrun.

## Churchroad attempt 0003 and bounded continuation

Attempt0003 built and checked Bitwuzla, Rosette/yaml, Lakeroad, full Yosys and its Churchroad plugin. The final native Rust driver failed solely on moved spec_filepath in capture instrumentation. CHURCHROAD-BORROW.patch changes that argument to a borrow; 34 combined protocol/capture tests plus Ruff/mypy pass, and the actual pinned-source comparison confirms exactly one generated Rust line changes. Root integrated it.

New reproduction_continue_churchroad.py retains the failed receipt, preparer/capture bytes, source and prerequisite manifests, and finished output hashes before the sole borrow change. It reuses the private environment/Cargo target and runs only guarded final driver build/help and library inventory gates, with fresh receipt/settings outside the failed attempt. Eight mocked continuation tests cover checkpoint identity, exact repair, evidence preservation, prerequisite mutation and guard stops; Ruff/mypy pass. Actual continuation not yet run at this note.

Actual live continuation0001 succeeded. Native driver compiled incrementally in 1.052s with observed group peak339,427,328bytes; driver help and all linked-library probes passed. Original failed receipt SHA25644f849f1cfd766ce752fa33a00aae29dbb05ee491258253052b59002cd0d97d7 remained unchanged; prerequisite product hashes were verified unchanged. Published live preparation/churchroad-continuation-0001/settings.json, driver hash fde371354d872a064b68e2716b598268d61fe6bb9905956cc27d19d15532e58d. Root added explicit5GiB per-child ceiling plus recorded guard metadata before launch. Heavy slot released immediately after completion. Source optimization/corpus replay still unrun.

## SpEQ PHI diagnostic-only repair

New speq_phi_diagnostic.py + C++/LLVM fixture support and six lightweight tests. Exact pinned source patch changes only edge-aware getPhiBr polarity, explicit unsupported-shape error, and its required include. Source C/reference rules/capture modules unchanged. Native harness injects actual original/patched function and checks real LLVM scalar/MemoryPhi cases including both incoming orders; no native commands run yet. SPEQ-PHI-REPAIR.md records precise Parboil gate, exact later guarded commands, and separate Polybench single-state liveout/range/LevelBounds requirements. Churchroad environment note updated wide_mul to measured300s ordinary timeout, full native completion retained.

## Real SpEQ PHI diagnostic and normal-lane opt-in

Held/released sole heavy slot for diagnostics0001–0003; all evidence retained live.0001 receipt-serialization stop before compilation;0002 exact original harness fails bypass, patched21/21pass, plugin found missing existing custom MemorySSA.h;0003 copied unchanged pinned header, full plugin compiled, allfour reference FIRs hash-identical, real Parboil PHIs correctly reversed and unchanged EqSat stillfindsHistogram cost108. No fullcapture/admission. Peak347MB,5GiBcap,60schildren,10GiBdiskreserve. Normalcomplete-mode opt-in now implemented, notrun: settingsphi_polarity_repair -> speq_phi_polarity_repair -> --repair-phi-polarity, freshpatchedplugin only, historicalprebuiltomissionexplicit, source/headergate and patchhashesretained. SPEQ-PHI-OPT-IN.patch9ownedfiles,101focusedtests Ruff/Mypypass. Rootownsactualintegration/dispatchidentity/nativecanary. Sharedunownedvalidation/staticreplay dependenciesrefreshedbyte-for-bytefromliveformirrortestsbutexcludedfromhandoff.

## LLVM12 HVX concat diagnostic slice

Four new files only; exact generated concat fragment and pinned common mapping accessor injected. Exhaustive LLVM constant-fold evaluation planned for direct/mapped scalar/mapped vector over both domains, exact fixed output types/lanes, 36 isolated rejection cases. 13 mocked protocol tests + Ruff/mypy pass; no native jobs. HVX-CONCAT-DIAGNOSTIC.patch and .md give guarded real command and explicit non-admission boundary.

## General Eggcc source observations

Three-file isolated patch ready; 103 lightweight tests plus Ruff/mypy pass. Native programs/raw captures remain unchanged; replay-only ordinary tables retain original initializer values grounded by unique typed native constructor rows. All selected facts and root multiplicity preserved, unknown/unsafe lifetime scopes fall back explicitly. Offline retained Bitwise all six roots produce 84/36/234/33/33/37-fact checks using 15 tables plus one verified global; no native run in this slice. EGGCC-SOURCE-ANCHORS-HANDOFF.md and EGGCC-SOURCE-ANCHORS-OFFLINE.json retain integration, gates, evidence and limitations.
