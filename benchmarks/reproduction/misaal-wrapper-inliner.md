# MISAAL blur3x3 parent SIGSEGV: diagnosis and bounded repair

The latest failure is a **host C++ argument-bounds bug in `CustomInliner`**, with strong matching crash/source evidence. It is not evidence that ARM cannot compile the x86 target. No compiler, generator, native debugger, build, or device code was executed for this investigation. Shared acquired sources were not edited.

## Evidence and confidence

The retained [parent capture](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/040dad21da9c00a6e1cfaa78546bbcddf70516668743a27b2535c3d667352d9c/attempt-0001/capture/generation/capture.json) reports `generator_returncode=-11`; its one [Python child](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/040dad21da9c00a6e1cfaa78546bbcddf70516668743a27b2535c3d667352d9c/attempt-0001/capture/generation/children/child-0000/capture.json) reports success with 198 required Hydride functions. That child's `legalizations[0].returncode` and `legalizations[0].validation.verify_returncode` are both 0. The verified legalized LLVM SHA-256 is `869d5d752fe9f68dae7a630d90dc495d2c6d5445cc39a24a88463ddfb043c638`. Thus Egglog/Python/LLVM legalization had completed before the parent failure; this does not establish completion of the parent compiler or final outputs.

The matching [macOS crash report](/Users/saul/Library/Logs/DiagnosticReports/blur3x3_generator-2026-09-24-223841.ips) records PID 66913, capture time `2026-09-24 22:38:38.5249 -0700`, ARM64 native (not translated), `EXC_BAD_ACCESS / SIGSEGV`, invalid address zero. Its SHA-256 is `ca63f6511b323469760e9153144374c1c870c789f706daee9a613e2680861938`. The top stack is:

```text
llvm::ValueHandleBase::AddToUseList() +32
llvm::ValueMap<...>::operator[](...) +68
Halide::Internal::CustomInliner(llvm::CallInst*) +212
Halide::Internal::CodeGen_LLVM::add_hydride_code() +3596
```

At [CodeGen_LLVM.cpp:373](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/prerequisites/misaal-44ff/attempt-20260925T051740Z-ef4010cc/sources/MISAAL/frontends/halide/src/CodeGen_LLVM.cpp:373), the custom inliner loops over `CI->getNumOperands()`, then accesses `CI->getArgOperand(i)` and `CF->arg_begin()+i`, inserting the latter in `VMap`. LLVM12 call operands include the callee and any bundle operands; [its actual installed API](</opt/homebrew/opt/llvm@12/include/llvm/IR/InstrTypes.h:1311>) exposes `arg_size()` separately and asserts `getArgOperand(i)` is within the argument range. The Halide [build flags](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/prerequisites/misaal-44ff/attempt-20260925T051740Z-ef4010cc/halide-build/src/CMakeFiles/Halide.dir/flags.make) include `-DNDEBUG`, suppressing LLVM's ordinary assertion. The loop consequently advances past the formal arguments and uses an invalid `Value*`, fitting the crash in `VMap`'s value-handle registration. The last printed wrapper body is not necessarily the wrapper being inlined when it crashes: the implementation collects calls before invoking `CustomInliner` on them.

This defect is present in exact revision `44ff893445d664cd87f52b08a138260ed2015ba8`, rather than caused by the new capture checks. Linux/x86 manifestation is untested: undefined behavior can differ by allocation/build, so Docker cannot be promised to repair it.

## Implemented patch and tests

Only these mirror files changed, against fresh `.baseline/misaal-inliner/` snapshots:

| File | SHA-256 |
|---|---|
| `scripts/reproduction_prepare_misaal.py` | `b54589a41fa5722e9e7721916e79cf745da1d363809be1edd1d9c0a5c96382c8` |
| `tests/test_reproduction_prepare_misaal.py` | `308b0e7ebf816d74359c92dd9577500607ef187ff03dd3ad3bcf1762843fa2d4` |

[Reviewable patch](MISAAL-INLINER.patch) adds `patch_wrapper_inliner`, called before the first Halide configure/build. Its exact-context source patch changes the bound to `CI->arg_size()` and requires a non-variadic callee with matching argument count using Halide's always-active `internal_assert`. It preserves instruction cloning, remapping, return replacement, rules, costs, and extraction. Requests now also pin `frontends/halide/src/CodeGen_LLVM.cpp`.

**10 lightweight tests passed; two-file Ruff, formatting and Mypy passed.** Tests verify unchanged surrounding source, rejection before mutation on context drift, before/after hash receipts and diff, and execution ordering before the first Halide configure. An offline copy of the actual acquired source matched the patch exactly: before `8598345443d9092fa97640d67db79c3438540389906ccb594842c293f91e06c4`, patched temporary fixture `d74788b6e6ad003503918ea42841efffb8d0fd8d4db32dee9aa51096eb80d453`. That fixture was temporary; acquired source remains unchanged. These checks do not claim the rebuilt compiler works.

## Smallest diagnostic and continuation gates

For an isolated native regression, compile a tiny LLVM12 harness containing this original helper and a one-argument wrapper call, with assertions enabled. The original should fail `getArgOperand`'s bounds assertion at the extra callee operand; patched code should inline and `verifyModule` should succeed. Add zero- and two-argument wrappers. No target device needs to execute. A harness using retained legalized IR may then check the real wrapper set before another eight-minute parent run. This is proposed, not executed.

For the existing preparation, the following **proposed continuation** uses the same exclusive lock and guarded, one-job, 5-GiB/30-minute build helper. It archives the exact original library, source, request, and implementation before the allowed source/build update, retains numbered request/result logs, and creates a separate request/settings file. Existing logs, requests, patches and crash evidence are never overwritten. The *derived build library at its old build path* will change, with both byte versions retained under the repair directory; the original failed capture remains historical and must not be relabeled successful. If the existing library/source no longer match, stop and investigate rather than updating expected hashes.

After copying the two patched modules into live root and waiting for the heavy slot, run from `/Users/saul/p/egglog-encoding`:

```bash
EGGLOG_BENCH_MEMORY_GUARD=1 .venv/bin/python - <<'PY'
from datetime import UTC, datetime
from pathlib import Path
import json, shutil, traceback
from scripts.reproduction_prepare_misaal import Preparation, patch_wrapper_inliner, sha256_file, write_json
from scripts.reproduction_process import exclusive_job

root = Path.cwd()
base = Path("/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/040dad21da9c00a6e1cfaa78546bbcddf70516668743a27b2535c3d667352d9c/attempt-0001/capture")
request_path = base / "request.json"
request = json.loads(request_path.read_text())
prep = Path(request["preparation"])
source = Path(request["checkout"]) / "frontends/halide/src/CodeGen_LLVM.cpp"
library = Path(request["library"])
with exclusive_job(root / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
    if sha256_file(source) != "8598345443d9092fa97640d67db79c3438540389906ccb594842c293f91e06c4":
        raise ValueError("CustomInliner source changed")
    if sha256_file(library) != request["library_sha256"]:
        raise ValueError("original Halide library changed")
    for path in (prep / "patches").glob("*.after.json"):
        record = json.loads(path.read_text())
        if sha256_file(Path(record["path"])) != record["sha256"]:
            raise ValueError(f"previous patch changed: {path}")
    repair = prep / f"inliner-repair-{datetime.now(UTC):%Y%m%dT%H%M%S%fZ}"
    repair.mkdir()
    before = {}
    for name, path in {
        "CodeGen_LLVM.cpp.before": source,
        "libHalide.before.dylib": library,
        "capture-request.before.json": request_path,
        "preparer.py": root / "scripts/reproduction_prepare_misaal.py",
    }.items():
        with path.open("rb") as src, (repair / name).open("xb") as dst:
            shutil.copyfileobj(src, dst)
        before[name] = {"original_path": str(path), "sha256": sha256_file(repair / name)}
    write_json(repair / "before.json", before)
    summary = {"status": "failed"}
    try:
        attempt = Preparation(prep, continuation=True)
        patch_wrapper_inliner(attempt)
        attempt.step("halide-inliner-rebuild", [
            "uv", "tool", "run", "--from", "cmake==3.31.10", "cmake", "--build",
            str(prep / "halide-build"), "--target", "Halide", "--parallel", "1",
        ], timeout=1800)
        with library.open("rb") as src, (repair / "libHalide.after.dylib").open("xb") as dst:
            shutil.copyfileobj(src, dst)
        request["library_sha256"] = sha256_file(library)
        request["source_hashes"]["frontends/halide/src/CodeGen_LLVM.cpp"] = sha256_file(source)
        patch = prep / "patches/halide-wrapper-inliner-arguments.patch"
        request["patches"][str(patch.relative_to(prep))] = sha256_file(patch)
        request["inliner_repair"] = str(repair)
        (repair / "requests").mkdir()
        new_request = repair / "requests/misaal-x86-blur3x3.json"
        write_json(new_request, request)
        settings = json.loads((root / "benchmarks/local/reproduction/settings.json").read_text())
        settings["misaal"]["paths"]["requests"] = str(repair / "requests")
        write_json(repair / "settings.json", settings)
        summary.update(status="rebuilt-not-validated", request=str(new_request),
                       library_sha256=request["library_sha256"], source_sha256=sha256_file(source),
                       settings=str(repair / "settings.json"))
    except BaseException:
        with (repair / "failure.txt").open("x") as output:
            output.write(traceback.format_exc())
        raise
    finally:
        write_json(repair / "summary.json", summary)
        print(json.dumps({"repair": str(repair), **summary}, indent=2))
PY
```

Use the printed fresh settings path in the next separately guarded coordinator run:

```bash
EGGLOG_BENCH_MEMORY_GUARD=1 .venv/bin/python -m scripts.suite_reproduction \
  --family misaal --case misaal-x86-blur3x3 --stage all \
  --settings /ABSOLUTE/PATH/PRINTED/ABOVE/settings.json
```

Success must include the complete parent and all declared generator outputs, verified host LLVM, materialized complete sessions, and standalone ordinary contracts. The old `.egg` prefix remains diagnostic until then. Fixing this bounds bug does not certify the entire custom inliner: its manual single-path cloning/return handling may expose separate bugs on other wrappers. Those need their own minimized evidence rather than broad speculative changes here.
