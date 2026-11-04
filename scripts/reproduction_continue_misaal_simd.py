"""Repair only the retained x86 SIMD pass mode; preserve all old native evidence.

The saved linked-LLVM diagnostic is not a source rerun or corpus admission.
The CLI owns the heavy-job lock; every native command uses the 5 GiB guard.
"""

from __future__ import annotations

import argparse
import copy
import difflib
import json
import os
import shutil
from pathlib import Path
from typing import Any

from scripts.reproduction_misaal_legalizer import audit_simd_lowering, simd_mode_replacements
from scripts.reproduction_prepare_misaal import HYDRIDE_REVISION, MISAAL_REVISION, Preparation, sha256_file, write_json
from scripts.reproduction_process import DISK_RESERVE_BYTES, exclusive_job

ROOT = Path(__file__).resolve().parents[1]
SELECTOR = "Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/x86/x86LegalizerAllArgs.cpp"
PATTERN_UTILS = "lib/patterns/PatternUtils.py"


def continue_misaal_simd(
    generators: Path, diagnostic_stage: Path, output: Path, engine: Path, *, timeout_sec: int = 600
) -> dict[str, Any]:
    """Verify the archived 32-parent environment, change one mode, rebuild and derive requests."""
    generators, diagnostic_stage, output, engine = (
        path.resolve() for path in (generators, diagnostic_stage, output, engine)
    )
    durable = (ROOT / "benchmarks/local/reproduction").resolve()
    if (
        output.exists()
        or not all(path.is_relative_to(durable) for path in (generators, diagnostic_stage, output))
        or output.is_relative_to(generators)
        or output.is_relative_to(diagnostic_stage.parent)
        or not engine.is_file()
        or timeout_sec <= 0
    ):
        raise ValueError("continuation requires retained inputs, an ordinary engine and a fresh separate output")
    output.mkdir(parents=True)
    before, native = output / "before", output / "native"
    before.mkdir()
    native.mkdir()
    preparation = Preparation(output)
    record: dict[str, Any] = {
        "status": "blocked",
        "reason": None,
        "generators": str(generators),
        "diagnostic_stage": str(diagnostic_stage),
        "implementation_sha256": sha256_file(Path(__file__)),
        "generator_execution": False,
        "device_execution": False,
        "corpus_admission": False,
    }
    verified: dict[str, str] = {}

    def verify(path: Path, digest: str | None = None) -> str:
        """Bind every prerequisite once, rejecting contradictory or changed archived identities."""
        name = str(path.absolute())
        if name not in verified:
            verified[name] = sha256_file(path)
        actual = verified[name]
        if digest is not None and actual != digest.removeprefix("sha256:"):
            raise ValueError(f"retained prerequisite changed: {path}")
        return actual

    def snapshot(path: Path, destination: Path, digest: str | None = None) -> None:
        """Copy verified original bytes before mutation, retaining their source identity."""
        actual = verify(path, digest)
        destination.parent.mkdir(parents=True, exist_ok=True)
        with path.open("rb") as source, destination.open("xb") as target:
            shutil.copyfileobj(source, target)
        if sha256_file(destination) != actual:
            raise ValueError(f"source changed during preservation: {path}")

    try:
        saved_path = generators / "preparation.json"
        saved = json.loads(saved_path.read_text())
        cases = saved["cases"]
        if (
            saved["status"] != "success"
            or saved["revision"] != MISAAL_REVISION
            or len(cases) != 32
            or {case["id"] for case in saved["selected_cases"]} != set(cases)
            or any(row["status"] != "prepared" or row["configuration"] != {"target": "x86"} for row in cases.values())
            or set((generators / "requests").glob("*.json"))
            != {generators / "requests" / f"{case_id}.json" for case_id in cases}
        ):
            raise ValueError("expected exactly the completed 32 original x86 generator preparations")
        snapshot(saved_path, before / "generator-preparation.json")
        snapshot(generators / "settings.json", before / "settings.json", saved["settings_sha256"])
        snapshot(generators / "identity.json", before / "generator-identity.json")
        requests = {}
        for case_id, row in cases.items():
            path = generators / "requests" / f"{case_id}.json"
            if row["request"] != str(path):
                raise ValueError("generator request escaped its retained preparation")
            snapshot(path, before / "requests" / path.name, row["request_sha256"])
            request = json.loads(path.read_text())
            if any(request[key] != row[key] for key in ("source", "configuration", "generator_sha256")) or (
                request["case_id"] != case_id or request["revision"] != MISAAL_REVISION
            ):
                raise ValueError("archived request differs from its original generator case")
            for key in ("backend", "llvm_as", "python", "generator", "library", "legalizer"):
                verify(Path(request[key]), request[key + "_sha256"])
            for relative, digest in request["source_hashes"].items():
                path = (Path(request["checkout"]) / relative).resolve()
                if not path.is_relative_to(Path(request["checkout"]).resolve()):
                    raise ValueError("request source escaped checkout")
                verify(path, digest)
            for path, digest in request["compile_dependencies"].items():
                verify(Path(path), digest)
            for relative, digest in request["patches"].items():
                verify(Path(request["preparation"]) / relative, digest)
            for step in row["build_steps"]:
                if json.loads(Path(step).read_text())["status"] != "success":
                    raise ValueError("generator preparation includes a failed native build")
                verify(Path(step))
            requests[case_id] = request
        seed = requests["misaal-x86-blur3x3"]
        common = ("checkout", "preparation", "library", "legalizer", "backend", "llvm_as", "python")
        if any(any(request[key] != seed[key] for key in common) for request in requests.values()):
            raise ValueError("generator requests do not share the retained native environment")
        checkout, previous = Path(seed["checkout"]), Path(seed["preparation"])
        if checkout != previous / "sources/MISAAL" or not previous.is_relative_to(durable):
            raise ValueError("unexpected acquired source layout")
        selector = checkout / SELECTOR
        build = previous / "legalizers-build"
        library = build / "libx86LegalizerAllArgs.so"
        if Path(seed["legalizer"]) != library:
            raise ValueError("saved x86 legalizer differs from the retained CMake target")
        stamp_path = previous / "patches/legalizer-exact-wide-constants.after.json"
        stamp = json.loads(stamp_path.read_text())
        if stamp["path"] != str(selector):
            raise ValueError("selector source lacks its retained wide-literal repair identity")
        verify(selector, stamp["sha256"])
        replacements = simd_mode_replacements(selector.read_text(), "x86")
        if len(replacements) != 1:
            raise ValueError("selector is already mode-repaired; use its recorded continuation instead")
        for path in sorted((previous / "patches").glob("*.after.json")):
            patch = json.loads(path.read_text())
            verify(Path(patch["path"]), patch["sha256"])
            snapshot(path, before / "patches" / path.name)
        cache = build / "CMakeCache.txt"
        cache_text = cache.read_text()
        llvm = Path(seed["llvm_as"]).parent.parent
        low_level = selector.parents[2]
        for setting in (
            f"CMAKE_HOME_DIRECTORY:INTERNAL={low_level}",
            f"LLVM_DIR:UNINITIALIZED={llvm}/lib/cmake/llvm",
            "CMAKE_CXX_COMPILER:STRING=/usr/bin/clang++",
        ):
            if setting not in cache_text.splitlines():
                raise ValueError("retained CMake configuration differs from the reviewed native target")
        snapshot(cache, before / "CMakeCache.txt")
        build_command = [
            "uv",
            "tool",
            "run",
            "--from",
            "cmake==3.31.10",
            "cmake",
            "--build",
            str(build),
            "--target",
            "x86LegalizerAllArgs",
            "--parallel",
            "1",
        ]
        old_build = previous / "steps/019-legalizer-build-repaired.request.json"
        old_result = old_build.with_name(old_build.name.replace("request.json", "result.json"))
        if (
            json.loads(old_build.read_text())["command"] != build_command
            or json.loads(old_result.read_text())["status"] != "success"
        ):
            raise ValueError("expected the successful retained original selector build")
        snapshot(old_build, before / old_build.name)
        snapshot(old_result, before / old_result.name)
        # This checks the actual repaired source tree before another native compilation.
        hydride = checkout / "Hydride"
        if (
            preparation.step("hydride-revision", ["git", "rev-parse", "HEAD"], cwd=hydride, timeout=30).strip()
            != HYDRIDE_REVISION
        ):
            raise ValueError("retained Hydride revision changed")
        changed = preparation.step(
            "hydride-local-changes",
            ["git", "diff", "--name-only", "HEAD", "--", "codegen-generator/tools/low-level-codegen"],
            cwd=hydride,
            timeout=30,
        ).splitlines()
        if set(changed) != {
            str((low_level / "CMakeLists.txt").relative_to(hydride)),
            str(selector.relative_to(hydride)),
        }:
            raise ValueError("retained legalizer tree has changes beyond the two recorded compatibility patches")
        pattern_source = preparation.step(
            "pattern-source", ["git", "show", f"{MISAAL_REVISION}:{PATTERN_UTILS}"], cwd=checkout, timeout=30
        )
        if pattern_source != (checkout / PATTERN_UTILS).read_text():
            raise ValueError("newly bound PatternUtils source differs from the pinned MISAAL revision")
        stage = json.loads(diagnostic_stage.read_text())
        if stage["case"] != seed["case_id"]:
            raise ValueError("diagnostic must be the retained blur3x3 source capture")
        snapshot(diagnostic_stage, before / "stage.json")
        captured_path = Path(stage["capture"])
        snapshot(captured_path, before / "capture.json", stage["artifacts"][str(captured_path)])
        captured = json.loads(captured_path.read_text())
        if len(captured["children"]) != 1:
            raise ValueError("diagnostic expects the one retained native Python child")
        child_path = Path(captured["children"][0]["path"])
        snapshot(child_path, before / "child.json", stage["artifacts"][str(child_path)])
        child = json.loads(child_path.read_text())
        if len(child["legalizations"]) != 1:
            raise ValueError("diagnostic expects one retained LLVM legalization")
        legal = child["legalizations"][0]
        functions = set(legal["required_functions"])
        legal_dir = child_path.parent / "legalize-0000"
        old_llvm = legal_dir / Path(legal["validation"]["path"]).name
        linked = old_llvm.with_name(old_llvm.name.replace(".legalize.ll", ".linked.ll"))
        snapshot(old_llvm, before / "original.legalize.ll", stage["artifacts"][str(old_llvm)])
        snapshot(linked, before / "original.linked.ll", stage["artifacts"][str(linked)])
        tools_path = legal_dir / "tools.json"
        snapshot(tools_path, before / "tools.json", stage["artifacts"][str(tools_path)])
        old_opt = json.loads(tools_path.read_text())[-1]
        opt = Path(old_opt["executable"])
        verify(opt, old_opt["executable_sha256"])
        if opt != llvm / "bin/opt" or old_opt["command"] != [
            "opt",
            "-load",
            str(library),
            "-enable-new-pm=0",
            "-x86-hydride-legalize",
            "-adce",
            "-globaldce",
            legal["validation"]["path"].replace(".legalize.ll", ".linked.ll"),
            "-S",
            "-o",
            legal["validation"]["path"],
        ]:
            raise ValueError("saved lowering command differs from the observed x86 pass")
        old_audit = audit_simd_lowering(old_llvm.read_text(), functions)
        write_json(before / "lowering-audit.json", old_audit)
        if old_audit["status"] != "failure" or set(old_audit["undefined_return_functions"]) != functions:
            raise ValueError("diagnostic does not reproduce the recorded undefined-result failure")
        if (
            shutil.disk_usage(output).free
            < DISK_RESERVE_BYTES + library.stat().st_size + Path(seed["library"]).stat().st_size
        ):
            raise ValueError("disk reserve is insufficient to retain native libraries")
        snapshot(selector, before / "selector.cpp", stamp["sha256"])
        snapshot(library, before / library.name, seed["legalizer_sha256"])
        snapshot(Path(seed["library"]), before / "libHalide.dylib", seed["library_sha256"])
        snapshot(checkout / PATTERN_UTILS, before / "PatternUtils.py")
        snapshot(ROOT / "scripts/reproduction_misaal_legalizer.py", before / "reproduction_misaal_legalizer.py")
        write_json(output / "before.json", verified)
        old, new = replacements[0]
        patched = selector.read_text().replace(old, new, 1)
        patch = output / "simd-mode.patch"
        patch.write_text(
            "".join(
                difflib.unified_diff(
                    selector.read_text().splitlines(True), patched.splitlines(True), "a/" + SELECTOR, "b/" + SELECTOR
                )
            )
        )
        selector.write_text(patched)
        write_json(
            output / "selector-after.json",
            {"path": str(selector), "sha256": sha256_file(selector), "patch_sha256": sha256_file(patch)},
        )
        preparation.step("x86-simd-rebuild", build_command, cwd=previous, timeout=timeout_sec)
        if not library.is_file() or not library.stat().st_size or sha256_file(library) == seed["legalizer_sha256"]:
            raise ValueError("rebuild did not produce a changed nonempty selector library")
        rebuilt = native / library.name
        shutil.copyfile(library, rebuilt)
        repaired_llvm = native / "repaired.legalize.ll"
        preparation.step(
            "retained-llvm-lowering",
            [
                str(opt),
                "-load",
                str(rebuilt),
                "-enable-new-pm=0",
                "-x86-hydride-legalize",
                "-adce",
                "-globaldce",
                str(before / "original.linked.ll"),
                "-S",
                "-o",
                str(repaired_llvm),
            ],
            timeout=30,
        )
        audit = audit_simd_lowering(repaired_llvm.read_text(), functions)
        write_json(output / "lowering-audit.json", audit)
        if audit["status"] != "success":
            raise ValueError("rebuilt selector failed the retained LLVM lowering diagnostic")
        preparation.step("retained-llvm-verify", [seed["llvm_as"], str(repaired_llvm), "-o", os.devnull], timeout=30)
        # No previously published request/receipt/runtime may silently change during rebuilding.
        for name, digest in verified.items():
            if name not in {str(selector), str(library)} and sha256_file(Path(name)) != digest:
                raise ValueError(f"unchanged prerequisite changed during continuation: {name}")
        evidence = {str(path): sha256_file(path) for path in sorted(output.rglob("*")) if path.is_file()}
        write_json(output / "evidence.json", evidence)
        request_dir = output / "requests"
        request_dir.mkdir()
        for case_id, old_request in requests.items():
            request = copy.deepcopy(old_request)
            request.update(
                legalizer=str(rebuilt), legalizer_sha256=sha256_file(rebuilt), simd_mode_continuation=str(output)
            )
            request["environment"]["LEGALIZERS_DIR"] = str(native)
            request["source_hashes"].update(
                {relative: sha256_file(checkout / relative) for relative in (SELECTOR, PATTERN_UTILS)}
            )
            request["identity_paths"] = [path for path in request.get("identity_paths", []) if path != str(library)] + [
                str(rebuilt),
                str(output / "evidence.json"),
            ]
            write_json(request_dir / f"{case_id}.json", request)
        settings = {
            "misaal": {
                "revision": MISAAL_REVISION,
                "paths": {"requests": str(request_dir), "checkout": str(checkout), "egglog": str(engine)},
                "timeout_sec": 300,
                "identity_paths": [
                    str(output / "evidence.json"),
                    str(before),
                    str(native),
                    str(llvm),
                    str(previous / "python/lib"),
                    seed["library"],
                    seed["backend"],
                    str(ROOT / "scripts/reproduction_misaal_legalizer.py"),
                ],
            }
        }
        write_json(output / "settings.json", settings)
        record.update(
            status="success",
            settings=str(output / "settings.json"),
            settings_sha256=sha256_file(output / "settings.json"),
            request_count=len(requests),
            requests={str(path): sha256_file(path) for path in sorted(request_dir.glob("*.json"))},
            evidence=str(output / "evidence.json"),
            evidence_sha256=sha256_file(output / "evidence.json"),
            diagnostic="retained linked LLVM only; full source rerun and ordinary validation required",
        )
    except (OSError, ValueError, RuntimeError, KeyError) as error:
        record["reason"] = str(error)
        results = sorted(preparation.logs.glob("*.result.json"))
        if results:
            last = json.loads(results[-1].read_text())
            if last["status"] not in {"success", "failure"}:
                record["status"] = "resource-stopped" if "guard refused" in str(last) else last["status"]
    finally:
        write_json(output / "continuation.json", record)
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generators", type=Path, required=True)
    parser.add_argument("--diagnostic-stage", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--egglog", type=Path, default=ROOT / "target/release/egglog-experimental")
    parser.add_argument("--timeout-sec", type=int, default=600)
    args = parser.parse_args()
    with exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        record = continue_misaal_simd(
            args.generators, args.diagnostic_stage, args.output, args.egglog, timeout_sec=args.timeout_sec
        )
    print(json.dumps(record, indent=2))
    return 0 if record["status"] == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
