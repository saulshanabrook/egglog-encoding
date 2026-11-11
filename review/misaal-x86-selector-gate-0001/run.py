"""One sealed, root-owned native diagnostic. Does not publish capture settings."""

import argparse
import hashlib
import json
import re
import shutil
import sys
import traceback
from pathlib import Path

HERE = Path(__file__).resolve().parent


def source_inventory(directory):
    """Pin membership and bytes before CMake can glob any source file."""
    files = {}
    for path in sorted(directory.rglob("*")):
        if path.is_symlink():
            raise ValueError(f"linked native source: {path}")
        if path.is_file():
            digest = hashlib.sha256()
            with path.open("rb") as stream:
                for block in iter(lambda: stream.read(1024 * 1024), b""):
                    digest.update(block)
            files[str(path.relative_to(directory))] = digest.hexdigest()
        elif not path.is_dir():
            raise ValueError(f"non-regular native source: {path}")
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    sys.path.insert(0, str(root))
    from scripts.reproduction_misaal_legalizer import audit_simd_lowering, simd_mode_replacements
    from scripts.reproduction_misaal_x86_literals import SELECTOR, patch_selector_literals
    from scripts.reproduction_prepare_misaal import Preparation, patch_wide_literals, sha256_file, write_json
    from scripts.reproduction_process import exclusive_job

    with exclusive_job(root / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=False)
        manifest_bytes = (HERE / "manifest.json").read_bytes()
        manifest = json.loads(manifest_bytes)
        result = {"status": "blocked", "corpus_admission": False, "gates": {},
                  "manifest_sha256": hashlib.sha256(manifest_bytes).hexdigest()}
        prep = Preparation(output)
        patched_sources = None

        def verify():
            assert (HERE / "manifest.json").read_bytes() == manifest_bytes, "manifest changed"
            for relative, expected in manifest["package_files"].items():
                assert sha256_file(HERE / relative) == expected, relative
            assert source_inventory(HERE / "sources") == manifest["source_members"], "sealed source tree changed"
            if patched_sources is not None:
                assert source_inventory(output / "sources") == patched_sources, "patched native sources changed"
            for relative, expected in manifest["implementation"].items():
                assert sha256_file(root / relative) == expected, relative
            for path, expected in manifest["external_sources"].items():
                assert sha256_file(Path(path)) == expected, path
            for path, expected in manifest["tools"].items():
                assert sha256_file(Path(path)) == expected, path
            assert sha256_file(Path(manifest["old_plugin"])) == manifest["old_plugin_sha256"]
            if result.get("new_plugin"):
                assert sha256_file(Path(result["new_plugin"]["path"])) == result["new_plugin"]["sha256"], "new plugin changed"

        try:
            verify()
            shutil.copytree(HERE / "sources", output / "sources")
            patch_selector_literals(prep)
            patch_wide_literals(prep)
            selector = output / "sources/MISAAL/Hydride" / SELECTOR
            prep.patch(selector, simd_mode_replacements(selector.read_text(), "x86"), "legalizer-simd-mode")
            no_match = "\n    \n}\n    \n\n};\n\n\nbool X86LegalizationPass::runOnFunction(Function &F) {\n"
            prep.patch(selector, [(no_match, no_match.replace("\n}\n", "\n  return false;\n}\n", 1))],
                       "legalizer-no-match-return")
            patched_sources = source_inventory(output / "sources")
            result["patched_sources"] = patched_sources
            verify()
            llvm = Path(manifest["llvm"])
            version = prep.step("llvm-version", [str(llvm / "bin/llvm-config"), "--version"])
            assert version.strip() == "12.0.1", version
            version = prep.step("cmake-version", [manifest["cmake"], "--version"])
            assert version.startswith("cmake version 3.31.10\n"), version
            source = selector.parents[2]
            build = output / "legalizers-build"
            prep.step("configure", [manifest["cmake"], "-S", str(source), "-B", str(build),
                      f"-DLLVM_DIR={llvm}/lib/cmake/llvm", "-DCMAKE_CXX_COMPILER=/usr/bin/clang++",
                      f'-DCMAKE_CXX_FLAGS=-I{manifest["boost"]}', "-DCMAKE_CXX_FLAGS_RELEASE=-O0 -DNDEBUG"])
            prep.step("build", [manifest["cmake"], "--build", str(build), "--target", "x86LegalizerAllArgs",
                                "--parallel", "1"], timeout=600)
            plugin = build / "libx86LegalizerAllArgs.so"
            result["new_plugin"] = {"path": str(plugin), "sha256": sha256_file(plugin)}
            result["patched_selector_sha256"] = sha256_file(selector)
            for variant, library in [("old", Path(manifest["old_plugin"])), ("fixed", plugin)]:
                for name, contract in manifest["fixtures"].items():
                    verify()
                    fixture = HERE / "fixtures" / (name + ".ll")
                    emitted = output / f"{variant}-{name}.ll"
                    key = f"{variant}-{name}"
                    prep.step(key, [str(llvm / "bin/opt"), "-load", str(library), "-enable-new-pm=0",
                                    "-x86-hydride-legalize", "-adce", "-globaldce", str(fixture), "-S", "-o", str(emitted)],
                              timeout=60)
                    text = emitted.read_text()
                    audit = audit_simd_lowering(text, {contract["function"]})
                    expect_lowered = variant == "fixed" and contract["expected"] == "success"
                    if expect_lowered:
                        assert audit["status"] == "success", (key, audit)
                        body = re.search(r'^define [^\n]*@' + re.escape(contract["function"]) + r'\([^\n]*\{\n(.*?)^}',
                                         text, re.M | re.S)
                        assert body and re.search(r'\bcall\b[^\n]*@' + contract["wrapper"] + r'\(', body[1]), key
                    else:
                        assert audit["missing_functions"] == audit["undefined_return_functions"] == [], (key, audit)
                        assert audit["unlowered_hydride_call_functions"] == [contract["function"]], (key, audit)
                    prep.step(key + "-verify", [str(llvm / "bin/llvm-as"), str(emitted), "-o", str(output / (key + ".bc"))], timeout=30)
                    result["gates"][key] = {"status": "passed", "expected_lowered": expect_lowered,
                                           "audit": audit, "output_sha256": sha256_file(emitted)}
            # Retained complete lowering inputs, not just reduced matching cases.
            for name, capture in manifest["captures"].items():
                verify()
                required = set(json.loads(Path(capture["verify"]).read_text())["required_functions"])
                emitted = output / f"capture-{name}.ll"
                prep.step("capture-" + name, [str(llvm / "bin/opt"), "-load", str(plugin), "-enable-new-pm=0",
                          "-x86-hydride-legalize", "-adce", "-globaldce", capture["linked"], "-S", "-o", str(emitted)],
                          timeout=60)
                audit = audit_simd_lowering(emitted.read_text(), required)
                assert audit["status"] == "success", (name, audit)
                prep.step("capture-" + name + "-verify", [str(llvm / "bin/llvm-as"), str(emitted), "-o",
                          str(output / f"capture-{name}.bc")], timeout=30)
                result["gates"]["capture-" + name] = {"status": "passed", "audit": audit,
                                                       "output_sha256": sha256_file(emitted)}
            verify()
            assert len(result["gates"]) == 12
            result["status"] = "success"
        except BaseException as error:
            result.update(status="failure", reason=f"{type(error).__name__}: {error}")
            (output / "traceback.txt").write_text(traceback.format_exc())
            receipts = sorted(prep.logs.glob("*.result.json"))
            if receipts:
                last = json.loads(receipts[-1].read_text())
                result["process"] = last
                if last["status"] in ("timed-out", "memory-limit", "resource-stopped", "launch-refused"):
                    result["status"] = last["status"]
            if isinstance(error, KeyboardInterrupt):
                result["status"] = "interrupted"
        finally:
            try:
                verify()
                result["inputs_unchanged"] = True
            except BaseException as verification_error:
                result["identity_error"] = f"{type(verification_error).__name__}: {verification_error}"
                if result["status"] not in ("timed-out", "memory-limit", "resource-stopped", "launch-refused", "interrupted"):
                    result["status"] = "failure"
            result["artifacts"] = {str(p.relative_to(output)): sha256_file(p) for p in output.rglob("*")
                                   if p.is_file() and p.name != "result.json"}
            write_json(output / "result.json", result)
        print(json.dumps({k: result[k] for k in ("status", "gates")}, indent=2))
        return int(result["status"] != "success")


if __name__ == "__main__":
    raise SystemExit(main())
