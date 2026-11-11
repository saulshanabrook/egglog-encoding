"""Data-only immutable request derivation; run only after the sealed native gate."""

import argparse
import copy
import hashlib
import importlib.util
import json
import shutil
import sys
import traceback
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
POLICY = "exact-render-last-v1"
FAMILIES = {"misaal", "eggcc", "churchroad", "dialegg", "speq", "hardboiled"}


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def require_successful_gate(gate, result_path, expected_manifest, sha_file=digest):
    """Require the sealed driver's complete native run and unchanged evidence."""
    manifest_path = gate / "manifest.json"
    if sha_file(manifest_path) != expected_manifest:
        raise ValueError("native gate manifest changed")
    manifest = json.loads(manifest_path.read_text())
    result = json.loads(result_path.read_text())
    if (result.get("status") != "success" or result.get("inputs_unchanged") is not True
            or result.get("manifest_sha256") != expected_manifest or result.get("corpus_admission") is not False):
        raise ValueError("complete native gate SUCCESS is required before publication")
    for relative, expected in manifest["package_files"].items():
        if sha_file(gate / relative) != expected:
            raise ValueError(f"sealed gate member changed: {relative}")
    spec = importlib.util.spec_from_file_location("sealed_selector_gate", gate / "run.py")
    driver = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(driver)
    if driver.source_inventory(gate / "sources") != manifest["source_members"]:
        raise ValueError("sealed source membership changed")
    attempt = result_path.parent.resolve()
    if driver.source_inventory(attempt / "sources") != result["patched_sources"]:
        raise ValueError("compiled source membership changed")
    for relative, expected in result["artifacts"].items():
        path = attempt / relative
        if not path.resolve().is_relative_to(attempt) or sha_file(path) != expected:
            raise ValueError(f"native output changed: {relative}")
    wanted = {f"{variant}-{name}" for variant in ("old", "fixed") for name in manifest["fixtures"]}
    wanted.update("capture-" + name for name in manifest["captures"])
    if len(wanted) != 12 or set(result["gates"]) != wanted:
        raise ValueError("native gate omitted or added a check")
    for name, row in result["gates"].items():
        if row.get("status") != "passed":
            raise ValueError(f"native check did not pass: {name}")
        should_lower = name.startswith("capture-") or (
            name.startswith("fixed-") and manifest["fixtures"][name.removeprefix("fixed-")]["expected"] == "success"
        )
        audit = row["audit"]
        if (audit["missing_functions"] or audit["undefined_return_functions"]
                or audit["status"] != ("success" if should_lower else "failure")
                or bool(audit["unlowered_hydride_call_functions"]) == should_lower):
            raise ValueError(f"native audit contract differs: {name}")
        emitted = attempt / (name + ".ll")
        if sha_file(emitted) != row["output_sha256"]:
            raise ValueError(f"native checked LLVM changed: {name}")
    step_names = ["llvm-version", "cmake-version", "configure", "build"]
    for variant in ("old", "fixed"):
        for name in manifest["fixtures"]:
            step_names.extend([f"{variant}-{name}", f"{variant}-{name}-verify"])
    for name in manifest["captures"]:
        step_names.extend(["capture-" + name, "capture-" + name + "-verify"])
    steps = sorted((attempt / "steps").glob("*.result.json"))
    if [p.name.partition("-")[2].removesuffix(".result.json") for p in steps] != step_names:
        raise ValueError("native process sequence is incomplete")
    for path in steps:
        process = json.loads(path.read_text())
        request_path = path.with_name(path.name.replace(".result.json", ".request.json"))
        request = json.loads(request_path.read_text())
        if (process["status"] != "success" or process["returncode"] != 0
                or request["memory_limit_bytes"] != 5 * 1024**3 or request["require_guard"] is not True
                or request["disk_reserve_bytes"] != 10 * 1024**3):
            raise ValueError(f"native step failed or guard contract changed: {path}")
    plugin = Path(result["new_plugin"]["path"])
    if (plugin.resolve() != attempt / "legalizers-build/libx86LegalizerAllArgs.so"
            or sha_file(plugin) != result["new_plugin"]["sha256"]):
        raise ValueError("new native plugin changed or escaped the build")
    derivation = attempt / "patches/legalizer-literal-derivation.json"
    proof = json.loads(derivation.read_text())
    if (proof["contract"] != "x86-selector-literals-v1" or proof["validated_cases"] != 2025
            or proof["validated_guards"] != 24536 or len(proof["changes"]) != 1951
            or len({c["instruction"] for c in proof["changes"]}) != 1349):
        raise ValueError("source-derived literal coverage changed")
    return manifest, result, plugin, derivation


def derive_request(original, plugin, plugin_sha256, provenance, dependencies):
    """Preserve every existing option; change only the approved publication fields."""
    if "pattern_deduplication" in original and original["pattern_deduplication"] != POLICY:
        raise ValueError("conflicting existing pattern policy")
    request = copy.deepcopy(original)
    request["pattern_deduplication"] = POLICY
    request["request_publication"] = provenance
    request["identity_paths"] = list(dict.fromkeys([*original.get("identity_paths", []), *dependencies]))
    if request["configuration"] == {"target": "x86"}:
        request.update(legalizer=str(plugin), legalizer_sha256=plugin_sha256)
        request["environment"]["LEGALIZERS_DIR"] = str(plugin.parent)
        request["compiled_selector_repair"] = {
            "contract": "x86-selector-literals-v1", "evidence": provenance,
            "runtime_checkout_unchanged": True,
            "source_location": "native gate patched_sources and literal derivation, outside the retained runtime checkout",
        }
    elif request["configuration"] not in ({"target": "arm"}, {"target": "hexagon"}):
        raise ValueError("unexpected MISAAL target")
    return request


def runtime_key(request, seal):
    """Cache expensive runtime-tree validation only for identical checked inputs.

    verify_runtime compares the fields below; the only dropped environment field
    is HYDRIDE_BENCHMARK, which it never reads. The verifier implementation is
    itself hash-bound. Per-case source/products still use verified_request.
    """
    fields = {key: request[key] for key in ("racket_runtime", "parameter_abi", "racket_group_containment",
              "racket", "racket_sha256", "environment_unset")}
    fields["environment"] = {k: v for k, v in request["environment"].items() if k != "HYDRIDE_BENCHMARK"}
    fields["source"] = {key: request[key] for key in seal["source"] if key != "source_hashes"}
    fields["source"]["source_hashes"] = {key: request["source_hashes"].get(key) for key in seal["source"]["source_hashes"]}
    return json.dumps(fields, sort_keys=True)


def bind_dedup_sources(request, expected, verified):
    """Add evidence for unchanged prerequisites missing from historical requests."""
    for relative, expected_source in expected.values():
        if relative in request["source_hashes"] and request["source_hashes"][relative] != expected_source:
            raise ValueError(f"conflicting existing deduplication pin: {relative}")
        source_path = str(Path(request["checkout"]) / relative)
        if source_path not in verified:
            verified[source_path] = digest(Path(source_path))
        if verified[source_path] != expected_source:
            raise ValueError(f"deduplication prerequisite changed: {relative}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--settings", type=Path, required=True)
    parser.add_argument("--settings-sha256", required=True)
    parser.add_argument("--gate", type=Path, required=True)
    parser.add_argument("--gate-result", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    sys.path.insert(0, str(root))
    from scripts.misaal_reproduction import verified_request
    from scripts.reproduction_misaal_patterns import SOURCE_SHA256 as DEDUP_SOURCES
    from scripts.reproduction_misaal_runtime import verify_runtime
    from scripts.reproduction_prepare_misaal import write_json
    from scripts.reproduction_process import exclusive_job
    from scripts.reproduction_stages import directory_identity

    manifest_path = HERE / "manifest.json"
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    output = args.output.resolve()
    with exclusive_job(root / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        # Refuse before creating requests unless the native gate actually passed.
        for path, expected in manifest["implementation"].items():
            if digest(root / path) != expected:
                raise ValueError(f"publication implementation changed: {path}")
        for path, expected in manifest["package_files"].items():
            if digest(HERE / path) != expected:
                raise ValueError(f"publication script changed: {path}")
        gate_manifest, native, plugin, derivation = require_successful_gate(
            args.gate.resolve(), args.gate_result.resolve(), manifest["native_manifest_sha256"])
        if digest(args.settings) != args.settings_sha256:
            raise ValueError("selected current settings bytes changed")
        settings_bytes = args.settings.read_bytes()
        settings = json.loads(settings_bytes)
        if set(settings) != FAMILIES:
            raise ValueError("publication requires the current six-family settings")
        requests = Path(settings["misaal"]["paths"]["requests"])
        if str(requests) != manifest["request_directory"] or {p.name for p in requests.glob("*.json")} != set(manifest["requests"]):
            raise ValueError("current102 request membership changed")
        output.mkdir(parents=True, exist_ok=False)
        record = {"status": "blocked", "corpus_admission": False, "required_canaries": ["misaal-x86-tensor_shr", "misaal-x86-conv_nn"]}
        try:
            before = output / "before"
            before.mkdir()
            (before / "settings.json").write_bytes(settings_bytes)
            old_rows = {}
            verified_runtime_scopes = set()
            verified_identities = {}
            dedup_sources = {}
            for name, expected in manifest["requests"].items():
                path = requests / name
                if digest(path) != expected:
                    raise ValueError(f"original request changed: {name}")
                request = verified_request(path)
                if name != request["case_id"] + ".json":
                    raise ValueError("request filename/case mismatch")
                if request["configuration"] == {"target": "x86"} and (
                    request["legalizer"] != gate_manifest["old_plugin"]
                    or request["legalizer_sha256"] != gate_manifest["old_plugin_sha256"]
                ):
                    raise ValueError("x86 request is not derived from the tested original plugin")
                bind_dedup_sources(request, DEDUP_SOURCES, dedup_sources)
                for dependency, expected_dependency in request.get("compile_dependencies", {}).items():
                    if digest(Path(dependency)) != expected_dependency:
                        raise ValueError(f"generator compile dependency changed: {dependency}")
                seal = json.loads(Path(request["racket_runtime"]["path"]).read_text())
                scope = runtime_key(request, seal)
                if scope not in verified_runtime_scopes:
                    verify_runtime(request)
                    verified_runtime_scopes.add(scope)
                for dependency in request.get("identity_paths", []):
                    if dependency not in verified_identities:
                        p = Path(dependency)
                        verified_identities[dependency] = directory_identity(p) if p.is_dir() else digest(p)
                shutil.copyfile(path, before / name)
                old_rows[name] = request
            if Counter(r["configuration"]["target"] for r in old_rows.values()) != {"x86": 32, "arm": 31, "hexagon": 39}:
                raise ValueError("original target population differs")
            evidence = output / "publication-evidence.json"
            write_json(evidence, {
                "contract": "retained-misaal-requests-x86-literals-v1", "pattern_deduplication": POLICY,
                "manifest": {"path": str(manifest_path), "sha256": digest(manifest_path)},
                "base_settings": {"path": str(args.settings.resolve()), "sha256": args.settings_sha256},
                "original_requests": {str(requests / k): v for k, v in manifest["requests"].items()},
                "native_gate": {"path": str(args.gate_result.resolve()), "sha256": digest(args.gate_result)},
                "native_manifest": {"path": str(args.gate.resolve() / "manifest.json"), "sha256": manifest["native_manifest_sha256"]},
                "derivation": {"path": str(derivation), "sha256": digest(derivation)},
                "patched_sources": native["patched_sources"], "new_plugin": native["new_plugin"],
                "dedup_sources": dedup_sources,
                "verified_runtime_scopes": len(verified_runtime_scopes), "reused_identity_paths": verified_identities,
                "scope": "canary request publication only; source and ordinary success still required",
            })
            dependencies = [str(evidence), str(args.gate_result.resolve()), str(args.gate.resolve() / "manifest.json"),
                            str(args.gate_result.resolve().parent / "sources"), str(derivation), str(plugin), *dedup_sources]
            provenance = {"path": str(evidence), "sha256": digest(evidence)}
            new_dir = output / "requests"
            new_dir.mkdir()
            for name, old in old_rows.items():
                new = derive_request(old, plugin, native["new_plugin"]["sha256"], provenance, dependencies)
                write_json(new_dir / name, new)
                verified_request(new_dir / name)
                seal = json.loads(Path(new["racket_runtime"]["path"]).read_text())
                scope = runtime_key(new, seal)
                if scope not in verified_runtime_scopes:
                    verify_runtime(new)
                    verified_runtime_scopes.add(scope)
            overlay = copy.deepcopy(settings)
            overlay["misaal"]["paths"]["requests"] = str(new_dir)
            overlay["misaal"]["identity_paths"] = list(dict.fromkeys([*settings["misaal"].get("identity_paths", []), *dependencies]))
            # No blockers or success rows are invented for the other100 cases.
            if any(overlay[f] != settings[f] for f in FAMILIES - {"misaal"}):
                raise ValueError("another family's settings changed")
            if digest(args.settings) != args.settings_sha256 or any(digest(requests / name) != expected for name, expected in manifest["requests"].items()):
                raise ValueError("original settings/request changed during publication")
            if any(digest(Path(path)) != expected for path, expected in dedup_sources.items()):
                raise ValueError("deduplication source changed during publication")
            require_successful_gate(args.gate.resolve(), args.gate_result.resolve(), manifest["native_manifest_sha256"])
            write_json(output / "settings-canaries.json", overlay)
            record.update(status="canary-ready", settings=str(output / "settings-canaries.json"),
                          request_count=len(old_rows), requests={str(p): digest(p) for p in sorted(new_dir.glob("*.json"))},
                          evidence=str(evidence), evidence_sha256=digest(evidence),
                          settings_sha256=digest(output / "settings-canaries.json"))
        except BaseException as error:
            record.update(reason=f"{type(error).__name__}: {error}")
            (output / "traceback.txt").write_text(traceback.format_exc())
        finally:
            write_json(output / "result.json", record)
        print(json.dumps({k: record[k] for k in ("status", "required_canaries")}, indent=2))
        return int(record["status"] != "canary-ready")


if __name__ == "__main__":
    raise SystemExit(main())
