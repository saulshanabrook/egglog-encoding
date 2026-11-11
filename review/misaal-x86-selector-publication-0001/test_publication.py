"""Small synthetic receipts only; never invokes native tools or real publication."""

import copy
import json
import tempfile
import unittest
from pathlib import Path

from publish import bind_dedup_sources, derive_request, digest, require_successful_gate, runtime_key


class RequestTests(unittest.TestCase):
    def test_historical_missing_dedup_pins_verified_without_mutating_request(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            expected = {}
            for name in ["PatternUtils.py", "Pattern.py", "Instructions.py", "Types.py"]:
                (root / name).write_text("original " + name)
                expected[name] = (name, digest(root / name))
            request = {"checkout": directory, "source_hashes": {"PatternUtils.py": expected["PatternUtils.py"][1]}}
            before = copy.deepcopy(request)
            verified = {}
            bind_dedup_sources(request, expected, verified)
            self.assertEqual(request, before)
            self.assertEqual(verified, {str(root / name): sha for name, sha in expected.values()})
            request["source_hashes"]["Pattern.py"] = "wrong pin"
            with self.assertRaisesRegex(ValueError, "conflicting existing"):
                bind_dedup_sources(request, expected, {})
            del request["source_hashes"]["Pattern.py"]
            (root / "Pattern.py").write_text("changed")
            with self.assertRaisesRegex(ValueError, "prerequisite changed"):
                bind_dedup_sources(request, expected, {})

    def test_all102_exact_policy_and_x86_only_replacement(self):
        count = 0
        for target, total in [("x86", 32), ("arm", 31), ("hexagon", 39)]:
            for index in range(total):
                old = {"case_id": f"{target}-{index}", "configuration": {"target": target},
                       "source_hashes": {"compiler": "unchanged"}, "legalizer": "/old/lib.so",
                       "legalizer_sha256": "old-plugin", "environment": {"LEGALIZERS_DIR": "/old", "LOOKAHEAD": "0"},
                       "identity_paths": ["/original/evidence"], "source_timeout_sec": 600,
                       "literal_width_guard": "positive-literal-halving-v1", "racket_runtime": {"path": "/seal", "sha256": "seal"}}
                original = copy.deepcopy(old)
                new = derive_request(old, Path("/fresh/libx86LegalizerAllArgs.so"), "new-plugin", {"path": "/provenance"}, ["/native/result"])
                self.assertEqual(old, original)
                expected = copy.deepcopy(old)
                expected.update(pattern_deduplication="exact-render-last-v1", request_publication={"path": "/provenance"},
                                identity_paths=["/original/evidence", "/native/result"])
                if target == "x86":
                    expected.update(legalizer="/fresh/libx86LegalizerAllArgs.so", legalizer_sha256="new-plugin")
                    expected["environment"]["LEGALIZERS_DIR"] = "/fresh"
                    expected["compiled_selector_repair"] = new["compiled_selector_repair"]
                    self.assertEqual(new["compiled_selector_repair"]["contract"], "x86-selector-literals-v1")
                self.assertEqual(new, expected)
                self.assertNotIn("configuration_blockers", new)
                count += 1
        self.assertEqual(count, 102)

    def test_conflicting_policy_and_unknown_target_fail(self):
        for policy in (None, False, "other"):
            with self.assertRaisesRegex(ValueError, "conflicting"):
                derive_request({"pattern_deduplication": policy}, Path("/new"), "hash", {}, [])
        with self.assertRaisesRegex(ValueError, "unexpected"):
            derive_request({"configuration": {"target": "fake"}}, Path("/new"), "hash", {}, [])

    def test_runtime_cache_omits_only_unchecked_benchmark_label(self):
        request = {"racket_runtime": {}, "parameter_abi": "abi", "racket_group_containment": "lease", "racket": "/racket",
                   "racket_sha256": "sha", "environment_unset": ["PLTCOLLECTS"], "checkout": "/source", "revision": "rev",
                   "source_hashes": {"source": "hash", "case.cpp": "case"},
                   "environment": {"HYDRIDE_BENCHMARK": "caseA", "PLTUSERHOME": "/sealed"}}
        seal = {"source": {"checkout": "/source", "revision": "rev", "source_hashes": {"source": "hash"}}}
        baseline = runtime_key(request, seal)
        request["environment"]["HYDRIDE_BENCHMARK"] = "caseB"
        self.assertEqual(runtime_key(request, seal), baseline)
        for field in ("PLTUSERHOME", "PLTEXTRA"):
            changed = copy.deepcopy(request)
            changed["environment"][field] = "wrong"
            self.assertNotEqual(runtime_key(changed, seal), baseline)
        request["source_hashes"]["source"] = "changed"
        self.assertNotEqual(runtime_key(request, seal), baseline)


class GateTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.gate = Path(self.temporary.name) / "gate"
        self.gate.mkdir()
        self.attempt = self.gate / "attempt"
        self.attempt.mkdir()
        code = "from pathlib import Path\nimport hashlib\ndef source_inventory(p):\n return {str(x.relative_to(p)): hashlib.sha256(x.read_bytes()).hexdigest() for x in p.rglob('*') if x.is_file()}\n"
        (self.gate / "run.py").write_text(code)
        for directory in (self.gate / "sources", self.attempt / "sources"):
            directory.mkdir()
            (directory / "selector.cpp").write_text("pinned")
        source_members = {"selector.cpp": digest(self.gate / "sources/selector.cpp")}
        fixtures = {"srav512": {"expected": "success"}, "srav256": {"expected": "success"},
                    "srav128": {"expected": "success"}, "wrong-boolean": {"expected": "rejected"},
                    "wrong-width-selector": {"expected": "rejected"}}
        manifest = {"package_files": {"run.py": digest(self.gate / "run.py")}, "source_members": source_members,
                    "fixtures": fixtures, "captures": {"tensor_shr": {}, "conv_nn": {}}}
        (self.gate / "manifest.json").write_text(json.dumps(manifest))
        self.expected_manifest = digest(self.gate / "manifest.json")
        plugin = self.attempt / "legalizers-build/libx86LegalizerAllArgs.so"
        plugin.parent.mkdir()
        plugin.write_text("compiled plugin")
        (self.attempt / "patches").mkdir()
        # Keep the real expected population/counts but tiny synthetic entries.
        proof = {"contract": "x86-selector-literals-v1", "validated_cases": 2025, "validated_guards": 24536,
                 "changes": [{"instruction": str(i % 1349)} for i in range(1951)]}
        (self.attempt / "patches/legalizer-literal-derivation.json").write_text(json.dumps(proof))
        gates = {}
        names = ["llvm-version", "cmake-version", "configure", "build"]
        for variant in ("old", "fixed"):
            for name, expected in fixtures.items():
                key = f"{variant}-{name}"
                lowered = variant == "fixed" and expected["expected"] == "success"
                gates[key] = self.row(key, lowered)
                names.extend([key, key + "-verify"])
        for name in manifest["captures"]:
            key = "capture-" + name
            gates[key] = self.row(key, True)
            names.extend([key, key + "-verify"])
        (self.attempt / "steps").mkdir()
        for index, name in enumerate(names, 1):
            prefix = self.attempt / "steps" / f"{index:03}-{name}"
            prefix.with_suffix(".result.json").write_text(json.dumps({"status": "success", "returncode": 0}))
            prefix.with_suffix(".request.json").write_text(json.dumps({"memory_limit_bytes": 5 * 1024**3,
                "require_guard": True, "disk_reserve_bytes": 10 * 1024**3}))
        self.result = {"status": "success", "inputs_unchanged": True, "corpus_admission": False,
                       "manifest_sha256": self.expected_manifest, "patched_sources": source_members,
                       "new_plugin": {"path": str(plugin), "sha256": digest(plugin)}, "gates": gates,
                       "artifacts": {str(p.relative_to(self.attempt)): digest(p) for p in self.attempt.rglob("*") if p.is_file()}}
        self.result_path = self.attempt / "result.json"
        self.result_path.write_text(json.dumps(self.result))

    def row(self, name, lowered):
        output = self.attempt / (name + ".ll")
        output.write_text("synthetic native output")
        return {"status": "passed", "output_sha256": digest(output), "audit": {
            "status": "success" if lowered else "failure", "missing_functions": [], "undefined_return_functions": [],
            "unlowered_hydride_call_functions": [] if lowered else ["original"]}}

    def test_complete_data_contract_accepted(self):
        _, result, plugin, _ = require_successful_gate(self.gate, self.result_path, self.expected_manifest)
        self.assertEqual(result["status"], "success")
        self.assertEqual(plugin.name, "libx86LegalizerAllArgs.so")

    def test_failed_incomplete_or_unchecked_negative_cannot_publish(self):
        for mutation in ("status", "gates", "negative", "guard"):
            with self.subTest(mutation=mutation):
                changed = copy.deepcopy(self.result)
                if mutation == "status":
                    changed["status"] = "memory-limit"
                elif mutation == "gates":
                    del changed["gates"]["capture-conv_nn"]
                elif mutation == "negative":
                    changed["gates"]["fixed-wrong-boolean"]["audit"]["status"] = "success"
                else:
                    path = self.attempt / "steps/001-llvm-version.result.json"
                    path.write_text(json.dumps({"status": "memory-limit", "returncode": -9}))
                    changed["artifacts"][str(path.relative_to(self.attempt))] = digest(path)
                self.result_path.write_text(json.dumps(changed))
                with self.assertRaises(ValueError):
                    require_successful_gate(self.gate, self.result_path, self.expected_manifest)

    def test_modified_or_added_compiler_source_refused(self):
        (self.attempt / "sources/added.cpp").write_text("unpinned compilation input")
        with self.assertRaisesRegex(ValueError, "source membership"):
            require_successful_gate(self.gate, self.result_path, self.expected_manifest)

    def test_modified_plugin_refused(self):
        Path(self.result["new_plugin"]["path"]).write_text("different plugin")
        with self.assertRaisesRegex(ValueError, "native output changed"):
            require_successful_gate(self.gate, self.result_path, self.expected_manifest)


if __name__ == "__main__":
    unittest.main()
