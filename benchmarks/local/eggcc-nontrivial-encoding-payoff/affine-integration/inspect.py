#!/usr/bin/env python3
"""Read and assert the retained affine integration evidence without changing it."""

from pathlib import Path
import hashlib
import json
import re

BASE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def accepted(result):
    queries = [query for query in result["queries"] if query.get("accepted") is True]
    assert queries, result["mode"]
    stable = [
        "key_equal",
        "a_equal_c",
        "b_equal_d",
        "pair_equal",
        "mixed_add_known_disequal",
        "z_known_disequal_w",
        "target_known_disequal",
        "export",
        "application_enabled",
    ]
    assert all(
        {field: query.get(field) for field in stable}
        == {field: queries[0].get(field) for field in stable}
        for query in queries
    ), result["mode"]
    return queries[0]


def check_result(result):
    """Bind a matrix row to its source, emitted program, native code, and receipts."""
    family, mode = result["family"], result["mode"]
    folder = BASE / "matrix" / family / mode
    source = BASE / "fixtures" / Path(result["source"]).name
    assert sha(source) == result["source_sha256"]
    assert sha(folder / "optimized.bril") == result["emitted_sha256"]
    assert sha(folder / "native/main.asm") == result["main_sha256"]
    emitter = json.loads(
        (BASE / "commands" / f"{family}-{mode}-emit" / "receipt.json").read_text()
    )
    expected_compiler = (
        BASE.parent / "admission/bin/eggcc" if mode == "u0" else BASE / "bin/eggcc"
    )
    assert emitter["argv"][0] == str(expected_compiler)
    assert emitter["argv"][-1] == str(source)
    assert emitter["scoped_mode"] == mode
    assert emitter["scoped_evidence"] == str(folder / "evidence")
    assert emitter["exit_code"] == 0 and not emitter["timed_out"]
    assert emitter["stdout_sha256"] == result["emitted_sha256"]
    assert any(
        item["path"] == str(expected_compiler)
        and item["sha256"] == sha(expected_compiler)
        for item in emitter["files"]
    )
    assert any(
        item["path"] == str(source) and item["sha256"] == sha(source)
        for item in emitter["files"]
    )
    assert any(
        item["path"] == str(folder / "emit.json")
        and item["sha256"] == sha(folder / "emit.json")
        for item in emitter["files"]
    )
    parsed_receipt = json.loads(
        (BASE / "commands" / f"{family}-{mode}-parse" / "receipt.json").read_text()
    )
    assert parsed_receipt["argv"][0] == str(BASE.parent / "admission/bin/eggcc")
    assert parsed_receipt["argv"][-1] == str(folder / "optimized.bril")
    assert parsed_receipt["exit_code"] == 0 and not parsed_receipt["timed_out"]
    assert any(
        item["path"] == str(folder / "optimized.bril")
        and item["sha256"] == result["emitted_sha256"]
        for item in parsed_receipt["files"]
    )
    parsed = json.loads((folder / "parse.json").read_text())
    assert parsed["original_interpreted"] == parsed["result_interpreted"]
    assert any(
        item["path"] == str(folder / "parse.json")
        and item["sha256"] == sha(folder / "parse.json")
        for item in parsed_receipt["files"]
    )
    lower = json.loads(
        (BASE / "commands" / f"{family}-{mode}-lower" / "receipt.json").read_text()
    )
    assert lower["argv"][0] == str(BASE.parent / "admission/bin/eggcc")
    assert lower["argv"][-1] == str(folder / "optimized.bril")
    assert lower["exit_code"] == 0 and not lower["timed_out"]
    for path in [
        BASE.parent / "admission/bin/eggcc",
        folder / "optimized.bril",
        folder / "native/program",
        folder / "native/program.ll",
        folder / "native/lower.json",
    ]:
        assert any(
            item["path"] == str(path) and item["sha256"] == sha(path)
            for item in lower["files"]
        )
    disassembled = json.loads(
        (BASE / "commands" / f"{family}-{mode}-disassemble" / "receipt.json").read_text()
    )
    assert disassembled["argv"][-1] == str(folder / "native/program")
    assert disassembled["exit_code"] == 0 and not disassembled["timed_out"]
    assert any(
        item["path"] == str(folder / "native/program")
        and item["sha256"] == sha(folder / "native/program")
        for item in disassembled["files"]
    )
    assembly = (folder / "native/program.asm").read_text()
    assert disassembled["stdout_sha256"] == sha(folder / "native/program.asm")
    lines = assembly.splitlines()
    main_blocks = []
    for index, line in enumerate(lines):
        if re.match(r"^[0-9a-f]+ <_?main>:", line):
            end = next(
                (later for later in range(index + 1, len(lines))
                 if re.match(r"^[0-9a-f]+ <.*>:", lines[later])),
                len(lines),
            )
            main_blocks.append("\n".join(lines[index:end]))
    assert main_blocks
    assert (folder / "native/main.asm").read_text() == "\n\n".join(main_blocks) + "\n"
    evidence = folder / "evidence"
    recorded = [
        query
        for path in sorted(evidence.glob("boundary*.json"))
        for query in json.loads(path.read_text())["queries"]
    ]
    assert result["queries"] == recorded, (family, mode)
    for index, row in enumerate(result["outputs"]):
        label = f"{family}-{mode}-native-{index:02}"
        assert (BASE / "commands" / label / "stdout").read_text() == row["stdout"]
        receipt = json.loads((BASE / "commands" / label / "receipt.json").read_text())
        assert receipt["argv"][0] == str(folder / "native/program")
        assert receipt["argv"][1:] == list(map(str, row["args"]))
        assert any(
            item["path"] == str(folder / "native/program")
            and item["sha256"] == sha(folder / "native/program")
            for item in receipt["files"]
        )
        assert receipt["exit_code"] == 0 and not receipt["timed_out"]
        assert row["stdout"] == row["expected"], label


def main():
    positives = json.loads((BASE / "positive-results.json").read_text())
    by_mode = {result["mode"]: result for result in positives}
    expected_modes = {
        "u0",
        "off",
        "seed-only",
        "primitive-only",
        "cancellation-off",
        "forward-off",
        "reverse-off",
        "identity-off",
        "target-rescue",
        "query-off",
        "manual",
        "encoding",
        "bridge-off",
        "application-off",
    }
    assert set(by_mode) == expected_modes
    for result in positives:
        check_result(result)
        assert len(result["outputs"]) == 10

    baseline_modes = {
        "off",
        "seed-only",
        "primitive-only",
        "cancellation-off",
        "forward-off",
        "reverse-off",
        "identity-off",
        "query-off",
        "bridge-off",
        "application-off",
    }
    baseline = by_mode["u0"]
    for mode in baseline_modes:
        assert by_mode[mode]["emitted_sha256"] == baseline["emitted_sha256"], mode
        assert by_mode[mode]["main_sha256"] == baseline["main_sha256"], mode
    encoding = by_mode["encoding"]
    for mode in ["manual", "target-rescue"]:
        assert by_mode[mode]["emitted_sha256"] == encoding["emitted_sha256"], mode
        assert by_mode[mode]["main_sha256"] == encoding["main_sha256"], mode
    assert encoding["emitted_sha256"] != baseline["emitted_sha256"]
    assert encoding["main_sha256"] != baseline["main_sha256"]

    baseline_bril = (BASE / "matrix/positive/u0/optimized.bril").read_text()
    encoding_bril = (BASE / "matrix/positive/encoding/optimized.bril").read_text()
    baseline_asm = (BASE / "matrix/positive/u0/native/main.asm").read_text()
    encoding_asm = (BASE / "matrix/positive/encoding/native/main.asm").read_text()
    assert "const 99" in baseline_bril and "const 99" not in encoding_bril
    assert "#0x63" in baseline_asm and "#0x63" not in encoding_asm

    receipts = {mode: accepted(by_mode[mode]) for mode in expected_modes - {"u0", "off"}}
    full = receipts["encoding"]
    assert full["encoding"] == "NEE"
    assert full["bottom"] is False and full["manual_bottom"] is False
    for field in [
        "key_equal",
        "a_equal_c",
        "b_equal_d",
        "pair_equal",
        "mixed_add_known_disequal",
        "z_known_disequal_w",
        "target_known_disequal",
        "export",
        "application_enabled",
    ]:
        assert full[field] is True, field
    manual = receipts["manual"]
    assert manual["manual_receipts"] == [True] * 7
    assert manual["manual_bottom"] is False
    assert manual["target_known_disequal"] is True and manual["export"] is True
    assert receipts["cancellation-off"]["a_equal_c"] is False
    assert receipts["cancellation-off"]["target_known_disequal"] is False
    assert receipts["forward-off"]["z_known_disequal_w"] is True
    assert receipts["forward-off"]["target_known_disequal"] is False
    assert receipts["reverse-off"]["a_equal_c"] is True
    assert receipts["reverse-off"]["z_known_disequal_w"] is False
    assert receipts["identity-off"]["pair_equal"] is True
    assert receipts["identity-off"]["a_equal_c"] is False
    assert receipts["query-off"]["z_known_disequal_w"] is True
    assert receipts["query-off"]["target_known_disequal"] is None
    assert receipts["bridge-off"]["target_known_disequal"] is True
    assert receipts["bridge-off"]["export"] is False
    assert receipts["application-off"]["target_known_disequal"] is True
    assert receipts["application-off"]["export"] is True
    assert receipts["application-off"]["application_enabled"] is False
    rescue = receipts["target-rescue"]
    assert rescue["target_known_disequal"] is True
    assert rescue["exact_target_rescue"] is True
    assert rescue["affine_marked"] is False
    assert rescue["odd_mul_marked"] is False
    assert rescue["reverse_enabled"] is False
    assert rescue["representation_identity"] is False
    primitive = receipts["primitive-only"]
    seed_only = receipts["seed-only"]
    assert primitive["program"] == seed_only["program"]
    assert primitive["injectivity_saturated"] is False
    assert primitive["engine_witness_queries_run"] is False
    assert primitive["primitive_only_dynamic_witness"] is False
    strip_schedule = lambda program: program.replace(
        "(run-schedule (saturate injectivity))\n", ""
    )
    assert primitive["program"] == strip_schedule(full["program"])

    negatives = json.loads((BASE / "negative-results.json").read_text())
    negative_summary = {}
    for family in sorted({result["family"] for result in negatives}):
        family_results = {result["mode"]: result for result in negatives if result["family"] == family}
        assert set(family_results) == {"u0", "off", "seed-only", "manual", "encoding"}
        reference = family_results["u0"]
        for result in family_results.values():
            check_result(result)
            assert result["emitted_sha256"] == reference["emitted_sha256"]
            assert result["main_sha256"] == reference["main_sha256"]
            assert len(result["outputs"]) == 1
            assert result["outputs"][0]["stdout"] == "99\n"
            assert not any(query.get("accepted") is True for query in result["queries"])
        negative_summary[family] = {
            "emitted_and_native_match_u0": True,
            "accepted_queries": 0,
        }

    contexts = json.loads((BASE / "context-negative-results.json").read_text())
    for result in contexts:
        check_result(result)
    contexts = {result["mode"]: result for result in contexts}
    assert set(contexts) == {"u0", "encoding"}
    assert contexts["u0"]["emitted_sha256"] == contexts["encoding"]["emitted_sha256"]
    assert contexts["u0"]["main_sha256"] == contexts["encoding"]["main_sha256"]
    assert contexts["encoding"]["queries"] == []
    assert all(len(result["outputs"]) == 10 for result in contexts.values())

    verification = json.loads((BASE / "verification.json").read_text())
    assert verification["status"] == "passed"
    assert verification["interpretations"] == 200
    laws = verification["semantic_laws"]
    assert laws["determinant"] == -1
    assert laws["full_width_pairs"] == 4145
    assert [row["width"] for row in laws["reduced_exhaustive"]] == list(range(2, 9))
    assert all(row["pairs"] == (1 << row["width"]) ** 2 for row in laws["reduced_exhaustive"])
    assert 3 * laws["inverse_of_three_mod_2_64"] % (1 << 64) == 1
    ledger = json.loads((BASE / "failure-ledger.json").read_text())
    assert ledger["semantic_attempts"] == 1
    assert ledger["semantic_revisions"] == 0
    assert len({row["label"] for row in verification["rows"]}) == 200
    for row in verification["rows"]:
        interpreted_path = BASE / "interpreted" / f"{row['label']}.json"
        program_path = interpreted_path.with_suffix(".bril")
        assert program_path.read_text().splitlines()[0] == (
            "# ARGS: " + " ".join(map(str, row["args"]))
        )
        receipt = json.loads(
            (BASE / "commands" / f"interp-{row['label'].replace('/', '-')}" / "receipt.json").read_text()
        )
        assert receipt["argv"][0] == str(BASE.parent / "admission/bin/eggcc")
        assert receipt["argv"][-1] == str(program_path)
        assert receipt["exit_code"] == 0 and not receipt["timed_out"]
        for path in [program_path, interpreted_path]:
            assert any(
                item["path"] == str(path) and item["sha256"] == sha(path)
                for item in receipt["files"]
            )
        interpreted = json.loads(interpreted_path.read_text())
        assert interpreted["original_interpreted"] == row["expected"]
        assert interpreted["result_interpreted"] == row["expected"]
        assert row["actual"] == row["expected"]

    command_receipts = sorted((BASE / "commands").glob("*/receipt.json"))
    command_data = {}
    for path in command_receipts:
        receipt = json.loads(path.read_text())
        assert sha(path.parent / "stdout") == receipt["stdout_sha256"], path
        assert sha(path.parent / "stderr") == receipt["stderr_sha256"], path
        command_data[path.parent.name] = receipt
    failed_commands = {
        label: receipt["exit_code"]
        for label, receipt in command_data.items()
        if receipt["exit_code"] != 0 or receipt["timed_out"]
    }

    identities = json.loads((BASE / "identities.json").read_text())
    assert identities["admitted_u0_mismatches"] == []
    assert identities["selected_engine_mismatches"] == []
    for tracked in identities["files"]:
        assert sha(Path(tracked["path"])) == tracked["sha256"], tracked["path"]

    validation = json.loads((BASE / "validation.json").read_text())
    assert validation["status"] == "native_gate_passed_broad_validation_failed"
    assert failed_commands == validation["failed_command_receipts"], failed_commands
    assert validation["snapshots_accepted"] is False
    assert validation["timing_campaign"] is False
    assert validation["native_gate"]["positive_runs"] == 140
    assert validation["native_gate"]["semantic_negative_runs"] == 25
    assert validation["native_gate"]["no_context_runs"] == 20
    assert validation["native_gate"]["source_and_emitted_interpretations"] == 200
    for field, label in [
        ("focused_tests", "validation-focused"),
        ("dag_library_tests", "validation-dag-lib"),
        ("format", "validation-format"),
        ("engine_tests", "validation-engine-final"),
        ("candidate_full_debug", "validation-full-workspace-final"),
        ("candidate_full_release", "validation-host-make-test-release"),
        ("dag_clippy", "validation-dag-clippy-final"),
        ("u0_full_debug", "validation-u0-full-workspace"),
        ("u0_full_release", "validation-u0-release-make-test"),
    ]:
        assert validation[field]["receipt"] == label
        assert validation[field]["exit_code"] == command_data[label]["exit_code"]
        assert validation[field]["timed_out"] == command_data[label]["timed_out"]
        for stream in ("stdout", "stderr"):
            assert validation[field][f"{stream}_sha256"] == command_data[label][f"{stream}_sha256"]
    for field, label, passed in [
        ("focused_tests", "validation-focused", 2),
        ("dag_library_tests", "validation-dag-lib", 66),
        ("engine_tests", "validation-engine-final", 18),
    ]:
        assert validation[field]["passed"] == passed
        assert f"{passed} passed; 0 failed" in (BASE / "commands" / label / "stdout").read_text()
    release_output = (BASE / "commands/validation-host-make-test-release/stdout").read_text()
    release_errors = (BASE / "commands/validation-host-make-test-release/stderr").read_text()
    assert "31 passed; 0 failed" in release_output
    assert "2421 passed; 0 failed" in release_output
    assert "info: 13 snapshots to review" in release_errors
    u0_release_output = (BASE / "commands/validation-u0-release-make-test/stdout").read_text()
    assert "31 passed; 0 failed" in u0_release_output
    assert "2421 passed; 0 failed" in u0_release_output
    assert "64 passed; 0 failed" in u0_release_output
    assert "info: no snapshots to review" in u0_release_output
    assert validation["u0_full_release"]["pending_snapshots"] == 0
    assert command_data["validation-u0-release-make-test"]["git_status_after"] == ""
    assert not list(Path("/private/tmp/eggcc-nontrivial-encoding-payoff-u0/tests/snapshots").glob("*.snap.new"))
    debug_errors = (BASE / "commands/validation-full-workspace-final/stderr").read_text()
    assert "fatal runtime error: stack overflow" in debug_errors
    candidate_debug_output = (BASE / "commands/validation-full-workspace-final/stdout").read_text()
    candidate_debug_failures = [
        line.removeprefix("test ").removesuffix(" ... FAILED").strip()
        for line in candidate_debug_output.splitlines()
        if line.startswith("test ") and line.endswith(" ... FAILED")
    ]
    assert candidate_debug_failures == validation["candidate_full_debug"]["failed_tests_before_abort"]
    u0_debug_output = (BASE / "commands/validation-u0-full-workspace/stdout").read_text()
    u0_debug_errors = (BASE / "commands/validation-u0-full-workspace/stderr").read_text()
    u0_debug_failures = [
        line.removeprefix("test ").removesuffix(" ... FAILED").strip()
        for line in u0_debug_output.splitlines()
        if line.startswith("test ") and line.endswith(" ... FAILED")
    ]
    assert u0_debug_failures == validation["u0_full_debug"]["failed_tests_before_abort"]
    assert "fatal runtime error: stack overflow" in u0_debug_errors
    clippy_errors = (BASE / "commands/validation-dag-clippy-final/stderr").read_text()
    assert clippy_errors.count("src/scoped_reasoning.rs:") == 17
    assert clippy_errors.count("src/extractiongymfastergreedydag.rs:") == 1
    assert clippy_errors.count("src/fastercbcextractor.rs:") == 1
    engine_full_receipt = Path(identities["reused_engine_full_check_receipt"])
    assert validation["engine_full_check"]["receipt"] == str(engine_full_receipt)
    assert json.loads(engine_full_receipt.read_text())["exit_code"] == 0
    parts32_snapshots = {
        row["name"]: row["sha256"]
        for row in json.loads((BASE.parent / "parts32-integration/eggcc-snapshot-comparison.json").read_text())
    }
    prior_release = json.loads(
        (BASE.parent / "parts32-integration/commands/eggcc-make-test/receipt.json").read_text()
    )
    assert prior_release["argv"] == ["make", "test"]
    assert prior_release["exit_code"] == 2 and not prior_release["timed_out"]
    assert validation["historical_engine_harness_failure"]["receipt"] == "validation-engine"
    assert validation["historical_engine_harness_failure"]["exit_code"] == command_data["validation-engine"]["exit_code"]
    retained_snapshots = {
        path.name: sha(path)
        for path in (BASE / "pending-snapshots").glob("*.snap.new")
    }
    candidate_snapshots = {
        path.name: sha(path)
        for path in Path("/private/tmp/eggcc-affine-candidate/tests/snapshots").glob("*.snap.new")
    }
    assert retained_snapshots == candidate_snapshots == parts32_snapshots
    assert validation["candidate_full_release"]["pending_snapshots"] == len(retained_snapshots)
    assert validation["snapshots_accepted"] is False

    summary = {
        "status": validation["status"],
        "semantic_revision_count": ledger["semantic_revisions"],
        "positive_modes": len(positives),
        "positive_native_runs": sum(len(result["outputs"]) for result in positives),
        "negative_fixtures": len(negative_summary),
        "negative_native_runs": sum(len(result["outputs"]) for result in negatives),
        "context_native_runs": sum(len(result["outputs"]) for result in contexts.values()),
        "source_and_emitted_interpretations": verification["interpretations"],
        "successful_captured_commands": len(command_data) - len(failed_commands),
        "failed_captured_commands": failed_commands,
        "u0_b1_emitted_parity": by_mode["u0"]["emitted_sha256"] == by_mode["off"]["emitted_sha256"],
        "u0_b1_native_parity": by_mode["u0"]["main_sha256"] == by_mode["off"]["main_sha256"],
        "manual_encoding_emitted_parity": by_mode["manual"]["emitted_sha256"] == encoding["emitted_sha256"],
        "manual_encoding_native_parity": by_mode["manual"]["main_sha256"] == encoding["main_sha256"],
        "u0": {
            "emitted_sha256": baseline["emitted_sha256"],
            "main_sha256": baseline["main_sha256"],
            "retains_99": True,
        },
        "encoding": {
            "emitted_sha256": encoding["emitted_sha256"],
            "main_sha256": encoding["main_sha256"],
            "retains_99": False,
        },
        "causal_receipts": {
            mode: {
                key: receipt.get(key)
                for key in [
                    "key_equal",
                    "a_equal_c",
                    "b_equal_d",
                    "pair_equal",
                    "mixed_add_known_disequal",
                    "z_known_disequal_w",
                    "target_known_disequal",
                    "export",
                    "application_enabled",
                ]
            }
            for mode, receipt in receipts.items()
        },
        "negative_summary": negative_summary,
        "context_parity": True,
        "files": {
            str(path.relative_to(BASE)): sha(path)
            for path in [
                BASE / "positive-results.json",
                BASE / "negative-results.json",
                BASE / "context-negative-results.json",
                BASE / "verification.json",
                BASE / "matrix.py",
                BASE / "verify.py",
                BASE / "identities.json",
                BASE / "validation.json",
            ]
        },
    }
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
