#!/usr/bin/env python3
"""Verify a future complete P1 capture without executing binaries."""
import argparse
import difflib
import hashlib
import json
import os
from pathlib import Path
import re

BASE = Path(__file__).resolve().parent
ROOT = Path(os.environ.get("PACK32_OUTPUT_ROOT", str(BASE / "probe-01")))
FIELDS = ["a_eq_c", "b_eq_d", "a_neq_b", "c_neq_d", "target_neq"]
EXPECTED = {
    "encoding": [True] * 5, "manual": [True] * 5,
    "cancellation-rescue": [True, False, True, True, True], "disequality-rescue": [True] * 5,
    "bridge-off": [True] * 5, "consumer-off": [True] * 5,
    "cancellation-off": [False] * 5, "reverse-off": [True, True, False, False, False],
    "forward-off": [True, True, True, True, False], "query-off": [True, True, True, True, None],
    "seed-only": [None] * 5, "primitive-only": [None] * 5,
}
BASELINE_MODES = ["off", "seed-only", "primitive-only", "cancellation-off", "reverse-off", "forward-off", "query-off", "bridge-off", "consumer-off"]
OPTIMIZED_MODES = ["manual", "encoding", "cancellation-rescue", "disequality-rescue"]


def inspect():
    positive = json.loads((ROOT / "positive-results.json").read_text())
    by = {row["mode"]: row for row in positive}
    assert set(by) == {"u0", *BASELINE_MODES, *OPTIMIZED_MODES}
    report = {"status": "actual-host/native mechanism gate only; no speedup claim", "causal": {}, "functions": {}, "gates": {}}
    for row in positive:
        mode = row["mode"]
        accepted = [query for query in row["queries"] if query["accepted"]]
        report["causal"][mode] = [{field: query.get(field) for field in [*FIELDS, "bottom", "export", "consumer_enabled"]} for query in accepted]
        if mode not in {"u0", "off"}:
            assert accepted, (mode, "no actual host query admitted")
            for query in accepted:
                assert "analysis_error" not in query, query
                assert [query[field] for field in FIELDS] == EXPECTED[mode], (mode, query)
                assert query["export"] == (mode in {*OPTIMIZED_MODES, "consumer-off"})
                assert query["bottom"] is (None if mode in {"seed-only", "primitive-only"} else False)
                assert len(query["source_signature"]["domains"]) == 4
        native = ROOT / "matrix/positive" / mode / "native"
        llvm = (native / "program.ll").read_text()
        functions = {}
        for name in ["main", "_main"]:
            match = re.search(r"^define [^\n]*@" + name + r"\([^\n]*\n.*?^\}", llvm, re.M | re.S)
            assert match, (mode, name)
            text = match.group(0) + "\n"
            (native / (name + ".ll")).write_text(text)
            functions[name] = {"score99": bool(re.search(r"\bi64 99\b", text)),
                               "i64_equalities": len(re.findall(r"\bicmp eq i64\b", text)),
                               "conditional_branches": len(re.findall(r"\bbr i1\b", text)),
                               "sha256": hashlib.sha256(text.encode()).hexdigest()}
        report["functions"][mode] = functions
        assert functions["main"]["score99"] == (mode not in OPTIMIZED_MODES), mode
    for mode in BASELINE_MODES:
        assert by[mode]["emitted_sha256"] == by["u0"]["emitted_sha256"], mode
        assert by[mode]["main_sha256"] == by["u0"]["main_sha256"], mode
    for mode in OPTIMIZED_MODES:
        assert by[mode]["emitted_sha256"] == by["encoding"]["emitted_sha256"], mode
        assert by[mode]["main_sha256"] == by["encoding"]["main_sha256"], mode
    assert by["encoding"]["main_sha256"] != by["u0"]["main_sha256"]
    encoding = next(query for query in by["encoding"]["queries"] if query["accepted"])
    for mode in ["seed-only", "primitive-only", "manual"]:
        first = next(query for query in by[mode]["queries"] if query["accepted"])
        assert first["source_signature"] == encoding["source_signature"], mode
        assert first["source_metadata"] == encoding["source_metadata"], mode
        assert first["original_graph_and_seeds"] == encoding["original_graph_and_seeds"], mode
    for mode in ["seed-only", "primitive-only"]:
        for query in by[mode]["queries"]:
            if not query["accepted"]:
                continue
            assert query["program"] == query["original_graph_and_seeds"]
            for flag in ["bottom_checked", "injectivity_saturated", "engine_witness_queries_run", "manual_closure_run", "equality_sort_reasoning_enabled"]:
                assert query[flag] is False, (mode, flag)
            assert query["original_equality_seed"] and query["original_disequality_seed"]
            if mode == "primitive-only":
                assert query["primitive_comparisons"] and all(item["equal"] for item in query["primitive_comparisons"])
                assert query["primitive_only_marked_fields"] == [] and not query["primitive_only_witness"]
    for mode in [*BASELINE_MODES, *OPTIMIZED_MODES]:
        for query in by[mode]["queries"]:
            if query["accepted"]:
                assert query["original_graph_and_seeds"].replace(":injective", "") == encoding["original_graph_and_seeds"].replace(":injective", "")
    negatives = []
    for phase in ["negative", "loop-negative", "context-negative"]:
        rows = json.loads((ROOT / (phase + "-results.json")).read_text())
        negatives.extend(rows)
        for row in rows:
            assert not any(query.get("export") for query in row["queries"]), row
        if phase != "context-negative":
            for family in {row["family"] for row in rows}:
                group = {row["mode"]: row for row in rows if row["family"] == family}
                for mode in ["off", "seed-only", "primitive-only", "manual", "encoding"]:
                    assert group[mode]["emitted_sha256"] == group["u0"]["emitted_sha256"], (family, mode)
                    assert group[mode]["main_sha256"] == group["u0"]["main_sha256"], (family, mode)
    for row in positive + negatives:
        assert all(item["stdout"] == item["expected_stdout"] for item in row["outputs"])
    commands = [json.loads(path.read_text()) for path in (ROOT / "commands").glob("*/receipt.json")]
    assert commands and all(row["exit_code"] == 0 and not row["timed_out"] for row in commands)
    for a, b in [("u0", "off"), ("manual", "encoding"), ("u0", "encoding")]:
        for name in ["main.ll", "_main.ll", "main.asm"]:
            left = (ROOT / "matrix/positive" / a / "native" / name).read_text()
            right = (ROOT / "matrix/positive" / b / "native" / name).read_text()
            (ROOT / (a + "-" + b + "-" + name + ".diff")).write_text("".join(difflib.unified_diff(left.splitlines(True), right.splitlines(True), fromfile=a + "/" + name, tofile=b + "/" + name)))
    report["gates"] = dict(actual_host_query_admitted=True, exact_outputs=True, native_difference=True,
                            B1_matches_U0=True, faithful_manual_matches_encoding=True,
                            causal_knockouts_restore_U0=True, both_intermediate_rescues_restore_encoding=True,
                            same_graph_seed_only_null=True, same_graph_executed_primitive_null=True,
                            negative_boundaries_preserved=True, complete_native_checks=sum(len(row["outputs"]) for row in positive + negatives),
                            performance_samples=0, full_validation="not evaluated by this inspection")
    output = ROOT / "inspection.json"
    assert not output.exists(), "Preserve prior inspection; choose a fresh output root"
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report["gates"], indent=2))


if __name__ == "__main__":
    argparse.ArgumentParser(description=__doc__).parse_args()
    inspect()
