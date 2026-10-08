"""Pinned equality/serialization behavior, without importing pattern populations."""

from __future__ import annotations

import hashlib
import itertools
import json
import pickle
import sys
from enum import Enum, auto
from pathlib import Path
from types import ModuleType
from typing import Any

import pytest

from scripts import reproduction_misaal_patterns as repair

FIXTURE = Path(__file__).parent / "fixtures/misaal-pattern-dedup-source.json"


@pytest.fixture
def original(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[ModuleType, dict[str, Any]]:
    """Compile verbatim source classes/functions, bypassing unrelated imports.

    Only integer-semantics construction and phase-test parsing/pruning support
    are stubbed. The equality, renderer, operand classes and dedup oracle are
    original code. Source-contract fixtures use their own recorded file hashes.
    """
    evidence = json.loads(FIXTURE.read_text())
    modules = {}
    for package in ("common", "compiler", "patterns"):
        parent = ModuleType(package)
        parent.__path__ = []
        monkeypatch.setitem(sys.modules, package, parent)
    shared: dict[str, Any] = {"Enum": Enum, "auto": auto}
    test_pins = {}
    for name in ("common.Types", "common.Instructions", "compiler.Pattern", "patterns.PatternUtils"):
        relative, expected = repair.SOURCE_SHA256[name]
        source = evidence["files"][relative]
        assert source["sha256"] == expected
        code = "\n\n".join(source["definitions"].values()) + "\n"
        path = tmp_path / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(code)
        module = ModuleType(name)
        module.__dict__.update(shared)
        module.__file__ = str(path)
        module.__dict__.update(
            parse_dict=lambda _: [], integer_arith_sema_dict={}, get_ctx_expr_ctx_names=lambda *_: []
        )
        monkeypatch.setitem(sys.modules, name, module)
        exec(compile(code, str(path), "exec", dont_inherit=True), module.__dict__)
        modules[name] = module
        shared.update({key: value for key, value in module.__dict__.items() if not key.startswith("__")})
        test_pins[name] = (relative, hashlib.sha256(path.read_bytes()).hexdigest())
    module = modules["patterns.PatternUtils"]
    module.__dict__["parse_pattern_from_string"] = lambda left, right, *args, **kwargs: module.Pattern(left, right)
    monkeypatch.setattr(repair, "SOURCE_SHA256", test_pins)
    request = {
        "checkout": str(tmp_path),
        "revision": evidence["revision"],
        "pattern_deduplication": repair.CONTRACT,
    }
    patch = (Path(__file__).parents[1] / "benchmarks/reproduction/patches/misaal-03-patterns.diff").read_text()
    hunk = patch.split("@@\n", 1)[1].split("\n@@", 1)[0]
    updated = "\n".join(line[1:] for line in hunk.splitlines() if line.startswith((" ", "+")))
    updated = updated.split("\ndef deduplicate_patterns_parallel", 1)[0]
    namespace = dict(module.__dict__)
    exec(compile(updated, "misaal-03-patterns.diff", "exec"), namespace)
    module.__dict__["patched_deduplicate_patterns"] = namespace["deduplicate_patterns"]
    return module, request


def context(module: ModuleType, name: str, *arguments: Any, halide: bool = False) -> Any:
    result = module.Context(name=name, dsl_name="typed:test", extensions={"halide": True} if halide else None)
    result.context_args = list(arguments)
    return result


def test_original_last_object_orientation_metadata_and_order(original: tuple[ModuleType, dict[str, Any]]) -> None:
    module, _ = original
    left = context(module, "left", module.Reg("0", 16, 128), halide=True)
    right = context(module, "right", module.Integer("k", value=7))
    first = module.Pattern(left, right, name="discarded", bidirectional=False, src_language="first")
    middle = module.Pattern(context(module, "other"), left, name="middle")
    last = module.Pattern(right, left, name="last", bidirectional=True, src_language="last")
    patterns = [first, middle, last]
    before = pickle.dumps(patterns)
    expected = module.deduplicate_patterns(patterns)
    actual = module.patched_deduplicate_patterns(patterns)
    assert [id(item) for item in actual] == [id(item) for item in expected] == [id(middle), id(last)]
    assert actual[-1].src_expr is right and actual[-1].target_expr is left
    assert actual[-1].name == "last" and actual[-1].src_language == "last" and actual[-1].bidirectional
    assert pickle.dumps(patterns) == before


def test_original_exact_rendering_and_non_context_equivalence(original: tuple[ModuleType, dict[str, Any]]) -> None:
    module, _ = original
    a = context(module, "a", module.Reg("0", 8, 128), halide=True)
    typed = context(module, "a", module.Reg("0", 16, 128), halide=True)
    named = context(module, "different-name", module.Reg("0", 8, 128), halide=True)
    nested = context(module, "nested", a, module.ConstBitVector("0xffff", 16))
    patterns = [
        module.Pattern(a, a),
        module.Pattern(a, typed),
        module.Pattern(a, named),
        module.Pattern(nested, a),
        module.Pattern(module.Reg("1", 8, 64), nested),
        module.Pattern(nested, module.Integer("different", 99)),
    ]
    assert patterns[-1].equal_to(patterns[-2])  # Preserve the original non-Context -> "Reg" quirk.
    expected = module.deduplicate_patterns(patterns)
    assert [id(p) for p in module.patched_deduplicate_patterns(patterns)] == [id(p) for p in expected]
    assert len(expected) == 5


def test_bounded_original_oracle_with_shared_objects(original: tuple[ModuleType, dict[str, Any]]) -> None:
    module, _ = original
    a, b = context(module, "a"), context(module, "b")
    choices = [module.Pattern(a, b), module.Pattern(b, a), module.Pattern(a, a), module.Pattern(b, b)]
    for indices in itertools.product(range(len(choices)), repeat=5):
        patterns = [choices[index] for index in indices]
        expected = module.deduplicate_patterns(patterns)
        assert [id(p) for p in module.patched_deduplicate_patterns(patterns)] == [id(p) for p in expected]
    assert module.patched_deduplicate_patterns([]) == []
    assert module.patched_deduplicate_patterns([choices[0]]) == [choices[0]]
    choices[0].swap()  # No stale persistent render-key cache after original mutation.
    assert module.patched_deduplicate_patterns(choices) == module.deduplicate_patterns(choices)


def test_render_count_is_linear(original: tuple[ModuleType, dict[str, Any]], monkeypatch: pytest.MonkeyPatch) -> None:
    module, _ = original
    patterns = [module.Pattern(context(module, str(i)), context(module, str(i + 1))) for i in range(128)]
    render = module.Context.emit_context_expr_string
    calls = 0

    def counted(self: Any, *args: Any, **kwargs: Any) -> str:
        nonlocal calls
        calls += 1
        return str(render(self, *args, **kwargs))

    monkeypatch.setattr(module.Context, "emit_context_expr_string", counted)
    assert module.patched_deduplicate_patterns(patterns) == patterns
    assert calls == 2 * len(patterns)


def test_bounded_real_source_renderings(original: tuple[ModuleType, dict[str, Any]]) -> None:
    module, _ = original
    samples = json.loads(FIXTURE.with_name("misaal-pattern-dedup-samples.json").read_text())["samples"]

    def restore(tree: dict[str, Any]) -> Any:
        if tree["kind"] == "reg":
            return module.Reg(tree["index"], tree["precision"], tree["size"], signed=tree["signed"])
        if tree["kind"] == "integer":
            return module.Integer("sample", value=tree["value"])
        result = context(module, tree["name"], *(restore(arg) for arg in tree["args"]), halide=True)
        result.dsl_name = tree["dsl_name"]
        return result

    patterns = []
    for sample in samples:
        expressions = [restore(item["tree"]) for item in sample["expressions"]]
        assert [expr.emit_context_expr_string() for expr in expressions] == [
            item["rendered"] for item in sample["expressions"]
        ]
        patterns.append(module.Pattern(*expressions, name=str(sample["source_record_index"])))
    patterns.extend([patterns[0], module.Pattern(patterns[1].target_expr, patterns[1].src_expr, name="reversed")])
    before = pickle.dumps(patterns)
    assert [id(p) for p in module.patched_deduplicate_patterns(patterns)] == [
        id(p) for p in module.deduplicate_patterns(patterns)
    ]
    assert pickle.dumps(patterns) == before


_PAPER_PARAMETER_SOURCE = r"""
class PatternAbstractor:
    def emit_create_param_abstract_spec(self, input_values, output_value):
        return "(TESTS {} (vector {}))".format(output_value, " ".join([str(v) for v in input_values]))

    def emit_synthesize_query(self, test_cases, depth = 2, num_src_regs = 2, exclude_regs = []):
        return "(synthesize-param-expression {} {} {} (list {}))".format(test_cases, depth, num_src_regs - 1, " ".join([str(reg) for reg in exclude_regs]))

    def generate_param_expr(self, src_param_map, dst_param_map, dst_param_name, depth = 2, only_src_params = False, exclude_regs = []):
        statements = []

        assert dst_param_name in dst_param_map, "Expected {} in dst_param_map".format(dst_param_name)

        num_test_cases = len(dst_param_map[dst_param_name])
        num_unique_test_cases = len(list(set(dst_param_map[dst_param_name])))

        # Short circuit for those parameters
        # which are always the same value
        if num_unique_test_cases == 1:
            return True, Integer("const", value = dst_param_map[dst_param_name][0])

        # Optimize for the case where the value is always to same as a src param
        dst_values = dst_param_map[dst_param_name]
        for src_param_name, src_values in src_param_map.items():
            if src_values == dst_values:
                print("Short circuited values")
                return True, Reg(int(src_param_name), 8, 8)


        if not self.examples_limit is None:
            num_test_cases = min(num_test_cases, self.examples_limit)
        test_cases_def = []
        for tc in range(num_test_cases):
            values = []

            target_value = dst_param_map[dst_param_name][tc]

            for src_val_name, src_vals in src_param_map.items():
                values.append(src_vals[tc])

            if not only_src_params:
                # Do not include other target pattern params if
                # want to synthesize in terms of src numeric parameters
                # only
                for dst_val_name, dst_vals in dst_param_map.items():
                    if dst_val_name == dst_param_name:
                        continue
                    values.append(dst_vals[tc])
            test_case = self.emit_create_param_abstract_spec(values, target_value)
            test_cases_def.append(test_case)


        test_def = "(define param-test-cases (list \n{}\n))".format("\n".join(test_cases_def))
        statements.append(test_def)

        synthesis_query = self.emit_synthesize_query("param-test-cases", depth = depth,  num_src_regs = len([key for key in src_param_map]), exclude_regs = exclude_regs)

        synthesis_result = "(define-values (sat? expr) {})".format(synthesis_query)
        statements.append(synthesis_result)

        sat_cond = "sat?"
        unsat_cond = "else"


        read_out_fname = next(tempfile._get_candidate_names()) + ".temp"
        sat_case = "(write-str-to-file (~v {}) \"{}\") (exit 0)".format("expr", read_out_fname)
        unsat_case = "(exit 1)"

        handler = emit_racket_cond([sat_cond, unsat_cond] , [sat_case, unsat_case])
        statements.append(handler)

        result = execute_racket_file(statements)

        success = result.returncode == 0

        simplified_expr = None
        if success:
            with open(read_out_fname, "r") as ReadFile:
                simplified_expr = ReadFile.read()
                if REMOVE_RKT_FILES:
                    subprocess.call("rm -f {}".format(read_out_fname), shell = True)
        return success, simplified_expr

    def generate_param_expr_general(self, param_map, param_name, depth = 2, exclude_regs = []):
        statements = []

        assert param_name in param_map, "Expected {} in param_map".format(param_name)

        num_test_cases = len(param_map[param_name])
        num_unique_test_cases = len(list(set(param_map[param_name])))

        # Short circuit for those parameters
        # which are always the same value
        if num_unique_test_cases == 1:
            return True, Integer("const", value = param_map[param_name][0])

        if not self.examples_limit is None:
            num_test_cases = min(num_test_cases, self.examples_limit)
        test_cases_def = []


        # Optimize for the case where the value is always to same as a src param
        dst_values = param_map[param_name]
        for other_param_name, other_values in param_map.items():
            if other_param_name == param_name:
                continue
            if other_param_name < (len(exclude_regs) + 1):
                continue
            if other_values == dst_values:
                print("Short circuited values general")
                return True, Reg(int(other_param_name) - 1, 8, 8)


        for tc in range(num_test_cases):
            values = []

            target_value = param_map[param_name][tc]

            for params, p_values in param_map.items():
                if params == param_name:
                    continue
                values.append(p_values[tc])

            test_case = self.emit_create_param_abstract_spec(values, target_value)
            test_cases_def.append(test_case)


        test_def = "(define param-test-cases (list \n{}\n))".format("\n".join(test_cases_def))
        statements.append(test_def)

        synthesis_query = self.emit_synthesize_query("param-test-cases", depth = depth, exclude_regs = exclude_regs)

        synthesis_result = "(define-values (sat? expr) {})".format(synthesis_query)
        statements.append(synthesis_result)

        sat_cond = "sat?"
        unsat_cond = "else"


        read_out_fname = next(tempfile._get_candidate_names()) + ".temp"
        sat_case = "(write-str-to-file (~v {}) \"{}\") (exit 0)".format("expr", read_out_fname)
        unsat_case = "(exit 1)"

        handler = emit_racket_cond([sat_cond, unsat_cond] , [sat_case, unsat_case])
        statements.append(handler)

        result = execute_racket_file(statements)

        success = result.returncode == 0

        simplified_expr = None
        if success:
            with open(read_out_fname, "r") as ReadFile:
                simplified_expr = ReadFile.read()
                if REMOVE_RKT_FILES:
                    subprocess.call("rm -f {}".format(read_out_fname), shell = True)
        return success, simplified_expr
"""  # noqa: E501 -- verbatim source evidence
_RACKET_COND_SOURCE = 'def emit_racket_cond(clauses, cases):\n\n    cond = ["(cond"]\n\n    for i in range(len(clauses)):\n        if i == len(clauses) - 1 and len(clauses) != 1:\n            cond.append("[else {}]".format(cases[i]))\n        else:\n            cond.append("[{} {}]".format(clauses[i], cases[i]))\n\n    cond.append(")")\n\n    return "\\n".join(cond)\n'  # noqa: E501 -- verbatim source evidence

_LITERAL_AXIOMS = r"""; Literals Casts
(rewrite
     (LIT val prec)
    (typed_cast-int-extend (LIT val (/ prec 2)) (/ prec 2) 1 1 prec)
    ;:when ((< val 255))
)

(rewrite
     (LIT val prec)
    (typed_cast-uint-extend (LIT val (/ prec 2)) (/ prec 2) 1 1 prec)
    ;:when ((< val 255))
)
(rewrite (Other x) (Other x))
"""


def test_literal_patch_preserves_rhs_and_blocks_only_nonpositive_halving(tmp_path: Path) -> None:
    import subprocess

    from scripts.hardboiled_replay import egglog_forms

    source = tmp_path / "targets/halide/axioms.egg"
    source.parent.mkdir(parents=True)
    original = _LITERAL_AXIOMS.replace(
        "(rewrite (Other x) (Other x))", "\n; Halide casts of broadcast is equal to broadcast of casts"
    )
    source.write_text(original)
    series = (Path(__file__).parents[1] / "benchmarks/reproduction/patches/misaal-03-patterns.diff").read_text()
    patch = tmp_path / "literal.diff"
    patch.write_text("--- a/targets/halide/axioms.egg" + series.split("--- a/targets/halide/axioms.egg", 1)[1])
    subprocess.run(["git", "apply", "--check", str(patch)], cwd=tmp_path, check=True)
    subprocess.run(["git", "apply", str(patch)], cwd=tmp_path, check=True)
    for kind in ("int", "uint"):
        before = next(tokens for _, _, tokens in egglog_forms(original) if f"typed_cast-{kind}-extend" in tokens)
        after = next(
            tokens for _, _, tokens in egglog_forms(source.read_text()) if f"typed_cast-{kind}-extend" in tokens
        )
        boundary = after.index(":when")
        assert after[:boundary] + [")"] == before
        assert after[boundary:] == [":when", "(", "(", ">", "prec", "1", ")", ")", ")"]
        for width in (1, 2, 8):
            assert (width > int(after[boundary + 5])) is (width // 2 > 0)
