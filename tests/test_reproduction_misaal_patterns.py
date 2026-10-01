"""Pinned equality/serialization behavior, without importing pattern populations."""

from __future__ import annotations

import ast
import hashlib
import itertools
import json
import pickle
import sys
import threading
from enum import Enum, auto
from pathlib import Path
from types import FunctionType, ModuleType, SimpleNamespace
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
    actual = repair.deduplicate_patterns(patterns, module.Context)
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
    assert [id(p) for p in repair.deduplicate_patterns(patterns, module.Context)] == [id(p) for p in expected]
    assert len(expected) == 5


def test_bounded_original_oracle_with_shared_objects(original: tuple[ModuleType, dict[str, Any]]) -> None:
    module, _ = original
    a, b = context(module, "a"), context(module, "b")
    choices = [module.Pattern(a, b), module.Pattern(b, a), module.Pattern(a, a), module.Pattern(b, b)]
    for indices in itertools.product(range(len(choices)), repeat=5):
        patterns = [choices[index] for index in indices]
        expected = module.deduplicate_patterns(patterns)
        assert [id(p) for p in repair.deduplicate_patterns(patterns, module.Context)] == [id(p) for p in expected]
    assert repair.deduplicate_patterns([], module.Context) == []
    assert repair.deduplicate_patterns([choices[0]], module.Context) == [choices[0]]
    choices[0].swap()  # No stale persistent render-key cache after original mutation.
    assert repair.deduplicate_patterns(choices, module.Context) == module.deduplicate_patterns(choices)


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
    assert repair.deduplicate_patterns(patterns, module.Context) == patterns
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
    assert [id(p) for p in repair.deduplicate_patterns(patterns, module.Context)] == [
        id(p) for p in module.deduplicate_patterns(patterns)
    ]
    assert pickle.dumps(patterns) == before


def test_phase_receipts_and_restoration(original: tuple[ModuleType, dict[str, Any]]) -> None:
    module, request = original
    names = ("create_patterns", "prune_redundant_patterns", "deduplicate_patterns")
    originals = {name: getattr(module, name) for name in names}
    record: dict[str, Any] = {}
    saved = []
    left, right = context(module, "left"), context(module, "right")
    with repair.accelerate_pattern_preparation(
        module, request, record, lambda: saved.append(json.loads(json.dumps(record))), threading.RLock()
    ):
        created = module.create_patterns([{"a": [{"property": {"src": left, "dst": right}}]}], [])
        pruned = module.prune_redundant_patterns(created, [])
        assert module.deduplicate_patterns([*pruned, *pruned]) == created
    observation = record["pattern_preparation"]
    assert observation["status"] == "complete"
    assert [p["phase"] for p in observation["phases"]] == list(names)
    assert [(p["input_count"], p["output_count"]) for p in observation["phases"]] == [(1, 1), (1, 1), (2, 1)]
    assert all(p["status"] == "success" and p["wall_sec"] >= 0 and p["caller"] for p in observation["phases"])
    for name in names:
        assert any(
            phase["phase"] == name and phase["status"] == "running" and "output_count" not in phase
            for snapshot in saved
            for phase in snapshot["pattern_preparation"]["phases"]
        )
    assert all(getattr(module, name) is original for name, original in originals.items())


def test_failed_phase_is_retained_and_restores(original: tuple[ModuleType, dict[str, Any]]) -> None:
    module, request = original
    record: dict[str, Any] = {}
    original_function = module.create_patterns
    with (
        pytest.raises(KeyError),
        repair.accelerate_pattern_preparation(module, request, record, lambda: None, threading.RLock()),
    ):
        module.create_patterns([{"bad": [{}]}], [])
    assert record["pattern_preparation"]["status"] == "failure"
    assert record["pattern_preparation"]["phases"][0]["status"] == "failure"
    assert module.create_patterns is original_function


@pytest.mark.parametrize("changed", list(repair.SOURCE_SHA256))
def test_source_changes_fail_before_replacement(original: tuple[ModuleType, dict[str, Any]], changed: str) -> None:
    module, request = original
    relative, _ = repair.SOURCE_SHA256[changed]
    with (Path(request["checkout"]) / relative).open("a") as file:
        file.write("\n# changed\n")
    before = module.deduplicate_patterns
    record: dict[str, Any] = {}
    with (
        pytest.raises(ValueError, match="source identity changed"),
        repair.accelerate_pattern_preparation(module, request, record, lambda: None, threading.RLock()),
    ):
        pytest.fail("unverified source reached generated imports")
    assert module.deduplicate_patterns is before
    assert record["pattern_preparation"]["status"] == "failure"


def test_loaded_replacement_rejected(original: tuple[ModuleType, dict[str, Any]]) -> None:
    module, request = original
    module.__dict__["deduplicate_patterns"] = lambda patterns: patterns
    with (
        pytest.raises(ValueError, match="already replaced"),
        repair.accelerate_pattern_preparation(module, request, {}, lambda: None, threading.RLock()),
    ):
        pytest.fail("replaced implementation accepted")


def test_same_filename_modified_code_rejected(original: tuple[ModuleType, dict[str, Any]]) -> None:
    module, request = original
    function = module.deduplicate_patterns
    changed = FunctionType(function.__code__.replace(co_consts=(*function.__code__.co_consts, "changed")), vars(module))
    module.__dict__["deduplicate_patterns"] = changed
    with (
        pytest.raises(ValueError, match="loaded code differs"),
        repair.accelerate_pattern_preparation(module, request, {}, lambda: None, threading.RLock()),
    ):
        pytest.fail("modified loaded code accepted")


def test_no_flag_has_no_effect() -> None:
    module = ModuleType("unrelated")
    function = object()
    module.__dict__["deduplicate_patterns"] = function
    record: dict[str, Any] = {}
    with repair.accelerate_pattern_preparation(module, {}, record, lambda: pytest.fail("unexpected write"), None):
        assert module.deduplicate_patterns is function
    assert record == {}


@pytest.mark.parametrize("field,value", [("pattern_deduplication", "unknown"), ("revision", "0" * 40)])
def test_unknown_contract_rejected(original: tuple[ModuleType, dict[str, Any]], field: str, value: str) -> None:
    module, request = original
    request[field] = value
    with (
        pytest.raises(ValueError, match="Unsupported"),
        repair.accelerate_pattern_preparation(module, request, {}, lambda: None, threading.RLock()),
    ):
        pytest.fail("unsupported contract accepted")


# Verbatim c098 parameter methods; the two 44ff edits below are independently
# checked against hashes of their actual retained source method excerpts.
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
_CURRENT_PARAMETER_SOURCE = _PAPER_PARAMETER_SOURCE.replace(
    '    def emit_synthesize_query(self, test_cases, depth = 2, num_src_regs = 2, exclude_regs = []):\n        return "(synthesize-param-expression {} {} {} (list {}))".format(test_cases, depth, num_src_regs - 1, " ".join([str(reg) for reg in exclude_regs]))',  # noqa: E501 -- verbatim source evidence
    '    def emit_synthesize_query(self, test_cases, depth = 2, num_src_regs = 2, exclude_regs = [], reg_only = False):\n        reg_only_str = "#t" if reg_only else "#f"\n        return "(synthesize-param-expression {} {} {} (list {}) {})".format(test_cases, depth, num_src_regs - 1, " ".join([str(reg) for reg in exclude_regs]), reg_only_str)',  # noqa: E501 -- verbatim source evidence
).replace(
    '        synthesis_query = self.emit_synthesize_query("param-test-cases", depth = depth, exclude_regs = exclude_regs)',  # noqa: E501 -- verbatim source evidence
    '        synthesis_query = self.emit_synthesize_query("param-test-cases", depth = depth, exclude_regs = exclude_regs, reg_only = True)',  # noqa: E501 -- verbatim source evidence
)
_PARAMETER_METHOD_SHA256 = {
    "emit_create_param_abstract_spec": "80e7983fa04bc46fb88b77e9c6920febea69815d75e21414a3a16d1e75b91706",
    "emit_synthesize_query": "76dbf34b699463af0e22c50c70ba10da0b3a3f14db9d99c811cfa0f8026fb04c",
    "generate_param_expr": "b22302441f0210286d32182324ca4a33aa5b9a0e2f8ee7e9b1b2dc423ad8f504",
    "generate_param_expr_general": "dc7ff63962eb2de58f7b8a222f9be89ceca12b699ae41d105d153b554886691f",
}
_PARAMETER_RACKET_SOURCE = """
(define (create-param-grammar num-regs)
  (define regs (build-list num-regs (lambda (x)   (reg (bv x 8)))))


  ;; Extend the grammar as needed
  (define-grammar  (param-grammar)
                   [expr_start (choose\x20
                                 (apply choose* regs)
                                 (SCALAR 1)
                                 (SCALAR 2)
                                 (ADD (expr_start) (expr_start))
                                 (MUL (expr_start) (expr_start))
                                 (SUB (expr_start) (expr_start))
                                 (DIV (expr_start) (expr_start))
                                 (MOD (expr_start) (expr_start))
                                 )
                               ]
                   )

  (define (grammar-fn k)
    (param-grammar #:depth k #:start expr_start)
    )
  grammar-fn
  )
(define (synthesize-param-expression test-cases grammar-depth reg-leq exclude-regs)
  (define test-0 (list-ref test-cases 0))
  (define num-reg-inputs (vector-length (TESTS-input-values test-0)))
  (define grammar-generator (create-param-grammar num-reg-inputs))
  (define expr-grammar (grammar-generator grammar-depth))
  (define sol
    (optimize\x20
      #:minimize (list (param_abstract:cost expr-grammar))
      #:guarantee
      (begin
        (generate-constraints test-cases expr-grammar)
        (generate-exclude-reg-constraints expr-grammar exclude-regs)
        ;(assert (param_abstract:contains-reg-leq expr-grammar reg-leq))
        )
      )
    )

  (cond\x20
    [(sat? sol)
     (values #t (evaluate expr-grammar sol))
     ]
    [else
      (values #f '())
      ]
    )
  )
"""
_RACKET_COND_SOURCE = 'def emit_racket_cond(clauses, cases):\n\n    cond = ["(cond"]\n\n    for i in range(len(clauses)):\n        if i == len(clauses) - 1 and len(clauses) != 1:\n            cond.append("[else {}]".format(cases[i]))\n        else:\n            cond.append("[{} {}]".format(clauses[i], cases[i]))\n\n    cond.append(")")\n\n    return "\\n".join(cond)\n'  # noqa: E501 -- verbatim source evidence


@pytest.fixture
def parameter_original(
    original: tuple[ModuleType, dict[str, Any]], monkeypatch: pytest.MonkeyPatch
) -> tuple[ModuleType, ModuleType, dict[str, Any]]:
    module, request = original
    source_path = Path(module.__file__ or "")
    source = source_path.read_text() + "\n" + _CURRENT_PARAMETER_SOURCE
    # A separate newer method must survive installation by object identity.
    source += '\n    def abstract_patterns(self):\n        return "newer bidirectional validation"\n'
    source_path.write_text(source)
    exec(compile(source, str(source_path), "exec", dont_inherit=True), vars(module))
    racket_path = Path(request["checkout"]) / "misaal/synthesis/param_abstract.rkt"
    racket_path.parent.mkdir(parents=True)
    racket_path.write_text(_PARAMETER_RACKET_SOURCE)
    pins = {
        "lib/patterns/PatternUtils.py": hashlib.sha256(source.encode()).hexdigest(),
        "misaal/synthesis/param_abstract.rkt": hashlib.sha256(racket_path.read_bytes()).hexdigest(),
    }
    monkeypatch.setattr(repair, "PARAMETER_ABI_SOURCE_SHA256", pins)
    monkeypatch.setitem(
        repair.SOURCE_SHA256,
        "patterns.PatternUtils",
        ("lib/patterns/PatternUtils.py", pins["lib/patterns/PatternUtils.py"]),
    )
    request.update(parameter_abi=repair.PARAMETER_ABI_CONTRACT, source_hashes=dict(pins))
    module.__dict__.update(
        tempfile=SimpleNamespace(_get_candidate_names=lambda: iter(["parameter-test"])), REMOVE_RKT_FILES=False
    )
    exec(compile(_RACKET_COND_SOURCE, "original-emit_racket_cond.py", "exec", dont_inherit=True), vars(module))
    paper = ModuleType("paper.PatternUtils")
    paper.__dict__.update({name: value for name, value in vars(module).items() if not name.startswith("__")})
    exec(compile(_PAPER_PARAMETER_SOURCE, "paper-PatternUtils.py", "exec", dont_inherit=True), vars(paper))
    return module, paper, request


def emitted_parameter_script(module: ModuleType, general: bool, *, only_src_params: bool = False) -> str:
    """Run the real generator and condition emitter, intercepting only launch.

    Return code 1 avoids a nonexistent solver result file; it does not select or
    change the statements. Constant/alias shortcuts cannot satisfy these maps.
    """
    captures = []

    def execute(statements: list[str]) -> SimpleNamespace:
        captures.append("\n".join(statements))
        return SimpleNamespace(returncode=1)

    module.__dict__["execute_racket_file"] = execute
    instance = module.PatternAbstractor.__new__(module.PatternAbstractor)
    instance.examples_limit = None
    if general:
        assert instance.generate_param_expr_general(
            {0: [2, 4, 6], 1: [1, 2, 3], 2: [5, 7, 11]}, 0, depth=1, exclude_regs=[1]
        ) == (False, None)
    else:
        assert instance.generate_param_expr(
            {0: [1, 2, 3]},
            {0: [2, 4, 6], 1: [5, 7, 11]},
            0,
            depth=2,
            only_src_params=only_src_params,
            exclude_regs=[] if only_src_params else [1],
        ) == (False, None)
    assert len(captures) == 1
    return captures[0]


def test_parameter_source_excerpts_match_retained_44ff() -> None:
    cls = next(item for item in ast.parse(_CURRENT_PARAMETER_SOURCE).body if isinstance(item, ast.ClassDef))
    lines = _CURRENT_PARAMETER_SOURCE.splitlines(keepends=True)
    for method in cls.body:
        assert isinstance(method, ast.FunctionDef) and method.end_lineno is not None
        excerpt = "".join(lines[method.lineno - 1 : method.end_lineno])
        assert hashlib.sha256(excerpt.encode()).hexdigest() == _PARAMETER_METHOD_SHA256[method.name]


@pytest.mark.parametrize("general,only_src_params", [(False, True), (False, False), (True, False)])
def test_real_parameter_generation_matches_paper(
    parameter_original: tuple[ModuleType, ModuleType, dict[str, Any]], general: bool, only_src_params: bool
) -> None:
    module, paper, request = parameter_original
    original_methods = dict(vars(module.PatternAbstractor))
    paths = [Path(request["checkout"]) / relative for relative in request["source_hashes"]]
    original_bytes = [path.read_bytes() for path in paths]
    expected = emitted_parameter_script(paper, general, only_src_params=only_src_params)
    before = emitted_parameter_script(module, general, only_src_params=only_src_params)
    assert before != expected
    assert ("(list 1) #t)" if general else "#f)") in before
    record: dict[str, Any] = {}
    saved = []
    with repair.restore_parameter_abi(module, request, record, lambda: saved.append(json.loads(json.dumps(record)))):
        actual = emitted_parameter_script(module, general, only_src_params=only_src_params)
        assert actual == expected
        assert (
            "(synthesize-param-expression param-test-cases 1 1 (list 1))" in actual
            if general
            else ("(synthesize-param-expression param-test-cases 2 0 (list " in actual)
        )
        assert "(TESTS 2 (vector 1" in actual and "(TESTS 6 (vector 3" in actual
        assert "(define-values (sat? expr)" in actual and "[else (exit 1)]" in actual
        for name, value in original_methods.items():
            if name not in {"emit_synthesize_query", "generate_param_expr_general"}:
                assert vars(module.PatternAbstractor)[name] is value
        assert module.PatternAbstractor().abstract_patterns() == "newer bidirectional validation"
        with pytest.raises(TypeError, match="reg_only"):
            module.PatternAbstractor().emit_synthesize_query("tests", reg_only=True)
    assert vars(module.PatternAbstractor) == original_methods
    assert [path.read_bytes() for path in paths] == original_bytes
    observation = record["parameter_abi"]
    assert observation["status"] == "complete"
    assert "mixed-revision" in observation["semantics"]
    assert set(observation["adapted_methods"]) == {"emit_synthesize_query", "generate_param_expr_general"}
    assert set(observation["original_methods"]) == {
        "emit_create_param_abstract_spec",
        "emit_synthesize_query",
        "generate_param_expr",
        "generate_param_expr_general",
        "abstract_patterns",
    }
    assert [snapshot["parameter_abi"]["status"] for snapshot in saved] == ["verifying", "active", "complete"]


def test_parameter_depth_one_is_not_a_register_only_contract(
    parameter_original: tuple[ModuleType, ModuleType, dict[str, Any]],
) -> None:
    module, paper, request = parameter_original
    with repair.restore_parameter_abi(module, request, {}, lambda: None):
        assert emitted_parameter_script(module, True) == emitted_parameter_script(paper, True)
    # Original depth-one query above needs arithmetic: no available input vector
    # equals the requested output. Its grammar retains scalar 2 and multiplication.
    assert [2, 4, 6] not in ([1, 2, 3], [5, 7, 11])
    assert [2 * value for value in [1, 2, 3]] == [2, 4, 6]
    assert "(SCALAR 2)" in _PARAMETER_RACKET_SOURCE
    assert "(MUL (expr_start) (expr_start))" in _PARAMETER_RACKET_SOURCE
    assert (
        "(define (synthesize-param-expression test-cases grammar-depth reg-leq exclude-regs)"
        in _PARAMETER_RACKET_SOURCE
    )
    # Do not silently re-enable the paper's commented source-register constraint.
    assert ";(assert (param_abstract:contains-reg-leq expr-grammar reg-leq))" in _PARAMETER_RACKET_SOURCE


def test_parameter_shortcuts_still_avoid_launch(
    parameter_original: tuple[ModuleType, ModuleType, dict[str, Any]],
) -> None:
    module, paper, request = parameter_original
    for candidate in (module, paper):
        candidate.__dict__["execute_racket_file"] = lambda _: pytest.fail("shortcut launched Racket")
    with repair.restore_parameter_abi(module, request, {}, lambda: None):
        for candidate in (module, paper):
            instance = candidate.PatternAbstractor()
            instance.examples_limit = None
            success, value = instance.generate_param_expr({0: [1, 2]}, {0: [7, 7]}, 0)
            assert success and value.value == 7
            success, value = instance.generate_param_expr({0: [1, 2]}, {0: [1, 2]}, 0)
            assert success and int(value.index) == 0
            success, value = instance.generate_param_expr_general({0: [7, 7], 1: [1, 2]}, 0)
            assert success and value.value == 7
            success, value = instance.generate_param_expr_general({0: [1, 2], 1: [1, 2]}, 0)
            assert success and int(value.index) == 0


@pytest.mark.parametrize("relative", list(repair.PARAMETER_ABI_SOURCE_SHA256))
@pytest.mark.parametrize("change", ["file", "request", "missing"])
def test_parameter_source_contract_fails_closed(
    parameter_original: tuple[ModuleType, ModuleType, dict[str, Any]], relative: str, change: str
) -> None:
    module, _, request = parameter_original
    before = dict(vars(module.PatternAbstractor))
    if change == "file":
        with (Path(request["checkout"]) / relative).open("a") as file:
            file.write("\n;changed\n")
    elif change == "request":
        request["source_hashes"][relative] = "0" * 64
    else:
        del request["source_hashes"][relative]
    record: dict[str, Any] = {}
    with (
        pytest.raises(ValueError, match="source identity changed"),
        repair.restore_parameter_abi(module, request, record, lambda: None),
    ):
        pytest.fail("unverified parameter source accepted")
    assert vars(module.PatternAbstractor) == before
    assert record["parameter_abi"]["status"] == "failure"


@pytest.mark.parametrize(
    "method", ["emit_synthesize_query", "generate_param_expr", "generate_param_expr_general", "abstract_patterns"]
)
@pytest.mark.parametrize("change", ["code", "globals", "defaults"])
def test_parameter_loaded_method_changes_fail_closed(
    parameter_original: tuple[ModuleType, ModuleType, dict[str, Any]], method: str, change: str
) -> None:
    module, _, request = parameter_original
    original = getattr(module.PatternAbstractor, method)
    code = original.__code__
    namespace = vars(module)
    defaults = original.__defaults__
    if change == "code":
        code = code.replace(co_consts=(*code.co_consts, "changed"))
    elif change == "globals":
        namespace = dict(namespace)
    else:
        defaults = (*defaults, False) if defaults else (False,)
    setattr(module.PatternAbstractor, method, FunctionType(code, namespace, method, defaults))
    before = dict(vars(module.PatternAbstractor))
    with (
        pytest.raises(ValueError, match="loaded method differs"),
        repair.restore_parameter_abi(module, request, {}, lambda: None),
    ):
        pytest.fail("modified parameter method accepted")
    assert vars(module.PatternAbstractor) == before


def test_parameter_equal_but_differently_typed_default_rejected(
    parameter_original: tuple[ModuleType, ModuleType, dict[str, Any]],
) -> None:
    module, _, request = parameter_original
    function = module.PatternAbstractor.emit_synthesize_query
    function.__defaults__ = (2.0, 2, [], False)
    with (
        pytest.raises(ValueError, match="loaded method differs"),
        repair.restore_parameter_abi(module, request, {}, lambda: None),
    ):
        pytest.fail("float depth was accepted as the original integer default")


@pytest.mark.parametrize("failure", ["body", "persist", "interrupt"])
def test_parameter_exception_restores_methods(
    parameter_original: tuple[ModuleType, ModuleType, dict[str, Any]], failure: str
) -> None:
    module, _, request = parameter_original
    before = dict(vars(module.PatternAbstractor))
    record: dict[str, Any] = {}

    def persist() -> None:
        if failure == "persist" and record["parameter_abi"]["status"] == "active":
            raise RuntimeError("receipt failure")

    with (
        pytest.raises(KeyboardInterrupt if failure == "interrupt" else RuntimeError),
        repair.restore_parameter_abi(module, request, record, persist),
    ):
        if failure == "interrupt":
            raise KeyboardInterrupt
        raise RuntimeError("body failure")
    assert vars(module.PatternAbstractor) == before
    assert record["parameter_abi"]["status"] == "failure"


def test_parameter_and_deduplication_contexts_coexist(
    parameter_original: tuple[ModuleType, ModuleType, dict[str, Any]],
) -> None:
    module, paper, request = parameter_original
    with (
        repair.accelerate_pattern_preparation(module, request, {}, lambda: None, threading.RLock()),
        repair.restore_parameter_abi(module, request, {}, lambda: None),
    ):
        assert emitted_parameter_script(module, True) == emitted_parameter_script(paper, True)
        assert module.deduplicate_patterns([]) == []


def test_parameter_no_flag_has_no_effect() -> None:
    record: dict[str, Any] = {}
    with repair.restore_parameter_abi(ModuleType("unrelated"), {}, record, lambda: pytest.fail("unexpected write")):
        assert record == {}


@pytest.mark.parametrize("field,value", [("parameter_abi", "unknown"), ("revision", "0" * 40)])
def test_parameter_unknown_contract_rejected(
    parameter_original: tuple[ModuleType, ModuleType, dict[str, Any]], field: str, value: str
) -> None:
    module, _, request = parameter_original
    request[field] = value
    with (
        pytest.raises(ValueError, match="Unsupported"),
        repair.restore_parameter_abi(module, request, {}, lambda: None),
    ):
        pytest.fail("unsupported parameter ABI accepted")


# Verbatim pinned compiler methods; imports and unrelated base behavior are stubbed.
_LITERAL_COMPILER_SOURCE = r"""import os
class CompilerBase:
    def __init__(self, patterns, src_dsl_list, target_dsl_list):
        self.patterns, self.src_dsl_list, self.target_dsl_list = patterns, src_dsl_list, target_dsl_list
    def get_swizzle_only_patterns(self, patterns): return patterns
    def get_swizzle_movement_only_patterns(self, patterns): return patterns
class EggLogCompiler(CompilerBase):
    def __init__(self, patterns, src_dsl_list = [], target_dsl_list = [], run_iterations = 10, egg_pkg_path = None, prune_patterns = False, skip_axioms = False):
        super().__init__(patterns, src_dsl_list = src_dsl_list, target_dsl_list = target_dsl_list)
        self.egg_pkg_path = egg_pkg_path
        self.egg_manifest_path = os.path.join(self.egg_pkg_path, "Cargo.toml")
        self.egglog_bin = os.path.join(self.egg_pkg_path, "target","debug","egglog")
        self.input_cost = 1000
        self.prune_patterns = prune_patterns
        self.output_cost = 1
        self.run_iterations = run_iterations
        self.compile_times = []
        self.memory_usages = []
        self.measure_egglog_time = True
        self.memo = {}
        self.MISAAL_ROOT = os.getenv('MISAAL_SRC')
        self.axioms_file = os.path.join(self.MISAAL_ROOT, "targets","halide","axioms.egg")
        self.skip_axioms = skip_axioms

    def emit_pattern_matching_based_compiler(self, expr, swizzle_cost = 1):
        egglog_decls = emit_egg_datatypes_two_dsl(self.src_dsl_list, self.target_dsl_list, input_cost = self.input_cost, output_cost = self.output_cost, swizzle_cost = swizzle_cost )

        test_patterns = self.patterns
        if self.prune_patterns:
            reachable_patterns = self.get_reachable_patterns_only(expr)

            print("Pruned patterns for expression ... # Patterns reduced from ", len(test_patterns), "to", len(reachable_patterns))
            test_patterns = reachable_patterns

        egglog_patterns = []
        for pattern in test_patterns:
            rewrite = emit_rewrite_expr(pattern.src_expr, pattern.target_expr, bidirectional = pattern.bidirectional)
            egglog_patterns.append(rewrite)


        axioms = ""

        if not self.skip_axioms:
            # Read in axioms file:
            with open(self.axioms_file, "r") as AxiomFile:
                axioms = AxiomFile.read()


        egg_log_desc = "\n".join([egglog_decls, axioms] + egglog_patterns)
        return egg_log_desc

    def emit_swizzle_pattern_matching_based_compiler(self, expr, swizzle_cost = 1):
        egglog_decls = emit_egg_datatypes_two_dsl(self.src_dsl_list, self.target_dsl_list, input_cost = self.input_cost, output_cost = self.output_cost, swizzle_cost = swizzle_cost )

        test_patterns = self.get_swizzle_only_patterns(self.patterns)
        print("# Swizzle only patterns:", len(test_patterns))

        egglog_patterns = []
        for pattern in test_patterns:
            rewrite = emit_rewrite_expr(pattern.src_expr, pattern.target_expr, bidirectional = pattern.bidirectional)
            egglog_patterns.append(rewrite)


        # Read in axioms file:
        with open(self.axioms_file, "r") as AxiomFile:
            axioms = AxiomFile.read()


        egg_log_desc = "\n".join([egglog_decls, axioms] + egglog_patterns)
        return egg_log_desc

    def emit_swizzle_movement_pattern_matching_based_compiler(self, expr, swizzle_cost = 1):
        egglog_decls = emit_egg_datatypes_two_dsl(self.src_dsl_list, self.target_dsl_list, input_cost = self.input_cost, output_cost = self.output_cost, swizzle_cost = swizzle_cost )

        test_patterns = self.get_swizzle_movement_only_patterns(self.patterns)
        print("# Swizzle only patterns:", len(test_patterns))

        egglog_patterns = []
        for pattern in test_patterns:
            rewrite = emit_rewrite_expr(pattern.src_expr, pattern.target_expr, bidirectional = pattern.bidirectional)
            egglog_patterns.append(rewrite)


        # Read in axioms file:
        with open(self.axioms_file, "r") as AxiomFile:
            axioms = AxiomFile.read()


        egg_log_desc = "\n".join([egglog_decls, axioms] + egglog_patterns)
        return egg_log_desc

"""  # noqa: E501 -- verbatim source evidence
_LITERAL_METHOD_SHA256 = {
    "__init__": "09461d48d00fb6db994c5c9dddb406e8109a2ef847b9e941fdbd34e80ef6bf7e",
    "emit_pattern_matching_based_compiler": "4b336a35ce0c5d320e6fb3fcd49de05af4c42c6b6a7e321cba0f80aa3500d032",
    "emit_swizzle_pattern_matching_based_compiler": "87c2389cf0f74624545cf4ef378ac47af58a4ca13944aec4bbca80eba79d3df9",
    "emit_swizzle_movement_pattern_matching_based_compiler": "0c0da7037029bb326ff8efe67a8d0e7ff8b2dacfa07342f890bf1e1c809b7ccd",  # noqa: E501
}  # noqa: E501
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
"""  # noqa: E501 -- verbatim source evidence


@pytest.fixture
def literal_original(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[ModuleType, dict[str, Any]]:
    sources = {"lib/compiler/EggLogCompiler.py": _LITERAL_COMPILER_SOURCE, "targets/halide/axioms.egg": _LITERAL_AXIOMS}
    for name, source in sources.items():
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
    path = tmp_path / "lib/compiler/EggLogCompiler.py"
    module = ModuleType("compiler.EggLogCompiler")
    module.__file__ = str(path)
    exec(compile(_LITERAL_COMPILER_SOURCE, str(path), "exec", dont_inherit=True), vars(module))
    module.__dict__["emit_egg_datatypes_two_dsl"] = lambda *args, **kwargs: "(datatype Fixture)"
    monkeypatch.setenv("MISAAL_SRC", str(tmp_path))
    pins = {name: hashlib.sha256(source.encode()).hexdigest() for name, source in sources.items()}
    monkeypatch.setattr(repair, "LITERAL_WIDTH_SOURCE_SHA256", pins)
    return module, {
        "checkout": str(tmp_path),
        "revision": "44ff893445d664cd87f52b08a138260ed2015ba8",
        "literal_width_guard": repair.LITERAL_WIDTH_CONTRACT,
        "source_hashes": dict(pins),
    }


def test_literal_compiler_excerpts_match_retained_source() -> None:
    cls = next(
        n
        for n in ast.parse(_LITERAL_COMPILER_SOURCE).body
        if isinstance(n, ast.ClassDef) and n.name == "EggLogCompiler"
    )
    lines = _LITERAL_COMPILER_SOURCE.splitlines(keepends=True)
    for node in cls.body:
        assert isinstance(node, ast.FunctionDef)
        excerpt = "".join(lines[node.lineno - 1 : node.end_lineno])
        assert hashlib.sha256(excerpt.encode()).hexdigest() == _LITERAL_METHOD_SHA256[node.name]


@pytest.mark.parametrize("fail", [False, True])
def test_literal_guard_routes_all_real_emitters_and_restores(
    literal_original: tuple[ModuleType, dict[str, Any]], tmp_path: Path, fail: bool
) -> None:
    module, request = literal_original
    before = dict(vars(module.EggLogCompiler))
    source_path = tmp_path / "targets/halide/axioms.egg"
    record: dict[str, Any] = {}
    instances = []
    snapshots = []
    try:
        with repair.guard_literal_width(
            module,
            request,
            tmp_path,
            record,
            lambda: snapshots.append(record["literal_width_guard"]["status"]),
            threading.Lock(),
        ):
            instance = module.EggLogCompiler([], egg_pkg_path="pinned/backend")
            instances.append(instance)
            assert Path(instance.axioms_file).is_relative_to(tmp_path / "literal-width-guard")
            guarded = Path(instance.axioms_file).read_text()
            # Exactly two insertions, preserving all comments and all other rules.
            assert guarded.count("    :when ((> prec 1))\n") == 2
            assert guarded.replace("    :when ((> prec 1))\n", "") == _LITERAL_AXIOMS
            for name in _LITERAL_METHOD_SHA256:
                if name != "__init__":
                    assert getattr(instance, name)(None) == "(datatype Fixture)\n" + guarded
            assert source_path.read_text() == _LITERAL_AXIOMS
            if fail:
                raise RuntimeError("source child failed")
    except RuntimeError:
        assert fail
    assert vars(module.EggLogCompiler) == before
    assert all(instance.axioms_file == str(source_path) for instance in instances)
    assert module.EggLogCompiler([], egg_pkg_path="backend").axioms_file == str(source_path)
    assert source_path.read_text() == _LITERAL_AXIOMS
    observation = record["literal_width_guard"]
    assert observation["status"] == ("failure" if fail else "complete")
    assert snapshots == ["verifying", "active", "active", observation["status"]]
    for name in ("original", "guarded"):
        item = observation[name + "_axioms"]
        assert hashlib.sha256(Path(item["path"]).read_bytes()).hexdigest() == item["sha256"]


@pytest.mark.parametrize("kind", ["int", "uint"])
@pytest.mark.parametrize("width", [1, 2, 8])
def test_literal_rule_preconditions_and_rhs_preserve_positive_widths(
    literal_original: tuple[ModuleType, dict[str, Any]], tmp_path: Path, kind: str, width: int
) -> None:
    """Inspect real emitted rules; native closure checks are a separate root-run gate."""
    from scripts.hardboiled_replay import egglog_forms

    module, request = literal_original
    with repair.guard_literal_width(module, request, tmp_path, {}, lambda: None, threading.Lock()):
        content = module.EggLogCompiler([], egg_pkg_path="backend").emit_pattern_matching_based_compiler(None)
    rule = next(tokens for _, _, tokens in egglog_forms(content) if f"typed_cast-{kind}-extend" in tokens)
    boundary = rule.index(":when")
    assert rule[boundary:] == [":when", "(", "(", ">", "prec", "1", ")", ")", ")"]
    original = next(tokens for _, _, tokens in egglog_forms(_LITERAL_AXIOMS) if f"typed_cast-{kind}-extend" in tokens)
    assert rule[:boundary] + [")"] == original
    # Evaluate the source predicate, rather than rewriting or dropping its RHS.
    assert (width > int(rule[boundary + 5])) is (width in (2, 8))
    assert width // 2 == {1: 0, 2: 1, 8: 4}[width]


@pytest.mark.parametrize("relative", list(repair.LITERAL_WIDTH_SOURCE_SHA256))
@pytest.mark.parametrize("mutation", ["file", "pin", "missing"])
def test_literal_source_mutations_fail_closed(
    literal_original: tuple[ModuleType, dict[str, Any]], tmp_path: Path, relative: str, mutation: str
) -> None:
    module, request = literal_original
    original = module.EggLogCompiler.__init__
    if mutation == "file":
        with (tmp_path / relative).open("a") as file:
            file.write("\nchanged")
    elif mutation == "pin":
        request["source_hashes"][relative] = "0" * 64
    else:
        del request["source_hashes"][relative]
    with (
        pytest.raises(ValueError, match="source identity changed"),
        repair.guard_literal_width(module, request, tmp_path, {}, lambda: None, threading.Lock()),
    ):
        pytest.fail("modified source accepted")
    assert module.EggLogCompiler.__init__ is original
    assert not (tmp_path / "literal-width-guard").exists()


@pytest.mark.parametrize("mutation", ["code", "globals", "defaults", "closure", "wrapper"])
def test_literal_loaded_initializer_mutations_fail_closed(
    literal_original: tuple[ModuleType, dict[str, Any]], tmp_path: Path, mutation: str
) -> None:
    module, request = literal_original
    original = module.EggLogCompiler.__init__
    code, namespace, defaults, closure = original.__code__, vars(module), original.__defaults__, original.__closure__
    if mutation == "code":
        code = code.replace(co_consts=(*code.co_consts, "changed"))
    elif mutation == "globals":
        namespace = dict(namespace)
    elif mutation == "defaults":
        defaults = (*defaults[:-1], True)
    elif mutation == "closure":
        closure = (type(closure[0])(object()),)
    candidate: Any = FunctionType(code, namespace, "__init__", defaults, closure)
    if mutation == "wrapper":

        def wrapper(*args: Any, **kwargs: Any) -> None:
            original(*args, **kwargs)

        wrapper.__dict__["__wrapped__"] = original
        candidate = wrapper
    module.EggLogCompiler.__init__ = candidate
    with (
        pytest.raises(ValueError, match="loaded initializer differs"),
        repair.guard_literal_width(module, request, tmp_path, {}, lambda: None, threading.Lock()),
    ):
        pytest.fail("modified initializer accepted")
    assert module.EggLogCompiler.__init__ is candidate


@pytest.mark.parametrize("contract", [None, "unknown"])
def test_literal_default_does_nothing_and_unknown_contract_is_rejected(tmp_path: Path, contract: str | None) -> None:
    module = ModuleType("unrelated")
    record: dict[str, Any] = {}
    with repair.guard_literal_width(module, {}, tmp_path, record, lambda: pytest.fail("default persisted"), None):
        assert record == {} and list(tmp_path.iterdir()) == []
    with (
        pytest.raises(ValueError, match="Unsupported"),
        repair.guard_literal_width(module, {"literal_width_guard": contract}, tmp_path, {}, lambda: None, None),
    ):
        pytest.fail("unknown contract accepted")
