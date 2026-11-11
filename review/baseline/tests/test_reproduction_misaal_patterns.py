"""Pinned equality/serialization behavior, without importing pattern populations."""

from __future__ import annotations

import hashlib
import itertools
import json
import pickle
import sys
import threading
from enum import Enum, auto
from pathlib import Path
from types import FunctionType, ModuleType
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
