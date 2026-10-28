"""Reference translation must preserve multipatterns and reject omitted constraints."""

import importlib
import random
from pathlib import Path
from typing import Any

import pytest

syntax = importlib.import_module("slotted.reference")
driver = importlib.import_module("slotted.test_program")
LANGUAGES = Path(__file__).resolve().parents[1] / "egglog-experimental/tests/slotted/languages"


def test_array_fuzzer_probes_nested_rewrite_terms(monkeypatch: pytest.MonkeyPatch) -> None:
    array = importlib.import_module("slotted.xdiff.xarray")
    lam = ("Lam", 0, ("App", ("Sym", "f1"), ("var", 0)))
    argument = ("App", ("Sym", "f2"), ("Sym", "x"))
    term = ("Let", 1, lam, argument)
    monkeypatch.setattr(array, "rand_term", lambda *_: term)
    case = array.rand_case(random.Random(0), 0)
    assert {term, lam, lam[2], argument, ("Sym", "x")} <= set(case.probes)
    assert all(probe[0] != "var" for probe in case.probes)


@pytest.mark.parametrize(
    "name,term,reference",
    [
        ("toy", ("F", ("Lam", 0, ("var", 0)), ("Num", 3)), "(f (lam $0 (var $0)) 3)"),
        ("array", ("App", ("Sym", "map"), ("Lam", 0, ("var", 0))), "(app map (lam $0 (var $0)))"),
        ("sdql", ("Add", ("Symbol", "sum"), ("Num", 3)), "(+ sym:sum 3)"),
    ],
)
def test_constructor_names_translate_to_reference_syntax(name: str, term: Any, reference: str) -> None:
    path = LANGUAGES / f"{name}.egg"
    lang = syntax.language(path, path.with_suffix(".ref"))
    assert set(lang.ops) == set(syntax.read_language(path))
    assert lang.sexpr(term) == reference


def source(tmp_path: Path) -> Any:
    path = tmp_path / "language.egg"
    path.write_text("(datatype U (F U U) (G U U) (Null))")
    src = syntax.Source(path)
    for op in src.lang.ops.values():
        op.ref = op.ctor
    return src


@pytest.mark.parametrize(
    "declaration",
    [
        "(datatype Var (Lam Var Var :binder 0) (Pair Var Var))",
        "(datatype* (Var (Lam Var Var :binder 0) (Pair Var Var)))",
        "(sort Var) (constructor Lam (Var Var) Var :binder 0) (constructor Pair (Var Var) Var)",
    ],
)
def test_var_is_an_ordinary_carrier_name(tmp_path: Path, declaration: str) -> None:
    path = tmp_path / "language.egg"
    path.write_text(declaration)
    src = syntax.Source(path)
    assert src.sorts == ["Var"]
    assert src.spec == {"Lam": [syntax.BINDER, syntax.CHILD], "Pair": [syntax.CHILD, syntax.CHILD]}
    assert src.term(syntax.parse("(Lam $a (Pair $a $b))")[0]) == (
        "Lam",
        src.slots.intern("$a"),
        ("Pair", ("var", src.slots.intern("$a")), ("var", src.slots.intern("$b"))),
    )


def test_multipattern_side_conditions_share_their_roots(tmp_path: Path) -> None:
    src = source(tmp_path)
    rule = syntax.parse("(rewrite (Null) a :when ((= t (Null)) (= t (F a b)) (= b (G a b))))")[0]
    lines = syntax.rule_lines(src, src.lang, rule)
    assert {"atom t Null ", "atom t F a b", "atom b G a b"} <= set(lines)
    with pytest.raises(syntax.NestedPatternUnsupported):
        syntax.rule_lines(src, src.lang, rule, nested=True)


def test_generated_reference_variables_do_not_alias_user_variables(tmp_path: Path) -> None:
    src = source(tmp_path)
    rule = syntax.parse("(rewrite (F _sl1 $x) _sl1 :when ((= _p (G $y _sl1))))")[0]
    lines = syntax.rule_lines(src, src.lang, rule)
    variable_roots = {line.split()[1] for line in lines if line.startswith("atom ") and line.split()[2] == "var"}
    assert len(variable_roots) == 2
    assert not variable_roots & {"_sl1", "_p"}
    lhs_root = next(line.split()[1] for line in lines if line.startswith("rhs "))
    assert lhs_root not in {"_sl1", "_p", *variable_roots}


@pytest.mark.parametrize("term", ["$a", "(F $a $b)", "(Null)"])
def test_reference_translation_does_not_expand_globals_into_patterns(tmp_path: Path, term: str) -> None:
    src = source(tmp_path)
    src.lang.bound["fixed"] = src.term(syntax.parse(term)[0])
    assert src.term("fixed", ground=True) == ("name", "fixed")
    rule = syntax.parse("(rewrite (F fixed x) x)")[0]
    for nested in (False, True):
        with pytest.raises(ValueError, match="does not support globals"):
            syntax.rule_lines(src, src.lang, rule, nested=nested)


def test_question_marks_are_preserved_in_reference_variables(tmp_path: Path) -> None:
    src = source(tmp_path)
    rule = syntax.parse("(rewrite (F x ?x) (G ?x x) :when ((not-free $s ?x)))")[0]
    for nested in (False, True):
        lines = syntax.rule_lines(src, src.lang, rule, nested=nested)
        assert lines[-1] == "cond notin $s ?x"
        assert any(line.endswith("(G ??x ?x)") for line in lines)
        lhs = "nested (F ?x ??x)" if nested else "atom _p F x ?x"
        assert lhs in lines

    multi = syntax.parse("(rewrite x (G ??x a) :when ((= x (F ?x ??x)) (= ?x (G a b))))")[0]
    lines = syntax.rule_lines(src, src.lang, multi)
    assert {"atom x F ?x ??x", "atom ?x G a b", "rhs x (G ???x ?a)"} <= set(lines)


def test_reordering_preserves_patterns_action_and_guards(tmp_path: Path) -> None:
    src = source(tmp_path)
    form = syntax.parse('(rewrite (F (G a b) ?a) b :when ((not-free $s ?a)) :name "test")')[0]
    rule = driver.Rule(src, src.lang, form)
    original = syntax.rewrite_parts(src, form)
    root, atoms = syntax.rule_atoms(src, src.lang, original)
    for first in range(len(atoms)):
        reordered = syntax.rewrite_parts(src, syntax.parse(rule.source(first_atom=first))[0])
        reordered_root, reordered_atoms = syntax.rule_atoms(src, src.lang, reordered)
        assert reordered_root == root
        assert reordered_atoms == [atoms[first], *atoms[:first], *atoms[first + 1 :]]
        for field in ("rhs", "conds", "name"):
            assert reordered[field] == original[field]


@pytest.mark.parametrize("options", [":when ((= a b))", ":when ((!= a b))"])
def test_unrepresented_reference_constraints_are_rejected(tmp_path: Path, options: str) -> None:
    src = source(tmp_path)
    rule = syntax.parse(f"(rewrite (F a b) a {options})")[0]
    for nested in (False, True):
        with pytest.raises(ValueError, match="unsupported reference rewrite options"):
            syntax.rule_lines(src, src.lang, rule, nested=nested)


@pytest.mark.parametrize("option", [":fresh $new", ":fresh $x", ":lead 0", ":lead 1"])
def test_unknown_rewrite_options_are_rejected(tmp_path: Path, option: str) -> None:
    src = source(tmp_path)
    rule = syntax.parse(f"(rewrite (F $x a) a {option})")[0]
    for nested in (False, True):
        with pytest.raises(SystemExit, match=f"got '{option.split()[0]}'"):
            syntax.rule_lines(src, src.lang, rule, nested=nested)


def test_side_patterns_can_bind_the_action_through_a_child(tmp_path: Path) -> None:
    src = source(tmp_path)
    rule = syntax.parse("(rewrite a (Null) :when ((= parent (F a b))))")[0]
    assert syntax.rule_lines(src, src.lang, rule)[-1] == "rhs a Null"
    unbound = syntax.parse("(rewrite missing (Null) :when ((= parent (F a b))))")[0]
    with pytest.raises(ValueError, match="root must be bound"):
        syntax.rule_lines(src, src.lang, unbound)
