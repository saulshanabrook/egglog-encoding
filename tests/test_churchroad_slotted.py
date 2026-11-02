"""Check Churchroad import semantics, typed interfaces, and bounded module discovery."""

import importlib
from itertools import product
from pathlib import Path
from typing import Any

import pytest

# The slotted tools intentionally remain outside the project's mypy scope.
import_egg = importlib.import_module("slotted.churchroad.importer").import_egg
ir = importlib.import_module("slotted.churchroad.ir")
modules = importlib.import_module("slotted.churchroad.modules")
export = importlib.import_module("slotted.churchroad.verilog").export
Circuit, evaluate, operation = ir.Circuit, ir.evaluate, ir.operation
Candidate, decode_module = modules.Candidate, modules.decode_module
enumerate_modules, program = modules.enumerate_modules, modules.program

FIXTURES = Path(__file__).resolve().parents[1] / "slotted/churchroad/fixtures"


def half_adder() -> Any:
    return import_egg((FIXTURES / "half_adder.egg").read_text(), ("o_sum", "o_carry"))


def test_imports_original_half_adder_semantics() -> None:
    circuit = half_adder()
    for a, b in product(range(2), repeat=2):
        inputs = {"i_bit1": a, "i_bit2": b}
        assert evaluate(circuit.outputs["o_sum"], inputs) == (a ^ b)
        assert evaluate(circuit.outputs["o_carry"], inputs) == (a & b)


def test_ripple_adder_matches_addition_for_every_input() -> None:
    circuit = import_egg((FIXTURES / "ripple-adder.egg").read_text())
    for a, b in product(range(4), repeat=2):
        inputs = {"i_a": a, "i_b": b}
        assert evaluate(circuit.outputs["o_s"], inputs) == (a + b) % 4
        assert evaluate(circuit.outputs["o_c"], inputs) == (a + b) // 4


def test_wide_multiply_preserves_zero_extension_and_truncation() -> None:
    circuit = import_egg((FIXTURES / "wide-mul.egg").read_text())
    for a, b in product([0, 1, 255, 65535], [0, 1, 65536, 2**32 - 1]):
        assert evaluate(circuit.outputs["out"], {"a": a, "b": b}) == a * b % (2**32)


def test_saved_workloads_match_the_generator_and_pinned_inputs() -> None:
    fixtures = importlib.import_module("slotted.churchroad.fixtures")
    fixtures.verify_inputs()
    for case in fixtures.CASES:
        assert (fixtures.BENCHES / f"{case}.egg").read_text() == fixtures.fixture_text(case)


def test_imports_input_ports_without_var_nodes_and_preserves_names() -> None:
    circuit = import_egg("""
        (let x (Wire "internal" 8))
        (let out (Op1 (ZeroExtend 16) x))
        (IsPort "top" "input/with.dots" (Input) x)
        (IsPort "top" "out" (Output) out)
        (run-schedule (saturate (seq typing misc)))
    """)
    assert circuit.inputs["input/with.dots"].width == 8
    assert evaluate(circuit.outputs["out"], {"input/with.dots": 255}) == 255
    original, _, _ = export(circuit, [], [])
    assert "\\input/with.dots " in original


@pytest.mark.parametrize(
    "source, message",
    [
        ('(let a (Var "a" 1)) (rewrite a (Op0 (BV 0 1)))', "unsupported.*command"),
        ('(let a (Var "a" 1)) (run-schedule (saturate transform))', "unsupported.*command"),
        ('(let a (Wire "a" 1)) (let out a)', "unconnected"),
        ('(let a (Wire "a" 8)) (union a (Op1 (Not) a)) (let out a)', "cyclic"),
        ('(let a (Var "a" 1)) (let a (Var "b" 1))', "duplicate"),
        ('(let a (Wire "a" 1)) (union a (Op0 (BV 0 8))) (let out a)', "wire width"),
        ('(let a (Var "a" 1)) (let out (Op2 (And) a (Var "b" 8)))', "unequal operand"),
        ('(let a (Var "a" 8)) (let out (Op1 (Extract 8 0) a))', "invalid.*8-bit"),
        ('(let a (Var "a" 8)) (let out (Op1 (Reg 0) a))', "sequential Reg"),
    ],
)
def test_rejects_unsupported_or_ill_typed_imports(source: str, message: str) -> None:
    with pytest.raises(ValueError, match=message):
        import_egg(source, ("out",))


def test_explicit_combinational_root_excludes_register() -> None:
    circuit = import_egg(
        """
      (let a (Var "a" 8))
      (let comb (Op1 (Not) a))
      (let registered (Op1 (Reg 0) comb))
      (IsPort "" "registered" (Output) registered)
    """,
        ("comb",),
    )
    assert evaluate(circuit.outputs["comb"], {"a": 7}) == 248


def test_distinct_input_wires_cannot_share_a_port_name() -> None:
    with pytest.raises(ValueError, match="names distinct wires"):
        import_egg("""
          (let a (Wire "a" 1)) (let b (Wire "b" 1))
          (IsPort "" "duplicate" (Input) a)
          (IsPort "" "duplicate" (Input) b)
          (IsPort "" "out" (Output) a)
        """)


def test_width_sensitive_operations_follow_churchroad_semantics() -> None:
    a = operation("Input", data=("a", 4))
    b = operation("Input", data=("b", 4))
    selector = operation("Input", data=("s", 1))
    mux = operation("Mux", [selector, a, b])
    for left, right, select in product(range(16), range(16), range(2)):
        inputs = {"a": left, "b": right, "s": select}
        assert evaluate(mux, inputs) == (right if select else left)
        assert evaluate(operation("Mul", [a, b]), inputs) == left * right % 16
        assert evaluate(operation("Sub", [a, b]), inputs) == (left - right) % 16
        assert evaluate(operation("Concat", [a, b]), inputs) == left * 16 + right
    assert evaluate(operation("SignExtend", [a], (8,)), {"a": 15}) == 255
    assert evaluate(operation("ZeroExtend", [a], (8,)), {"a": 15}) == 15
    assert evaluate(operation("Shl", [a, b]), {"a": 15, "b": 15}) == 0


def test_enumeration_retains_repeated_input_aliases_and_widths() -> None:
    a, b, c, d = [operation("Input", data=(name, 1)) for name in "abcd"]
    candidates = [
        Candidate((operation("And", [a, b]),), (a, b), 1),
        Candidate((operation("And", [c, d]),), (c, d), 1),
        Candidate((operation("And", [a, a]),), (a,), 1),
    ]
    assert candidates[0].legacy_key() == candidates[1].legacy_key()
    assert candidates[0].body(0) != candidates[1].body(1)
    assert candidates[0].legacy_key() != candidates[2].legacy_key()
    wide = operation("Input", data=("wide", 8))
    assert Candidate((wide,), (wide,), 1).legacy_key() != Candidate((a,), (a,), 1).legacy_key()


def test_bounded_enumeration_reports_omitted_work_and_handles_shared_boundary() -> None:
    circuit = half_adder()
    full, truncated = enumerate_modules(circuit)
    assert len(full) == 3 and not truncated
    bounded, truncated = enumerate_modules(circuit, max_candidates=1)
    assert len(bounded) == 1 and truncated
    assert len(bounded[0].roots) == 2
    assert len(bounded[0].inputs) == 2
    too_narrow, _ = enumerate_modules(circuit, max_inputs=1)
    assert not too_narrow


def test_extracted_interfaces_are_checked_before_verilog_export() -> None:
    inputs, roots, kind = decode_module(
        ["BindInput", "1", "$x", ["BindInput", "1", "$y", ["HalfAdder", "0", "$x", "$y"]]]
    )
    assert kind == "HalfAdder" and len(inputs) == len(roots) == 2
    for a, b in product(range(2), repeat=2):
        assert [evaluate(r, {"in0": a, "in1": b}) for r in roots] == [a ^ b, a & b]
    with pytest.raises(ValueError, match="half-adder interface"):
        decode_module(["BindInput", "8", "$x", ["HalfAdder", "0", "$x", "$x"]])
    with pytest.raises(ValueError, match="free slot"):
        decode_module(["BindInput", "1", "$x", ["HalfAdder", "0", "$x", "$free"]])
    with pytest.raises(ValueError, match="declares 8 bits, computes 1"):
        decode_module(["BindInput", "1", "$x", ["OutputCons", "8", ["Xor", "8", "$x", "$x"], ["NoOutputs"]]])


def test_export_preserves_the_engine_checked_module_signature() -> None:
    circuit = half_adder()
    candidate = Candidate(tuple(circuit.outputs.values()), tuple(reversed(tuple(circuit.inputs.values()))), 1)
    good = ["BindInput", "1", "$x", ["BindInput", "1", "$y", ["HalfAdder", "0", "$x", "$y"]]]
    original, mapped, stats = export(circuit, [candidate], [good])
    assert "module reference" in original
    assert "module cr_module_0" in mapped and "cr_instance_0" in mapped
    assert stats["emitted_recognized_instances"] == {"HalfAdder": 1}
    with pytest.raises(ValueError, match="ordered input signature"):
        export(circuit, [candidate], [["BindInput", "1", "$x", ["HalfAdder", "0", "$x", "$x"]]])


def test_generated_program_checks_every_instantiated_candidate() -> None:
    circuit = half_adder()
    candidates, _ = enumerate_modules(circuit)
    text = program(circuit, candidates)
    for i in range(len(candidates)):
        assert f"(check (= instance_{i} expected_{i}))" in text
    assert "(subst body $x arg)" in text
    assert "debruijnify" not in text and "MakeModule" not in text
