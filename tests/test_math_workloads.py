"""Complete registered Math bytes determine native schedules and terminal witnesses."""

import re
from pathlib import Path

import pytest

from benchmarking import engines, targets, workloads

ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize(
    "treatment,mode",
    [("egg", "off"), ("egg-proofs", "enabled"), ("egg-proof-extraction", "extract"), ("egg-proof-testing", "check")],
)
def test_readable_math_copy_keeps_native_mode(tmp_path: Path, treatment: engines.Treatment, mode: str) -> None:
    path = tmp_path / "math-iteration-11.egg"
    path.write_bytes((ROOT / engines.MATH_WORKLOAD_PATH).read_bytes())
    (file,) = workloads.resolve_files([str(path)], tmp_path)
    engines.validate_engine_workload(file, treatment)
    assert targets.workload_command(tmp_path / "egg", file, treatment) == [str(tmp_path / "egg"), "--proof-mode", mode]


@pytest.mark.parametrize(
    "original,replacement",
    [("(run 11)", "(run 10)"), ('(Var "five")', '(Var "six")'), ("(rewrite (Add a b) (Add b a))", "")],
)
def test_changed_math_input_is_rejected(tmp_path: Path, original: str, replacement: str) -> None:
    source = (ROOT / engines.MATH_WORKLOAD_PATH).read_text()
    assert original in source
    path = tmp_path / "math-iteration-11.egg"
    path.write_text(source.replace(original, replacement))
    (file,) = workloads.resolve_files([str(path)], tmp_path)
    with pytest.raises(ValueError, match="fixed Math11"):
        engines.validate_engine_workload(file, "egg-proof-testing")


@pytest.mark.parametrize("treatment", ["egg", "egg-proofs", "egg-proof-extraction", "egg-proof-testing"])
def test_math12_copy_derives_exact_native_schedule_and_witness(tmp_path: Path, treatment: engines.Treatment) -> None:
    path = tmp_path / "renamed.egg"
    path.write_bytes((ROOT / engines.MATH12_WORKLOAD_PATH).read_bytes())
    (file,) = workloads.resolve_files([str(path)], tmp_path)
    engines.validate_engine_workload(file, treatment)
    assert engines.math_workload_arguments(file) == (
        "--iterations",
        "12",
        "--check-left",
        engines.MATH12_CHECK_LEFT,
        "--check-right",
        engines.MATH12_CHECK_RIGHT,
    )
    assert targets.workload_command(tmp_path / "egg", file, treatment) == [
        str(tmp_path / "egg"),
        *engines.TREATMENT_SPECS[treatment].flags,
        *engines.math_workload_arguments(file),
    ]


@pytest.mark.parametrize(
    "original,replacement",
    [
        ("(run 12)", "(run 11)"),
        ('(Var "five")', '(Var "six")'),
        ("(rewrite (Add a b) (Add b a))", ""),
        ("(check (= (Mul", "(check (= (Add"),
    ],
)
def test_changed_math12_schedule_seed_rule_or_witness_is_rejected(
    tmp_path: Path,
    original: str,
    replacement: str,
) -> None:
    source = (ROOT / engines.MATH12_WORKLOAD_PATH).read_text()
    assert original in source
    path = tmp_path / "renamed.egg"
    path.write_text(source.replace(original, replacement))
    (file,) = workloads.resolve_files([str(path)], tmp_path)
    with pytest.raises(ValueError, match="registered Math"):
        engines.validate_engine_workload(file, "egg-proof-testing")


def test_math12_preserves_complete_math11_setup() -> None:
    old = (ROOT / engines.MATH_WORKLOAD_PATH).read_text()
    new = (ROOT / engines.MATH12_WORKLOAD_PATH).read_text()
    assert (
        new[new.index("(datatype Math") : new.index("(run 12)")]
        == old[old.index("(datatype Math") : old.index("(run 11)")]
    )
    assert engines.MATH12_CHECK_LEFT != engines.MATH12_CHECK_RIGHT


def test_frozen_math12_native_arguments_and_egglog_check_are_the_same_witness() -> None:
    source = (ROOT / engines.MATH12_WORKLOAD_PATH).read_text()
    check = source.split("(run 12)", 1)[1]
    native_to_egglog = {
        "+": "Add",
        "*": "Mul",
        "d": "Diff",
        "i": "Integral",
        "cos": "Cos",
        "x": '(Var "x")',
        "-1": "(Const (rational -1 1))",
    }
    expressions = []
    for native in [engines.MATH12_CHECK_LEFT, engines.MATH12_CHECK_RIGHT]:
        tokens = re.findall(r"[()]|[^\s()]+", native)
        expressions.append(" ".join(native_to_egglog.get(token, token) for token in tokens))
    expected = f"(check (= {expressions[0]} {expressions[1]}))"
    assert re.findall(r"[()]|[^\s()]+", check) == re.findall(r"[()]|[^\s()]+", expected)
