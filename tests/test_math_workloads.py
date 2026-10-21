"""Native Math accepts byte-identical copies, never a changed schedule or witness."""

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
