"""The native adapter accepts only the unchanged fixed Math11 workload."""

from pathlib import Path

import pytest

from benchmarking import engines, math_workloads, targets
from benchmarking.models import FileSpec


@pytest.mark.parametrize(
    "treatment,mode",
    [("egg", "off"), ("egg-proofs", "enabled"), ("egg-proof-extraction", "extract"), ("egg-proof-testing", "check")],
)
def test_fixed_math_uses_legacy_hash_and_bare_native_flags(
    tmp_path: Path, treatment: engines.Treatment, mode: str
) -> None:
    path = math_workloads.ROOT / engines.MATH_WORKLOAD_PATH
    math_workloads.recognize_math_workload(path)
    assert targets.sha256_file(path) == "sha256:" + math_workloads.LEGACY_SHA256
    file = FileSpec(path.name, path, targets.sha256_file(path))
    assert targets.workload_command(tmp_path / "egg", file, treatment) == [str(tmp_path / "egg"), "--proof-mode", mode]


@pytest.mark.parametrize(
    "edit",
    [
        lambda text: text.replace("(run 11)", "(run 10)"),
        lambda text: text.replace('(Var "five")', '(Var "six")'),
        lambda text: text.replace("(rewrite (Add a b) (Add b a))", ""),
    ],
)
def test_changed_schedule_seed_or_rule_cannot_address_the_native_cache(tmp_path: Path, edit: object) -> None:
    source = (math_workloads.ROOT / engines.MATH_WORKLOAD_PATH).read_text()
    assert callable(edit)
    changed = edit(source)
    assert changed != source
    path = tmp_path / "math-microbenchmark-rational.egg"
    path.write_text(changed)
    file = FileSpec(path.name, path, targets.sha256_file(path))
    with pytest.raises(ValueError, match="fixed Math11"):
        engines.validate_engine_workload(file, "egg")
