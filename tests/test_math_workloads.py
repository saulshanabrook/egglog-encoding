"""The native adapter must run the complete workload selected by the cache key."""

from pathlib import Path

import pytest

from benchmarking import engines, math_workloads, targets
from benchmarking.models import FileSpec


def test_all_frozen_inputs_match_their_complete_native_parameters(tmp_path: Path) -> None:
    witnesses = math_workloads.load_witnesses()
    for witness in witnesses:
        path = math_workloads.ROOT / (
            engines.MATH_WORKLOAD_PATH
            if witness.iterations == 11
            else Path(f"benchmarks/math/math-{witness.iterations:02}.egg")
        )
        assert (
            path.read_text().split("(datatype", 1)[1]
            == math_workloads.render_math_workload(witness).split("(datatype", 1)[1]
        )
        assert math_workloads.recognize_math_workload(path) == witness
        file = FileSpec(path.name, path, targets.sha256_file(path))
        command = targets.workload_command(tmp_path / "egg", file, "egg-proof-extraction")
        if witness.iterations == 11:
            assert "--iterations" not in command  # Existing fixture/cache identity is retained.
        else:
            assert command[command.index("--iterations") + 1] == str(witness.iterations)
            assert command[command.index("--check-left") + 1] == witness.left
            assert command[command.index("--check-right") + 1] == witness.right
    assert math_workloads.recognize_math_workload(math_workloads.ROOT / engines.MATH_WORKLOAD_PATH) == witnesses[-1]


@pytest.mark.parametrize(
    "edit",
    [
        lambda text: text.replace("(run 1)", "(run 2)"),
        lambda text: text.replace('(Var "five")', '(Var "six")'),
        lambda text: text.replace("(rewrite (Add a b) (Add b a))", ""),
    ],
)
def test_changed_schedule_seed_or_rule_cannot_address_the_native_cache(tmp_path: Path, edit: object) -> None:
    # Even a familiar basename cannot select a different native computation.
    source = math_workloads.render_math_workload(math_workloads.load_witnesses()[0])
    assert callable(edit)
    changed = edit(source)
    assert changed != source
    path = tmp_path / "math-microbenchmark-rational.egg"
    path.write_text(changed)
    file = FileSpec(path.name, path, targets.sha256_file(path))
    with pytest.raises(ValueError, match="noncanonical"):
        engines.validate_engine_workload(file, "egg")


@pytest.mark.parametrize("expression", ["(d x)", "(mystery x)", "(cos x) (sin x)", "unknown", "(cos x y)"])
def test_native_translation_rejects_ambiguous_or_unsupported_terms(expression: str) -> None:
    with pytest.raises(ValueError):
        math_workloads.egglog_expression(expression)
