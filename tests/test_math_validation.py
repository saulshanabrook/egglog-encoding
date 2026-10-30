"""The correctness diagnostic shares the benchmark's native launch policy."""

import json
import sys
from pathlib import Path

import pytest

import native_memory
from benchmarks import validate_math


def test_math_validation_forwards_shared_native_policy_and_records_the_same_cap(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(validate_math, "NATIVE_LIMIT_BYTES", 12345)
    monkeypatch.setattr(native_memory, "NATIVE_ALLOCATOR_ENV", {"TEST_NATIVE_POLICY": "shared"})
    binary = tmp_path / "boundary-test"
    binary.write_text(
        f"#!{sys.executable}\n"
        "import json, os, sys\n"
        "assert sys.argv[1:] == ['--exact', 'tests::bounded_math12_case', '--ignored', '--nocapture']\n"
        "assert os.environ['TEST_NATIVE_POLICY'] == 'shared'\n"
        "assert os.environ['RUST_TEST_THREADS'] == '1'\n"
        "print('MATH_BOUNDARY_RESULT ' + json.dumps({\n"
        "    'engine': os.environ['MATH_BOUNDARY_ENGINE'],\n"
        "    'proof': os.environ['MATH_BOUNDARY_PROOF'],\n"
        "    'iterations': int(os.environ['MATH_BOUNDARY_ITERATIONS']),\n"
        "    'native_limit_bytes': int(os.environ['MATH_BOUNDARY_MEMORY_LIMIT_BYTES']),\n"
        "    'constructors': {'Var': 1}, 'classes': 1,\n"
        "}))\n"
    )
    binary.chmod(0o755)
    output = tmp_path / "validation"

    summary = validate_math.validate(binary, output)

    assert summary["complete"]
    assert summary["native_limit_bytes"] == 12345
    assert [
        (case["result"]["engine"], case["result"]["proof"], case["result"]["iterations"]) for case in summary["cases"]
    ] == list(validate_math.CASES)
    assert all(case["result"]["native_limit_bytes"] == summary["native_limit_bytes"] for case in summary["cases"])
    assert json.loads((output / "validation.json").read_text()) == summary
