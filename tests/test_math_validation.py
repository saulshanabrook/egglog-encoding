"""The Math12 test launcher shares native policy and propagates test failures."""

import subprocess
import sys
from pathlib import Path

import pytest

import native_memory
from benchmarks import validate_math


@pytest.mark.parametrize("exit_code", [0, 86])
def test_math_validation_uses_shared_policy_and_propagates_test_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, exit_code: int
) -> None:
    monkeypatch.setattr(validate_math, "NATIVE_LIMIT_BYTES", 12345)
    monkeypatch.setattr(native_memory, "NATIVE_ALLOCATOR_ENV", {"TEST_NATIVE_POLICY": "shared"})
    binary = tmp_path / "math12-test"
    binary.write_text(
        f"#!{sys.executable}\n"
        "import os, sys\n"
        "assert sys.argv[1:] == ['--exact', 'tests::math12_graph_parity', '--ignored', '--nocapture']\n"
        "assert os.environ['TEST_NATIVE_POLICY'] == 'shared'\n"
        "assert os.environ['RUST_TEST_THREADS'] == '1'\n"
        "assert os.environ['MATH12_MEMORY_LIMIT_BYTES'] == '12345'\n"
        f"sys.exit({exit_code})\n"
    )
    binary.chmod(0o755)
    monkeypatch.setattr(sys, "argv", ["validate-math", "--test-binary", str(binary)])

    if exit_code:
        with pytest.raises(subprocess.CalledProcessError) as error:
            validate_math.main()
        assert error.value.returncode == exit_code
    else:
        validate_math.main()
