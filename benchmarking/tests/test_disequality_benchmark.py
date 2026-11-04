"""The benchmark CLI no longer exposes a disequality representation selector."""

import pytest

from benchmarking import benchmark


@pytest.mark.parametrize("flag", ["--disequality-encoding", "--compare-disequality-encoding"])
@pytest.mark.parametrize("encoding", ["nee", "ee"])
def test_benchmark_has_no_disequality_encoding_selector(flag: str, encoding: str) -> None:
    with pytest.raises(SystemExit):
        benchmark.parse_benchmark_args([flag, encoding])
