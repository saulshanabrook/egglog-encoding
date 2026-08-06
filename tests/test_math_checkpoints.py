"""Test the committed sparse Math checkpoint family."""

from __future__ import annotations

import subprocess
import sys

from scripts import generate_math_checkpoints


def test_math_checkpoints_match_the_generator() -> None:
    subprocess.run(
        [sys.executable, str(generate_math_checkpoints.ROOT / "scripts/generate_math_checkpoints.py"), "--check"],
        cwd=generate_math_checkpoints.ROOT,
        check=True,
    )

    assert tuple(range(0, 101, 10)) == generate_math_checkpoints.CHECKPOINTS
    assert set(generate_math_checkpoints.CHECKPOINTS) == set(generate_math_checkpoints.EXPECTED_TABLE_TOTALS)
    assert set(generate_math_checkpoints.CHECKPOINTS) == set(generate_math_checkpoints.EXPECTED_TABLE_SIZES)
    for iterations in generate_math_checkpoints.CHECKPOINTS:
        source = generate_math_checkpoints.checkpoint_path(iterations).read_text(encoding="utf-8")
        assert source == generate_math_checkpoints.render_checkpoint(iterations)
        assert generate_math_checkpoints.fixed_iteration_schedule(iterations) in source
        assert source.count(f"(run-with {generate_math_checkpoints.SCHEDULER_NAME})") == iterations
        assert f":match-limit {generate_math_checkpoints.MATCH_LIMIT}" in source
        assert f":ban-length {generate_math_checkpoints.BAN_LENGTH}" in source
        assert generate_math_checkpoints.checkpoint_check(iterations) in source
        sizes = generate_math_checkpoints.EXPECTED_TABLE_SIZES[iterations]
        assert len(sizes) == len(generate_math_checkpoints.TABLES)
        assert sum(sizes) == generate_math_checkpoints.EXPECTED_TABLE_TOTALS[iterations]
        for table in generate_math_checkpoints.TABLES:
            assert f"(print-size {table})" in source
