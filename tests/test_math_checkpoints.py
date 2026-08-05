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
    for iterations in generate_math_checkpoints.CHECKPOINTS:
        source = generate_math_checkpoints.checkpoint_path(iterations).read_text(encoding="utf-8")
        assert source == generate_math_checkpoints.render_checkpoint(iterations)
        assert f"(run {iterations})" in source
        assert source.rstrip().endswith(generate_math_checkpoints.checkpoint_check(iterations))
