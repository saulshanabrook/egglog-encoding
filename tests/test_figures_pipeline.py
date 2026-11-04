"""Verify that parallel Make preserves the figure pipeline's collection boundary."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path


def test_parallel_make_finishes_collection_before_projection_and_rendering(tmp_path: Path) -> None:
    root = Path(__file__).resolve().parents[1]
    shutil.copyfile(root / "Makefile", tmp_path / "Makefile")
    (tmp_path / "figures").mkdir()
    (tmp_path / "bin").mkdir()
    executable = f"#!{sys.executable}\n"
    collector = tmp_path / "bench.py"
    collector.write_text(
        executable
        + "import json, pathlib, sys\n"
        + "root = pathlib.Path.cwd()\n"
        + "lock = root / 'collecting'\n"
        + "lock.mkdir()\n"
        + "with (root / 'events.jsonl').open('a') as out:\n"
        + "    out.write(json.dumps(['collect', *sys.argv[1:]]) + '\\n')\n"
        + "lock.rmdir()\n"
    )
    collector.chmod(0o755)
    projector = tmp_path / "bin" / "uv"
    projector.write_text(
        executable
        + "import json, pathlib, sys\n"
        + "root = pathlib.Path.cwd()\n"
        + "assert not (root / 'collecting').exists()\n"
        + "assert len((root / 'events.jsonl').read_text().splitlines()) == 4\n"
        + "with (root / 'events.jsonl').open('a') as out:\n"
        + "    out.write(json.dumps(['project', *sys.argv[1:]]) + '\\n')\n"
        + "(root / 'figures' / 'ready').touch()\n"
    )
    projector.chmod(0o755)
    (tmp_path / "figures" / "Makefile").write_text(
        "all:\n\t@test -f ready\n\t@printf '[\"render\"]\\n' >> ../events.jsonl\n"
    )

    subprocess.run(
        ["make", "-j8", "figures", "figures-data", "figures-bench"],
        cwd=tmp_path,
        env={**os.environ, "PATH": f"{tmp_path / 'bin'}{os.pathsep}{os.environ['PATH']}"},
        check=True,
        capture_output=True,
        text=True,
    )
    events = [json.loads(line) for line in (tmp_path / "events.jsonl").read_text().splitlines()]
    assert [event[0] for event in events] == ["collect", "collect", "collect", "collect", "project", "render"]
    assert events[0][1:] == [
        "--target",
        "figures=.",
        "--treatment",
        "proofs",
        "--compare-treatment",
        "off",
        "--rounds",
        "30",
        "--timeout-sec",
        "120",
    ]
    assert events[1][1:] == [
        "--target",
        "figures=.",
        "--treatment",
        "proof-extraction",
        "--compare-treatment",
        "off",
        "--rounds",
        "30",
        "--timeout-sec",
        "120",
    ]
    assert events[2][1:] == [
        "egglog-experimental/tests/math-microbenchmark-rational.egg",
        "--target",
        "figures=.",
        "--treatment",
        "proof-extraction",
        "--compare-treatment",
        "egg-proof-extraction",
        "--rounds",
        "30",
        "--timeout-sec",
        "120",
    ]
    assert events[3][1:] == [
        "egglog-experimental/tests/math-microbenchmark-rational.egg",
        "--target",
        "figures=.",
        "--treatment",
        "off",
        "--compare-treatment",
        "egg",
        "--rounds",
        "30",
        "--timeout-sec",
        "120",
    ]
    assert events[4][1:] == ["run", "--locked", "python", "-m", "figures.prepare"]
