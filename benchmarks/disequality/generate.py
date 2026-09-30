#!/usr/bin/env python3
"""Find the first random parameter-analysis workload that proves a contradiction.

Download the paper's generator unchanged and try successive seeds. Accept a
workload only when both NE and EE detect a contradiction and validate its proof,
then save it as a runnable egglog benchmark. Consistent workloads permit another
seed; errors stop the search. No expressions are filtered or constraints injected.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import io
import platform
import random
import re
import runpy
import shutil
import subprocess
import tempfile
import urllib.request
import zipfile
from collections.abc import Callable
from pathlib import Path
from typing import cast

ARCHIVE_URL = "https://zenodo.org/records/13938878/files/die-graph.zip"
ARCHIVE_SHA256 = "3e9080ca461457af0a10cfc433a5150952f82f752b4c316df1e03236d93599c4"
MEMBER = "parameter-analysis/rand_exprs.py"
GENERATOR_SHA256 = "1fa476fbacac1f8c8040e1ca1a47e8bf4effe761383c86041cdc7f3a34b3e12d"
ROOT = Path(__file__).resolve().parents[2]
EQUALITIES = 100_000
DISEQUALITIES = 10_000
CHECK = "(check-contradiction)\n"


def fetch_generator(cache: Path) -> Path:
    """Verify the complete archive before extracting exactly one bounded member."""
    cache.mkdir(parents=True, exist_ok=True)
    archive = cache / "die-graph.zip"
    if not archive.exists():
        temporary = archive.with_suffix(".download")
        try:
            with urllib.request.urlopen(ARCHIVE_URL, timeout=60) as response, temporary.open("wb") as output:
                shutil.copyfileobj(response, output)
            temporary.replace(archive)
        finally:
            temporary.unlink(missing_ok=True)
    with archive.open("rb") as source:
        digest = hashlib.file_digest(source, "sha256").hexdigest()
    if digest != ARCHIVE_SHA256:
        raise ValueError(f"archive checksum mismatch: {digest}")
    with zipfile.ZipFile(archive) as source:
        matches = [entry for entry in source.infolist() if entry.filename == MEMBER]
        if len(matches) != 1 or matches[0].file_size > 64 * 1024:
            raise ValueError("archive must contain exactly one small generator member")
        content = source.read(matches[0])
    if hashlib.sha256(content).hexdigest() != GENERATOR_SHA256:
        raise ValueError("generator checksum mismatch")
    generator = cache / "rand_exprs.py"
    generator.write_bytes(content)
    return generator


def expressions(generator: Path, seed: int, count: int) -> list[str]:
    """Keep the script's output and continue its RNG stream with its own function."""
    state = random.getstate()
    try:
        random.seed(seed)
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            namespace = runpy.run_path(str(generator))
        result = output.getvalue().splitlines()
        if len(result) != 60_000:
            raise ValueError("unexpected archive generator output count")
        gen = cast(Callable[[int], str], namespace["gen"])
        result.extend(gen(5) for _ in range(max(0, count - len(result))))
        return result[:count]
    finally:
        random.setstate(state)


def source_program(terms: list[str], seed: int, equalities: int, disequalities: int) -> str:
    """Preserve adjacent pairs and the artifact's disequalities-first partition."""
    if len(terms) != 2 * (equalities + disequalities):
        raise ValueError("incorrect number of generated expressions")
    lines = [
        "; Parameter analysis from Dis-Equality Graphs (Zakhour et al.).",
        f"; Artifact: {ARCHIVE_URL}",
        f"; Archive SHA-256: {ARCHIVE_SHA256}",
        f"; Unmodified generator: {MEMBER}, SHA-256: {GENERATOR_SHA256}",
        f"; Seed: {seed}; Python: {platform.python_version()}; depth: 5.",
        f"; {equalities} equality pairs; {disequalities} random disequality pairs; 10 numeral disequalities.",
        "; Selected for a natural contradiction; no injected pair or per-pair filtering.",
        "; Numeral constraints follow the paper (the archive driver emits only six).",
        f"; Regenerate: python benchmarks/disequality/generate.py --seed {seed} --max-attempts 1",
        "(datatype Term (N1) (N2) (N3) (N4) (N5) (f Term) (g Term Term) (h Term Term Term))",
    ]
    lines.extend(f"(disequal (N{x}) (N{y}))" for x in range(1, 6) for y in range(x + 1, 6))
    for index in range(0, len(terms), 2):
        pair = [re.sub(r"\b([1-5])\b", r"(N\1)", term) for term in terms[index : index + 2]]
        command = "disequal" if index < 2 * disequalities else "union"
        lines.append(f"({command} {pair[0]} {pair[1]})")
    return "\n".join(lines) + "\n" + CHECK


def check_candidate(binary: Path, candidate: Path, encoding: str, timeout: int, *, proofs: bool = False) -> bool:
    """Only the exact final failed contradiction check permits another seed.

    CLI diagnostics are not a general result protocol: recognize just this
    pinned CheckError suffix, then confirm the negative with an expected-failure
    replay. Any other diagnostic, crash, timeout, or proof failure is fatal.
    Files (not the interactive stdin loop) give meaningful CLI exit statuses.
    """
    command = [str(binary), "--mode", "no-messages", "--disequality-encoding", encoding]
    if proofs:
        command.append("--proof-testing")
    result = subprocess.run([*command, str(candidate)], capture_output=True, text=True, timeout=timeout)
    if result.returncode == 0:
        return True
    contradiction = {
        "nee": "(@disequality-contradiction)",
        "ee": "(= (@disequality-true) (@disequality-false))",
    }[encoding]
    if (
        not proofs
        and result.returncode == 1
        and result.stderr.rstrip().endswith(f"Check failed: \n    {contradiction}")
    ):
        negative = candidate.with_name("consistent.egg")
        source = candidate.read_text()
        if not source.endswith(CHECK):
            raise ValueError("candidate is missing its final contradiction check")
        negative.write_text(source[: -len(CHECK)] + "(fail (check-contradiction))\n")
        replay = subprocess.run([*command, str(negative)], capture_output=True, text=True, timeout=timeout)
        if replay.returncode == 0:
            return False
        raise RuntimeError(f"negative replay failed ({encoding}):\n{replay.stderr}")
    raise RuntimeError(f"candidate failed ({encoding}, proofs={proofs}, exit={result.returncode}):\n{result.stderr}")


def select_candidate(generator: Path, binary: Path, output: Path, seed: int, max_attempts: int, timeout: int) -> int:
    """Select the first confirmed contradiction, never retrying implementation failures."""
    if max_attempts < 1:
        raise ValueError("max-attempts must be positive")
    with tempfile.TemporaryDirectory(prefix="disequality-generation-") as directory:
        candidate = Path(directory) / "candidate.egg"
        for attempt in range(seed, seed + max_attempts):
            terms = expressions(generator, attempt, 2 * (EQUALITIES + DISEQUALITIES))
            candidate.write_text(source_program(terms, attempt, EQUALITIES, DISEQUALITIES))
            del terms
            outcomes = [check_candidate(binary, candidate, encoding, timeout) for encoding in ("nee", "ee")]
            print(f"seed {attempt}: nee={outcomes[0]}, ee={outcomes[1]}", flush=True)
            if outcomes[0] != outcomes[1]:
                raise RuntimeError("encodings disagree; refusing to retry")
            if not outcomes[0]:
                continue
            for encoding in ("nee", "ee"):
                check_candidate(binary, candidate, encoding, timeout, proofs=True)
            output.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(candidate, output)
            print(f"accepted seeds {seed}..{attempt}; SHA-256 {hashlib.sha256(output.read_bytes()).hexdigest()}")
            return attempt
    raise RuntimeError(f"no contradiction in {max_attempts} attempts; no benchmark written")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=2025)
    parser.add_argument("--max-attempts", type=int, default=20)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--cache", type=Path, default=Path.home() / ".cache/egglog-encoding/disequality")
    parser.add_argument("--binary", type=Path, default=ROOT / "target/release/egglog-experimental")
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("parameter-analysis.egg"))
    args = parser.parse_args()
    select_candidate(
        fetch_generator(args.cache), args.binary.resolve(), args.output, args.seed, args.max_attempts, args.timeout
    )


if __name__ == "__main__":
    main()
