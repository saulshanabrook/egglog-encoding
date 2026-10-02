#!/usr/bin/env python3
"""Translate the checked-in author corpus to the matching Egglog assertions."""

from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
INPUT = HERE.parent / "parameter-analysis.in"
OUTPUT = HERE.parent / "parameter-analysis.egg"


def source_program(native: str, equalities: int = 100_000, disequalities: int = 10_000) -> str:
    """Match the unchanged drivers' fixed constraints, pair partition, and order."""
    expressions = native.splitlines()
    count = 2 * (equalities + disequalities)
    if equalities < 0 or disequalities < 0 or len(expressions) < count:
        raise ValueError("not enough native expressions for the requested nonnegative pair counts")
    lines = [
        "; Parameter analysis from the author-supplied Dis-Equality Graphs corpus.",
        f"; Native input SHA-256: {hashlib.sha256(native.encode()).hexdigest()}",
        f"; {equalities} equality pairs; {disequalities} disequality pairs; six original numeral constraints.",
        "; Regenerate: python benchmarks/disequality/native/generate.py",
        "(datatype Term (N1) (N2) (N3) (N4) (N5) (f Term) (g Term Term) (h Term Term Term))",
    ]
    # Preserve the authors' exclusive upper bound: numeral 5 is not constrained.
    lines.extend(f"(disequal (N{x}) (N{y}))" for x in range(1, 6) for y in range(x + 1, 5))
    for index in range(0, count, 2):
        pair = expressions[index : index + 2]
        if not all(term.strip() for term in pair):
            raise ValueError(f"empty native expression in pair {index // 2}")
        lhs, rhs = (re.sub(r"\b([1-5])\b", r"(N\1)", term) for term in pair)
        command = "union" if index < 2 * equalities else "disequal"
        lines.append(f"({command} {lhs} {rhs})")
    return "\n".join(lines) + "\n(check-contradiction)\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=INPUT)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    args.output.write_text(source_program(args.input.read_text()))


if __name__ == "__main__":
    main()
