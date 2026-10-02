"""Adapt each complete DialEgg invocation without changing its schedule."""

from __future__ import annotations

import re

from scripts.paper_benchmarks import materialize


def modernize_dialegg_invocation(source: str, prelude: str) -> str:
    """Translate constructor/global/cost syntax while retaining the source schedule."""
    source = materialize.replace_once(source, '(include "src/base.egg")', prelude, "shared prelude")
    source = source.replace("(function nrows (Type) i64)", "(function nrows (Type) i64 :merge old)")
    source = source.replace("(function ncols (Type) i64)", "(function ncols (Type) i64 :merge old)")
    source = source.replace("(unstable-cost ", "(set-cost ")
    source = materialize.constructors(source)
    if "(set-cost (linalg_matmul " in source:
        source = materialize.replace_once(
            source,
            "(constructor linalg_matmul (Op Op Op Type) Op)",
            "(with-dynamic-cost (constructor linalg_matmul (Op Op Op Type) Op))",
            "dynamic cost constructor",
        )
    globals_ = set(re.findall(r"^\(let ([^\s()]+)", source, re.MULTILINE))
    modern = materialize.prefix_atoms(source, globals_).rstrip() + "\n"
    return modern
