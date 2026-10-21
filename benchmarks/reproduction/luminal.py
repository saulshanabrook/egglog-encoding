"""A source-derived output query for Luminal's published schedules."""

import re


def luminal_witness(source: str) -> tuple[str, str]:
    """Select a seeded Iota whose KernelIota form is derived by the source rule."""
    rule = (
        "(rule ((= ?__rw0 (Op (Iota ?v4_expr ?v4_range) ?__inputs))) "
        "((union ?__rw0 (Op (KernelIota ?v4_expr ?v4_range) ?__inputs)) "
        "(set (dtype (Op (KernelIota ?v4_expr ?v4_range) ?__inputs)) (Int))) :ruleset kernel_lower)"
    )
    normalized_rules = re.sub(r"\?v[0-9]+_(expr|range)", r"?v4_\1", source)
    if rule not in normalized_rules or "(run kernel_lower)" not in source:
        raise ValueError("source does not contain the expected active Iota lowering rule")
    for line in source.splitlines():
        match = re.fullmatch(r"\(let (t[0-9]+) (\(Op \(Iota .*)\)", line)
        if match:
            root, original = match.groups()
            derived = original.replace("(Iota ", "(KernelIota ", 1)
            if any(derived in seed for seed in source.splitlines() if seed.startswith("(let ")):
                continue
            return root, f"(check (= {root} {derived}))"
    raise ValueError("no seeded Iota has a newly derived KernelIota witness")
