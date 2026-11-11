"""Repair SIMD pass mode and reject the observed loss of selected LLVM results."""

from __future__ import annotations

import re
from typing import Any


def simd_mode_replacements(source: str, target: str) -> list[tuple[str, str]]:
    """Set the selected SIMD pass instance's mode; leave BitSIMD's default intact.

    Works on checked-in C++ or the same literal emitted by Rose's ARM generator.
    The pinned common Legalizer uses InstToInstMap only when bitsimd is false;
    true instead replaces calls with undef for its separate PIM execution path.
    """
    names = {
        "x86": ("X86LegalizationPass", "X86Legalizer"),
        "arm": ("ARMLegalizationPass", "ARMLegalizer"),
        "hvx": ("HexLegalizationPass", "HexLegalizer"),
    }
    if target not in names:
        raise ValueError("only x86, ARM and HVX SIMD pass instances may be repaired")
    pass_name, selector = names[target]
    signature = f"bool {pass_name}::runOnFunction(Function &F)"
    if source.count(signature) != 1:
        raise ValueError(f"expected exactly one original {pass_name} definition")
    pattern = re.compile(
        rf"^(?P<indent>[ \t]*)Legalizer \*L = new {selector}\(\);\n"
        r"(?P<mode>(?P=indent)L->bitsimd = false;\n)?(?P=indent)return L->legalize\(F\);",
        re.M,
    )
    matches = list(pattern.finditer(source))
    if len(matches) != 1:
        raise ValueError(f"expected one unambiguous {selector} allocation followed by legalization")
    match = matches[0]
    if match.group("mode"):
        return []
    old = match.group()
    new = old.replace("\n", "\n" + match.group("indent") + "L->bitsimd = false;\n", 1)
    return [(old, new)]


def audit_simd_lowering(llvm: str, required_functions: set[str]) -> dict[str, Any]:
    """Check the native intermediate before it is returned to the parent compiler.

    This catches the demonstrated valid-LLVM/undefined-result failure and residual
    target-agnostic calls. It is not a proof of full LLVM semantic equivalence.
    """
    if not required_functions:
        raise ValueError("SIMD lowering audit requires the actual requested function names")
    definitions = {
        quoted or plain: body
        for quoted, plain, body in re.findall(
            r'^define\b[^\n@]*@(?:"([^"\n]+)"|([\w.$-]+))[^\n]*\{\n(.*?)^\}', llvm, re.M | re.S
        )
    }
    missing = sorted(required_functions - definitions.keys())
    undefined = []
    unlowered = []
    for name in sorted(required_functions & definitions.keys()):
        body = definitions[name]
        if re.search(r"^\s*ret\b[^\n]*\s(?:undef|poison)\s*(?:,\s*!.*)?$", body, re.M):
            undefined.append(name)
        if re.search(r'\b(?:call|invoke)\b[^\n]*@"?llvm\.hydride\.', body):
            unlowered.append(name)
    return {
        "status": "failure" if missing or undefined or unlowered else "success",
        "required_functions": sorted(required_functions),
        "missing_functions": missing,
        "undefined_return_functions": undefined,
        "unlowered_hydride_call_functions": unlowered,
        "scope": "function presence, direct undefined returns and remaining hydride calls; not semantic equivalence",
    }
