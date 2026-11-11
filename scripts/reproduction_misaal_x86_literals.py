"""Repair the pinned x86 selector's binary-as-hexadecimal literal decoding.

Only fresh preparation calls this materializer. Existing source/product trees and
the LLVM lowering audit are untouched; the native gates remain mandatory.
"""

from __future__ import annotations

import ast
import hashlib
import inspect
import json
import re
from pathlib import Path
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from scripts.reproduction_prepare_misaal import Preparation

SELECTOR = "codegen-generator/tools/low-level-codegen/InstSelectors/x86/x86LegalizerAllArgs.cpp"
GENERATOR = "codegen-generator/tools/low-level-codegen/InstSelectors/x86/RoseX86LegalizerGen.py"
SEMANTICS = "code-synthesizer/dsl-ir/x86SemanticsAllArgs.py"
SOURCE_SHA256 = {
    SELECTOR: "745e093b192cf6db338022b4943cf5329d1fc4a06e2ac4d59455c70ed82998f6",
    GENERATOR: "6c6433a488f876f3014579a70af070aec898fa1ff7f1d17cd4f96f02adedaec0",
    SEMANTICS: "bebe9f04ec1f28dfa1451eceebd9e3e12d71526cf3e4b55aead6274408e55f6e",
}
EXPECTED_REPAIR_COUNTS = (1951, 1349)
OLD_DECODE = """            ArgVal = ArgVal.replace("(bv #", "").strip()
            ArgVal = ArgVal[:ArgVal.index(" ")]
            ArgVal = "0" + ArgVal
            intArg = int(ArgVal, 16)
            ArgVal = hex(intArg)+"_cppi"  # Use boost literal to support int512_t initialization"""


def parse_selector_literal(literal: str) -> int:
    """Decode an integer or concrete bitvector into the selector's numeric bits.

    Rosette's bv masks integers to the stated width, including negative values.
    Legalizer compares ConstantInt hex bit patterns, so bv results are unsigned;
    plain integer parameters retain their sign. The selector uses int512_t.
    This self-contained function is also embedded in the acquired generator.
    """
    import re

    text = literal.strip()
    if re.fullmatch(r"[+-]?[0-9]+", text):
        value = int(text, 10)
        if abs(value).bit_length() > 512:
            raise ValueError("selector integer exceeds int512_t")
        return value
    match = re.fullmatch(r"\(bv\s+(#[bB][+-]?[01]+|#[xX][+-]?[0-9a-fA-F]+|[+-]?[0-9]+)\s+([0-9]+)\)", text)
    if match is None:
        raise ValueError(f"unsupported selector literal: {literal!r}")
    token, width_token = match.groups()
    width = int(width_token)
    if not 1 <= width <= 512:
        raise ValueError("selector bitvector width must be in 1..512")
    base = {"b": 2, "x": 16}[token[1].lower()] if token.startswith("#") else 10
    value = int(token[2:] if token.startswith("#") else token, base)
    return value % (1 << width)


def repair_generated_cases(source: str, semantics: dict[str, Any]) -> tuple[str, list[dict[str, Any]]]:
    """Bind every emitted case/guard to its source entry before changing digits.

    Rose emits names and branches in the same order, including div/rem branches
    without wrappers. Preserve that order, every guard, permutation and action.
    The caller hash-gates the entire source and table before materialization.
    """
    instructions: dict[str, Any] = {}
    for group in semantics.values():
        for name, info in group["target_instructions"].items():
            if name in instructions:
                raise ValueError(f"ambiguous semantics entry: {name}")
            instructions[name] = info
    groups = list(re.finditer(r"std::vector<std::string> InstNames = \{([^}]*)\};", source))
    if not groups:
        raise ValueError("no generated selector groups")
    edits = []
    changes = []
    seen: set[str] = set()
    for index, group in enumerate(groups):
        end = (
            groups[index + 1].start()
            if index + 1 < len(groups)
            else source.index("bool X86LegalizationPass::", group.end())
        )
        names = re.findall(r'"llvm\.hydride\.(\w+)_dsl"', group[1])
        if re.sub(r'"llvm\.hydride\.\w+_dsl"|[\s,]', "", group[1]):
            raise ValueError("unsupported generated name list")
        cases = list(re.finditer(r"if\((isAMatch\(CI,.*?)(?=\) \{)", source[group.end() : end], re.S))
        if len(cases) != len(names):
            raise ValueError("generated case/name count differs")
        for name, case in zip(names, cases, strict=True):
            if name in seen or name not in instructions:
                raise ValueError(f"unknown or duplicate generated case: {name}")
            seen.add(name)
            info = instructions[name]
            expected = [
                (i, arg)
                for i, (arg, permutation) in enumerate(zip(info["args"], info["arg_permute_map"], strict=True))
                if "SYMBOLIC_BV" not in arg and permutation == -1
            ]
            guard = re.compile(r'isAMatch\(CI, (\d+), (?P<value>-?\d+|int512_t\("-?\d+"\))\)')
            guards = list(guard.finditer(case[1]))
            if len(guards) != len(expected) or re.sub(r"[\s&]", "", guard.sub("", case[1])):
                raise ValueError(f"unsupported guard shape: {name}")
            for call, (argument, literal) in zip(guards, expected, strict=True):
                token = call["value"]
                actual = int(token.removeprefix('int512_t("').removesuffix('")'))
                # Reproduce the original decoder only as an equality guard on
                # the old source; the replacement uses the real radix/width.
                old = (
                    int("0" + literal.replace("(bv #", "").strip().split(" ")[0], 16)
                    if "bv" in literal
                    else int(literal)
                )
                if int(call[1]) != argument or actual != old:
                    raise ValueError(f"source/selector guard mismatch: {name} argument {argument}")
                value = parse_selector_literal(literal)
                if value == old:
                    continue
                if not literal.startswith("(bv #b"):
                    raise ValueError("pinned repair would change a non-binary source literal")
                start = group.end() + case.start(1) + call.start("value")
                stop = group.end() + case.start(1) + call.end("value")
                edits.append((start, stop, str(value)))
                changes.append(
                    {"instruction": name, "argument": argument, "literal": literal, "before": old, "after": value}
                )
    for start, stop, replacement in reversed(edits):
        source = source[:start] + replacement + source[stop:]
    return source, changes


def repair_generator(source: str) -> str:
    """Replace the exact faulty decoder and embed the same tested parser."""
    marker = "class RoseInstSelectorGenerator():"
    if source.count(OLD_DECODE) != 1 or source.count(marker) != 1 or "def parse_selector_literal(" in source:
        raise ValueError("selector generator decoder/context changed")
    source = source.replace(
        OLD_DECODE,
        '            ArgVal = hex(parse_selector_literal(ArgVal)) + "_cppi"\n'
        "          else:\n"
        "            ArgVal = str(parse_selector_literal(ArgVal))",
    )
    return source.replace(marker, inspect.getsource(parse_selector_literal) + "\n\n" + marker)


def patch_selector_literals(preparation: Preparation) -> None:
    """Patch fresh pinned source only, retaining all derivations before building."""
    hydride = preparation.directory / "sources/MISAAL/Hydride"
    sources = {name: (hydride / name).read_text() for name in SOURCE_SHA256}
    for name, expected in SOURCE_SHA256.items():
        if hashlib.sha256(sources[name].encode()).hexdigest() != expected:
            raise ValueError(f"x86 literal repair source changed: {name}")
    definitions = [
        node.value
        for node in ast.parse(sources[SEMANTICS]).body
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "semantcs" for t in node.targets)
    ]
    if len(definitions) != 1:
        raise ValueError("expected one pinned semantics dictionary")
    selector, changes = repair_generated_cases(sources[SELECTOR], ast.literal_eval(definitions[0]))
    generator = repair_generator(sources[GENERATOR])
    if (len(changes), len({c["instruction"] for c in changes})) != EXPECTED_REPAIR_COUNTS:
        raise ValueError("pinned binary literal repair coverage differs")
    preparation.patch(hydride / SELECTOR, [(sources[SELECTOR], selector)], "legalizer-binary-literals")
    preparation.patch(hydride / GENERATOR, [(sources[GENERATOR], generator)], "legalizer-generator-literals")
    receipt = {
        "contract": "x86-selector-literals-v1",
        "source_sha256": SOURCE_SHA256,
        "helper_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "after_sha256": {
            SELECTOR: hashlib.sha256(selector.encode()).hexdigest(),
            GENERATOR: hashlib.sha256(generator.encode()).hexdigest(),
        },
        "validated_cases": len(re.findall(r'"llvm\.hydride\.\w+_dsl"', sources[SELECTOR])),
        "validated_guards": sources[SELECTOR].count("isAMatch(CI, "),
        "changes": changes,
    }
    with (preparation.directory / "patches/legalizer-literal-derivation.json").open("x") as output:
        json.dump(receipt, output, indent=2)
        output.write("\n")
