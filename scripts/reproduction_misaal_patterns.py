"""Provenance for MISAAL repairs applied to pinned source before imports."""

CONTRACT = "exact-render-last-v1"

SOURCE_SHA256 = {
    "patterns.PatternUtils": (
        "lib/patterns/PatternUtils.py",
        "e89b1a4c9dda901f2416100dbc6b5e47554264e00eb755c52c669f48b54eb8d5",
    ),
    "compiler.Pattern": (
        "lib/compiler/Pattern.py",
        "aa82c2f0378242316e6ed1dffebf0add9419d27ba65039185df8fd315e3ba826",
    ),
    "common.Instructions": (
        "Hydride/code-synthesizer/dsl-ir/common/Instructions.py",
        "a6d267428a19017dcec7e6b4931e20256d16dde38f0fd4679b31fe2cadd34a26",
    ),
    "common.Types": (
        "Hydride/code-synthesizer/dsl-ir/common/Types.py",
        "aa2056271dcb75e5c9c8c1aaab0d026c2e005e748414a38ab1441bc4d0633d01",
    ),
}

PARAMETER_ABI_CONTRACT = "c098-four-argument-v1"

PARAMETER_ABI_SOURCE_SHA256 = {
    "lib/patterns/PatternUtils.py": "e89b1a4c9dda901f2416100dbc6b5e47554264e00eb755c52c669f48b54eb8d5",
    "misaal/synthesis/param_abstract.rkt": "762f379a373b30c965d8bb3760b2908515f52945e58a76c820c11da2fa6c2b47",
}

LITERAL_WIDTH_CONTRACT = "positive-literal-halving-v1"

LITERAL_WIDTH_SOURCE_SHA256 = {
    "targets/halide/axioms.egg": "5c710032858d34440ad94979c8788bb96967d1d71e93e55f3ea2bad2184ab4c1",
    "lib/compiler/EggLogCompiler.py": "87a96401b12291e184cf7eb65efe1f481bccd6faac514c56aef0502f1cc7c479",
}
