#!/usr/bin/env python3
"""Future actual-host P1 causal/native replay; contains no performance campaign."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import hashlib
import re

BASE = Path(__file__).resolve().parent
ROOT = Path(os.environ.get("PACK32_OUTPUT_ROOT", str(BASE / "probe-01")))
SCREEN = BASE.parent / "pack32-screen"
LOWER = BASE.parent / "admission/bin/eggcc"
BIN = Path(os.environ.get("PACK32_BINARY", str(BASE / "bin/eggcc")))
LLVM = Path("/opt/homebrew/opt/llvm@18/bin")
spec = importlib.util.spec_from_file_location("pack32_capture", BASE / "run.py")
capture = importlib.util.module_from_spec(spec)
spec.loader.exec_module(capture)
capture.ROOT = ROOT
MODES = ["off", "seed-only", "primitive-only", "cancellation-off", "cancellation-rescue",
         "reverse-off", "disequality-rescue", "forward-off", "query-off", "manual",
         "encoding", "bridge-off", "consumer-off"]


def reference(args, kind):
    """Independent bounded byte packing; explicit wrapping model for weakened laws."""
    a, b, c, d, n = args
    fields = [a, b, c, d]
    for index, value in enumerate(fields):
        if value < 0 and not (index == 0 and kind == "missing-lower-bound"):
            return "-2\n"
        if value >= 1 << 32 and not (index == 0 and kind == "missing-bound") and not (index == 1 and kind == "missing-low-upper-bound"):
            return "-2\n"
    if not 0 <= n <= 1000000:
        return "-2\n"
    base, mask, seven, total = 1 << 32, (1 << 32) - 1, 7, 0
    def wrap(value):
        value &= (1 << 64) - 1
        return value if value < 1 << 63 else value - (1 << 64)
    def pack(high, low, width):
        if width == 1 << 32 and 0 <= high < 1 << 32 and 0 <= low < 1 << 32:
            return int.from_bytes(high.to_bytes(4, "big") + low.to_bytes(4, "big"), "big", signed=True)
        return wrap(high * width + low)
    for _ in range(n):
        ab, cd, ca = pack(a, b, base), pack(c, d, 65536 if kind == "different-width" else base), pack(c, a, base)
        equal = ab == cd
        if kind == "wrong-first-branch":
            equal = not equal
        if not equal and kind != "unresolved-fields":
            score = 3
        elif ca == ab and kind != "missing-parent-disequality":
            score = 5
        else:
            left = b if kind == "swapped-target-field" else c
            right_shift = 8 if kind == "wrong-translation" else seven
            score = 99 if wrap(left + seven) == wrap(d + right_shift) else 7
        total = wrap(total + score)
        if kind == "changed-mask":
            mask = wrap(mask + 1)
        if kind == "changed-base":
            base = wrap(base + 1)
        if kind == "changed-seven":
            seven = wrap(seven + 1)
        a = wrap(a + 1) if kind == "unmasked-backedge" else wrap(a + 1) & mask
        b, c, d = wrap(b + 3) & mask, wrap(c + 1) & mask, wrap(d + 3) & mask
    return f"{total}\n"


def fixtures(phase):
    source = (SCREEN / "source.bril").read_text()
    oracle = json.loads((SCREEN / "oracle.json").read_text())
    if phase == "positive":
        return [("positive", source, oracle["positive_rows"])]
    changes = {
        "missing-bound": ("  a_hi: bool = lt a base;", "  a_hi: bool = const true;", [1 << 32, 0, 0, 0, 1]),
        "different-width": ("  pc_hi: int = mul c base;", "  other_base: int = const 65536;\n  pc_hi: int = mul c other_base;", [0, 65537, 1, 1, 1]),
        "unresolved-fields": ("  br same_key .equal_key .different_key;", "  jmp .equal_key;", [1, 0, 0, 0, 1]),
        "missing-lower-bound": ("  a_lo: bool = ge a zero;", "  a_lo: bool = const true;", [-1, (1 << 32) - 1, (1 << 32) - 1, (1 << 32) - 1, 1]),
        "missing-low-upper-bound": ("  b_hi: bool = lt b base;", "  b_hi: bool = const true;", [0, (1 << 32) + 1, 1, 1, 1]),
        "missing-parent-disequality": ("  br second_same .same_fields .different_fields;", "  jmp .different_fields;", [1, 1, 1, 1, 1]),
        "wrong-first-branch": ("  br same_key .equal_key .different_key;", "  br same_key .different_key .equal_key;", [1, 0, 0, 0, 1]),
        "wrong-translation": ("  td: int = add d seven;", "  eight: int = const 8;\n  td: int = add d eight;", [2, 1, 2, 1, 1]),
        "swapped-target-field": ("  tc: int = add c seven;", "  tc: int = add b seven;", [1, 2, 1, 2, 1]),
        "unmasked-backedge": ("  a: int = bitand aa mask;", "  a: int = id aa;", [(1 << 32) - 1, (1 << 32) - 3, (1 << 32) - 1, (1 << 32) - 3, 2]),
        "changed-mask": ("  a: int = bitand aa mask;", "  mask: int = add mask one;\n  a: int = bitand aa mask;", [1, 2, 1, 2, 2]),
        "changed-base": ("  sum: int = add sum score;", "  base: int = add base one;\n  sum: int = add sum score;", [1, 2, 1, 2, 2]),
        "changed-seven": ("  sum: int = add sum score;", "  seven: int = add seven one;\n  sum: int = add sum score;", [1, 2, 1, 2, 2]),
    }
    names = list(changes)[:9] if phase == "negative" else list(changes)[9:]
    if phase == "context-negative":
        return [("no-context", source, oracle["positive_rows"])]
    assert phase in {"negative", "loop-negative"}
    result = []
    for name in names:
        old, new, args = changes[name]
        assert source.count(old) == 1
        text = source.replace(old, new).replace("# ARGS: 1 2 1 2 8", "# ARGS: " + " ".join(map(str, args)))
        expected = reference(args, name)
        if phase == "negative":
            assert expected == "99\n", (name, expected)
        result.append((name, text, [dict(args=args, expected_stdout=expected)]))
    return result


def test(family, mode, source, rows, context):
    folder = ROOT / "matrix" / family / mode
    folder.mkdir(parents=True, exist_ok=False)
    capture.ENV["EGGCC_SCOPED_MODE"] = mode
    capture.ENV["EGGCC_SCOPED_EVIDENCE"] = str(folder / "evidence")
    argv = [LOWER if mode == "u0" else BIN]
    if context:
        argv += ["--with-context"]
    argv += ["--run-mode", "optimize", "--run-data-out", folder / "emit.json", source]
    emitted = folder / "optimized.bril"
    emitted.write_bytes(capture.run(f"{family}-{mode}-emit", argv))
    capture.ENV.pop("EGGCC_SCOPED_EVIDENCE", None)
    capture.ENV["EGGCC_SCOPED_MODE"] = "off"
    capture.run(f"{family}-{mode}-parse", [LOWER, "--with-context", "--run-mode", "parse", "--interp", "--run-data-out", folder / "parse.json", emitted])
    parsed = json.loads((folder / "parse.json").read_text())
    assert parsed["original_interpreted"] == parsed["result_interpreted"] == rows[0]["expected_stdout"]
    native = folder / "native"
    native.mkdir()
    binary = native / "program"
    capture.run(f"{family}-{mode}-lower", [LOWER, "--with-context", "--run-mode", "llvm", "--optimize-egglog", "false", "--optimize-bril-llvm", "O3_O3", "-o", binary, "--llvm-output-dir", native / "program.ll", "--run-data-out", native / "lower.json", emitted])
    assembly = capture.run(f"{family}-{mode}-disassemble", [LLVM / "llvm-objdump", "--disassemble", "--no-show-raw-insn", binary], 30).decode()
    (native / "program.asm").write_text(assembly)
    main = re.search(r"^[0-9a-f]+ <_main>:\n.*?(?=\n[0-9a-f]+ <|\Z)", assembly, re.M | re.S)
    assert main
    (native / "main.asm").write_text(main.group(0) + "\n")
    outputs = []
    for index, row in enumerate(rows):
        output = capture.run(f"{family}-{mode}-native-{index:02}", [binary, *row["args"]], 30).decode()
        assert output == row["expected_stdout"], (family, mode, row, output)
        outputs.append(dict(args=row["args"], expected_stdout=row["expected_stdout"], stdout=output))
    queries = [query for path in sorted((folder / "evidence").glob("boundary*.json")) for query in json.loads(path.read_text())["queries"]]
    return dict(family=family, mode=mode, source=str(source), source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                compiler_sha256=hashlib.sha256(Path(argv[0]).read_bytes()).hexdigest(),
                emitted_sha256=hashlib.sha256(emitted.read_bytes()).hexdigest(),
                main_sha256=hashlib.sha256((native / "main.asm").read_bytes()).hexdigest(), outputs=outputs, queries=queries)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["positive", "negative", "loop-negative", "context-negative"], nargs="?", default="positive")
    phase = parser.parse_args().phase
    output = ROOT / (phase + "-results.json")
    assert not output.exists(), "Choose a fresh PACK32_OUTPUT_ROOT"
    inputs = ROOT / "fixtures"
    inputs.mkdir(parents=True, exist_ok=True)
    results = []
    for family, text, rows in fixtures(phase):
        source = inputs / (family + ".bril")
        if source.exists():
            assert source.read_text() == text
        else:
            source.write_text(text)
        parse_path = inputs / (family + "-source-parse.json")
        capture.ENV["EGGCC_SCOPED_MODE"] = "off"
        capture.ENV.pop("EGGCC_SCOPED_EVIDENCE", None)
        capture.run(family + "-source-parse", [LOWER, "--with-context", "--run-mode", "parse", "--interp", "--run-data-out", parse_path, source])
        parsed = json.loads(parse_path.read_text())
        assert parsed["original_interpreted"] == parsed["result_interpreted"] == rows[0]["expected_stdout"]
        modes = ["u0", *MODES] if phase == "positive" else ["u0", "off", "seed-only", "primitive-only", "manual", "encoding"]
        if phase == "context-negative":
            modes = ["encoding"]
        for mode in modes:
            results.append(test(family, mode, source, rows, phase != "context-negative"))
    output.write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
