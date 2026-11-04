#!/usr/bin/env python3
"""Actual compiler/native sort-key causal matrix; never records timings."""

from pathlib import Path
import hashlib
import importlib.util
import json
import os
import re
import sys

BASE = Path(__file__).resolve().parent
ROOT = Path(os.environ.get("SORT_OUTPUT_ROOT", str(BASE)))
spec = importlib.util.spec_from_file_location("capture", BASE / "run.py")
capture = importlib.util.module_from_spec(spec)
spec.loader.exec_module(capture)
capture.ROOT = ROOT
U0 = BASE.parent / "admission/bin/eggcc"
CANDIDATE = Path(os.environ.get("SORT_BINARY", str(BASE / "bin/eggcc")))
LLVM = Path("/opt/homebrew/opt/llvm@18/bin")
MODES = [
    "off",
    "seed-only",
    "primitive-only",
    "cancellation-off",
    "forward-off",
    "reverse-off",
    "identity-off",
    "cancellation-rescue",
    "reverse-rescue",
    "query-off",
    "manual",
    "encoding",
    "bridge-off",
    "application-off",
]


def emit(family, mode, source, context=True):
    folder = ROOT / "matrix" / family / mode
    if folder.exists():
        assert (folder / "optimized.bril").is_file()
        return folder
    folder.mkdir(parents=True)
    capture.ENV["EGGCC_SCOPED_MODE"] = mode
    evidence = folder / "evidence"
    capture.ENV["EGGCC_SCOPED_EVIDENCE"] = str(evidence)
    argv = [U0 if mode == "u0" else CANDIDATE]
    if context:
        argv += ["--with-context"]
    argv += ["--run-mode", "optimize", "--run-data-out", folder / "emit.json", source]
    if mode == "source":
        (folder / "optimized.bril").write_bytes(source.read_bytes())
    else:
        (folder / "optimized.bril").write_bytes(capture.run(f"{family}-{mode}-emit", argv))
    capture.ENV.pop("EGGCC_SCOPED_EVIDENCE", None)
    capture.ENV["EGGCC_SCOPED_MODE"] = "off"
    capture.run(
        f"{family}-{mode}-parse",
        [
            U0,
            "--with-context",
            "--run-mode",
            "parse",
            "--interp",
            "--run-data-out",
            folder / "parse.json",
            folder / "optimized.bril",
        ],
    )
    return folder


def native(folder, label):
    output = folder / "native"
    if output.exists():
        assert (output / "program").is_file()
        return output / "program"
    output.mkdir()
    capture.ENV["EGGCC_SCOPED_MODE"] = "off"
    capture.ENV.pop("EGGCC_SCOPED_EVIDENCE", None)
    capture.run(
        label + "-lower",
        [
            U0,
            "--with-context",
            "--run-mode",
            "llvm",
            "--optimize-egglog",
            "false",
            "--optimize-bril-llvm",
            "O3_O3",
            "-o",
            output / "program",
            "--llvm-output-dir",
            output / "program.ll",
            "--run-data-out",
            output / "lower.json",
            folder / "optimized.bril",
        ],
    )
    assembly = capture.run(
        label + "-disassemble",
        [LLVM / "llvm-objdump", "--disassemble", "--no-show-raw-insn", output / "program"],
        30,
    ).decode()
    (output / "program.asm").write_text(assembly)
    lines = assembly.splitlines()
    blocks = []
    for index, line in enumerate(lines):
        if re.match(r"^[0-9a-f]+ <_*main>:", line):
            end = next(
                (
                    later
                    for later in range(index + 1, len(lines))
                    if re.match(r"^[0-9a-f]+ <.*>:", lines[later])
                ),
                len(lines),
            )
            blocks.append("\n".join(lines[index:end]))
    (output / "main.asm").write_text("\n\n".join(blocks) + "\n")
    return output / "program"


def receipts(folder):
    evidence = folder / "evidence"
    if not evidence.exists():
        return []
    return [
        query
        for path in sorted(evidence.glob("boundary*.json"))
        for query in json.loads(path.read_text())["queries"]
    ]


def test(family, mode, source, rows, context=True):
    folder = emit(family, mode, source, context)
    binary = native(folder, family + "-" + mode)
    parsed = json.loads((folder / "parse.json").read_text())
    assert parsed["original_interpreted"] == parsed["result_interpreted"], parsed
    outputs = []
    for index, row in enumerate(rows):
        expected = row.get("expected_stdout", parsed["original_interpreted"])
        stdout = capture.run(
            f"{family}-{mode}-native-{index:02}",
            [binary, *map(str, row["args"])],
            30,
        ).decode()
        assert stdout == expected, (family, mode, row["args"], stdout, expected)
        outputs.append({"args": row["args"], "expected": expected, "stdout": stdout})
    return {
        "family": family,
        "mode": mode,
        "source": str(source),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "emitted_sha256": hashlib.sha256((folder / "optimized.bril").read_bytes()).hexdigest(),
        "main_sha256": hashlib.sha256((folder / "native/main.asm").read_bytes()).hexdigest(),
        "outputs": outputs,
        "queries": receipts(folder),
    }


def args_from_source(path):
    first = path.read_text().splitlines()[0]
    assert first.startswith("# ARGS:")
    return [int(value) for value in first.removeprefix("# ARGS:").split()]


def main():
    phase = sys.argv[1] if len(sys.argv) > 1 else "positive"
    fixtures = BASE / "fixtures"
    source = fixtures / "source.bril"
    results = []
    if phase == "positive":
        rows = [
            {"args": row["args"], "expected_stdout": row["expected_stdout"]}
            for row in json.loads((BASE / "positive-oracle.json").read_text())
        ]
        for mode in ["source", "u0", *MODES]:
            results.append(test("positive", mode, source, rows))
    elif phase == "negative":
        for name in [
            "omitted-tag",
            "omitted-min",
            "omitted-max",
            "reversed-right-tag",
            "changed-right-tag",
            "even-multiplier",
            "wrong-mixed-branch",
            "no-key-context",
        ]:
            negative = fixtures / f"{name}.bril"
            row = {"args": args_from_source(negative)}
            for mode in ["source", "u0", "off", "seed-only", "primitive-only", "manual", "encoding"]:
                results.append(test(name, mode, negative, [row]))
    elif phase == "context-negative":
        rows = [
            {"args": row["args"], "expected_stdout": row["expected_stdout"]}
            for row in json.loads((BASE / "positive-oracle.json").read_text())
        ]
        for mode in ["u0", "encoding"]:
            results.append(test("no-context-final", mode, source, rows, False))
    else:
        raise ValueError(phase)
    (ROOT / f"{phase}-results.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
