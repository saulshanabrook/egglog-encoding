"""Frozen Math checkpoint witnesses, canonical inputs, and untimed parity gates.

The eleven inputs keep the original rules and seeds. Their complete file bytes
include the cutoff and equality, so ordinary file hashes remain sufficient for
benchmark caching. Witness discovery is deliberately not part of the runner.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
MATH_WORKLOAD_PATH = Path("egglog-experimental/tests/math-microbenchmark-rational.egg")
# Pin the unchanged language/rules/seeds, rather than accepting whatever happens
# to occupy the legacy filename when a native binary ignores its contents.
LEGACY_SHA256 = "29e120079c588d0bf079891b393ae041ec4e1a45d369114cde3754e5c6b7878f"
MATH_CONSTRUCTORS = {
    "Diff": 2,
    "Integral": 2,
    "Add": 2,
    "Sub": 2,
    "Mul": 2,
    "Div": 2,
    "Pow": 2,
    "Ln": 1,
    "Sqrt": 1,
    "Sin": 1,
    "Cos": 1,
    "Const": 1,
    "Var": 1,
}


@dataclass(frozen=True)
class MathWitness:
    iterations: int
    left: str
    right: str


def load_witnesses() -> tuple[MathWitness, ...]:
    """Load the explicit, reviewed checkpoint list; never discover new queries."""

    records = json.loads((ROOT / "benchmarks/math/witnesses.json").read_text())
    witnesses = tuple(MathWitness(**record) for record in records)
    if tuple(witness.iterations for witness in witnesses) != tuple(range(1, 12)):
        raise ValueError("Math witnesses must contain the predeclared cutoffs 1 through 11 in order")
    return witnesses


def egglog_expression(expression: str) -> str:
    """Translate a ground native Math expression without evaluating or inserting it."""

    operators = {
        "d": ("Diff", 2),
        "i": ("Integral", 2),
        "+": ("Add", 2),
        "-": ("Sub", 2),
        "*": ("Mul", 2),
        "/": ("Div", 2),
        "pow": ("Pow", 2),
        "ln": ("Ln", 1),
        "sqrt": ("Sqrt", 1),
        "sin": ("Sin", 1),
        "cos": ("Cos", 1),
    }
    tokens = re.findall(r"\(|\)|[^\s()]+", expression)
    cursor = 0

    def render() -> str:
        nonlocal cursor
        if cursor >= len(tokens):
            raise ValueError("incomplete native Math expression")
        token = tokens[cursor]
        cursor += 1
        if token == "(":
            if cursor >= len(tokens) or tokens[cursor] not in operators:
                raise ValueError("unknown native Math operator")
            name, arity = operators[tokens[cursor]]
            cursor += 1
            children = [render() for _ in range(arity)]
            if cursor >= len(tokens) or tokens[cursor] != ")":
                raise ValueError("wrong native Math operator arity")
            cursor += 1
            return f"({name} {' '.join(children)})"
        if re.fullmatch(r"-?\d+(?:/[1-9]\d*)?", token):
            numerator, _, denominator = token.partition("/")
            return f"(Const (rational {numerator} {denominator or '1'}))"
        if token in {"x", "y", "five"}:
            return f"(Var {json.dumps(token)})"
        raise ValueError(f"unknown native Math atom: {token}")

    result = render()
    if cursor != len(tokens):
        raise ValueError("trailing tokens in native Math expression")
    return result


def render_math_workload(witness: MathWitness, *, iterations: int | None = None) -> str:
    """Materialize the original program plus one frozen cutoff/equality pair."""

    legacy = (ROOT / MATH_WORKLOAD_PATH).read_bytes()
    if hashlib.sha256(legacy).hexdigest() != LEGACY_SHA256:
        raise ValueError("canonical Math fixture changed; review the native port and frozen workloads together")
    program = legacy.decode().split("(datatype Math", 1)[1].split("\n(run 11)", 1)[0]
    cutoff = witness.iterations if iterations is None else iterations
    return (
        f"; Math{witness.iterations}: this witness is first established by these schedules at iteration "
        f"{witness.iterations}.\n"
        "; Original PLDI 2023 Math language, 24 rules, and seven seeds; no backoff.\n\n"
        f"(datatype Math{program}\n(run {cutoff})\n"
        f"(check (= {egglog_expression(witness.left)} {egglog_expression(witness.right)}))\n"
    )


def recognize_math_workload(path: Path) -> MathWitness:
    """Bind native parameters to the entire input, rejecting filename-only matches."""

    try:
        contents = path.read_bytes()
    except OSError as error:
        raise ValueError(f"cannot read canonical Math workload: {path}") from error
    witnesses = load_witnesses()
    if hashlib.sha256(contents).hexdigest() == LEGACY_SHA256:
        return witnesses[-1]
    for witness in witnesses:
        if contents == render_math_workload(witness).encode():
            return witness
    raise ValueError(
        f"native egg only supports {MATH_WORKLOAD_PATH.as_posix()} and exact frozen benchmarks/math inputs; "
        f"noncanonical workload: {path}"
    )


def validate_math_workload(
    path: Path,
    egg_binary: Path,
    egglog_binary: Path,
    evidence_directory: Path,
    *,
    runner: Callable[..., Any],
    timeout_sec: float = 120,
    memory_limit_bytes: int,
) -> dict[str, Any]:
    """Require the frozen N−1/N boundary, strict proofs, and logical-size parity.

    Negative Egglog checks run once unwrapped to distinguish an absent equality
    from other errors, and once under ``fail`` to inspect the graph afterwards.
    All diagnostics are untimed pilot evidence, outside the measurement cache.
    """
    from dataclasses import asdict

    witness = recognize_math_workload(path)
    evidence_directory.mkdir(parents=True, exist_ok=True)
    results: list[dict[str, Any]] = []
    snapshots: dict[int, dict[str, Any]] = {}
    count_rules = "\n".join(
        f"(rule ((= e ({name} {' '.join(f'x{i}' for i in range(arity))}))) "
        "((SeenMathEClass e)) :ruleset count-math-classes)"
        for name, arity in MATH_CONSTRUCTORS.items()
    )
    instrumentation = (
        "(relation SeenMathEClass (Math))\n(ruleset count-math-classes)\n"
        f"{count_rules}\n(run count-math-classes 1)\n(print-size)\n"
    )
    for cutoff in (witness.iterations - 1, witness.iterations):
        positive = cutoff == witness.iterations
        for engine, binary, mode, flags in (
            ("egg", egg_binary, "off", ["--proof-mode", "off"]),
            ("egglog", egglog_binary, "off", []),
            ("egg", egg_binary, "extraction", ["--proof-mode", "extract"]),
            ("egglog", egglog_binary, "extraction", ["--proof-extraction"]),
            *(
                (
                    ("egg", egg_binary, "strict", ["--proof-mode", "check"]),
                    ("egglog", egglog_binary, "strict", ["--proof-testing"]),
                )
                if positive
                else ()
            ),
        ):
            prefix = evidence_directory / f"{cutoff:02}-{engine}-{mode}"
            diagnostic = prefix.with_suffix(".json")
            if engine == "egg":
                command = [
                    str(binary),
                    *flags,
                    "--iterations",
                    str(cutoff),
                    "--check-left",
                    witness.left,
                    "--check-right",
                    witness.right,
                    "--diagnostic-output",
                    str(diagnostic),
                ]
                if not positive:
                    command.append("--expect-check-failure")
            else:
                program, check = render_math_workload(witness, iterations=cutoff).rsplit("(check ", 1)
                check = "(check " + check.strip()
                source = prefix.with_suffix(".egg")
                if not positive:
                    source.write_text(program + check + "\n")
                    negative = runner(
                        [str(binary), *flags, str(source)],
                        ROOT,
                        Path(str(prefix) + "-unwrapped"),
                        timeout_sec=timeout_sec,
                        memory_limit_bytes=memory_limit_bytes,
                    )
                    results.append(
                        {
                            "engine": engine,
                            "mode": mode,
                            "cutoff": cutoff,
                            "expected_unestablished": True,
                            **asdict(negative),
                        }
                    )
                    expected_error = (
                        "Check failed:" if mode == "off" else "Could not find a proof due to query not matching"
                    )
                    if negative.status != "failure" or expected_error not in negative.stderr_path.read_text():
                        return {
                            "status": negative.status
                            if negative.status in ("timed-out", "memory-limit")
                            else "failure",
                            "reason": (
                                f"N−1 {engine} {mode} expected an unestablished equality: "
                                f"{negative.message or 'check succeeded'}"
                            ),
                            "runs": results,
                        }
                    check = f"(fail {check})"
                source.write_text(program + instrumentation + check + "\n(run count-math-classes 1)\n(print-size)\n")
                command = [str(binary), *flags, str(source)]
            result = runner(
                command,
                ROOT,
                prefix,
                timeout_sec=timeout_sec,
                memory_limit_bytes=memory_limit_bytes,
            )
            entry = {"engine": engine, "mode": mode, "cutoff": cutoff, **asdict(result)}
            results.append(entry)
            if result.status != "success":
                return {"status": result.status, "reason": result.message, "runs": results}
            if engine == "egg":
                sizes = json.loads(diagnostic.read_text())
                if sizes["check_passed"] != positive or sizes["iterations"] != cutoff:
                    return {"status": "failure", "reason": "native check boundary differs", "runs": results}
            else:
                pairs = re.findall(r"\((\w+) (\d+)\)", result.stdout_path.read_text())
                names = set(MATH_CONSTRUCTORS) | {"SeenMathEClass"}
                pairs = [(name, int(count)) for name, count in pairs if name in names]
                if len(pairs) != 2 * len(names) or any(
                    {name for name, _ in pairs[start : start + len(names)]} != names for start in (0, len(names))
                ):
                    return {"status": "failure", "reason": "missing or ambiguous Egglog logical sizes", "runs": results}
                sizes = {}
                for label, start in (("before", 0), ("after", len(names))):
                    counts = dict(pairs[start : start + len(names)])
                    sizes[label] = {"classes": counts.pop("SeenMathEClass"), "constructors": counts}
                diagnostic.write_text(json.dumps(sizes, indent=2) + "\n")
            entry["sizes"] = sizes
            if sizes["before"] != sizes["after"]:
                return {"status": "failure", "reason": "query changed the logical graph", "runs": results}
            expected = snapshots.setdefault(cutoff, sizes["before"])
            if sizes["before"] != expected:
                return {
                    "status": "failure",
                    "reason": f"cross-engine/proof-mode size mismatch at {cutoff}",
                    "runs": results,
                }
    return {"status": "success", "reason": None, "iterations": witness.iterations, "runs": results}
