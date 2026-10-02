"""The fixed Math11 input and its separate, untimed correctness diagnostics."""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Callable
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


def recognize_math_workload(path: Path) -> None:
    """Accept only the complete unchanged Math11 input used by the native runner."""

    try:
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError as error:
        raise ValueError(f"cannot read canonical Math workload: {path}") from error
    if digest != LEGACY_SHA256:
        raise ValueError(f"native egg supports only the fixed Math11 workload ({MATH_WORKLOAD_PATH}): {path}")


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
    All diagnostics remain outside the measurement cache.
    """
    from dataclasses import asdict

    recognize_math_workload(path)
    canonical_program, canonical_check = path.read_text().rsplit("(check ", 1)
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
    for cutoff in (10, 11):
        positive = cutoff == 11
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
                    "--diagnostic-output",
                    str(diagnostic),
                ]
                if not positive:
                    command.append("--expect-check-failure")
            else:
                program = canonical_program.replace("(run 11)", f"(run {cutoff})")
                check = "(check " + canonical_check.strip()
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
    return {"status": "success", "reason": None, "iterations": 11, "runs": results}
