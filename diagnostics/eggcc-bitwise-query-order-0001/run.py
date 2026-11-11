"""One guarded fact-order diagnostic; never admits or changes a corpus workload."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter
from collections.abc import Callable
from dataclasses import asdict
from pathlib import Path

ENGINE_SHA256 = "7eb04703af3707fb60c1ebe8cef66a86f72de1dc55081c636b8ea38fe06229b2"
REPLAY_SHA256 = "ced29250ea65acb944aba02f05d92070c7aa0431017e85e26c3431ecf06f7768"
CAPTURE_SHA256 = "d9eb2fa090b404600bddfe68970e7a93c3457aa616b02114a9ecde839d1b2fbf"
INTENT_SHA256 = "1c7da56b5c7ac4a91dca39cc78585f18f5b17dafaeee7582351a7166a034bb74"


def reorder_check(source: str, parse_forms: Callable[[str], list[tuple[int, int, list[str]]]]) -> tuple[str, dict]:
    """Move two whole existing facts, proving exact conjunction preservation."""
    forms = parse_forms(source)
    checks = [(index, form) for index, form in enumerate(forms) if form[2][1] == "check"]
    assert len(checks) == 6, "expected the six original native-root checks"
    command, (start, end, _) = checks[2]
    assert command == 1000, "third-check command boundary changed"
    original_check = source[start:end]
    opening = re.match(r"\(\s*check\b", original_check)
    assert opening is not None and original_check.endswith(")")
    body = original_check[opening.end() : -1]
    facts = parse_forms(body)
    assert len(facts) == 1110 and all(tokens[:2] == ["(", "="] for _, _, tokens in facts)
    fresh = [i for i, (_, _, t) in enumerate(facts) if "@GeneratedFreshTable4" in t]
    assert fresh == [376], "expected exactly the recorded fresh-context row"
    assert facts[376][2][:5] == ["(", "=", "reproduction_2_o31", "(", "@GeneratedFreshTable4"]
    assert len(facts[376][2]) == 27, "fresh-context row must retain all 20 arguments"
    assert facts[-1][2] == ["(", "=", "reproduction_2_seed306", "reproduction_2_s225", ")"]
    order = [376, 1109, *(i for i in range(1110) if i not in {376, 1109})]
    reordered_check = "(check\n  " + "\n  ".join(body[facts[i][0] : facts[i][1]] for i in order) + "\n)"
    reordered = source[:start] + reordered_check + source[end:]
    new_forms = parse_forms(reordered)
    assert len(new_forms) == len(forms)
    for index, (before, after) in enumerate(zip(forms, new_forms, strict=True)):
        if index != command:
            assert source[before[0] : before[1]] == reordered[after[0] : after[1]]
    new_body = reordered_check[len("(check") : -1]
    new_facts = parse_forms(new_body)
    original_multiset = Counter(tuple(tokens) for _, _, tokens in facts)
    assert original_multiset == Counter(tuple(tokens) for _, _, tokens in new_facts)
    assert [tokens for _, _, tokens in new_facts] == [facts[i][2] for i in order]
    assert reordered[:start] == source[:start] and reordered[start + len(reordered_check) :] == source[end:]
    multiset_json = json.dumps(sorted((list(tokens), count) for tokens, count in original_multiset.items()))
    return reordered, {
        "command_index": command,
        "native_root": "loop_subroutine",
        "check_count": len(checks),
        "fact_count": len(facts),
        "original_fact_positions_moved_to_front": [376, 1109],
        "new_fact_order": order,
        "fact_token_multiset_sha256": hashlib.sha256(multiset_json.encode()).hexdigest(),
        "identical_fact_token_multisets": True,
        "all_other_command_bytes_unchanged": True,
        "prefix_and_suffix_bytes_unchanged": True,
        "new_actions_or_constraints": 0,
    }


def main() -> int:
    if not __debug__:
        raise RuntimeError("this diagnostic requires Python assertions; do not use -O or PYTHONOPTIMIZE")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True, help="fresh durable attempt directory")
    args = parser.parse_args()
    root, output = args.root.resolve(), args.output.resolve()
    durable = root / "benchmarks/local/reproduction/diagnostics"
    if not output.is_relative_to(durable.resolve()) or output.exists():
        raise ValueError("output must be a fresh directory below root/benchmarks/local/reproduction/diagnostics")
    sys.path.insert(0, str(root))
    from benchmarking.pilot import run_bounded_command
    from scripts.hardboiled_replay import egglog_forms
    from scripts.reproduction_process import exclusive_job

    previous = durable / "eggcc-bitwise-stage-boundary-0001/intent.json"
    previous_bytes = previous.read_bytes()
    assert hashlib.sha256(previous_bytes).hexdigest() == INTENT_SHA256
    prior = json.loads(previous_bytes)
    receipt = Path(prior["capture"])
    receipt_bytes = receipt.read_bytes()
    assert hashlib.sha256(receipt_bytes).hexdigest() == CAPTURE_SHA256
    capture = json.loads(receipt_bytes)
    session = capture["sessions"][2]
    program = Path(session["replay"])
    original = program.read_bytes()
    assert hashlib.sha256(original).hexdigest() == REPLAY_SHA256 == session["replay_sha256"].removeprefix("sha256:")
    assert session["roots"][2]["name"] == "loop_subroutine"
    engine = root / "target/release/egglog-experimental"
    files = {
        "engine": engine,
        "script": Path(__file__).resolve(),
        "parser": root / "scripts/hardboiled_replay.py",
        "runner": root / "benchmarking/pilot.py",
        "guard": root / "benchmarking/memory_guard.py",
        "lock": root / "scripts/reproduction_process.py",
    }
    identities = {}
    for name, path in files.items():
        with path.open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        identities[name] = {"path": str(path), "sha256": digest}
    assert identities["engine"]["sha256"] == ENGINE_SHA256 == capture["replay_engine_sha256"].removeprefix("sha256:")
    adapted, assertions = reorder_check(original.decode(), egglog_forms)
    with exclusive_job(root / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        output.mkdir(parents=True, exist_ok=False)
        (output / "original.egg").write_bytes(original)
        variant = output / "reordered.egg"
        variant.write_bytes(adapted.encode())
        (output / "source-capture.json").write_bytes(receipt_bytes)
        (output / "previous-diagnostic-intent.json").write_bytes(previous_bytes)
        (output / "runner-source.py").write_bytes(files["script"].read_bytes())
        command = [
            "/usr/bin/env",
            "RUST_LOG=egglog=info",
            str(engine),
            "-j",
            "1",
            str(variant),
        ]
        intent = {
            "meaning": "One query-order diagnostic; not corpus admission or a performance observation",
            "source_capture": str(receipt),
            "source_capture_sha256": CAPTURE_SHA256,
            "source_replay": str(program),
            "original_sha256": REPLAY_SHA256,
            "adapted_sha256": hashlib.sha256(adapted.encode()).hexdigest(),
            "identities": identities,
            "assertions": assertions,
            "command": command,
            "timeout_sec": 60,
            "memory_limit_bytes": 5 * 1024**3,
            "disk_reserve_bytes": 10 * 1024**3,
            "require_guard": True,
            "allow_warning_pressure": True,
            "admitted": False,
        }
        (output / "intent.json").write_text(json.dumps(intent, indent=2) + "\n")
        try:
            process = run_bounded_command(
                command,
                root,
                output / "process",
                timeout_sec=60,
                memory_limit_bytes=5 * 1024**3,
                require_guard=True,
                disk_reserve_bytes=10 * 1024**3,
                allow_warning_pressure=True,
            )
        except (OSError, ValueError, RuntimeError) as error:
            (output / "result.json").write_text(
                json.dumps({"status": "launch-refused", "reason": str(error), "admitted": False}, indent=2) + "\n"
            )
            return 2
        (output / "result.json").write_text(json.dumps(asdict(process), indent=2, default=str) + "\n")
        with process.stderr_path.open() as stream:
            completed_checks = sum(line.startswith("[INFO ] Checked fact ") for line in stream)
        passed = process.status == "success" and process.returncode == 0 and completed_checks == 6
        interpretation = {
            "status": "all-six-checks-completed" if passed else "diagnostic-did-not-complete-all-checks",
            "process_status": process.status,
            "completed_checks": completed_checks,
            "required_completed_checks": 6,
            "admitted": False,
            "reason": (
                "Even success requires reviewed adapter changes and normal complete-parent validation before admission"
            ),
        }
        (output / "interpretation.json").write_text(json.dumps(interpretation, indent=2) + "\n")
        print(json.dumps(interpretation))
        return 0 if passed else 2 if process.status in {"timed-out", "memory-limit", "resource-stopped"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
