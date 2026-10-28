#!/usr/bin/env python3
"""Check proofs of equivalent probes from the existing toy and Array fuzzers."""

import argparse
import json
import os
import random
import re
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from slotted import reference  # noqa: E402
from slotted import test_program as driver  # noqa: E402
from slotted.xdiff import xarray, xdiff  # noqa: E402


def source_program(case, language):
    rules = (
        [r.source() for r in case.rules]
        if language == "array"
        else [xdiff.source_rule(atoms, action, conds) for atoms, action, conds in case.rules if atoms]
    )
    return driver.source_program(language, case.lang, rules, case.terms, case.unions, case.probes, case.rounds * 3)


def proof_queries(case, partition):
    groups = re.findall(r"\[[\d,]+\]", partition.split(" missing", 1)[0])
    pairs = [(group[0], index) for group in (json.loads(group) for group in groups) for index in group]
    assert sorted(right for _, right in pairs) == list(range(len(case.probes)))
    terms = [driver.term(case.lang, term) if term[0] == "var" else f"_p{i}" for i, term in enumerate(case.probes)]
    return [f"(check (renaming-= {terms[left]} {terms[right]}))" for left, right in pairs]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("count", nargs="?", type=int, default=100)
    parser.add_argument("seed", nargs="?", type=int, default=0)
    parser.add_argument("--language", choices=("toy", "array"), default="toy")
    parser.add_argument("--no-aliasing", action="store_true")
    parser.add_argument("--timeout", type=float, default=60)
    parser.add_argument("--failures", type=Path)
    args = parser.parse_args()
    if args.count <= 0:
        parser.error("count must be positive")
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    if args.no_aliasing and args.language != "array":
        parser.error("--no-aliasing requires --language array; toy rules use multipatterns")
    generator = xarray if args.language == "array" else xdiff
    rng = random.Random(args.seed)
    if args.failures:
        args.failures.mkdir(parents=True, exist_ok=True)
    mode = "no-aliasing" if args.no_aliasing else "aliasing"
    failures = Path(tempfile.mkdtemp(prefix=f"proof-fuzz-{args.language}-{args.seed}-{mode}-", dir=args.failures))

    def keep(name, source, reason, stdout="", *, proofs=True):
        saved = failures / f"{name}.egg"
        saved.write_text(source)
        command = [
            str(driver.EGGLOG),
            "--slotted",
            *(["--proofs"] if proofs else []),
            *(["--slotted-no-aliasing"] if args.no_aliasing else []),
            str(saved),
        ]
        replay = f"cd {shlex.quote(str(ROOT))} && {shlex.join(command)}"
        saved.with_suffix(".log").write_text(f"{replay}\n\n{reason}")
        saved.with_suffix(".proof.txt").write_text(stdout)

    passed = failed = limited = claims = with_rules = 0
    with tempfile.TemporaryDirectory(prefix="slotted-proof-fuzz-") as tmp:
        path = Path(tmp) / "case.egg"
        output = Path(tmp) / "proof.txt"
        for index in range(args.count):
            case = generator.rand_case(rng, index)
            source = source_program(case, args.language)
            encoded = driver.compile_source(source, no_aliasing=args.no_aliasing)
            status, partition = driver.run_encoding(
                encoded + driver.probe_observer(case.lang, case.probes), len(case.probes), args.timeout
            )
            if status == "TIMEOUT":
                limited += 1
                keep(case.name, source, partition, proofs=False)
                print(f"LIMIT {case.name}: ordinary run timed out ({partition})", flush=True)
                continue
            if status != "OK":
                failed += 1
                keep(case.name, source, partition, proofs=False)
                print(f"FAIL {case.name}: ordinary run: {partition}", flush=True)
                continue
            queries = proof_queries(case, partition)
            source += "\n".join(queries) + "\n"
            path.write_text(source)
            with output.open("w") as proof:
                try:
                    result = subprocess.run(
                        [
                            str(driver.EGGLOG),
                            "--slotted",
                            "--proofs",
                            *(["--slotted-no-aliasing"] if args.no_aliasing else []),
                            str(path),
                        ],
                        cwd=ROOT,
                        stdout=proof,
                        stderr=subprocess.PIPE,
                        text=True,
                        env={**os.environ, "RUST_LOG": "error"},
                        timeout=args.timeout,
                    )
                except subprocess.TimeoutExpired:
                    limited += 1
                    keep(case.name, source, f"proof run exceeded {args.timeout}s", output.read_text())
                    print(f"LIMIT {case.name}: proof run timed out", flush=True)
                    continue
            text = output.read_text()
            failure = f"exit {result.returncode}: {result.stderr}" if result.returncode else None
            if failure is None:
                try:
                    proofs = [
                        form for form in reference.parse(text) if not isinstance(form, list) or form[:1] != ["let"]
                    ]
                    if len(proofs) != len(queries):
                        failure = f"{len(proofs)} proofs for {len(queries)} claims"
                except (ValueError, IndexError, RecursionError) as error:
                    failure = f"invalid proof output: {error}"
            if failure is not None:
                failed += 1
                keep(case.name, source, failure, text)
                print(f"FAIL {case.name}: {' '.join(failure.splitlines()[:2])}", flush=True)
                continue
            passed += 1
            claims += len(proofs)
            with_rules += bool(re.search(r"\(Rule\b", text))
            if (index + 1) % 10 == 0:
                print(f"{index + 1}/{args.count} generated cases run", flush=True)
    print(f"{passed}/{passed + failed} proof cases checked; {limited} timed out; {args.count} generated")
    print(f"{claims} checked claims; {with_rules} cases used rewrite steps")
    if failed or limited:
        print(f"Reproductions: {failures}")
    else:
        failures.rmdir()
    return int(failed != 0 or passed == 0)


if __name__ == "__main__":
    sys.exit(main())
