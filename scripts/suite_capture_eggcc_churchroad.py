#!/usr/bin/env python3
"""Capture pinned Eggcc pass-one and Churchroad mapping-phase invocations.

This deliberately does not update the catalog or run correctness admission.
Every attempt gets a new evidence directory, including unsuccessful attempts.
Run with ``uv run python -m scripts.suite_capture_eggcc_churchroad FAMILY``.
Captures and logs live below STORAGE; compiler outputs remain disposable below BUILD.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import io
import json
import re
import shutil
import sys
import tarfile
import time
import urllib.request
from dataclasses import asdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from benchmarking.pilot import run_bounded_command  # noqa: E402
from scripts.paper_benchmarks.materialize import (  # noqa: E402
    CHURCHROAD_MAIN_SHA256,
    CHURCHROAD_PLUGIN_SHA256,
    CHURCHROAD_PRELUDE_SHA256,
    churchroad_mapping_program,
    constructors,
    read_verified,
)

STORAGE = ROOT / "benchmarks/local"
BUILD = ROOT / "target/benchmark-acquisition"
PINS = {
    "eggcc": "16be0063133ef0b8ba21cd75ee377002dc3ecbed",
    "churchroad": "9f82ca23b273a5a500cc6a1ca60b30d3c33c5721",
}
EGGCC_HELPERS = {
    "TypeList-length",
    "ListExpr-length",
    "tuple-length",
    "Length-List<i64+IntInterval>",
    "Length-List<PtrPointees>",
    "succ",
}
EGGCC_QUERY = '(check (Function "main" in out body) (HasType body out))'
EGGCC_CAPTURE_PATCH = """                // Capture this pass boundary before frontend desugaring. The one-pass
                // export path constructs exactly one invocation. Never overwrite a capture.
                if let Some(directory) = std::env::var_os("EGGCC_CAPTURE_DIR") {
                    use std::io::Write;
                    let destination = std::path::Path::new(&directory).join("invocation-000.egg");
                    let mut output = std::fs::OpenOptions::new()
                        .create_new(true).write(true).open(destination).unwrap();
                    output.write_all(egglog.as_bytes()).unwrap();
                }
"""
YOSYS_EXTRA_OBJECTS = [
    "techlibs/common/prep.o",
    "passes/cmds/check.o",
    "passes/cmds/future.o",
    "passes/memory/memory_collect.o",
    "passes/opt/wreduce.o",
    "passes/cmds/splice.o",
    "passes/cmds/splitnets.o",
]


def prepare_compiler(family: str, destination: Path) -> None:
    """Acquire exact source archives and perform small serial native builds.

    Changes are confined to isolated ignored sources: exporter instrumentation,
    workspace isolation, and a reduced Yosys build containing the required passes.
    Full source digests, build-only patches, and bounded process logs are retained.
    """
    if shutil.disk_usage(STORAGE).free < 2 * 1024**3:
        raise RuntimeError("compiler preparation needs at least 2 GiB of free disk")
    repositories = (
        [("eggcc", "egraphs-good/eggcc", PINS["eggcc"])]
        if family == "eggcc"
        else [
            ("churchroad", "gussmith23/churchroad", PINS["churchroad"]),
            ("yosys", "YosysHQ/yosys", "f8d4d7128cf72456cc03b0738a8651ac5dbe52e1"),
        ]
    )
    for name, repository, revision in repositories:
        url = f"https://codeload.github.com/{repository}/tar.gz/{revision}"
        with urllib.request.urlopen(url, timeout=60) as response:
            archive = response.read(64 * 1024**2 + 1)
        if len(archive) > 64 * 1024**2:
            raise ValueError(f"unexpectedly large source archive: {name}")
        source = STORAGE / "sources" / name
        manifest: dict[str, Any] = {"url": url, "archive_sha256": hashlib.sha256(archive).hexdigest(), "files": {}}
        patch = ""
        with tarfile.open(fileobj=io.BytesIO(archive)) as tree:
            for member in tree.getmembers():
                if not member.isfile():
                    continue
                relative = Path(*Path(member.name).parts[1:])
                if relative.is_absolute() or ".." in relative.parts:
                    raise ValueError("unexpected archive member path")
                stream = tree.extractfile(member)
                assert stream is not None
                original = stream.read()
                payload = original
                manifest["files"][relative.as_posix()] = hashlib.sha256(original).hexdigest()
                if name == "eggcc" and relative == Path("Cargo.toml"):
                    payload += b"\n[workspace]\n"
                elif name == "eggcc" and relative == Path("src/util.rs"):
                    needle = (
                        "                let mut egraph = egglog::new_experimental_egraph();\n"
                        "                let resolved = egraph"
                    )
                    text = original.decode()
                    if text.count(needle) != 1:
                        raise ValueError("pinned Eggcc export boundary changed")
                    payload = text.replace(needle, EGGCC_CAPTURE_PATCH + needle).encode()
                elif name == "yosys" and relative == Path("Makefile"):
                    payload += (
                        "\n# Acquisition frontend only; no optimization or debug symbols.\n"
                        "CXXFLAGS += -g0 -O0\nOBJS += " + " ".join(YOSYS_EXTRA_OBJECTS) + "\n"
                    ).encode()
                if payload != original:
                    patch += "".join(
                        difflib.unified_diff(
                            original.decode().splitlines(True),
                            payload.decode().splitlines(True),
                            fromfile=f"a/{relative}",
                            tofile=f"b/{relative}",
                        )
                    )
                output = source / relative
                output.parent.mkdir(parents=True, exist_ok=True)
                if not output.exists() or output.read_bytes() != payload:
                    output.write_bytes(payload)
                    output.chmod(member.mode)
        (destination / f"{name}-source.json").write_text(json.dumps(manifest, indent=2) + "\n")
        (destination / f"{name}-build.patch").write_text(patch)
    if family == "eggcc":
        commands = [
            [
                "env",
                "LLVM_SYS_180_PREFIX=/opt/homebrew/opt/llvm@18",
                "LIBRARY_PATH=/opt/homebrew/lib",
                f"CARGO_TARGET_DIR={BUILD / 'eggcc'}",
                "CARGO_PROFILE_DEV_DEBUG=0",
                "CARGO_INCREMENTAL=0",
                "RUSTC_WRAPPER=",
                "cargo",
                "+1.88.0",
                "build",
                "--locked",
                "-j1",
                "--bin",
                "eggcc",
            ]
        ]
        directories = [STORAGE / "sources/eggcc"]
    else:
        for name in ("yosys", "churchroad"):
            shutil.copytree(STORAGE / "sources" / name, BUILD / name, dirs_exist_ok=True)
        commands = [
            [
                "make",
                "-j1",
                "SMALL=1",
                "ENABLE_ABC=0",
                "ENABLE_TCL=0",
                "ENABLE_READLINE=0",
                "ENABLE_ZLIB=0",
                *YOSYS_EXTRA_OBJECTS,
                "yosys",
                "yosys-config",
            ],
            [
                "clang++",
                "-std=c++17",
                "-g0",
                "-O0",
                "-fPIC",
                "-D_YOSYS_",
                f"-I{BUILD / 'yosys'}",
                "-shared",
                "-undefined",
                "dynamic_lookup",
                "-o",
                str(BUILD / "churchroad/yosys-plugin/churchroad.so"),
                str(BUILD / "churchroad/yosys-plugin/churchroad.cc"),
            ],
        ]
        directories = [BUILD / "yosys", BUILD / "churchroad"]
    for index, (command, directory) in enumerate(zip(commands, directories, strict=True)):
        result = run_bounded_command(command, directory, destination / f"build-{index}", timeout_sec=600)
        (destination / f"build-{index}.json").write_text(
            json.dumps({"command": command, **asdict(result)}, default=str, indent=2) + "\n"
        )
        if result.status != "success":
            raise RuntimeError(f"{family} build failed; see {result.stderr_path}")


def adapt_eggcc(source: str) -> str:
    """Apply the checked-in pass-one fixture's compatibility changes exactly.

    The unused ExprSet block must have no references outside its contiguous
    declaration block. Only the six deterministic length/successor functions
    may replace no-merge with merge-old. Keep every schedule command intact.
    """
    start = source.index("(sort ExprSetPrim (Set Expr))")
    end = source.index("(datatype Pointees ", start)
    source = source[:start] + source[end:]
    if re.search(r"\bExprSet\b|\bExprSetPrim\b|\(ES[\s)]", source):
        raise ValueError("ExprSet is referenced outside its unused helper block")
    found = set(re.findall(r"^\(function (\S+) .*:no-merge\)$", source, re.MULTILINE))
    if found != EGGCC_HELPERS:
        raise ValueError(f"unexpected no-merge helper set: {sorted(found)}")
    source = source.replace(":no-merge", ":merge old")
    # Main-body typing is inferred by the original type-analysis schedule.
    # FunctionHasType alone would merely recheck an asserted initialization fact.
    main_facts = [line.strip() for line in source.splitlines() if line.strip().startswith('(FunctionHasType "main" ')]
    if len(main_facts) != 1 or not main_facts[0].endswith(")"):
        raise ValueError("expected exactly one main FunctionHasType seed")
    return (
        "; Captured Eggcc pass-one invocation; original commands retained in acquisition evidence.\n"
        f"; Pinned compiler: {PINS['eggcc']}\n"
        "; Adaptations match eggcc-2mm-pass1: omit unreferenced ExprSet helpers;\n"
        "; deterministic length/succ no-merge functions use merge-old.\n"
        "; Oracle: the main function body's inferred result type agrees with the declared result type.\n"
        + source.rstrip()
        + "\n\n"
        + EGGCC_QUERY
        + "\n"
    )


def capture_eggcc(cases: list[dict], destination: Path, prior_capture: Path | None) -> list[dict]:
    """Export every declared source independently and retain complete outcomes."""
    checkout = STORAGE / "sources/eggcc"
    binary = BUILD / "eggcc/debug/eggcc"
    if not binary.is_file():
        raise FileNotFoundError(f"build the pinned instrumented Eggcc exporter first: {binary}")
    binary_sha256 = hashlib.sha256(binary.read_bytes()).hexdigest()
    engine = ROOT / "target/release/egglog-experimental"
    engine_sha256 = hashlib.sha256(engine.read_bytes()).hexdigest()
    prior = {} if prior_capture is None else {row["id"]: row for row in json.loads(prior_capture.read_text())}
    records = []
    for case in cases:
        attempt = destination / case["id"]
        attempt.mkdir()
        command = [
            "env",
            f"EGGCC_CAPTURE_DIR={attempt}",
            str(binary),
            "--run-mode",
            "egglog",
            "--stop-after-n-passes",
            "1",
            str(checkout / case["source"]),
        ]
        if prior_capture is None:
            result = run_bounded_command(command, checkout, attempt / "export")
            process = asdict(result)
        else:
            earlier = prior[case["id"]]
            for relative in earlier["raw_invocations"]:
                original = ROOT / relative
                (attempt / original.name).write_bytes(original.read_bytes())
            process = earlier["process"]
            command = earlier["command"]
        record = {
            "id": case["id"],
            "revision": PINS["eggcc"],
            "command": command,
            "binary_sha256": binary_sha256 if prior_capture is None else prior[case["id"]]["binary_sha256"],
            "source_sha256": hashlib.sha256((checkout / case["source"]).read_bytes()).hexdigest(),
            "process": process,
            "status": "blocked",
            "workloads": [],
            "capture_boundary": "build_program before desugaring, pass one",
            "oracle": EGGCC_QUERY,
            "replay_engine_sha256": engine_sha256,
        }
        invocations = sorted(attempt.glob("invocation-*.egg"))
        record["raw_invocations"] = [str(path.relative_to(ROOT)) for path in invocations]
        if prior_capture is not None:
            record["reused_capture"] = str(prior_capture.relative_to(ROOT))
        if process["status"] == "success" and len(invocations) == 1:
            try:
                content = adapt_eggcc(invocations[0].read_text())
                replay = attempt / "replay-000.egg"
                replay.write_text(content)
                negative = attempt / "initialization-only.egg"
                if content.count("(run-schedule") != 1 or "(run initialization 1)" not in content:
                    raise ValueError("unexpected pass-one schedule boundary")
                negative.write_text(content.split("(run-schedule", 1)[0] + EGGCC_QUERY + "\n")
                before = run_bounded_command([str(engine), str(negative)], ROOT, attempt / "oracle-initialization")
                after = run_bounded_command([str(engine), str(replay)], ROOT, attempt / "oracle-scheduled")
                record["oracle_controls"] = {"initialization_only": asdict(before), "original_schedule": asdict(after)}
                record["workloads"] = [str(replay.relative_to(ROOT))]
                if (
                    before.status == "failure"
                    and "Check failed" in (before.message or "")
                    and after.status == "success"
                ):
                    record["status"] = "captured"
                    stable = STORAGE / "workloads/eggcc/expanded" / f"{case['id']}-pass1.egg"
                    stable.parent.mkdir(parents=True, exist_ok=True)
                    stable.write_text(content)
                    record["replay_capture"] = str(replay.relative_to(ROOT))
                    record["workloads"] = [str(stable.relative_to(ROOT))]
                else:
                    record["reason"] = (
                        "derived-result oracle requires failed initialization-only and successful scheduled checks"
                    )
            except ValueError as error:
                record["reason"] = f"capture adaptation failed: {error}"
        else:
            record["reason"] = process["message"] or f"expected one invocation, captured {len(invocations)}"
        (attempt / "capture.json").write_text(json.dumps(record, default=str, indent=2) + "\n")
        records.append(record)
        print(f"{case['id']}: {record['status']}", flush=True)
    return records


def rename_churchroad_globals(source: str, query: str, rules: str) -> tuple[str, str, dict[str, str]]:
    """Give frontend aliases fresh base names without changing literal circuit names.

    Egglog's shadowing check compares a global's base name with rule variables,
    so merely adding ``$`` does not isolate ports named ``a`` or ``b``. This
    token substitution applies only to the frontend actions and appended query;
    the original rules and both schedules remain unchanged.
    """
    tokens = re.compile(r';[^\n]*|"(?:\\.|[^"\\])*"|[^\s();"]+')
    names = re.findall(r"^\(let ([^\s()]+)", source, re.MULTILINE)
    aliases = {name: f"$churchroad-global-{name}" for name in names}
    occupied = {token.lstrip("$") for token in tokens.findall(source + query + rules)}
    if any(alias.lstrip("$") in occupied for alias in aliases.values()):
        raise ValueError("Churchroad global alias prefix collides with an existing atom")
    return (
        tokens.sub(lambda match: aliases.get(match[0], match[0]), source),
        tokens.sub(lambda match: aliases.get(match[0], match[0]), query),
        aliases,
    )


def capture_churchroad(cases: list[dict], destination: Path) -> list[dict]:
    """Capture both Verilog frontends and the driver's original mapping phase.

    The mapping phase excludes external synthesis results. Module-enumeration
    rules require a Rust primitive, but the mapping schedule never runs them.
    These omissions are phase boundaries, never reported as full-driver capture.
    """
    checkout = STORAGE / "sources/churchroad"
    yosys = BUILD / "yosys/yosys"
    plugin = BUILD / "churchroad/yosys-plugin/churchroad.so"
    original_prelude = read_verified(checkout / "egglog_src/churchroad.egg", CHURCHROAD_PRELUDE_SHA256)
    prelude = constructors(original_prelude)
    main_source = read_verified(checkout / "src/main.rs", CHURCHROAD_MAIN_SHA256)
    read_verified(checkout / "yosys-plugin/churchroad.cc", CHURCHROAD_PLUGIN_SHA256)
    mapping = churchroad_mapping_program(main_source)
    schedule = "(run-schedule (saturate (seq typing transform mapping)))"
    if schedule not in main_source:
        raise ValueError("the pinned driver mapping schedule changed")
    records = []
    for case in cases:
        attempt = destination / case["id"]
        attempt.mkdir()
        source = checkout / case["source"]
        program = f'read_verilog -sv "{source}"; hierarchy -simcheck -top mul; prep; write_churchroad -letbindings'
        command = [str(yosys), "-m", str(plugin), "-q", "-p", program]
        result = run_bounded_command(command, checkout, attempt / "frontend")
        record = {
            "id": case["id"],
            "revision": PINS["churchroad"],
            "command": command,
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "process": asdict(result),
            "status": "blocked",
            "workloads": [],
            "capture_boundary": "original mapping phase through saturating schedule",
            "engine_sessions": 1,
            "raw_call_semantics": "ordered calls into one persistent EGraph; fragments are not independent workloads",
            "external_phases": {
                "lakeroad": "not captured: later driver synthesis and returned Egglog commands require LAKEROAD_DIR",
                "module_enumeration": (
                    "not active in mapping schedule; imported rules require Rust debruijnify primitive"
                ),
                "simulation": "not captured: external Verilator and proprietary architecture simulation models",
            },
        }
        if result.status == "success":
            generated = result.stdout_path.read_text()
            (attempt / "invocation-000-prelude.egg").write_text(original_prelude)
            (attempt / "invocation-001-module-enumeration.egg").write_text(
                (checkout / "egglog_src/module_enumeration_rewrites.egg").read_text()
            )
            (attempt / "invocation-002-design.egg").write_text(generated)
            (attempt / "invocation-003-mapping-rules.egg").write_text(mapping + "\n")
            (attempt / "invocation-004-mapping-schedule.egg").write_text(schedule + "\n")
            expected = (
                "(check (= v2 (PrimitiveInterfaceDSP v0 v1)))"
                if case["id"] == "churchroad-simple_mul"
                else "(check (= (Op2 (Mul) (Op1 (ZeroExtend 32) v0) "
                "(Op1 (ZeroExtend 32) (Op1 (Extract 15 0) v1))) "
                "(PrimitiveInterfaceDSP v0 (Op1 (Extract 15 0) v1))))"
            )
            generated, expected, aliases = rename_churchroad_globals(generated, expected, prelude + mapping)
            replay = attempt / "mapping-phase.egg"
            replay.write_text(
                "; Churchroad mapping-phase prefix: original saturating schedule preserved.\n"
                "; External Lakeroad synthesis/returned commands and simulation are not captured.\n"
                "; Unscheduled module enumeration requires Rust debruijnify and is outside this phase.\n"
                "; Adaptations: current constructors, hygienic global aliases, "
                "deterministic wire salt, mapping oracle.\n"
                + prelude
                + "\n\n"
                + generated
                + "\n"
                + mapping
                + "\n"
                + schedule
                + "\n"
                + expected
                + "\n"
            )
            stable = STORAGE / "workloads/churchroad/expanded" / f"{case['id']}-mapping-phase.egg"
            stable.parent.mkdir(parents=True, exist_ok=True)
            stable.write_bytes(replay.read_bytes())
            record.update(
                status="phase-prefix",
                workloads=[str(stable.relative_to(ROOT))],
                replay_capture=str(replay.relative_to(ROOT)),
                replay_sha256=hashlib.sha256(replay.read_bytes()).hexdigest(),
                global_aliases=aliases,
                reason="Mapping phase captured; full driver remains blocked on external Lakeroad synthesis.",
                raw_invocations=[str(path.relative_to(ROOT)) for path in sorted(attempt.glob("invocation-*.egg"))],
            )
        else:
            record["reason"] = result.message
        (attempt / "capture.json").write_text(json.dumps(record, default=str, indent=2) + "\n")
        records.append(record)
        print(f"{case['id']}: {record['status']}", flush=True)
    return records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("family", choices=tuple(PINS))
    parser.add_argument(
        "--prepare", action="store_true", help="acquire pinned sources and build isolated compilers first"
    )
    parser.add_argument("--prepare-only", action="store_true", help="prepare compilers without capturing inputs")
    parser.add_argument(
        "--from-capture", type=Path, help="reuse retained raw Eggcc exports and revalidate replay oracles"
    )
    args = parser.parse_args()
    cases = [
        case
        for case in json.loads((ROOT / "benchmarks/catalog.json").read_text())["cases"]
        if case["family"] == args.family
    ]
    destination = STORAGE / "evidence" / args.family / f"capture-{time.time_ns()}"
    destination.mkdir(parents=True)
    if args.prepare or args.prepare_only:
        prepare_compiler(args.family, destination)
    if args.prepare_only:
        print(destination.relative_to(ROOT))
        return
    records = (
        capture_eggcc(cases, destination, None if args.from_capture is None else args.from_capture.resolve())
        if args.family == "eggcc"
        else capture_churchroad(cases, destination)
    )
    output = destination / "results.json"
    output.write_text(json.dumps(records, default=str, indent=2) + "\n")
    (STORAGE / "evidence" / args.family / "latest-capture.json").write_text(
        json.dumps({"results": str(output.relative_to(ROOT))}, indent=2) + "\n"
    )
    print(output.relative_to(ROOT))


if __name__ == "__main__":
    main()
