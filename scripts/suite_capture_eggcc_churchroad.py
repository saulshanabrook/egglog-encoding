#!/usr/bin/env python3
"""Capture pinned Eggcc and Churchroad invocations and complete optimizations.

This never updates the catalog or performance cache. Complete mode validates
ordinary native-output checks; prefix mode retains its historical phase boundary.
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
import os
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
from benchmarking.targets import sha256_file  # noqa: E402
from scripts.eggcc_churchroad_complete import (  # noqa: E402
    CaptureError,
    CaptureResourceError,
    churchroad_mapping_session,
    churchroad_sessions,
    eggcc_sessions,
    patched_churchroad_sources,
    patched_eggcc_sources,
    read_events,
    write_native_patch,
)
from scripts.hardboiled_replay import egglog_forms  # noqa: E402
from scripts.paper_benchmarks.materialize import (  # noqa: E402
    CHURCHROAD_MAIN_SHA256,
    CHURCHROAD_PLUGIN_SHA256,
    CHURCHROAD_PRELUDE_SHA256,
    churchroad_mapping_program,
    constructors,
    read_verified,
)
from scripts.reproduction_validation import (  # noqa: E402
    CHURCHROAD_PLACEHOLDERS,
    churchroad_circuit_contract,
    native_check_contract,
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
# Pinned memory.egg's first ten forms, excluding comments/whitespace only.
EGGCC_EXPR_SET_TOKENS_SHA256 = "992434eb3686e88fcd37cbe063c331f02150714343e3421ed36b550d8aac4eb8"
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


def prepare_compiler(family: str, destination: Path, *, complete: bool = False) -> None:
    """Acquire exact source archives and perform small serial native builds.

    Changes are confined to isolated ignored sources: exporter instrumentation,
    workspace isolation, and a reduced Yosys build containing the required passes.
    Full source digests, build-only patches, and bounded process logs are retained.
    """
    reserve_bytes = (10 if complete else 2) * 1024**3
    if shutil.disk_usage(STORAGE).free < reserve_bytes:
        raise RuntimeError(f"compiler preparation needs a {reserve_bytes // 1024**3} GiB free-disk reserve")
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
        if complete:
            (destination / f"{name}-{revision}.tar.gz").write_bytes(archive)
        source = BUILD / f"{name}-complete-source" if complete else STORAGE / "sources" / name
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
                elif name == "eggcc" and relative == Path("src/util.rs") and not complete:
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
    if complete:
        checkout = BUILD / f"{family}-complete-source"
        patched = patched_eggcc_sources(checkout) if family == "eggcc" else patched_churchroad_sources(checkout)
        write_native_patch(checkout, patched, destination / f"{family}-native-capture.patch")
        for patched_relative, content in patched.items():
            (checkout / patched_relative).write_text(content)
    if family == "eggcc":
        commands = [
            [
                "env",
                "LLVM_SYS_180_PREFIX=/opt/homebrew/opt/llvm@18",
                "LIBRARY_PATH=/opt/homebrew/lib",
                f"CARGO_TARGET_DIR={BUILD / ('eggcc-complete' if complete else 'eggcc')}",
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
        directories = [BUILD / "eggcc-complete-source" if complete else STORAGE / "sources/eggcc"]
    else:
        if not complete:
            for name in ("yosys", "churchroad"):
                shutil.copytree(STORAGE / "sources" / name, BUILD / name, dirs_exist_ok=True)
        yosys_build = BUILD / ("yosys-complete-source" if complete else "yosys")
        churchroad_build = BUILD / ("churchroad-complete-source" if complete else "churchroad")
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
                f"-I{yosys_build}",
                "-shared",
                "-undefined",
                "dynamic_lookup",
                "-o",
                str(churchroad_build / "yosys-plugin/churchroad.so"),
                str(churchroad_build / "yosys-plugin/churchroad.cc"),
            ],
        ]
        directories = [yosys_build, churchroad_build]
        if complete:
            commands.append(
                [
                    "env",
                    f"CARGO_TARGET_DIR={BUILD / 'churchroad-complete'}",
                    "CARGO_PROFILE_DEV_DEBUG=0",
                    "CARGO_INCREMENTAL=0",
                    "RUSTC_WRAPPER=",
                    "cargo",
                    "+1.88.0",
                    "build",
                    "-j1",
                    "--bin",
                    "churchroad",
                ]
            )
            directories.append(churchroad_build)
    for index, (command, directory) in enumerate(zip(commands, directories, strict=True)):
        result = run_bounded_command(
            command,
            directory,
            destination / f"build-{index}",
            timeout_sec=600,
            require_guard=complete,
            disk_reserve_bytes=10 * 1024**3 if complete else 0,
            allow_warning_pressure=complete,
        )
        (destination / f"build-{index}.json").write_text(
            json.dumps({"command": command, **asdict(result)}, default=str, indent=2) + "\n"
        )
        if result.status != "success":
            raise RuntimeError(f"{family} build failed; see {result.stderr_path}")
    if complete:
        checkout = BUILD / f"{family}-complete-source"
        lock = checkout / "Cargo.lock"
        if lock.is_file():
            shutil.copyfile(lock, destination / f"{family}-Cargo.lock")
        executable = BUILD / f"{family}-complete/debug/{family}"
        (destination / "complete-preparation.json").write_text(
            json.dumps(
                {
                    "family": family,
                    "revision": PINS[family],
                    "checkout": str(checkout),
                    "binary": str(executable),
                    "binary_sha256": sha256_file(executable),
                    "native_patch_sha256": sha256_file(destination / f"{family}-native-capture.patch"),
                    "lockfile_sha256": sha256_file(lock) if lock.is_file() else None,
                    "commands": commands,
                },
                indent=2,
            )
            + "\n"
        )


def adapt_eggcc(source: str, *, typing_oracle: bool = True) -> str:
    """Apply the checked-in pass-one fixture's compatibility changes exactly.

    The unused ExprSet block must have no references outside its contiguous
    declaration block. Only the six deterministic length/successor functions
    may replace no-merge with merge-old. Keep every schedule command intact.
    """
    forms = egglog_forms(source)
    starts = [i for i, (_, _, tokens) in enumerate(forms) if tokens[1:3] == ["sort", "ExprSetPrim"]]
    ends = [i for i, (_, _, tokens) in enumerate(forms) if tokens[1:3] == ["datatype", "Pointees"]]
    if len(starts) != 1 or len(ends) != 1 or ends[0] - starts[0] != 10:
        raise ValueError("expected exactly the pinned ten-form ExprSet helper block before Pointees")
    start, end = starts[0], ends[0]
    block = [tokens for _, _, tokens in forms[start:end]]
    if hashlib.sha256(json.dumps(block, separators=(",", ":")).encode()).hexdigest() != EGGCC_EXPR_SET_TOKENS_SHA256:
        raise ValueError("ExprSet helper block differs from the pinned compiler")
    if any(
        token in {"ExprSet", "ExprSetPrim", "ES"} or token.startswith("ExprSet-")
        for _, _, tokens in forms[:start] + forms[end:]
        for token in tokens
    ):
        raise ValueError("ExprSet is referenced outside its unused helper block")
    source = source[: forms[start][0]] + source[forms[end][0] :]
    found = set(re.findall(r"^\(function (\S+) .*:no-merge\)$", source, re.MULTILINE))
    if found != EGGCC_HELPERS:
        raise ValueError(f"unexpected no-merge helper set: {sorted(found)}")
    source = source.replace(":no-merge", ":merge old")
    # Main-body typing is inferred by the original type-analysis schedule.
    # FunctionHasType alone would merely recheck an asserted initialization fact.
    if typing_oracle:
        main_facts = [
            line.strip() for line in source.splitlines() if line.strip().startswith('(FunctionHasType "main" ')
        ]
        if len(main_facts) != 1 or not main_facts[0].endswith(")"):
            raise ValueError("expected exactly one main FunctionHasType seed")
    else:
        return (
            "; Complete native Eggcc optimization invocation; raw commands retained separately.\n"
            "; Compatibility: unused ExprSet helpers omitted; deterministic helpers use merge-old.\n"
            + source.rstrip()
            + "\n"
        )
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


def rename_churchroad_globals(
    source: str, query: str, rules: str, *, aliases: dict[str, str] | None = None
) -> tuple[str, str, dict[str, str]]:
    """Preserve paper-era global references at each command's declaration time.

    The native engine resolves bare names to previously declared globals, even
    inside later rules. Carry aliases between source parts, but leave earlier
    rule locals alone. Fresh base names avoid current global-shadowing errors.
    """
    tokens = re.compile(r';[^\n]*|"(?:\\.|[^"\\])*"|[()]|[^\s();"]+')
    bindings = dict(aliases or {})
    occupied = {token.lstrip("$") for token in tokens.findall(source + query + rules)}
    translated = []
    for program in (source, query):
        edits = []
        for start, end, form in egglog_forms(program):
            kind = form[1]
            atoms = [m for m in tokens.finditer(program, start, end) if not m[0].startswith(";")]
            if kind in {"push", "pop", "include"} or any(
                atoms[i - 1][0] == "(" and atom[0] == "let" for i, atom in enumerate(atoms[2:], 2)
            ):
                raise CaptureError("Churchroad nested binding/scope needs a reviewed global adaptation")
            name = form[2] if kind == "let" else None
            if name is not None:
                alias = f"$churchroad-global-{name}"
                if name in bindings:
                    raise CaptureError("Churchroad global rebinding needs a reviewed adaptation")
                if alias.lstrip("$") in occupied:
                    raise ValueError("Churchroad global alias prefix collides with an existing atom")
                edits.append((atoms[2].start(), atoms[2].end(), alias))
            # Declaration names, sort names, schedule names and rule attributes
            # are not expression variables. The pinned source has no global
            # references in declaration defaults/merges or schedule conditions.
            if kind in {"sort", "datatype", "function", "constructor", "relation", "ruleset", "run", "run-schedule"}:
                if bindings and any(option in form for option in (":default", ":merge", ":until")):
                    raise CaptureError("Churchroad declaration/schedule expression needs a reviewed global adaptation")
            else:
                depth = 0
                attributes = False
                for i, atom in enumerate(atoms):
                    if atom[0] == "(":
                        depth += 1
                    elif atom[0] == ")":
                        depth -= 1
                    elif depth == 1 and atom[0].startswith(":"):
                        attributes = True
                    elif (
                        not attributes
                        and not (kind == "let" and i == 2)
                        and atoms[i - 1][0] != "("
                        and atom[0] in bindings
                    ):
                        edits.append((atom.start(), atom.end(), bindings[atom[0]]))
            if name is not None:
                bindings[name] = alias
        for start, end, replacement in sorted(edits, reverse=True):
            program = program[:start] + replacement + program[end:]
        translated.append(program)
    return translated[0], translated[1], bindings


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


RAYTRACE_CASE = "eggcc-raytrace--statewalk"
RAYTRACE_POLICY = "raytrace-384mib-v1"
RAYTRACE_EVIDENCE_BYTES = 384 * 1024**2
RESUME_PREDECESSOR_ADAPTER = "sha256:7a8593559c8042e16ce4037cacc542b7e78b1aac8effbdf88168dbce3d629a6e"


def materialize_sessions(record: dict[str, Any], sessions: list[dict[str, Any]], attempt: Path) -> None:
    """Preserve native session state while adapting syntax and binding observer checks."""
    family = record["family"]
    record["materialization"] = {
        "expected_sessions": len(sessions),
        "materialized_sessions": 0,
        "complete": False,
    }
    for index, session in enumerate(sessions):
        raw = attempt / f"session-{index:03}-{session['kind']}.raw.egg"
        raw.write_text(session["program"])
        if family == "eggcc":
            content = (
                adapt_eggcc(session.get("replay_program", session["program"]), typing_oracle=False)
                if session["kind"] == "optimization"
                else session["program"]
            )
            # Compatibility rewrites only the six original no-merge
            # helpers. Append strict observer functions afterwards.
            content += session.get("lookup_program", "")
        else:
            chunks = []
            check_positions = []
            command_count = 0
            aliases: dict[str, str] = {}
            for part in session["parts"]:
                program = constructors(part["program"])
                program, _, aliases = rename_churchroad_globals(program, "", session["program"], aliases=aliases)
                command_count += len(egglog_forms(program))
                for start, end, _ in egglog_forms(part["checks"]):
                    check_positions.append((command_count, part["checks"][start:end]))
                    command_count += 1
                chunks.append(program + "\n" + part["checks"])
            content = "\n".join(chunks)
            if session["kind"] == "circuit-extraction":
                # Visibility affects extraction only, not constructor insertion,
                # congruence, unions, rule matching or the native schedule.
                for _, end, tokens in reversed(egglog_forms(content)):
                    if tokens[1] == "constructor" and tokens[2] in CHURCHROAD_PLACEHOLDERS:
                        content = content[: end - 1] + " :unextractable" + content[end - 1 :]
        if "reproduction_" in session["program"].replace("; reproduction-", "; capture-"):
            raise CaptureError("native source collides with reserved reproduction query variables")
        replay = attempt / f"session-{index:03}-{session['kind']}.egg"
        if family == "eggcc":
            command_count = len(egglog_forms(content))
            check_positions = [
                (command_count + number, session["checks"][start:end])
                for number, (start, end, _) in enumerate(egglog_forms(session["checks"]))
            ]
            content += "\n" + session["checks"]
        replay.write_text(content)
        session_record = {
            key: value
            for key, value in session.items()
            if key not in {"program", "replay_program", "lookup_program", "checks", "parts"}
        }
        roots = session["roots"]
        if session["kind"] == "circuit-extraction":
            roots = [{**root, "replay_alias": aliases[root["name"]]} for root in roots]
        session_record.update(
            session=index,
            raw=str(raw),
            replay=str(replay),
            raw_sha256=sha256_file(raw),
            replay_sha256=sha256_file(replay),
            roots=roots,
            output_contract=(
                churchroad_circuit_contract(content, roots)
                if session["kind"] == "circuit-extraction"
                else native_check_contract(content, check_positions, roots)
            ),
        )
        record["sessions"].append(session_record)
        record["materialization"]["materialized_sessions"] = len(record["sessions"])
    record["materialization"]["complete"] = True
    record["status"] = "ordinary-validation-pending"


def materialize_complete_events(
    record: dict[str, Any], attempt: Path, *, max_evidence_bytes: int = 128 * 1024**2
) -> dict[str, Any]:
    """Apply the unchanged completion, provenance and replay contracts to real events."""
    family = record["family"]
    process = record["process"]
    events_directory = attempt / "native-events"
    record["raw_invocations"] = []
    event_paths = sorted(events_directory.glob("event-*.json"))
    evidence_bytes = sum(path.stat().st_size for path in event_paths)
    record["evidence_bytes"] = evidence_bytes
    for path in event_paths if evidence_bytes <= max_evidence_bytes else []:
        try:
            event = json.loads(path.read_text())
            if event["kind"] not in {"optimization-start", "tiger-result", "commands"}:
                continue
            raw = attempt / f"invocation-{event['sequence']:06}-{event['kind']}.egg"
            raw.write_text(event["payload"]["program"])
            record["raw_invocations"].append(
                {
                    "event": event["sequence"],
                    "kind": event["kind"],
                    "path": str(raw),
                    "sha256": sha256_file(raw),
                }
            )
        except (KeyError, ValueError):
            # The admission reader below rejects incomplete native events;
            # retaining their bytes is still useful after a crashed parent.
            continue
    if process["status"] != "success" or process["returncode"] != 0:
        record["reason"] = f"native parent did not complete: {process['status']}: {process.get('message')}"
    else:
        try:
            events = read_events(events_directory, max_bytes=max_evidence_bytes)
            record["parent_completed"] = True
            completion_path = events_directory / f"event-{events[-1]['sequence']:06}.json"
            record["source_completion"].update(
                parent_completed=True,
                outputs=[
                    {"path": str(path), "sha256": sha256_file(path)}
                    for path in (completion_path, Path(process["stdout_path"]))
                ],
            )
            if family == "churchroad":
                native_output = attempt / "native-output.v"
                if not native_output.is_file() or native_output.read_text() != events[-1]["payload"].get("verilog"):
                    raise CaptureError("Churchroad final Verilog file does not match the native completion evidence")
                record["source_completion"]["outputs"].append(
                    {
                        "path": str(native_output),
                        "sha256": sha256_file(native_output),
                    }
                )
            else:
                for index, output in enumerate(events[-1]["payload"].get("outputs", [])):
                    native_output = attempt / f"native-output-{index:03}.txt"
                    native_output.write_text(output["result"])
                    record["source_completion"]["outputs"].append(
                        {
                            "path": str(native_output),
                            "sha256": sha256_file(native_output),
                            "native_name": output.get("name"),
                            "native_extension": output.get("file_extension"),
                        }
                    )
            sessions = eggcc_sessions(events) if family == "eggcc" else churchroad_sessions(events)
            materialize_sessions(record, sessions, attempt)
        except (CaptureError, ValueError, KeyError) as error:
            record["reason"] = f"complete-capture evidence or representability gate: {error}"
            if isinstance(error, CaptureResourceError):
                record.update(status="resource-stopped", resource_stop=True)
    record["raw_events"] = [
        {"path": str(path), "sha256": sha256_file(path)} for path in sorted(events_directory.glob("event-*.json"))
    ]
    return record


def recover_churchroad_mapping_phase(
    complete_stage: Path, destination: Path, *, circuit_extract: bool = False
) -> dict[str, Any]:
    """Materialize an observed complete Egglog phase without invoking its failed parent."""
    complete_stage = complete_stage.resolve()
    stage = json.loads(complete_stage.read_text())
    if stage.get("stage") != "complete" or stage["identity"]["case"]["family"] != "churchroad":
        raise CaptureError("mapping-phase recovery requires a retained Churchroad complete-stage receipt")
    if (
        complete_stage != Path(stage["attempt"]).resolve() / "stage.json"
        or stage["identity_sha256"]
        != hashlib.sha256(json.dumps(stage["identity"], sort_keys=True).encode()).hexdigest()
    ):
        raise CaptureError("retained Churchroad stage path or input identity changed")
    artifacts = stage["artifacts"]
    capture_path = Path(stage["capture"])
    if capture_path != complete_stage.parent / "capture-result.json" or str(capture_path) not in artifacts:
        raise CaptureError("retained Churchroad capture is not bound to its stage artifacts")
    for path, digest in artifacts.items():
        if not Path(path).is_file() or sha256_file(Path(path)) != digest:
            raise CaptureError(f"retained Churchroad artifact changed: {path}")
    parent = json.loads(capture_path.read_text())
    if (
        parent["family"] != "churchroad"
        or parent["revision"] != PINS["churchroad"]
        or parent["id"] != stage["case"]
        or parent["id"] != stage["identity"]["case"]["id"]
        or parent.get("capture_mode") != "complete"
        or parent.get("parent_completed")
        or parent["process"]["status"] != "failure"
        or parent["process"]["returncode"] in (None, 0)
    ):
        raise CaptureError("mapping-phase recovery requires the pinned incomplete source parent, without a safety stop")
    events_directory = Path(stage["attempt"]) / "capture" / parent["id"] / "native-events"
    paths = sorted(events_directory.glob("event-*.json"))
    if parent["raw_events"] != [{"path": str(path), "sha256": artifacts.get(str(path))} for path in paths]:
        raise CaptureError("retained Churchroad event inventory differs from its captured artifacts")
    events = read_events(events_directory, require_parent_complete=False)
    session = churchroad_mapping_session(events, circuit_outputs=circuit_extract)
    destination = destination.resolve()
    destination.mkdir(parents=True, exist_ok=False)
    record = {
        key: parent[key]
        for key in ("id", "family", "revision", "source_sha256", "binary_sha256", "replay_engine_sha256")
    }
    scope = "churchroad-circuit-extraction" if circuit_extract else "churchroad-mapping-phase"
    output_events = (
        [session["mapping_snapshot_event"]]
        if circuit_extract
        else [root["selection_event"] for root in session["roots"]]
    )
    record.update(
        capture_mode=scope,
        status="blocked",
        parent_completed=False,
        workloads=[],
        sessions=[],
        source_completion={
            "status": "complete",
            "scope": scope,
            "parent_completed": False,
            "boundary": session["phase_boundary"],
            "outputs": [{"path": str(paths[index]), "sha256": artifacts[str(paths[index])]} for index in output_events],
        },
        originating_parent={
            "stage": str(complete_stage),
            "stage_sha256": sha256_file(complete_stage),
            "capture": str(capture_path),
            "capture_sha256": sha256_file(capture_path),
            "case": stage["identity"]["case"],
            "status": parent["status"],
            "reason": parent.get("reason"),
            "process": parent["process"],
            "source_completion": parent["source_completion"],
        },
        phase_events=[parent["raw_events"][index] for index in session["events"]],
        implementation_sha256={
            name: sha256_file(ROOT / name)
            for name in ("scripts/eggcc_churchroad_complete.py", "scripts/suite_capture_eggcc_churchroad.py")
        },
    )
    if circuit_extract:
        record["implementation_sha256"]["scripts/reproduction_validation.py"] = sha256_file(
            ROOT / "scripts/reproduction_validation.py"
        )
        record["source_completion"]["output_semantics"] = (
            "native Egglog phase complete; behavioral output extraction is adapted and awaits ordinary validation"
        )
    materialize_sessions(record, [session], destination)
    (destination / "capture.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def materialize_complete_request(request_path: Path) -> None:
    """Internal child: verify retained origin, then materialize under the caller's guard."""
    request = json.loads(request_path.read_text())
    attempt = Path(request["attempt"])
    record = request["record"]
    identity = request["identity"]
    if (record["family"], record["id"], request["max_evidence_bytes"]) != (
        "eggcc",
        RAYTRACE_CASE,
        RAYTRACE_EVIDENCE_BYTES,
    ):
        raise CaptureError("unknown guarded materialization policy")
    from scripts.suite_reproduction import case_identity

    if identity is not None and case_identity(identity["case"], identity["settings"]) != identity:
        raise CaptureError("current source/runtime/materializer identity changed")
    originals: dict[str, str] = {}
    copied_inputs: dict[str, str] = {}
    if request["resume_stage"] is not None:
        stage_path = Path(request["resume_stage"])
        if sha256_file(stage_path) != request["resume_stage_sha256"]:
            raise CaptureError("retained stage receipt changed")
        stage = json.loads(stage_path.read_text())
        if identity is None or stage["case"] != RAYTRACE_CASE or stage["stage"] != "complete":
            raise CaptureError("retained stage is not the requested complete Eggcc parent")
        prior = stage["identity"]
        if (
            stage_path.resolve() != (Path(stage["attempt"]) / "stage.json").resolve()
            or stage["identity_sha256"] != hashlib.sha256(json.dumps(prior, sort_keys=True).encode()).hexdigest()
        ):
            raise CaptureError("retained stage path or identity digest differs")
        settings = {key: value for key, value in identity["settings"].items() if key != "materialization_policy"}
        prior_settings = dict(prior["settings"])
        if prior_settings.pop("materialization_policy", None) not in {None, RAYTRACE_POLICY}:
            raise CaptureError("unknown retained materialization policy")
        if prior["case"] != identity["case"] or prior_settings != settings:
            raise CaptureError("retained case, configuration or source settings differ")
        adapter = str(Path(__file__).resolve())
        old_inputs, current_inputs = dict(prior["inputs"]), dict(identity["inputs"])
        if old_inputs.pop(adapter, None) not in {RESUME_PREDECESSOR_ADAPTER, sha256_file(Path(adapter))}:
            raise CaptureError("unreviewed predecessor capture adapter")
        if current_inputs.pop(adapter, None) != sha256_file(Path(adapter)) or old_inputs != current_inputs:
            raise CaptureError("retained native source/tool/input identities differ")
        if stage.get("artifact_directories"):
            raise CaptureError("unexpected retained directory artifacts")
        originals = dict(stage["artifacts"])
        originals[str(stage_path)] = request["resume_stage_sha256"]
        for name, digest in originals.items():
            if not Path(name).is_file() or Path(name).is_symlink() or sha256_file(Path(name)) != digest:
                raise CaptureError(f"retained artifact changed: {name}")
        capture_path = Path(stage["capture"])
        if str(capture_path) not in originals:
            raise CaptureError("retained capture is not bound by its stage")
        old = json.loads(capture_path.read_text())
        if (
            old["id"] != record["id"]
            or old["family"] != "eggcc"
            or old["capture_mode"] != "complete"
            or old["process"]["status"] != "success"
            or old["process"]["returncode"] != 0
            or old["process"] != record["process"]
            or any(
                old[key] != record[key]
                for key in ("revision", "source_sha256", "binary_sha256", "replay_engine_sha256")
            )
        ):
            raise CaptureError("retained native process/source/binary does not match the request")
        if (
            old["command"][0] != "env"
            or not old["command"][1].startswith("EGGLOG_REPRO_CAPTURE_DIR=")
            or old["command"][2:] != record["command"][2:]
        ):
            raise CaptureError("retained native command/options differ")
        event_directory = Path(old["command"][1].split("=", 1)[1])
        events = {row["path"]: row["sha256"] for row in old["raw_events"]}
        if len(events) != len(old["raw_events"]) or set(events) != {
            str(path) for path in event_directory.glob("event-*.json")
        }:
            raise CaptureError("retained event inventory differs")
        if any(originals.get(name) != digest for name, digest in events.items()):
            raise CaptureError("retained events are not bound by the stage")
        if sum(Path(name).stat().st_size for name in events) > RAYTRACE_EVIDENCE_BYTES:
            raise CaptureResourceError("retained native evidence exceeds the fixed raytrace budget")
        for name, digest in events.items():
            target = attempt / "native-events" / Path(name).name
            shutil.copyfile(name, target)
            copied_inputs[str(target)] = digest
            if sha256_file(target) != digest:
                raise CaptureError("native event changed during recovery copy")
        record["acquisition_origin"] = {
            "stage": str(stage_path),
            "stage_sha256": request["resume_stage_sha256"],
            "capture": str(capture_path),
            "capture_sha256": originals[str(capture_path)],
            "prior_capture_status": old["status"],
            "prior_resource_stop": old.get("resource_stop", False),
            "command": old["command"],
            "process": old["process"],
            "predecessor_adapter_sha256": prior["inputs"][adapter],
            "materializer_adapter_sha256": sha256_file(Path(adapter)),
            "artifacts": originals,
        }
        record["command"] = old["command"]
        for stream in ("stdout", "stderr"):
            name = old["process"][f"{stream}_path"]
            if name not in originals:
                raise CaptureError("native process log is not bound by the stage")
            target = attempt / f"native.{stream}.log"
            shutil.copyfile(name, target)
            copied_inputs[str(target)] = originals[name]
            if sha256_file(target) != originals[name]:
                raise CaptureError("native log changed during recovery copy")
            record["process"][f"{stream}_path"] = str(target)
    bindings = {
        record["command"][2]: record["binary_sha256"],
        record["command"][3]: record["source_sha256"],
        request["engine"]: record["replay_engine_sha256"],
    }
    if any(sha256_file(Path(name)) != digest for name, digest in bindings.items()):
        raise CaptureError("native source/compiler or ordinary engine changed")
    event_inputs = {str(path): sha256_file(path) for path in sorted((attempt / "native-events").glob("event-*.json"))}
    if any(event_inputs.get(name) != digest for name, digest in copied_inputs.items() if "/native-events/" in name):
        raise CaptureError("copied event changed before materialization")
    materialize_complete_events(record, attempt, max_evidence_bytes=RAYTRACE_EVIDENCE_BYTES)
    if set(event_inputs) != {str(path) for path in (attempt / "native-events").glob("event-*.json")}:
        raise CaptureError("native event inventory changed during materialization")
    if record["status"] == "ordinary-validation-pending" and len(record["sessions"]) != 6:
        raise CaptureError("raytrace requires all six optimization/reconstruction sessions")
    for name, digest in (originals | bindings | event_inputs | copied_inputs).items():
        if sha256_file(Path(name)) != digest:
            raise CaptureError(f"input changed during materialization: {name}")
    if identity is not None and case_identity(identity["case"], identity["settings"]) != identity:
        raise CaptureError("source/runtime/materializer identity changed during materialization")
    (attempt / "materialization-result.json").write_text(json.dumps(record, indent=2) + "\n")


def guarded_materialization(
    record: dict[str, Any],
    attempt: Path,
    engine: Path,
    max_evidence_bytes: int,
    resume_stage: Path | None,
    identity: dict[str, Any] | None,
) -> dict[str, Any]:
    """Keep every large event decode in a separately bounded, native-free child."""
    request = attempt / "materialization-request.json"
    request.write_text(
        json.dumps(
            {
                "record": record,
                "attempt": str(attempt),
                "engine": str(engine),
                "identity": identity,
                "max_evidence_bytes": max_evidence_bytes,
                "resume_stage": str(resume_stage) if resume_stage else None,
                "resume_stage_sha256": sha256_file(resume_stage) if resume_stage else None,
            },
            indent=2,
            default=str,
        )
        + "\n"
    )
    try:
        process = run_bounded_command(
            [sys.executable, str(Path(__file__).resolve()), "_materialize-complete", str(request.resolve())],
            ROOT,
            attempt / "materialization",
            timeout_sec=300,
            memory_limit_bytes=5 * 1024**3,
            require_guard=True,
            disk_reserve_bytes=10 * 1024**3,
            allow_warning_pressure=True,
        )
        if process.status == "success":
            result = json.loads((attempt / "materialization-result.json").read_text())
            if result["id"] != record["id"] or result["process"]["status"] != record["process"]["status"]:
                raise CaptureError("materializer returned another native parent")
            record = result
        else:
            record.update(status=process.status, reason=process.message or "materialization child failed", workloads=[])
        record["materialization_process"] = asdict(process)
    except (OSError, ValueError) as error:
        record.update(
            status="resource-stopped" if "guard refused" in str(error) else "blocked", reason=str(error), workloads=[]
        )
    record["materialization_policy"] = {
        "name": RAYTRACE_POLICY,
        "max_evidence_bytes": max_evidence_bytes,
        "memory_limit_bytes": 5 * 1024**3,
        "timeout_sec": 300,
        "host_reserve_bytes": 2 * 1024**3,
        "disk_reserve_bytes": 10 * 1024**3,
        "allow_warning_pressure": True,
        "request": str(request),
        "request_sha256": sha256_file(request),
    }
    return record


def capture_complete(
    family: str,
    cases: list[dict],
    destination: Path,
    checkout: Path,
    binary: Path,
    engine: Path,
    *,
    timeout_sec: float = 300,
    max_evidence_bytes: int = 128 * 1024**2,
    validate_ordinary: bool = True,
    resume_stage: Path | None = None,
    resume_identity: dict[str, Any] | None = None,
) -> list[dict]:
    """Run the native parent and materialize every resulting session.

    Successful prefixes never become completed workloads. Each case owns a fresh
    event directory, and neither this path nor the native hook returns fake output
    to the parent compiler. The direct API validates ordinary replays by default;
    the coordinator defers them to its separate, stronger validation stage.
    Deferred materialization never exposes admitted workloads. No stable catalog
    or performance cache is modified.
    """
    if family not in PINS:
        raise ValueError(f"unknown complete-capture family {family!r}")
    if max_evidence_bytes > 128 * 1024**2 and (
        family != "eggcc"
        or [case["id"] for case in cases] != [RAYTRACE_CASE]
        or max_evidence_bytes != RAYTRACE_EVIDENCE_BYTES
    ):
        raise ValueError("larger evidence budget is reserved for the fixed raytrace policy")
    if resume_stage is not None and (max_evidence_bytes != RAYTRACE_EVIDENCE_BYTES or resume_identity is None):
        raise ValueError("retained-parent recovery requires the raytrace policy and current input identity")
    binary = binary.resolve()
    checkout = checkout.resolve()
    engine = engine.resolve()
    for executable in (binary, engine):
        if not executable.is_file():
            raise FileNotFoundError(f"missing complete-capture executable: {executable}")
    records = []
    for case in cases:
        attempt = destination / case["id"]
        attempt.mkdir(parents=True, exist_ok=False)
        events_directory = attempt / "native-events"
        events_directory.mkdir()
        source = checkout / case["source"]
        command = ["env", f"EGGLOG_REPRO_CAPTURE_DIR={events_directory.resolve()}"]
        if family == "eggcc":
            command.extend([str(binary), str(source), "--run-mode", "optimize"])
        else:
            command.append(f"CARGO_MANIFEST_DIR={checkout}")
            yosys = BUILD / "yosys-complete-source"
            if (yosys / "yosys").is_file():
                command.append(f"PATH={yosys}:{os.environ.get('PATH', '')}")
            command.extend(
                [
                    str(binary),
                    "--filepath",
                    str(source),
                    "--top-module-name",
                    case.get("top_module_name", "mul"),
                    "--architecture",
                    case.get("architecture", "xilinx-ultrascale-plus"),
                    "--out-filepath",
                    str((attempt / "native-output.v").resolve()),
                ]
            )
        # The source-backed manifest owns graph-changing variants. These are
        # compiler options, not a shell fragment, and cannot enable device runs
        # or truncate a native optimization into an apparently complete parent.
        options = case.get("native_options", [])
        forbidden = {
            "--interp",
            "--run-mode",
            "--stop-after-n-passes",
            "--optimize-function",
            "--debug-dir",
            "--simulate",
            "--filepath",
            "--out-filepath",
        }
        if any(option.split("=", 1)[0] in forbidden for option in options):
            raise CaptureError("complete capture options may not interpret, truncate, or replace the optimizer")
        command.extend(options)
        if resume_stage is None:
            process = run_bounded_command(
                command,
                checkout,
                attempt / "native",
                timeout_sec=timeout_sec,
                require_guard=True,
                disk_reserve_bytes=10 * 1024**3,
                allow_warning_pressure=False,
            )
            process_record = asdict(process)
        else:
            # Small metadata only; the guarded child verifies all original bytes.
            prior_stage = json.loads(resume_stage.read_text())
            prior_capture = json.loads(Path(prior_stage["capture"]).read_text())
            process_record = prior_capture["process"]
        record: dict[str, Any] = {
            "id": case["id"],
            "family": family,
            "revision": case.get("revision", PINS[family]),
            "capture_mode": "complete",
            "command": command,
            "process": process_record,
            "source_sha256": sha256_file(source),
            "binary_sha256": sha256_file(binary),
            "replay_engine_sha256": sha256_file(engine),
            "parent_completed": False,
            "status": "blocked",
            "workloads": [],
            "sessions": [],
            "source_completion": {
                "status": process_record["status"],
                "parent_completed": False,
                "outputs": [],
            },
        }
        if max_evidence_bytes > 128 * 1024**2 and record["process"]["status"] != "success":
            record.update(
                status=record["process"]["status"],
                reason="native parent did not complete; guarded materialization was not launched",
                raw_invocations=[],
                raw_events=[
                    {"path": str(path), "sha256": sha256_file(path)}
                    for path in sorted(events_directory.glob("event-*.json"))
                ],
            )
        elif max_evidence_bytes > 128 * 1024**2:
            record = guarded_materialization(record, attempt, engine, max_evidence_bytes, resume_stage, resume_identity)
        else:
            record = materialize_complete_events(record, attempt, max_evidence_bytes=max_evidence_bytes)
        if validate_ordinary and record["status"] == "ordinary-validation-pending":
            try:
                for index, session_record in enumerate(record["sessions"]):
                    validated = run_bounded_command(
                        [
                            str(engine),
                            "--mode",
                            "no-messages",
                            "-j",
                            "1",
                            str(Path(session_record["replay"]).resolve()),
                        ],
                        attempt,
                        attempt / f"validate-{index:03}",
                        timeout_sec=timeout_sec,
                        require_guard=True,
                        disk_reserve_bytes=10 * 1024**3,
                        allow_warning_pressure=False,
                    )
                    session_record["validation"] = asdict(validated)
                    if validated.status != "success":
                        record["status"] = "ordinary-validation-failed"
                        raise CaptureError(f"ordinary replay failed for session {index}: {validated.status}")
                record["status"] = "reproduced"
                record["workloads"] = [session["replay"] for session in record["sessions"]]
            except CaptureError as error:
                record["reason"] = str(error)
        (attempt / "capture.json").write_text(json.dumps(record, default=str, indent=2) + "\n")
        records.append(record)
        print(f"{case['id']}: {record['status']}", flush=True)
        if (
            record.get("resource_stop")
            or record["process"]["status"] in {"memory-limit", "resource-stopped", "timed-out"}
            or any(
                session.get("validation", {}).get("status") in {"memory-limit", "resource-stopped", "timed-out"}
                for session in record["sessions"]
            )
        ):
            break
    return records


def main() -> None:
    if len(sys.argv) == 3 and sys.argv[1] == "_materialize-complete":
        request_path = Path(sys.argv[2])
        try:
            materialize_complete_request(request_path)
        except (OSError, ValueError, KeyError) as error:
            request = json.loads(request_path.read_text())
            record = request["record"]
            record.update(
                status="resource-stopped" if isinstance(error, CaptureResourceError) else "blocked",
                reason=f"retained-parent materialization refused: {error}",
                workloads=[],
            )
            (Path(request["attempt"]) / "materialization-result.json").write_text(json.dumps(record, indent=2) + "\n")
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("family", choices=tuple(PINS))
    parser.add_argument(
        "--prepare", action="store_true", help="acquire pinned sources and build isolated compilers first"
    )
    parser.add_argument("--prepare-only", action="store_true", help="prepare compilers without capturing inputs")
    parser.add_argument(
        "--complete", action="store_true", help="capture successful native optimization and all outputs"
    )
    parser.add_argument("--case", action="append", default=[], help="select a catalog case ID; repeatable")
    parser.add_argument("--checkout", type=Path, help="prepared native source checkout for complete capture")
    parser.add_argument("--binary", type=Path, help="instrumented native compiler for complete capture")
    parser.add_argument("--engine", type=Path, default=ROOT / "target/release/egglog-experimental")
    parser.add_argument("--timeout-sec", type=float, default=300)
    parser.add_argument("--max-evidence-bytes", type=int, default=128 * 1024**2)
    parser.add_argument(
        "--from-capture", type=Path, help="reuse retained raw Eggcc exports and revalidate replay oracles"
    )
    parser.add_argument(
        "--recover-mapping-phase",
        type=Path,
        help="recover a completed Churchroad Egglog phase from a failed complete-stage receipt; never run native work",
    )
    parser.add_argument("--output", type=Path, help="fresh destination for --recover-mapping-phase")
    parser.add_argument(
        "--circuit-extract", action="store_true", help="extract behavioral circuits for an empty-proposal phase"
    )
    args = parser.parse_args()
    if args.recover_mapping_phase is not None:
        if (
            args.family != "churchroad"
            or args.output is None
            or args.complete
            or args.prepare
            or args.prepare_only
            or args.from_capture is not None
            or args.case
        ):
            parser.error(
                "--recover-mapping-phase requires churchroad --output and cannot run native capture/preparation"
            )
        recover_churchroad_mapping_phase(args.recover_mapping_phase, args.output, circuit_extract=args.circuit_extract)
        print((args.output / "capture.json").resolve())
        return
    if args.output is not None or args.circuit_extract:
        parser.error("--output and --circuit-extract require --recover-mapping-phase")
    cases = [
        case
        for case in json.loads((ROOT / "benchmarks/catalog.json").read_text())["cases"]
        if case["family"] == args.family
    ]
    if args.case:
        unknown = set(args.case) - {case["id"] for case in cases}
        if unknown:
            parser.error(f"unknown {args.family} case IDs: {', '.join(sorted(unknown))}")
        cases = [case for case in cases if case["id"] in args.case]
    if args.complete and args.from_capture is not None:
        parser.error("--from-capture retains only phase prefixes; complete mode must observe native completion")
    destination = STORAGE / "evidence" / args.family / f"capture-{time.time_ns()}"
    destination.mkdir(parents=True)
    if args.prepare or args.prepare_only:
        prepare_compiler(args.family, destination, complete=args.complete)
    if args.prepare_only:
        print(destination.relative_to(ROOT))
        return
    if args.complete:
        records = capture_complete(
            args.family,
            cases,
            destination,
            args.checkout or BUILD / f"{args.family}-complete-source",
            args.binary or BUILD / f"{args.family}-complete/debug/{args.family}",
            args.engine,
            timeout_sec=args.timeout_sec,
            max_evidence_bytes=args.max_evidence_bytes,
        )
    else:
        records = (
            capture_eggcc(cases, destination, None if args.from_capture is None else args.from_capture.resolve())
            if args.family == "eggcc"
            else capture_churchroad(cases, destination)
        )
    output = destination / "results.json"
    output.write_text(json.dumps(records, default=str, indent=2) + "\n")
    latest = "latest-complete-capture.json" if args.complete else "latest-capture.json"
    (STORAGE / "evidence" / args.family / latest).write_text(
        json.dumps({"results": str(output.relative_to(ROOT))}, indent=2) + "\n"
    )
    print(output.relative_to(ROOT))


if __name__ == "__main__":
    main()
