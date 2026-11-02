"""Measure bounded e-graph module discovery, independently of DSP synthesis."""

import argparse
import hashlib
import json
import math
import os
import shutil
import statistics
import subprocess
import sys
import time
from collections import defaultdict
from pathlib import Path

from benchmarks.reproduction.source_tools import sha256_file
from native_memory import NATIVE_LIMIT_BYTES
from slotted.reference import render

from .discovery import encoding, native_input, signature, source_nodes
from .evaluation import NATIVE_PIN, ROOT, execute, git_revision, phases, write_json
from .fixtures import CASES, DIRECTORY, verify_inputs
from .importer import import_egg
from .ir import Circuit, operation

CURRENT = ROOT / "target/release/examples/churchroad_discovery"
TREATMENTS = ("native", "vector", "slotted-eager", "slotted")
DISCOVERY_PHASES = ("enumeration", "interfaces", "slot_maintenance")


def generated_ripple(bits, copies):
    """Scale the gate topology of the MIT-licensed two-bit Churchroad fixture."""
    inputs, outputs = {}, {}
    for copy in range(copies):
        a, b = [operation("Input", data=(f"{name}{copy}", bits)) for name in ("a", "b")]
        inputs.update({a.data[0]: a, b.data[0]: b})
        carry, sums = None, []
        for bit in range(bits):
            x, y = [operation("Extract", [port], (bit, bit)) for port in (a, b)]
            s = operation("Xor", [x, y])
            sums.append(s if carry is None else operation("Xor", [s, carry]))
            product = operation("And", [x, y])
            carry = (
                product
                if carry is None
                else operation(
                    "Or", [operation("Or", [product, operation("And", [y, carry])]), operation("And", [x, carry])]
                )
            )
        total = sums[-1]
        for lower in reversed(sums[:-1]):
            total = operation("Concat", [total, lower])
        outputs.update({f"sum{copy}": total, f"carry{copy}": carry})
    return Circuit(inputs, outputs)


def build(toolchain, output, treatments):
    commands = []
    if "native" in treatments:
        checkout = toolchain / "sources/churchroad"
        helper = checkout / "src/bin/churchroad-discovery-native.rs"
        helper.parent.mkdir(exist_ok=True)
        shutil.copyfile(Path(__file__).with_name("eval_discovery_native.rs"), helper)
        commands.append(
            (
                "native",
                [
                    "cargo",
                    "+1.88.0",
                    "build",
                    "--release",
                    "--locked",
                    "--manifest-path",
                    str(checkout / "Cargo.toml"),
                    "--bin",
                    "churchroad-discovery-native",
                ],
                toolchain / "build/cargo",
            )
        )
    if set(treatments) - {"native"}:
        commands.append(
            (
                "current",
                [
                    "cargo",
                    "build",
                    "--release",
                    "--locked",
                    "-p",
                    "egglog-experimental",
                    "--example",
                    "churchroad_discovery",
                ],
                ROOT / "target",
            )
        )
    for name, command, target in commands:
        print(f"Building {name} discovery worker…", file=sys.stderr, flush=True)
        with (output / f"build-{name}.log").open("w") as log:
            subprocess.run(
                command,
                cwd=ROOT,
                check=True,
                stdout=log,
                stderr=subprocess.STDOUT,
                env={
                    **os.environ,
                    "CARGO_BUILD_JOBS": os.environ.get("CARGO_BUILD_JOBS", "2"),
                    "CARGO_TARGET_DIR": str(target),
                },
            )


def parity(rows, treatments, samples):
    expected = {(t, s) for t in treatments for s in range(samples)}
    actual = {(r["treatment"], r["sample"]) for r in rows if r["status"] == "success"}
    if actual != expected or len(treatments) < 2:
        return "not-established"
    return "passed" if len({r["signature_sha256"] for r in rows}) == 1 else "failed"


def summarize(rows):
    result = {}
    for treatment in dict.fromkeys(r["treatment"] for r in rows):
        attempted = [r for r in rows if r["treatment"] == treatment]
        complete = [r for r in attempted if r["status"] == "success"]
        summary = {"attempted": len(attempted), "successful": len(complete)}
        for key in (
            "discovery_sec",
            "engine_setup_and_discovery_sec",
            "worker_wall_sec",
            "max_child_rss_kib",
            "normalization_sec",
            "candidates",
            "templates",
        ):
            summary[key + "_median"] = statistics.median(r[key] for r in complete) if complete else None
        result[treatment] = summary
    return result


def rule_profile(document):
    """Non-overlapping backend timings, grouped by ruleset (current engine)."""
    result = defaultdict(lambda: defaultdict(float))

    def seconds(duration):
        return duration["secs"] + duration["nanos"] / 1e9

    for iteration in document["iterations"]:
        out = result[iteration["name"]]
        report = iteration["report"]
        out["assembly_sec"] += seconds(report["assembly_time"])
        rules = report["rule_set_report"]
        out["merge_sec"] += seconds(rules["merge_time"])
        for fields in rules["pre_merge"].values():
            for name, duration in fields.items():
                out[name + "_sec"] += seconds(duration)
    return {name: dict(values) for name, values in result.items()}


def bound_templates(rows):
    """Untyped BindInput interfaces: exactly the native Graph/Hole semantics."""
    templates = sorted({row[1] for row in rows})
    lines = [
        "(datatype M (Node0 String) (Node1 String M) (Node2 String M M) (Node3 String M M M)",
        "  (BindInput M M :binder 0))",
    ]
    for i, encoded in enumerate(templates):
        names = set()

        def term(body, names=names):
            if body[0] == "Hole":
                names.add(body[1])
                return f"$arg{body[1]}"
            return [f"Node{len(body[1])}", json.dumps(body[0]), *(term(c) for c in body[1])]

        body = term(json.loads(encoded))
        for arg in sorted(names, reverse=True):
            body = ["BindInput", f"$arg{arg}", body]
        lines.append(render(["let", f"module_{i}", body]))
    return "\n".join(lines) + "\n"


def trial(args, nodes, treatment, sample, binary, checkout, directory):
    directory.mkdir()
    row = dict(treatment=treatment, sample=sample, directory=str(directory), status="error")
    before = time.monotonic()
    request = {"input": native_input(nodes)} if treatment == "native" else encoding(nodes, treatment != "vector")
    row["encoding_sec"] = time.monotonic() - before
    request.update(directory=str(directory), rounds=args.rounds, eager_maintenance=treatment == "slotted-eager")
    write_json(directory / "request.json", request)
    for name in ("declarations", "input", "rules"):
        if name in request:
            (directory / f"{name}.egg").write_text(request[name] + "\n")
    row["request_sha256"] = sha256_file(directory / "request.json")
    try:
        process = execute(
            [str(binary), str(directory / "request.json")],
            directory,
            "engine",
            args.timeout,
            {"RAYON_NUM_THREADS": "1", "CARGO_MANIFEST_DIR": str(checkout)},
        )
        row["worker_wall_sec"] = process.wall_sec
        row["max_child_rss_kib"] = int((directory / "engine.rss-kib").read_text().strip())
        before = time.monotonic()
        document = json.loads((directory / "graph.json").read_text())
        candidates = None if treatment == "native" else json.loads((directory / "candidates.json").read_text())
        result = signature(document, candidates)
        row["normalization_sec"] = time.monotonic() - before
        write_json(directory / "signature.json", result)
        row.update(
            signature_sha256=hashlib.sha256(json.dumps(result, separators=(",", ":")).encode()).hexdigest(),
            candidates=len(result),
            templates=len({r[1] for r in result}),
            engine_nodes=len(document["nodes"]),
            engine_classes=len(document["class_data"]),
            status="success",
        )
    except (OSError, ValueError, KeyError, AssertionError, RecursionError) as error:
        row["error"] = f"{type(error).__name__}: {error}"
    row["phases_sec"] = phases(directory)
    if (directory / "run-report.json").exists():
        row["ruleset_profile_sec"] = rule_profile(json.loads((directory / "run-report.json").read_text()))
    row["discovery_sec"] = sum(row["phases_sec"].get(name, 0) for name in DISCOVERY_PHASES)
    row["engine_setup_and_discovery_sec"] = sum(v for k, v in row["phases_sec"].items() if k != "graph_export")
    write_json(directory / "result.json", row)
    return row


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--toolchain", type=Path, default=ROOT / "benchmarks/local/reproduction/slotted-churchroad")
    source = parser.add_mutually_exclusive_group()
    source.add_argument("--case", choices=[*CASES, "ripple-generated"], default="ripple-adder")
    source.add_argument("--input", type=Path, help="saved Churchroad frontend .egg file")
    parser.add_argument("--outputs", nargs="*", default=[])
    parser.add_argument("--bits", type=int, default=4, help="width for ripple-generated")
    parser.add_argument("--copies", type=int, default=1, help="independent copies for ripple-generated")
    parser.add_argument("--rounds", type=int, default=8, help="fixed enumeration rounds; not a saturation claim")
    parser.add_argument("--samples", type=int, default=5)
    parser.add_argument("--timeout", type=float, default=60)
    parser.add_argument("--treatments", nargs="+", choices=TREATMENTS, default=TREATMENTS)
    parser.add_argument("--no-build", action="store_true")
    args = parser.parse_args(argv)
    try:
        if not math.isfinite(args.timeout) or min(args.bits, args.copies, args.rounds, args.samples, args.timeout) <= 0:
            raise ValueError("bits, copies, rounds, samples, and timeout must be positive and finite")
        if len(set(args.treatments)) != len(args.treatments):
            raise ValueError("duplicate treatments")
        if args.output_dir.exists():
            raise ValueError("output directory must be fresh")
        if sys.platform != "linux" or not Path("/usr/bin/time").exists() or not shutil.which("prlimit"):
            raise ValueError("Linux, GNU time, and prlimit are required")
        toolchain = args.toolchain.resolve()
        checkout = toolchain / "sources/churchroad"
        if "native" in args.treatments and git_revision(checkout) != NATIVE_PIN:
            raise ValueError("native Churchroad revision differs from the pinned revision")
        provenance = {}
        if args.input:
            text = args.input.read_text()
            circuit = import_egg(text, args.outputs)
            provenance = {"input": str(args.input.resolve()), "sha256": sha256_file(args.input)}
        elif args.case == "ripple-generated":
            circuit = generated_ripple(args.bits, args.copies)
            provenance = {"generator": "ripple-generated", "bits": args.bits, "copies": args.copies}
            text = None
        else:
            verify_inputs()
            filename, outputs = CASES[args.case]
            text = (DIRECTORY / filename).read_text()
            circuit = import_egg(text, args.outputs or outputs)
            provenance = {"fixture": filename, "sha256": sha256_file(DIRECTORY / filename)}
        nodes = source_nodes(circuit)
        output = args.output_dir.resolve()
        output.mkdir(parents=True)
        write_json(output / "source-nodes.json", nodes)
        if text is not None:
            (output / "frontend.egg").write_text(text)
        (output / "frozen-native.egg").write_text(native_input(nodes) + "\n")
        if not args.no_build:
            build(toolchain, output, args.treatments)
        binaries = {
            t: toolchain / "build/cargo/release/churchroad-discovery-native" if t == "native" else CURRENT
            for t in args.treatments
        }
        report = dict(
            schema_version=1,
            scope="bounded-module-discovery-on-frozen-combinational-DAG",
            source=provenance,
            native_revision=NATIVE_PIN,
            current_revision=git_revision(ROOT),
            rounds=args.rounds,
            samples=args.samples,
            environment={"RAYON_NUM_THREADS": "1", "cpu_affinity": sorted(os.sched_getaffinity(0))},
            source_nodes=len(nodes),
            rows=[],
            limits=dict(timeout_sec=args.timeout, address_space_bytes=NATIVE_LIMIT_BYTES),
            binaries={t: dict(path=str(p), sha256=sha256_file(p)) for t, p in binaries.items()},
            source_hashes={
                str(p.relative_to(ROOT)): sha256_file(p)
                for p in [
                    Path(__file__),
                    Path(__file__).with_name("discovery.py"),
                    Path(__file__).with_name("eval_discovery_native.rs"),
                    ROOT / "egglog-experimental/examples/churchroad_discovery.rs",
                    ROOT / "egglog-experimental/src/slotted/runtime/renaming.rs",
                ]
            },
            notes=[
                "All engines enumerate inside Egglog; Python only lowers the frozen source DAG and validates exports.",
                "Frontend typing/misc and arithmetic expansion do not run during discovery. "
                "Cyclic e-graphs are outside this experiment.",
                "Native rules are unchanged, including the shared underscore variable "
                "joining incorporated children's index vectors.",
                "Var and Var_ are distinct boundary identities, as in native Churchroad. "
                "Only the unused/0 implementation sentinel is excluded from signatures.",
                "Vector uses the current engine, the original graph/index-vector representation, "
                "and canonical integer source identities; it omits native find overhead.",
                "Slotted uses existing slot renaming/shape primitives and ordinary relational "
                "joins over lowered slotted constructors.",
                "Ordered templates have no equality rules. Per-template initialization seeds exact slot invariants; "
                "eager additionally runs generic maintenance each round.",
                "The interface trace is cached per template to preserve the native shared-index-vector join; "
                "interface-rename does no source-name canonicalization.",
                "Discovery includes enumeration, interface traces, and slot maintenance. "
                "Setup, export, normalization, and worker wall time are separate.",
                "Timings include fixed-budget successful runs, not necessarily saturated graphs. "
                "Failures never establish parity or speedups.",
                "RSS is GNU time's process high-water mark and includes export. No Lakeroad or solver processes run.",
            ],
        )
        if "native" in args.treatments:
            report["native_source_hashes"] = {
                p: sha256_file(checkout / p)
                for p in [
                    "src/lib.rs",
                    "egglog_src/churchroad.egg",
                    "egglog_src/module_enumeration_rewrites.egg",
                    "Cargo.lock",
                ]
            }
        write_json(output / "report.json", report)
        for sample in range(args.samples):
            order = list(args.treatments)
            shift = sample % len(order)
            for treatment in order[shift:] + order[:shift]:
                print(f"Module discovery {sample + 1}/{args.samples}: {treatment}", file=sys.stderr, flush=True)
                row = trial(
                    args, nodes, treatment, sample, binaries[treatment], checkout, output / f"{sample:03}-{treatment}"
                )
                report["rows"].append(row)
                write_json(output / "report.json", report)
                if row["status"] != "success":
                    print(row["error"], file=sys.stderr)
        report["candidate_parity"] = parity(report["rows"], args.treatments, args.samples)
        report["summary"] = summarize(report["rows"])
        successes = [r for r in report["rows"] if r["status"] == "success"]
        if successes and report["candidate_parity"] != "failed":
            rows = json.loads((Path(successes[0]["directory"]) / "signature.json").read_text())
            (output / "templates.egg").write_text(bound_templates(rows))
        write_json(output / "report.json", report)
        print("Treatment       Success   Discovery median   Setup + discovery   Worker RSS", file=sys.stderr)
        for treatment, row in report["summary"].items():
            values = (
                f"{row['discovery_sec_median']:.6f} s       {row['engine_setup_and_discovery_sec_median']:.6f} s"
                f"        {row['max_child_rss_kib_median'] / 1024:.1f} MiB"
                if row["successful"]
                else "incomplete"
            )
            print(f"{treatment:15} {row['successful']}/{row['attempted']}      {values}", file=sys.stderr)
        print(f"Candidate parity: {report['candidate_parity']}. Report: {output / 'report.json'}", file=sys.stderr)
        return int(len(successes) != len(report["rows"]) or report["candidate_parity"] == "failed")
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Churchroad discovery: {error}", file=sys.stderr)
        return 2
