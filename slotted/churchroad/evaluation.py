"""Independent Churchroad evaluation; no bench.py cache reads or writes."""

import argparse
import ctypes
import hashlib
import json
import math
import os
import re
import resource
import shutil
import statistics
import subprocess
import sys
import time
from collections import defaultdict
from contextlib import contextmanager, suppress
from pathlib import Path

from benchmarks.reproduction.materialize import churchroad_mapping_program, constructors
from benchmarks.reproduction.reproduction_process import run_bounded_command
from benchmarks.reproduction.source_tools import sha256_file
from benchmarks.reproduction.suite_capture_eggcc_churchroad import rename_churchroad_globals
from native_memory import NATIVE_LIMIT_BYTES

from .eval_mapping import native_graph, specialized, specialized_graph
from .importer import import_egg

ROOT = Path(__file__).resolve().parents[2]
NATIVE_PIN = "9f82ca23b273a5a500cc6a1ca60b30d3c33c5721"
LAKEROAD_PIN = "7a69047ad20cad54e5c78d68d397b716b42ff462"
TREATMENTS = ("native", "named", "typed-named", "slotted")
CURRENT = ROOT / "target/release/examples/churchroad_eval"


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n")


def read_events(path):
    return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []


def phases(directory):
    result = defaultdict(float)
    for event in read_events(directory / "phases.jsonl"):
        result[event["phase"]] += event["seconds"]
    return dict(result)


def git_revision(path):
    return subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()


def build(toolchain, checkout, output):
    helper = checkout / "src/bin/churchroad-eval-native.rs"
    helper.parent.mkdir(exist_ok=True)
    shutil.copyfile(Path(__file__).with_name("eval_native.rs"), helper)
    jobs = os.environ.get("CARGO_BUILD_JOBS", "4")
    commands = [
        (
            [
                "cargo",
                "+1.88.0",
                "build",
                "--release",
                "--locked",
                "--manifest-path",
                str(checkout / "Cargo.toml"),
                "--bin",
                "churchroad-eval-native",
            ],
            {"CARGO_TARGET_DIR": str(toolchain / "build/cargo")},
        ),
        (
            ["cargo", "build", "--release", "--locked", "-p", "egglog-experimental", "--example", "churchroad_eval"],
            {"CARGO_TARGET_DIR": str(ROOT / "target")},
        ),
    ]
    for index, (command, extra) in enumerate(commands):
        print(
            f"Building {'native Churchroad' if index == 0 else 'current Egglog'} measurement worker…", file=sys.stderr
        )
        with (output / f"build-{index}.log").open("w") as log:
            subprocess.run(
                command,
                cwd=ROOT,
                env={**os.environ, "CARGO_BUILD_JOBS": jobs, **extra},
                stdout=log,
                stderr=subprocess.STDOUT,
                check=True,
            )


def wrappers(directory, tools):
    """Observe child lifetimes without changing their arguments or output streams."""
    directory.mkdir()
    for name, executable in tools.items():
        if not executable:
            continue
        script = directory / name
        script.write_text(f"""#!{sys.executable}
import json, os, resource, shutil, subprocess, sys, time
from pathlib import Path
path = Path(os.environ["CHURCHROAD_EVAL_TOOL_EVENTS"])
def emit(event):
    fd = os.open(path, os.O_CREAT | os.O_APPEND | os.O_WRONLY, 0o600)
    os.write(fd, (json.dumps({{"tool": {name!r}, "pid": os.getpid(), **event}}) + "\\n").encode())
    os.close(fd)
if {name!r} == "racket" and "--verilog-module-filepath" in sys.argv:
    spec = sys.argv[sys.argv.index("--verilog-module-filepath") + 1]
    shutil.copyfile(spec, path.parent / ("lakeroad-spec-" + str(os.getpid()) + ".v"))
start = time.monotonic()
emit({{"event": "start", "monotonic_sec": start}})
arguments = sys.argv[1:]
if {name!r} == "racket" and "--verilog-module-filepath" in arguments:
    arguments.insert(0, os.environ["CHURCHROAD_EVAL_ROSETTE_LOADER"])
code = subprocess.call([{str(executable)!r}, *arguments])
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
emit({{"event": "exit", "seconds": time.monotonic() - start, "exit_code": code,
       "user_cpu_sec": usage.ru_utime, "system_cpu_sec": usage.ru_stime}})
sys.exit(code)
""")
        script.chmod(0o755)


@contextmanager
def reap_descendants():
    """Own orphaned tool children even when container PID 1 does not reap them.

    Used around one isolated command at a time. The bounded supervisor kills
    its process group before returning; this scope then waits for adopted
    descendants, including solvers whose immediate parent has exited.
    """
    libc = ctypes.CDLL(None, use_errno=True)
    previous = ctypes.c_int()
    if libc.prctl(37, ctypes.byref(previous), 0, 0, 0) or libc.prctl(36, 1, 0, 0, 0):
        raise OSError(ctypes.get_errno(), "could not establish child subreaper")
    try:
        yield
    finally:
        try:
            while True:
                try:
                    os.waitpid(-1, 0)
                except InterruptedError:
                    continue
                except ChildProcessError:
                    break
        finally:
            if libc.prctl(36, previous.value, 0, 0, 0):
                raise OSError(ctypes.get_errno(), "could not restore child subreaper")


def execute(command, directory, name, timeout, environment):
    write_json(directory / f"{name}.command.json", command)
    # GNU time's maximum RSS includes the waited-for descendants. It is not a
    # sampled sum of simultaneously resident processes; retain that definition.
    measured = [
        "prlimit",
        f"--as={NATIVE_LIMIT_BYTES}",
        "--",
        "/usr/bin/time",
        "-f",
        "%M",
        "-o",
        str(directory / f"{name}.rss-kib"),
        *command,
    ]
    with reap_descendants():
        result = run_bounded_command(measured, ROOT, directory / name, timeout_sec=timeout, env_overrides=environment)
    write_json(
        directory / f"{name}.process.json",
        {
            "status": result.status,
            "returncode": result.returncode,
            "wall_sec": result.wall_sec,
            "message": result.message,
        },
    )
    if result.status != "success":
        raise ValueError(f"{name}: {result.status}; logs: {result.stdout_path}, {result.stderr_path}")
    return result


def current_request(checkout, source, rules, circuit, treatment, max_iterations):
    if treatment == "named":
        aliases = {}
        chunks = []
        for part in [(checkout / "egglog_src/churchroad.egg").read_text(), source, rules]:
            text, _, aliases = rename_churchroad_globals(constructors(part), "", rules, aliases=aliases)
            chunks.append(text)
        declarations, inputs, rewrites = chunks
        schedule = "(run-schedule (saturate (seq typing transform mapping)))"
    else:
        declarations, inputs, rewrites = specialized(circuit, treatment == "slotted")
        schedule = None
    return dict(
        declarations=declarations,
        input=inputs,
        rules=rewrites,
        schedule=schedule,
        slotted=treatment == "slotted",
        max_iterations=max_iterations,
    )


def frontend(source, top, yosys, plugin, directory, timeout, environment):
    # Identical passes to the original driver's commands_from_verilog_file.
    script = (
        f"read_verilog -sv {json.dumps(str(source))}; hierarchy -simcheck -top {top}; prep; "
        "write_churchroad -salt evaluation -letbindings"
    )
    result = execute([str(yosys), "-m", str(plugin), "-q", "-p", script], directory, "frontend", timeout, environment)
    text = result.stdout_path.read_text()
    (directory / "frontend.egg").write_text(text)
    return text, result.wall_sec


def validation(source, top, mapped, model, yosys, directory, timeout, environment, vectors):
    """Random simulation of the original source against the synthesized netlist.

    Lakeroad checks its local synthesis queries. This additional whole-design
    simulation is explicitly not a proof of the wide multiplication identity.
    """
    import random

    circuit = import_egg((directory / "frontend.egg").read_text())
    for name, file, module, extra in [
        ("reference", source, top, ""),
        # Keep the vendor model as a black box during synthesis normalization;
        # simulate its original body and delays in Icarus below.
        ("mapped", mapped, "top", f"read_verilog -sv -lib -DXIL_XECLIB {json.dumps(str(model))}; "),
    ]:
        script = (
            extra + f"read_verilog -sv {json.dumps(str(file))}; hierarchy -check -top {module}; "
            f"proc; flatten; opt; clean; check -assert; rename {module} {name}; "
            f"write_verilog -noattr {json.dumps(str(directory / (name + '-normalized.v')))}"
        )
        execute([str(yosys), "-Q", "-T", "-p", script], directory, f"validate-{name}", timeout, environment)
    declarations, connections = [], []
    for name in [*circuit.inputs, *circuit.outputs]:
        if not re.fullmatch(r"[a-zA-Z_][a-zA-Z0-9_$]*", name):
            raise ValueError(f"simulation does not support escaped Verilog port identifier: {name!r}")
    for i, (name, expr) in enumerate(circuit.inputs.items()):
        declarations.append(f"reg [{expr.width - 1}:0] in{i};")
        connections.append(f".{name}(in{i})")
    checks = []
    instances = []
    for side in ("reference", "mapped"):
        ports = connections.copy()
        for i, (name, expr) in enumerate(circuit.outputs.items()):
            declarations.append(f"wire [{expr.width - 1}:0] {side}{i};")
            ports.append(f".{name}({side}{i})")
            if side == "mapped":
                checks.append(
                    f'if (reference{i} !== mapped{i}) $fatal(1, "output {i}: reference=%h mapped=%h", '
                    f"reference{i}, mapped{i});"
                )
        instances.append(f"{side} {side}_instance ({', '.join(ports)});")
    rng = random.Random(0)
    stimuli = []
    for index in range(vectors):
        for i, expr in enumerate(circuit.inputs.values()):
            value = [0, (1 << expr.width) - 1, 1][index] if index < 3 else rng.getrandbits(expr.width)
            stimuli.append(f"in{i} = {expr.width}'d{value};")
        stimuli.append("#10; " + " ".join(checks))
    testbench = "\n".join(
        [
            "`timescale 1ns/1ps",
            "module testbench;",
            *declarations,
            *instances,
            "initial begin",
            *stimuli,
            f'$display("PASS {vectors}"); $finish;',
            "end endmodule",
        ]
    )
    (directory / "testbench.v").write_text(testbench)
    executable = directory / "simulation"
    execute(
        [
            "iverilog",
            "-g2012",
            "-DXIL_XECLIB",
            "-s",
            "testbench",
            "-o",
            str(executable),
            str(directory / "reference-normalized.v"),
            str(directory / "mapped-normalized.v"),
            str(model),
            str(directory / "testbench.v"),
        ],
        directory,
        "simulation-build",
        timeout,
        environment,
    )
    result = execute(["vvp", str(executable)], directory, "simulation", timeout, environment)
    if f"PASS {vectors}" not in result.stdout_path.read_text():
        raise ValueError("simulation completed without the expected success marker")
    return {
        "status": "passed",
        "kind": "deterministic-random-simulation",
        "vectors": vectors,
        "seed": 0,
        "whole_design_formal_equivalence": "not-run",
    }


def mapping_result(directory, treatment, row):
    graph_document = json.loads((directory / "graph.json").read_text())
    before = time.monotonic()
    if treatment in {"native", "named"}:
        graph = native_graph(graph_document)
    else:
        circuit = import_egg((directory / "frontend.egg").read_text())
        graph = specialized_graph(graph_document, list(circuit.inputs))
    row["graph_normalization_sec"] = time.monotonic() - before
    row["logical_graph"] = {
        "classes": len(graph.reachable()),
        "nodes": sum(len(graph.nodes[c]) for c in graph.reachable()),
    }
    row["engine_graph"] = {"classes": len(graph_document["class_data"]), "nodes": len(graph_document["nodes"])}
    signature = graph.signature()
    write_json(directory / "signature.json", signature)
    row["signature_sha256"] = hashlib.sha256(json.dumps(signature, sort_keys=True).encode()).hexdigest()
    row["dsp_proposals"] = len(signature["proposals"])
    return graph


def run_trial(args, treatment, sample, source, top, rules, paths, directory):
    directory.mkdir()
    # Rosette kills solver PIDs directly. Interposing a wrapper would change
    # that lifecycle; observe its reporter events instead.
    tools = {"yosys": paths["yosys"], "racket": shutil.which("racket")}
    wrappers(directory / "tools", tools)
    environment = {
        "PATH": os.pathsep.join([str(directory / "tools"), str(paths["prefix"] / "bin"), os.environ["PATH"]]),
        "CARGO_MANIFEST_DIR": str(paths["checkout"]),
        "LAKEROAD_DIR": str(paths["lakeroad"]),
        "CHURCHROAD_EVAL_TOOL_EVENTS": str(directory / "tool-events.jsonl"),
        "CHURCHROAD_EVAL_ROSETTE_EVENTS": str(directory / "rosette-events.jsonl"),
        "CHURCHROAD_EVAL_ROSETTE_LOADER": str(Path(__file__).with_name("eval_lakeroad.rkt")),
        "RAYON_NUM_THREADS": "1",
    }
    row = {
        "treatment": treatment,
        "sample": sample,
        "directory": str(directory),
        "status": "error",
        "validation": {"status": "not-run"},
    }
    start = time.monotonic()
    try:
        if treatment == "native":
            request = dict(
                directory=str(directory), verilog=str(source), top=top, rules=rules, synthesis=not args.mapping_only
            )
            binary = paths["native"]
        else:
            source_egg, seconds = frontend(
                source, top, paths["yosys"], paths["plugin"], directory, args.timeout, environment
            )
            row["frontend_process_sec"] = seconds
            circuit = import_egg(source_egg)
            before = time.monotonic()
            request = current_request(paths["checkout"], source_egg, rules, circuit, treatment, args.max_iterations)
            row["encoding_sec"] = time.monotonic() - before
            request["directory"] = str(directory)
            binary = CURRENT
        write_json(directory / "request.json", request)
        execute([str(binary), str(directory / "request.json")], directory, "engine", args.timeout, environment)
        graph = mapping_result(directory, treatment, row)
        if treatment != "native" and not args.mapping_only:
            bridge = directory / "bridge"
            bridge.mkdir()
            before = time.monotonic()
            bridge_source = graph.bridge_program()
            row["bridge_encoding_sec"] = time.monotonic() - before
            (bridge / "input.egg").write_text(bridge_source)
            write_json(bridge / "request.json", dict(directory=str(bridge), input=bridge_source, synthesis=True))
            execute([str(paths["native"]), str(bridge / "request.json")], bridge, "engine", args.timeout, environment)
            shutil.copyfile(bridge / "mapped.v", directory / "mapped.v")
            row["bridge_phases_sec"] = phases(bridge)
        row["pipeline_wall_sec"] = time.monotonic() - start
        if args.mapping_only:
            row["validation"] = {"status": "not-run", "reason": "mapping-only requested"}
        if not args.mapping_only:
            mapped = directory / "mapped.v"
            row["dsp_instances"] = mapped.read_text().count("DSP48E2 #(")
            # Capture timing tool events before validation launches more processes.
            row["tool_events"] = read_events(directory / "tool-events.jsonl")
            row["validation"] = {"status": "failed", "kind": "deterministic-random-simulation"}
            row["validation"] = validation(
                source, top, mapped, paths["model"], paths["yosys"], directory, args.timeout, environment, args.vectors
            )
            if not args.verilog and args.case == "wide-mul" and row["dsp_instances"] != 2:
                raise ValueError("wide-mul did not reproduce the paper's two DSP instances")
        row["status"] = "success"
    except (OSError, ValueError, KeyError) as error:
        row["error"] = str(error)
    # A downstream failure must not erase a successfully exported mapping graph.
    if "signature_sha256" not in row and (directory / "graph.json").exists():
        try:
            mapping_result(directory, treatment, row)
        except (OSError, ValueError, KeyError) as error:
            row["mapping_error"] = str(error)
    row["rosette_phases_sec"] = dict(sum_events(read_events(directory / "rosette-events.jsonl"), "phase"))
    row["tool_phases_sec"] = dict(
        sum_events(
            [
                event
                for event in row.get("tool_events", read_events(directory / "tool-events.jsonl"))
                if event.get("event") == "exit"
            ],
            "tool",
        )
    )
    if (directory / "bridge").exists():
        row["bridge_phases_sec"] = phases(directory / "bridge")
    row["elapsed_including_validation_sec"] = time.monotonic() - start
    row["phases_sec"] = phases(directory)
    row.setdefault("tool_events", read_events(directory / "tool-events.jsonl"))
    rss = []
    for path in directory.glob("**/engine.rss-kib"):
        with suppress(ValueError, IndexError):
            rss.append(int(path.read_text().splitlines()[-1]))
    row["max_child_rss_kib"] = max(rss, default=None)
    write_json(directory / "result.json", row)
    return row


def sum_events(events, key):
    result = defaultdict(float)
    for event in events:
        result[event[key]] += event["seconds"]
    return result


def mapping_parity(rows):
    signatures = {row["signature_sha256"] for row in rows if "signature_sha256" in row}
    if len(signatures) > 1:
        return "failed"
    treatments = {row["treatment"] for row in rows}
    if (
        len(signatures) == 1
        and all("signature_sha256" in row for row in rows)
        and "native" in treatments
        and len(treatments) > 1
    ):
        return "passed"
    return "not-established"


def summarize(rows):
    groups = defaultdict(list)
    for row in rows:
        groups[row["treatment"]].append(row)
    summary = {}
    for treatment, group in groups.items():
        completed = [row for row in group if "pipeline_wall_sec" in row]
        times = [row["pipeline_wall_sec"] for row in completed]
        saturation = [row["phases_sec"]["eqsat"] for row in group if "eqsat" in row["phases_sec"]]
        solver = [row["rosette_phases_sec"]["solve"] for row in completed if "solve" in row["rosette_phases_sec"]]
        lakeroad = [row["tool_phases_sec"]["racket"] for row in completed if "racket" in row["tool_phases_sec"]]
        summary[treatment] = {
            "successful": sum(row["status"] == "success" for row in group),
            "attempted": len(group),
            "pipeline_completed": len(times),
            "pipeline_median_sec": statistics.median(times) if times else None,
            "pipeline_min_sec": min(times) if times else None,
            "pipeline_max_sec": max(times) if times else None,
            "eqsat_median_sec": statistics.median(saturation) if saturation else None,
            "solver_query_median_sec": statistics.median(solver) if solver else None,
            "lakeroad_median_sec": statistics.median(lakeroad) if lakeroad else None,
        }
    return summary


def provenance(paths, full):
    data = {"python": sys.version, "platform": sys.platform, "nofile_limit": resource.getrlimit(resource.RLIMIT_NOFILE)}
    data["evaluation_sources"] = {
        p.name: sha256_file(p)
        for p in [
            Path(__file__),
            Path(__file__).with_name("eval_mapping.py"),
            Path(__file__).with_name("eval_native.rs"),
            Path(__file__).with_name("eval_lakeroad.rkt"),
            ROOT / "egglog-experimental/examples/churchroad_eval.rs",
        ]
    }
    data["native_sources"] = {
        name: sha256_file(paths["checkout"] / name)
        for name in ["src/lib.rs", "src/main.rs", "egglog_src/churchroad.egg", "Cargo.lock"]
    }
    if full:
        for tool in ["racket", "raco", "iverilog", "vvp"]:
            data[tool + "_path"] = shutil.which(tool)
        data["racket_version"] = subprocess.check_output(["racket", "--version"], text=True).strip()
        data["racket_packages"] = subprocess.check_output(
            ["raco", "pkg", "show", "--all", "--long", "rosette", "yaml"], text=True
        )
        data["lakeroad_sources"] = {
            name: sha256_file(paths["lakeroad"] / name)
            for name in [
                "bin/main.rkt",
                "racket/synthesize.rkt",
                "racket/btor.rkt",
                "racket/signal.rkt",
                "architecture_descriptions/xilinx_ultrascale_plus.yml",
                "racket/generated/xilinx-ultrascale-plus-dsp48e2.rkt",
                "modules_for_importing/xilinx_ultrascale_plus/DSP48E2.v",
                "dependencies.sh",
            ]
        }
    return data


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv and argv[0] == "discovery":
        from .discovery_eval import main as discovery_main

        return discovery_main(argv[1:])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.epilog = "For bounded module discovery: churchroad-eval.py discovery --help"
    parser.add_argument("--toolchain", type=Path, default=ROOT / "benchmarks/local/reproduction/slotted-churchroad")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--case", choices=["wide-mul", "simple-mul"], default="wide-mul")
    parser.add_argument("--verilog", type=Path)
    parser.add_argument("--top", default="mul")
    parser.add_argument("--samples", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=120, help="seconds per child command (default: 120)")
    parser.add_argument("--max-iterations", type=int, default=20)
    parser.add_argument("--vectors", type=int, default=256)
    parser.add_argument("--mapping-only", action="store_true", help="explicitly omit Lakeroad and final RTL validation")
    parser.add_argument("--treatments", nargs="+", choices=TREATMENTS, default=TREATMENTS)
    parser.add_argument("--no-build", action="store_true", help="reuse existing measurement workers")
    args = parser.parse_args(argv)
    try:
        if (
            not math.isfinite(args.timeout)
            or min(args.samples, args.timeout, args.max_iterations, args.vectors) <= 0
            or args.vectors < 3
        ):
            raise ValueError("positive limits and at least three validation vectors are required")
        if len(set(args.treatments)) != len(args.treatments):
            raise ValueError("duplicate treatments")
        if not re.fullmatch(r"[a-zA-Z_][a-zA-Z0-9_$]*", args.top):
            raise ValueError("--top must be a simple Verilog identifier")
        if not Path("/usr/bin/time").exists() or shutil.which("prlimit") is None:
            raise ValueError("Linux GNU time and prlimit are required")
        if sys.platform != "linux":
            raise ValueError("Churchroad evaluation currently requires Linux child-process supervision")
        if args.output_dir.exists():
            raise ValueError("output directory must be fresh")
        toolchain = args.toolchain.resolve()
        checkout = toolchain / "sources/churchroad"
        if git_revision(checkout) != NATIVE_PIN:
            raise ValueError("native Churchroad checkout does not match the pinned paper-era revision")
        output = args.output_dir.resolve()
        output.mkdir(parents=True)
        prefix = toolchain / "prefix"
        paths = dict(
            checkout=checkout,
            prefix=prefix,
            yosys=prefix / "bin/yosys",
            plugin=checkout / "yosys-plugin/churchroad.so",
            native=toolchain / "build/cargo/release/churchroad-eval-native",
            bitwuzla=prefix / "bin/bitwuzla",
            lakeroad=checkout / "lakeroad",
            model=checkout / "lakeroad/verilog/simulation/xilinx-ultrascale-plus/DSP48E2.v",
        )
        source = (
            args.verilog.resolve()
            if args.verilog
            else checkout / "tests/integration_tests" / (args.case.replace("-", "_") + ".v")
        )
        # The pinned native frontend interpolates paths into a Yosys command
        # without quoting. Reject unsupported paths before launching it.
        if any(re.fullmatch(r"[A-Za-z0-9_./-]+", str(path)) is None for path in [source, toolchain]):
            raise ValueError("native Churchroad requires source/toolchain paths without spaces or shell syntax")
        if not args.no_build:
            build(toolchain, checkout, output)
        rules = churchroad_mapping_program((checkout / "src/main.rs").read_text())
        report = {
            "schema_version": 1,
            "scope": "mapping-only" if args.mapping_only else "mapping-and-native-synthesis-continuation",
            "source": str(source),
            "source_sha256": sha256_file(source),
            "native_revision": NATIVE_PIN,
            "current_revision": git_revision(ROOT),
            "samples": args.samples,
            "rows": [],
            "limits": {
                "timeout_per_command_sec": args.timeout,
                "address_space_bytes": NATIVE_LIMIT_BYTES,
                "max_iterations": args.max_iterations,
            },
            "measurement_notes": [
                "Whole-design validation is outside pipeline_wall_sec. "
                "Pipeline timings include completed runs that fail validation.",
                "Mapping signatures compare the complete output-reachable expression graph and every DSP proposal.",
                "Rosette solve is check-sat/model-reading elapsed time, including IPC and possible process startup; "
                "not pure solver CPU.",
                "Rosette events and child wrappers add instrumentation overhead to every full treatment.",
                "Specialized treatments include explicit graph-export convergence checks.",
                "Non-native full runs include normalization and reconstruction "
                "into the unchanged native synthesis bridge.",
                "Lakeroad and solver process durations overlap; do not add nested tool times.",
                "max_child_rss_kib is GNU time maximum RSS, not summed concurrent process-tree memory.",
                "typed-named versus slotted isolates names from width specialization; "
                "named versus native also changes engine version.",
            ],
        }
        report["binaries"] = {
            name: {"path": str(path), "sha256": sha256_file(path)}
            for name, path in {
                "native": paths["native"],
                "current": CURRENT,
                "yosys": paths["yosys"],
                "plugin": paths["plugin"],
            }.items()
        }
        if not args.mapping_only:
            report["lakeroad_revision"] = git_revision(paths["lakeroad"])
            if report["lakeroad_revision"] != LAKEROAD_PIN:
                raise ValueError("Lakeroad revision differs from the pinned submodule")
            report["dsp_model_sha256"] = sha256_file(paths["model"])
            report["bitwuzla_sha256"] = sha256_file(paths["bitwuzla"])
            if any(shutil.which(tool) is None for tool in ["racket", "iverilog", "vvp"]):
                raise ValueError(
                    "full evaluation requires racket, iverilog, and vvp; see slotted/churchroad/EVALUATION.md"
                )
        report["provenance"] = provenance(paths, not args.mapping_only)
        write_json(output / "report.json", report)
        for sample in range(args.samples):
            order = list(args.treatments)
            shift = sample % len(order)
            for treatment in order[shift:] + order[:shift]:
                print(f"Churchroad {sample + 1}/{args.samples}: {treatment}", file=sys.stderr, flush=True)
                row = run_trial(
                    args, treatment, sample, source, args.top, rules, paths, output / f"{sample:03}-{treatment}"
                )
                report["rows"].append(row)
                write_json(output / "report.json", report)
                if row["status"] != "success":
                    print(row["error"], file=sys.stderr)
        successes = [row for row in report["rows"] if row["status"] == "success"]
        report["mapping_parity"] = mapping_parity(report["rows"])
        report["summary"] = summarize(report["rows"])
        write_json(output / "report.json", report)
        print("Treatment     Success    Pipeline median    Eqsat median     Lakeroad / solver query", file=sys.stderr)

        def seconds(value):
            return f"{value:.4f} s" if value is not None else "—"

        for treatment, row in report["summary"].items():
            pipeline, eqsat = row["pipeline_median_sec"], row["eqsat_median_sec"]
            print(
                f"{treatment:13} {row['successful']}/{row['attempted']}        "
                + (f"{pipeline:9.4f} s       {eqsat:9.6f} s" if pipeline is not None else "incomplete")
                + f"    {seconds(row['lakeroad_median_sec'])} / {seconds(row['solver_query_median_sec'])}",
                file=sys.stderr,
            )
        print(f"Mapping parity: {report['mapping_parity']}. Report: {output / 'report.json'}", file=sys.stderr)
        return int(len(successes) != len(report["rows"]) or report["mapping_parity"] == "failed")
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Churchroad evaluation: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
