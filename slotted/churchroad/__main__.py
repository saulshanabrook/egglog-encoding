"""Discover and reuse slotted modules in Churchroad's combinational frontend IR."""

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

from benchmarks.reproduction.reproduction_process import run_bounded_command
from benchmarks.reproduction.source_tools import sha256_file
from slotted.reference import parse

from .importer import import_egg
from .modules import enumerate_modules, program
from .verilog import export

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = Path(__file__).with_name("fixtures")


def execute(command, output, name, timeout, *, native=False):
    (output / f"{name}.command.json").write_text(json.dumps(command, indent=2) + "\n")
    result = run_bounded_command(command, ROOT, output / name, timeout_sec=timeout, native_limit=native)
    if result.status != "success":
        detail = result.stderr_path.read_text()[-2000:]
        raise ValueError(f"{name}: {result.status}; {detail}\nLogs: {result.stdout_path}, {result.stderr_path}")
    return result


def yosys_path(path):
    path = str(Path(path).resolve())
    if any(c in path for c in '\n\r"\\'):
        raise ValueError("Yosys paths must not contain quotes, backslashes, or newlines")
    return '"' + path + '"'


def capture(verilog, top, yosys, plugin, output, timeout):
    if not re.fullmatch(r"[a-zA-Z_][a-zA-Z_0-9]*", top):
        raise ValueError("the source top module must be a simple Verilog identifier")
    script = f"read_verilog -sv {yosys_path(verilog)}; prep -top {top}; pmuxtree; prep; write_churchroad"
    result = execute([str(yosys), "-q", "-T", "-m", str(plugin), "-p", script], output, "frontend", timeout)
    source = result.stdout_path.read_text()
    (output / "input.egg").write_text(source)
    return source


def verify(yosys, reference, candidate, output, timeout, *, reference_top="reference", name="equivalence"):
    # ABC and vendor simulation libraries are unnecessary for this combinational SAT check.
    script = f"read_verilog -sv {yosys_path(reference)}; hierarchy -top {reference_top}; "
    if reference_top != "reference":
        script += f"rename {reference_top} reference; "
    script += (
        f"read_verilog -sv {yosys_path(candidate)}; "
        "miter -equiv -flatten reference mapped miter; prep -top miter; "
        "sat -verify -prove trigger 0 -show-inputs -show-outputs miter"
    )
    execute([str(yosys), "-Q", "-T", "-p", script], output, name, timeout)


def run(source, output, binary, *, outputs=(), max_depth=2, max_inputs=4, max_candidates=256, timeout=60):
    circuit = import_egg(source, outputs)
    candidates, truncated = enumerate_modules(
        circuit, max_depth=max_depth, max_inputs=max_inputs, max_candidates=max_candidates
    )
    encoded = program(circuit, candidates)
    path = output / "slotted.egg"
    path.write_text(encoded)
    result = execute([str(binary), "--slotted", str(path)], output, "egglog", timeout, native=True)
    extracted = parse(result.stdout_path.read_text())
    if len(extracted) != len(candidates):
        raise ValueError(f"expected {len(candidates)} extracted modules, got {len(extracted)}")
    original, mapped, stats = export(circuit, candidates, extracted)
    (output / "original.v").write_text(original)
    (output / "mapped.v").write_text(mapped)
    (output / "modules.json").write_text(json.dumps(extracted, indent=2) + "\n")
    return {
        "input_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "binary_sha256": sha256_file(binary),
        "slotted_program_sha256": hashlib.sha256(encoded.encode()).hexdigest(),
        "input_ports": {name: expr.width for name, expr in circuit.inputs.items()},
        "output_ports": {name: expr.width for name, expr in circuit.outputs.items()},
        "source_nodes": len(circuit.nodes()),
        "max_depth": max_depth,
        "max_inputs": max_inputs,
        "max_candidates": max_candidates,
        "candidate_limit_reached": truncated,
        "egglog_wall_sec": result.wall_sec,
        **stats,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--input", type=Path, help="raw Churchroad frontend .egg commands")
    source.add_argument("--verilog", type=Path, help="import Verilog through Churchroad's Yosys plugin")
    source.add_argument("--case", choices=["half-adder", "ripple-adder", "wide-mul"])
    parser.add_argument("--outputs", nargs="+", default=(), help="explicit .egg output bindings, if IsPort is absent")
    parser.add_argument("--top", default="top", help="source Verilog module")
    parser.add_argument("--output-dir", type=Path, required=True, help="fresh directory for all generated artifacts")
    parser.add_argument("--binary", type=Path, default=ROOT / "target/release/egglog-experimental")
    parser.add_argument("--yosys", type=Path, help="also check original and mapped Verilog with Yosys SAT")
    parser.add_argument("--plugin", type=Path, help="Churchroad .so built with this Yosys")
    parser.add_argument("--max-depth", type=int, default=2)
    parser.add_argument("--max-inputs", type=int, default=4)
    parser.add_argument("--max-candidates", type=int, default=256)
    parser.add_argument("--timeout", type=float, default=60)
    args = parser.parse_args(argv)
    try:
        if min(args.max_depth, args.max_inputs, args.max_candidates, args.timeout) <= 0:
            raise ValueError("resource limits must be positive")
        output = args.output_dir.resolve()
        if output.exists():
            raise ValueError(f"output directory already exists: {output}")
        reference_verilog = args.verilog
        if args.case:
            from .fixtures import verify_inputs

            verify_inputs()
        if args.case == "half-adder":
            args.input, args.outputs = FIXTURES / "half_adder.egg", ("o_sum", "o_carry")
        elif args.case:
            reference_verilog, args.top = {
                "ripple-adder": (FIXTURES / "2bit-rca.sv", "top"),
                "wide-mul": (FIXTURES / "wide_mul.v", "mul"),
            }[args.case]
            if args.plugin:
                args.verilog = reference_verilog
            else:
                args.input = FIXTURES / f"{args.case}.egg"
        if args.verilog and (not args.yosys or not args.plugin):
            raise ValueError("Verilog import needs both --yosys and --plugin; see slotted/churchroad/README.md")
        output.mkdir(parents=True)
        if args.verilog:
            source = capture(args.verilog, args.top, args.yosys.resolve(), args.plugin.resolve(), output, args.timeout)
        else:
            source = args.input.read_text()
            (output / "input.egg").write_text(source)
        report = run(
            source,
            output,
            args.binary.resolve(),
            outputs=args.outputs,
            max_depth=args.max_depth,
            max_inputs=args.max_inputs,
            max_candidates=args.max_candidates,
            timeout=args.timeout,
        )
        report["yosys_equivalence"] = "not-run"
        report["source_verilog_equivalence"] = "not-run"
        if args.yosys:
            verify(args.yosys.resolve(), output / "original.v", output / "mapped.v", output, args.timeout)
            report["yosys_equivalence"] = "passed"
            if reference_verilog:
                verify(
                    args.yosys.resolve(),
                    reference_verilog,
                    output / "mapped.v",
                    output,
                    args.timeout,
                    reference_top=args.top,
                    name="source-equivalence",
                )
                report["source_verilog_equivalence"] = "passed"
        (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2))
        return 0
    except (OSError, ValueError) as error:
        print(f"Churchroad case study: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
