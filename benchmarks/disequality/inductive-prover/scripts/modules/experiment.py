################################################################################
# experiment.py
# The logic for running an experiment.
################################################################################

import subprocess
import sys
import time
import argparse
import json

from modules.benchmark import *
from modules.printing import *
from modules.performance import *
from modules.util import *

# Command line arguments
class Args:
    """The command line arguments of this script."""
    def __init__(self):
        self.raw = None
        self.parser = argparse.ArgumentParser(description="evaluate a Propel binary against Propel's benchmarks")
        self.parser.add_argument(
            "-b", "--binary",
            type=str,
            default="/usr/local/bin/propel",
            help="the Propel binary to use for evaluation [default: /usr/local/bin/propel]"
        )
        self.parser.add_argument(
            "-v", "--variant",
            type=str,
            default="de",
            help="the egraph variant to use in propel: either de, ee, or nee. [default: de]"
        )
        self.parser.add_argument(
            "-d", "--disable-disequalities",
            action="store_true",
            default=False,
            help="disable disequalities when running the propel binary [default: False]"
        )
        self.parser.add_argument(
            "-t", "--timeout",
            type=int,
            default=60,
            help="the default timeout in seconds before considering a benchmark as timed out [default: 60]"
        )
        self.parser.add_argument(
            "-i", "--input",
            type=str,
            default="/inductive-prover/benchmarks/propel",
            help=(
                "the input directory where the .propel benchmarks are contained or one of the following built-in benchmarks:"
                " Available built-in benchmarks are:"
                " @builtin: the set of builtin benchmarks of propel;"
                " @tip: the subset of tip benchmarks inside @builtin;"
                " [default: /inductive-prover/benchmarks/propel]"
            )
        )
        self.parser.add_argument(
            "-o", "--output",
            type=str,
            default=os.path.join(".output"),
            help="the output directory where the evaluation results are contained [default: ./.output]"
        )
        self.parser.add_argument(
            "-f", "--filename",
            type=str,
            default=f"{Id.tid()}",
            help="the name of the output files generated during the evaluation [default: <current-time>]"
        )
        self.parser.add_argument(
            "-j", "--build-json",
            action="store_true",
            default=False,
            help="enable the creation of a FILENAME.json file with the results [default: False]"
        ),
        self.parser.add_argument(
            "-c", "--build-csv",
            action="store_true",
            default=False,
            help="enable the creation of a FILENAME.csv file with the results [default: False]"
        )

    def parse(self):
        """Initialise these command line arguments."""
        self.raw = self.parser.parse_args()
        return self

    def propel(self): return self.raw.binary
    def egraph_variant(self): return self.raw.variant
    def disable_disequalities(self): return self.raw.disable_disequalities
    def should_build_json(self): return self.raw.build_json
    def should_build_csv(self): return self.raw.build_csv
    def timeout(self): return self.raw.timeout
    def input(self): return self.raw.input
    def output_directory(self): return self.raw.output
    def output_filename(self): return self.raw.filename
    def benchmark_path(self):
        input = self.raw.input
        if input == "@propel":
            return Benchmarks.Propel.DefaultPath
        else:
            return None if input.startswith("@") else input
    def benchmarks(self):
        input = self.raw.input
        if input == "@builtin":
            return Benchmarks.Builtin.All
        elif input == "@tip":
            return Benchmarks.Builtin.TipBenchmarks
        else:
            return Benchmarks.Propel.load_propel_benchmarks(input)

# Entry point of the script
def experiment(args):
    output_file = os.path.join(args.output_directory(), args.output_filename())
    txt_output_file = output_file + ".txt"
    os.makedirs(name=args.output_directory(), exist_ok=True)
    console = Logger(output_file=txt_output_file)

    # Print the configuration of the experiment
    console.log("Configuration:")
    console.push()
    console.log("Python Version:", sys.version.replace('\n', ''))
    console.log("Input Benchmarks:", args.input())
    console.log("Benchmarks:", len(args.benchmarks()))
    console.log("Working Directory:", os.getcwd())
    console.log("Output File:", output_file)
    if os.path.exists(args.propel()):
        console.log("Propel Binary:", args.propel())
    else:
        console.log("Command", args.propel(), "not found.")
        raise ValueError("Invalid path to propel binary.")
    console.log("EGraph Variant:", args.egraph_variant().upper())
    console.log("Disequalities:", "Disabled" if args.disable_disequalities() else "Enabled")
    console.log("Timeout:", f"{args.timeout()}s")
    console.log("Build Json:", f"{args.should_build_json()}")
    console.log("Build CSV:", f"{args.should_build_csv()}")
    console.pop()

    # Execute the experiment
    console.log("Execution:")
    console.push()
    table = PerformanceTableLogger(console)
    performances = Performances()
    propel_command = (
        [args.propel(), "--variant", args.egraph_variant()] +
        (["-b"] if args.benchmark_path() is None else ["-f"])
    )
    for benchmark in sorted(args.benchmarks()):
        benchmark_name = benchmark.removesuffix(".propel")
        benchmark_id = benchmark if args.benchmark_path() is None else os.path.join(args.benchmark_path(), benchmark)
        try:
            command = propel_command + [benchmark_id] + (["--no-ineq"] if args.disable_disequalities() else [])
            start_time_ns = time.time_ns()
            process = subprocess.run(args=command, timeout=args.timeout(), stdout=subprocess.PIPE, universal_newlines=True)
            end_time_ns = time.time_ns()
            duration_ns = end_time_ns - start_time_ns
            [result_line, stats_line] = process.stdout.splitlines()[-2:]
            [n_egraphs, n_eclasses, n_enodes] = [float(n_str) for n_str in stats_line.split(";")[1:]]
            result = None
            if "✔" in result_line:
                result = Success.singleton()
            elif "✘" in result_line:
                result = Failure.singleton()
            else:
                console.log(process.stdout)
                console.log(process.stderr)
            performances.update(benchmark_name, Performance(n_egraphs, n_eclasses, n_enodes, duration_ns, result))
        except subprocess.TimeoutExpired:
            performances.update(benchmark_name, Performance(0, 0, 0, args.timeout() * 1e9, Timeout.singleton()))
        finally:
            table.log_performance_row(benchmark_name, performances.get(benchmark_name))
    performance_sum = Performance.sum(list(performances.entries.values()))
    performance_average = performance_sum.average()
    table.log_line()
    table.log_performance_row("Total", performance_sum)
    table.log_performance_row("Average", performance_average)
    console.pop()

    # Print the results of the experiment
    console.log("Results:")
    console.push()
    results = performance_sum.result.as_collection()
    console.log("Successes:", results.n_successes, "✔")
    console.log("Failures:", results.n_failures, "✘")
    console.log("Timeouts:", results.n_timeouts, "⧗")
    console.pop()

    # Save the results of the experiment
    if args.should_build_json():
        json_output_file = output_file + ".json"
        with open(json_output_file, "w") as file:
            print(json.dumps(performances.to_json(), indent=2), file=file)

    if args.should_build_csv():
        csv_output_file = output_file + ".csv"
        with open(csv_output_file, "w") as file:
            csv_rows = []
            csv_header = ["Benchmark", "# Equalities", "# EClasses", "# ENodes", "NodePerClass", "Duration (ns)", "Result"]
            csv_rows.append(csv_header)
            for (benchmark, performance) in performances.entries.items():
                csv_row = [benchmark, performance.n_egraphs, performance.n_classes, performance.n_enodes, performance.enode_per_class(), performance.duration_ns, performance.result]
                csv_rows.append(csv_row)
            for (benchmark, performance) in [("Total", performance_sum), ("Average", performance_average)]:
                csv_row = [benchmark, performance.n_egraphs, performance.n_classes, performance.n_enodes, performance.enode_per_class(), performance.duration_ns, performance.result]
                csv_rows.append(csv_row)
            csv = '\n'.join([",".join([str(col) for col in row]) for row in csv_rows])
            print(csv, file=file)

    return performances