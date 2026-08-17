#!/usr/bin/env python3
"""Generate compact source snapshots for the EUF and Propel integrations."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

ENCODINGS = ("ee", "oee", "nee", "de")
TREATMENTS = {
    "ordinary": (),
    "term": ("--term-encoding",),
    "proofs": ("--proofs",),
    "proof-testing": ("--proof-testing",),
    "proof-extraction": ("--proof-extraction",),
}


def run_checked(command: list[str], description: str, success_suffix: str) -> None:
    process = subprocess.run(
        command,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if process.returncode != 0:
        raise RuntimeError(f"{description} failed:\n{process.stdout}")
    if not any(line.strip().endswith(success_suffix) for line in process.stdout.splitlines()):
        raise RuntimeError(f"{description} produced no success marker:\n{process.stdout}")


def validate_direct_snapshot(contents: bytes, sort_name: str, description: str) -> None:
    source = contents.decode()
    required = (f"(sort {sort_name})", f"(constructor Atom (String) {sort_name})")
    forbidden = ("BenchmarkNode", "BenchmarkTerms", "vec-of")
    missing = [fragment for fragment in required if fragment not in source]
    present = [fragment for fragment in forbidden if fragment in source]
    if missing or present:
        raise RuntimeError(
            f"{description} is not a direct-constructor snapshot: missing={missing}, forbidden={present}",
        )


def replay_all_treatments(binary: Path, encoding: str | None, path: Path) -> None:
    for treatment, treatment_args in TREATMENTS.items():
        command = [str(binary), *treatment_args]
        if encoding is not None:
            command.extend(("--disequality-encoding", encoding))
        command.append(str(path))
        process = subprocess.run(
            command,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        if process.returncode != 0:
            encoding_label = encoding or "desugared"
            raise RuntimeError(f"replaying {path} with {encoding_label}/{treatment} failed:\n{process.stdout}")


def replay_snapshots(binary: Path, output: Path) -> int:
    replay_count = 0
    for path in sorted(output.rglob("*.egg")):
        if path.name.endswith(".desugared.egg"):
            replay_all_treatments(binary, None, path)
            replay_count += len(TREATMENTS)
        else:
            for encoding in ENCODINGS:
                replay_all_treatments(binary, encoding, path)
                replay_count += len(TREATMENTS)
    return replay_count


def generate(args: argparse.Namespace) -> dict[Path, bytes]:
    output: dict[Path, bytes] = {}
    manifest: dict[str, object] = {
        "schema_version": 3,
        "encodings": list(ENCODINGS),
        "replay_treatments": list(TREATMENTS),
        "euf": {},
        "propel": {},
    }
    with tempfile.TemporaryDirectory(prefix="egglog-disequality-snapshots-") as temporary:
        temporary_path = Path(temporary)

        euf_sources: list[bytes] = []
        euf_input = args.euf_input.resolve()
        for encoding in ENCODINGS:
            directory = temporary_path / "euf" / encoding
            directory.mkdir(parents=True)
            run_checked(
                [
                    str(args.euf_binary.resolve()),
                    "--backend",
                    f"egglog-{encoding}",
                    "--term-language",
                    "direct",
                    "--emit-source-dir",
                    str(directory),
                    str(euf_input),
                ],
                f"EUF {encoding}",
                ": sat",
            )
            raw = sorted(directory.glob("*.egg"))
            raw = [path for path in raw if not path.name.endswith(".desugared.egg")]
            desugared = sorted(directory.glob("*.desugared.egg"))
            if len(raw) != 1 or len(desugared) != 1:
                raise RuntimeError(f"EUF {encoding} emitted {len(raw)} raw and {len(desugared)} desugared snapshots")
            raw_source = raw[0].read_bytes()
            validate_direct_snapshot(raw_source, "EufTerm", f"EUF {encoding}")
            euf_sources.append(raw_source)
            output[Path("euf") / f"sat.{encoding}.desugared.egg"] = desugared[0].read_bytes()
        if len(set(euf_sources)) != 1:
            raise RuntimeError("EUF encodings emitted different pre-desugaring programs")
        output[Path("euf") / "sat.egg"] = euf_sources[0]
        manifest["euf"] = {
            "input": "euf-solver/tests/sat.smt2",
            "input_sha256": hashlib.sha256(euf_input.read_bytes()).hexdigest(),
            "model_count": 1,
            "term_language": "direct",
        }

        propel_sources: list[bytes] = []
        graph_counts: list[int] = []
        propel_input = args.propel_input.resolve()
        selected_index: int | None = None
        for encoding in ENCODINGS:
            directory = temporary_path / "propel" / encoding
            directory.mkdir(parents=True)
            run_checked(
                [
                    str(args.propel_binary.resolve()),
                    "-f",
                    str(propel_input),
                    "--variant",
                    f"egglog-{encoding}",
                    "--term-language",
                    "direct",
                    "--emit-source-dir",
                    str(directory),
                ],
                f"Propel {encoding}",
                "Check successful.",
            )
            raw = sorted(directory.glob("*.egg"))
            raw = [path for path in raw if not path.name.endswith(".desugared.egg")]
            desugared = sorted(directory.glob("*.desugared.egg"))
            if not raw or len(raw) != len(desugared):
                raise RuntimeError(f"Propel {encoding} emitted {len(raw)} raw and {len(desugared)} desugared snapshots")
            graph_counts.append(len(raw))
            index = len(raw) - 1 if args.propel_graph_index < 0 else args.propel_graph_index
            if index >= len(raw):
                raise RuntimeError(f"Propel graph index {index} is outside the {len(raw)} emitted graphs")
            selected_index = index
            raw_source = raw[index].read_bytes()
            validate_direct_snapshot(raw_source, "PropelTerm", f"Propel {encoding}")
            propel_sources.append(raw_source)
            output[Path("propel") / f"gset_comm.{encoding}.desugared.egg"] = desugared[index].read_bytes()
        if len(set(graph_counts)) != 1:
            raise RuntimeError(f"Propel encodings emitted different graph counts: {graph_counts}")
        if len(set(propel_sources)) != 1:
            raise RuntimeError("Propel encodings emitted different pre-desugaring programs")
        output[Path("propel") / "gset_comm.egg"] = propel_sources[0]
        manifest["propel"] = {
            "input": "inductive-prover/benchmarks/propel/gset_comm.propel",
            "input_sha256": hashlib.sha256(propel_input.read_bytes()).hexdigest(),
            "graph_count": graph_counts[0],
            "selected_graph_index": selected_index,
            "term_language": "direct",
        }

    files = {
        str(path): hashlib.sha256(contents).hexdigest()
        for path, contents in sorted(output.items(), key=lambda item: str(item[0]))
    }
    manifest["files"] = files
    output[Path("manifest.json")] = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()
    return output


def main() -> int:
    root = Path(__file__).resolve().parents[3]
    case_study = root / "benchmarks" / "disequality"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--euf-binary",
        type=Path,
        default=case_study / "euf-solver" / "target" / "debug" / "euf-solver",
    )
    parser.add_argument(
        "--euf-input",
        type=Path,
        default=case_study / "euf-solver" / "tests" / "sat.smt2",
    )
    parser.add_argument(
        "--propel-binary",
        type=Path,
        default=case_study / "inductive-prover" / "propel" / ".native" / "target" / "scala-3.4.2" / "propel",
    )
    parser.add_argument(
        "--egglog-binary",
        type=Path,
        default=root / "target" / "debug" / "egglog-experimental",
    )
    parser.add_argument(
        "--propel-input",
        type=Path,
        default=case_study / "inductive-prover" / "benchmarks" / "propel" / "gset_comm.propel",
    )
    parser.add_argument("--propel-graph-index", type=int, default=-1)
    parser.add_argument(
        "--output",
        type=Path,
        default=case_study / "snapshots",
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--force", action="store_true")
    mode.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    required_binaries = (
        (args.egglog_binary,)
        if args.replay
        else (
            args.euf_binary,
            args.propel_binary,
            args.egglog_binary,
        )
    )
    for binary in required_binaries:
        if not binary.is_file():
            parser.error(f"binary does not exist: {binary}")

    if args.replay:
        if not args.output.is_dir():
            parser.error(f"snapshot directory does not exist: {args.output}")
        replay_count = replay_snapshots(args.egglog_binary.resolve(), args.output)
        print(f"replayed {replay_count} treatments from {args.output}")
        return 0

    generated = generate(args)
    existing = (
        {path.relative_to(args.output): path.read_bytes() for path in args.output.rglob("*") if path.is_file()}
        if args.output.is_dir()
        else {}
    )
    if args.check:
        if generated != existing:
            missing = sorted(str(path) for path in generated.keys() - existing.keys())
            extra = sorted(str(path) for path in existing.keys() - generated.keys())
            changed = sorted(
                str(path) for path in generated.keys() & existing.keys() if generated[path] != existing[path]
            )
            raise SystemExit(f"snapshot mismatch: missing={missing}, extra={extra}, changed={changed}")
        replay_count = replay_snapshots(args.egglog_binary.resolve(), args.output)
        print(f"verified {len(generated)} files and replayed {replay_count} treatments in {args.output}")
        return 0

    args.output.mkdir(parents=True, exist_ok=True)
    for path in existing.keys() - generated.keys():
        (args.output / path).unlink()
    for path, contents in generated.items():
        destination = args.output / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(contents)
    replay_count = replay_snapshots(args.egglog_binary.resolve(), args.output)
    print(f"wrote {len(generated)} files and replayed {replay_count} treatments in {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
