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


def run_checked(command: list[str], description: str) -> None:
    process = subprocess.run(
        command,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if process.returncode != 0:
        raise RuntimeError(f"{description} failed:\n{process.stdout}")
    if "sat" not in process.stdout.lower() and "Check successful." not in process.stdout:
        raise RuntimeError(f"{description} produced no success marker:\n{process.stdout}")


def replay(binary: Path, encoding: str | None, path: Path) -> None:
    command = [str(binary)]
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
        raise RuntimeError(f"replaying {path} failed:\n{process.stdout}")


def generate(args: argparse.Namespace) -> dict[Path, bytes]:
    output: dict[Path, bytes] = {}
    manifest: dict[str, object] = {
        "schema_version": 1,
        "encodings": list(ENCODINGS),
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
                    "--emit-source-dir",
                    str(directory),
                    str(euf_input),
                ],
                f"EUF {encoding}",
            )
            raw = sorted(directory.glob("*.egg"))
            raw = [path for path in raw if not path.name.endswith(".desugared.egg")]
            desugared = sorted(directory.glob("*.desugared.egg"))
            if len(raw) != 1 or len(desugared) != 1:
                raise RuntimeError(f"EUF {encoding} emitted {len(raw)} raw and {len(desugared)} desugared snapshots")
            euf_sources.append(raw[0].read_bytes())
            output[Path("euf") / f"sat.{encoding}.desugared.egg"] = desugared[0].read_bytes()
        if len(set(euf_sources)) != 1:
            raise RuntimeError("EUF encodings emitted different pre-desugaring programs")
        output[Path("euf") / "sat.egg"] = euf_sources[0]
        manifest["euf"] = {
            "input": "euf-solver/tests/sat.smt2",
            "input_sha256": hashlib.sha256(euf_input.read_bytes()).hexdigest(),
            "model_count": 1,
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
                    "--emit-source-dir",
                    str(directory),
                ],
                f"Propel {encoding}",
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
            propel_sources.append(raw[index].read_bytes())
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
    parser.add_argument("--propel-binary", type=Path, required=True)
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
    args = parser.parse_args()
    for binary in (args.euf_binary, args.propel_binary, args.egglog_binary):
        if not binary.is_file():
            parser.error(f"binary does not exist: {binary}")

    generated = generate(args)
    with tempfile.TemporaryDirectory(prefix="egglog-disequality-replay-") as temporary:
        temporary_path = Path(temporary)
        for path, contents in generated.items():
            if path.suffix != ".egg":
                continue
            destination = temporary_path / path
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(contents)
            encoding = None
            if not path.name.endswith(".desugared.egg"):
                encoding = next(
                    (candidate for candidate in ENCODINGS if f".{candidate}." in path.name),
                    "ee",
                )
            replay(args.egglog_binary.resolve(), encoding, destination)
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
        print(f"verified {len(generated)} files in {args.output}")
        return 0

    args.output.mkdir(parents=True, exist_ok=True)
    for path in existing.keys() - generated.keys():
        (args.output / path).unlink()
    for path, contents in generated.items():
        destination = args.output / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(contents)
    print(f"wrote {len(generated)} files to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
