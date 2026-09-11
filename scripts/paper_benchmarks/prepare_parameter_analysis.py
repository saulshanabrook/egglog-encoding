#!/usr/bin/env python3
"""Prepare relational Egglog facts from the Dis/Equality Graphs parameter analysis."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import shutil
import struct
import urllib.request
import zipfile
from collections.abc import Sequence
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath

ZENODO_RECORD = "13938878"
ARCHIVE_URL = f"https://zenodo.org/api/records/{ZENODO_RECORD}/files/die-graph.zip/content"
ARCHIVE_SHA256 = "3e9080ca461457af0a10cfc433a5150952f82f752b4c316df1e03236d93599c4"
ARCHIVE_MD5 = "fc6661447dcbc1c01a8330db664df094"
SOURCE_SHA256 = "829b712812d7e1c8563e2f9c9dbd5a8b520c967086d05bc407d8f7b733f70638"
SOURCE_SUFFIX = ("parameter-analysis", "exprs.in")
EUF_SOURCE_MEMBER = "euf-solver/benchmarks/smt-uf-non-incremental/sledgehammer/FFT/uf.614981.smt2"
EUF_SOURCE_SHA256 = "3f6de121f080be7d0b8220993fe72610a2bb50dbb80e9e8a21ef9e056335a5da"
NATIVE_MEMBERS = {
    "parameter-analysis/exprs.in": SOURCE_SHA256,
    "parameter-analysis/ee/Cargo.toml": "9cdab4ccf2056c52e769cd1a1a166ef35c76dbc78f7df5d4482602b6b6e1e92c",
    "parameter-analysis/ee/Cargo.lock": "4690e4d57983b95afa299077e1895b0754582e0d4db8f4d6e68e3675eec59584",
    "parameter-analysis/ee/src/main.rs": "191e514134f6db5f9f5f59a53c526d8f9e7a1a40c280e3ca2d37a9f6107b5ed2",
    "parameter-analysis/de/Cargo.toml": "318fbdd403865ca469d521f36cb1d58f2f12cb1c3566c7b8d4040473fb3d0e83",
    "parameter-analysis/de/Cargo.lock": "8246de8558ff9055cf3f1b01ddd586696785cbb17dcb144af6584655e666ca5c",
    "parameter-analysis/de/src/main.rs": "6f657b083321d6fb3a2afd3aa68cca7d29a53b33ab4e1d86a154814420300ef3",
}
SCHEMA_VERSION = 1


def sha256_bytes(data: bytes) -> str:
    """Return a lowercase SHA-256 digest."""

    return hashlib.sha256(data).hexdigest()


def file_digests(path: Path) -> tuple[str, str]:
    """Hash a file once with the two artifact provenance algorithms."""

    sha256 = hashlib.sha256()
    md5 = hashlib.md5(usedforsecurity=False)
    with path.open("rb") as source:
        while chunk := source.read(1024 * 1024):
            sha256.update(chunk)
            md5.update(chunk)
    return sha256.hexdigest(), md5.hexdigest()


def verified_archive(path: Path) -> Path:
    """Reject an archive other than the recorded Zenodo payload."""

    sha256, md5 = file_digests(path)
    if (sha256, md5) != (ARCHIVE_SHA256, ARCHIVE_MD5):
        raise ValueError(
            f"unexpected archive at {path}: expected SHA-256 {ARCHIVE_SHA256} and MD5 {ARCHIVE_MD5}, "
            f"got {sha256} and {md5}"
        )
    return path


def download_archive(cache_path: Path) -> Path:
    """Download the recorded archive atomically, reusing a verified cache."""

    if cache_path.is_file():
        return verified_archive(cache_path)
    cache_path.parent.mkdir(parents=True, exist_ok=True)
    partial = cache_path.with_suffix(cache_path.suffix + ".part")
    request = urllib.request.Request(ARCHIVE_URL, headers={"User-Agent": "egglog-encoding-artifact-review"})
    try:
        with urllib.request.urlopen(request, timeout=60) as response, partial.open("wb") as output:
            shutil.copyfileobj(response, output, length=1024 * 1024)
        verified_archive(partial).replace(cache_path)
    except BaseException:
        partial.unlink(missing_ok=True)
        raise
    return cache_path


def source_member_bytes(path: Path) -> bytes:
    """Read one safe parameter-analysis member without extracting a ZIP."""

    with zipfile.ZipFile(path) as archive:
        candidates = []
        for member in archive.infolist():
            parts = PurePosixPath(member.filename).parts
            if not member.is_dir() and parts[-len(SOURCE_SUFFIX) :] == SOURCE_SUFFIX:
                if ".." in parts:
                    raise ValueError(f"unsafe archive member {member.filename!r}")
                candidates.append(member)
        if len(candidates) != 1:
            names = ", ".join(member.filename for member in candidates)
            raise ValueError(f"expected one */parameter-analysis/exprs.in member, found: {names or 'none'}")
        return archive.read(candidates[0])


def exact_member_bytes(path: Path, name: str, expected_sha256: str) -> bytes:
    """Read one named regular member and verify its recorded content hash."""

    parts = PurePosixPath(name).parts
    if not parts or ".." in parts or PurePosixPath(name).is_absolute():
        raise ValueError(f"unsafe archive member {name!r}")
    with zipfile.ZipFile(path) as archive:
        try:
            member = archive.getinfo(name)
        except KeyError as error:
            raise ValueError(f"archive member is missing: {name}") from error
        if member.is_dir():
            raise ValueError(f"archive member is not a file: {name}")
        data = archive.read(member)
    actual = sha256_bytes(data)
    if actual != expected_sha256:
        raise ValueError(f"unexpected {name} in {path}: expected {expected_sha256}, got {actual}")
    return data


def write_exact_file(output: Path, data: bytes, force: bool) -> None:
    """Write generated content idempotently and reject an unexpected replacement."""

    if output.is_file() and output.read_bytes() == data:
        return
    if output.exists() and not force:
        raise ValueError(f"output already exists: {output}; pass --force to replace it")
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(output.name + ".tmp")
    temporary.write_bytes(data)
    temporary.replace(output)


def extract_native_sources(archive_path: Path, output: Path, disegg_path: Path, force: bool) -> None:
    """Materialize the two published parameter-analysis executables under target/."""

    verified_archive(archive_path)
    if output.exists():
        if not force:
            raise ValueError(f"output already exists: {output}; pass --force to replace it")
        shutil.rmtree(output)
    temporary = output.with_name(output.name + ".tmp")
    shutil.rmtree(temporary, ignore_errors=True)
    try:
        extracted: dict[str, dict[str, object]] = {}
        for archive_name, expected_sha256 in NATIVE_MEMBERS.items():
            data = exact_member_bytes(archive_path, archive_name, expected_sha256)
            relative = Path(archive_name).relative_to("parameter-analysis")
            destination = temporary / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            if relative.name == "Cargo.toml":
                original = data.decode("utf-8")
                if relative == Path("de/Cargo.toml"):
                    dependency = 'disegg = { path = "/disegg/" }'
                    if original.count(dependency) != 1:
                        raise ValueError("published DE manifest no longer has the expected /disegg dependency")
                    relative_disegg = Path(
                        os.path.relpath(disegg_path.resolve(), destination.parent.resolve())
                    ).as_posix()
                    original = original.replace(
                        dependency,
                        f'disegg = {{ path = "{relative_disegg}" }}',
                    )
                data = (original.rstrip() + "\n\n[workspace]\n").encode()
            destination.write_bytes(data)
            extracted[relative.as_posix()] = {
                "archive_member": archive_name,
                "archive_sha256": expected_sha256,
                "generated_sha256": sha256_bytes(data),
            }
        manifest = {
            "schema_version": 1,
            "archive_sha256": ARCHIVE_SHA256,
            "disegg_source": "benchmarks/disequality/disegg",
            "files": extracted,
        }
        (temporary / "manifest.json").write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        output.parent.mkdir(parents=True, exist_ok=True)
        temporary.replace(output)
    except BaseException:
        shutil.rmtree(temporary, ignore_errors=True)
        raise


def source_from_archive(path: Path) -> str:
    """Read the verified parameter-analysis input without extracting the archive."""

    verified_archive(path)
    data = source_member_bytes(path)
    if sha256_bytes(data) != SOURCE_SHA256:
        raise ValueError(f"unexpected exprs.in in {path}")
    return data.decode("utf-8")


def verified_source(path: Path) -> str:
    """Read an explicitly supplied copy of the recorded exprs.in."""

    data = path.read_bytes()
    actual = sha256_bytes(data)
    if actual != SOURCE_SHA256:
        raise ValueError(f"unexpected source at {path}: expected {SOURCE_SHA256}, got {actual}")
    return data.decode("utf-8")


def f32(value: float) -> float:
    """Round one arithmetic operation to IEEE-754 binary32."""

    return float(struct.unpack("!f", struct.pack("!f", value))[0])


def disequality_cutoff(ratio_text: str, line_slots: int, pair_count: int) -> tuple[float, int]:
    """Reproduce the artifact driver's f32 threshold and trailing-line behavior."""

    ratio = f32(float(ratio_text))
    if not math.isfinite(ratio) or not 0.0 <= ratio <= 1.0:
        raise ValueError("ratio must be a finite number between 0 and 1")
    scaled = f32(ratio * f32(float(line_slots)))
    pairs = int(f32(scaled / f32(2.0)))
    return ratio, min(pairs, pair_count)


@dataclass
class Tables:
    """Primitive rows consumed by the parameter-analysis Egglog program."""

    numerals: list[tuple[int, int]] = field(default_factory=list)
    unary: list[tuple[int, int]] = field(default_factory=list)
    binary: list[tuple[int, int, int]] = field(default_factory=list)
    ternary: list[tuple[int, int, int, int]] = field(default_factory=list)
    pairs: list[tuple[int, int, int]] = field(default_factory=list)


class ExpressionParser:
    """Parse the artifact's five numerals and fixed-arity f/g/h expressions."""

    def __init__(self, tables: Tables) -> None:
        self.tables = tables
        self.next_id = 0

    def parse_line(self, source: str, line_number: int) -> int:
        cursor = 0

        def skip_whitespace() -> None:
            nonlocal cursor
            while cursor < len(source) and source[cursor].isspace():
                cursor += 1

        def fresh_id() -> int:
            node_id = self.next_id
            self.next_id += 1
            return node_id

        def parse() -> int:
            nonlocal cursor
            skip_whitespace()
            if cursor < len(source) and source[cursor] in "12345":
                numeral = int(source[cursor])
                cursor += 1
                node_id = fresh_id()
                self.tables.numerals.append((node_id, numeral))
                return node_id
            if cursor >= len(source) or source[cursor] != "(":
                raise ValueError(f"line {line_number}: expected an expression at character {cursor + 1}")
            cursor += 1
            skip_whitespace()
            if cursor >= len(source) or source[cursor] not in "fgh":
                raise ValueError(f"line {line_number}: expected f, g, or h at character {cursor + 1}")
            function = source[cursor]
            cursor += 1
            arity = {"f": 1, "g": 2, "h": 3}[function]
            children = tuple(parse() for _ in range(arity))
            skip_whitespace()
            if cursor >= len(source) or source[cursor] != ")":
                raise ValueError(f"line {line_number}: expected ')' at character {cursor + 1}")
            cursor += 1
            node_id = fresh_id()
            if function == "f":
                self.tables.unary.append((node_id, children[0]))
            elif function == "g":
                self.tables.binary.append((node_id, children[0], children[1]))
            else:
                self.tables.ternary.append((node_id, children[0], children[1], children[2]))
            return node_id

        root = parse()
        skip_whitespace()
        if cursor != len(source):
            raise ValueError(f"line {line_number}: unexpected input at character {cursor + 1}")
        return root


def parse_source(source: str) -> tuple[Tables, int, int]:
    """Parse every expression and pair consecutive roots without interning."""

    lines = source.splitlines()
    if len(lines) % 2 != 0:
        raise ValueError("artifact input must contain an even number of expressions")
    tables = Tables()
    parser = ExpressionParser(tables)
    roots = [parser.parse_line(line, index) for index, line in enumerate(lines, start=1)]
    tables.pairs.extend(
        (pair_id, roots[offset], roots[offset + 1]) for pair_id, offset in enumerate(range(0, len(roots), 2))
    )
    return tables, parser.next_id, len(source.split("\n"))


def encode_rows(rows: Sequence[Sequence[int]]) -> bytes:
    """Encode integer rows in egglog's tab-separated input format."""

    return "".join("\t".join(map(str, row)) + "\n" for row in rows).encode()


def materialized_files(source: str, ratio_text: str) -> dict[str, bytes]:
    """Return every deterministic output file, including its manifest."""

    tables, node_count, line_slots = parse_source(source)
    ratio, cutoff = disequality_cutoff(ratio_text, line_slots, len(tables.pairs))
    files = {
        "numerals.tsv": encode_rows(tables.numerals),
        "f.tsv": encode_rows(tables.unary),
        "g.tsv": encode_rows(tables.binary),
        "h.tsv": encode_rows(tables.ternary),
        "pairs.tsv": encode_rows(tables.pairs),
        "config.tsv": encode_rows(((cutoff,),)),
    }
    row_counts = {
        "numerals.tsv": len(tables.numerals),
        "f.tsv": len(tables.unary),
        "g.tsv": len(tables.binary),
        "h.tsv": len(tables.ternary),
        "pairs.tsv": len(tables.pairs),
        "config.tsv": 1,
    }
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "artifact": {
            "zenodo_record": ZENODO_RECORD,
            "archive_url": ARCHIVE_URL,
            "archive_sha256": ARCHIVE_SHA256,
            "archive_md5": ARCHIVE_MD5,
            "source_member_suffix": "/".join(SOURCE_SUFFIX),
            "source_sha256": sha256_bytes(source.encode()),
        },
        "generation": {
            "ratio_text": ratio_text,
            "ratio_f32": ratio,
            "source_line_slots": line_slots,
            "expressions": len(tables.pairs) * 2,
            "pairs": len(tables.pairs),
            "disequality_pairs": cutoff,
            "equality_pairs": len(tables.pairs) - cutoff,
            "nodes": node_count,
            "node_ids": "unique per AST occurrence, allocated postorder",
        },
        "files": {
            name: {
                "sha256": sha256_bytes(data),
                "bytes": len(data),
                "rows": row_counts[name],
            }
            for name, data in sorted(files.items())
        },
    }
    files["manifest.json"] = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()
    return files


def write_files(output: Path, files: dict[str, bytes], force: bool) -> None:
    """Write a complete generated directory, rejecting accidental replacement."""

    if output.exists():
        if not force:
            raise ValueError(f"output already exists: {output}; pass --force to replace it")
        shutil.rmtree(output)
    output.mkdir(parents=True)
    for name, data in files.items():
        (output / name).write_bytes(data)


def compare_files(output: Path, files: dict[str, bytes]) -> None:
    """Fail when committed generated data differs from fresh output."""

    actual_names = {path.name for path in output.iterdir() if path.is_file()}
    if actual_names != set(files):
        raise ValueError(f"generated file set differs: expected {sorted(files)}, got {sorted(actual_names)}")
    changed = [name for name, data in files.items() if (output / name).read_bytes() != data]
    if changed:
        raise ValueError(f"generated files differ: {', '.join(sorted(changed))}")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--input", type=Path, help="Previously extracted artifact exprs.in")
    source.add_argument("--download", action="store_true", help="Download and cache the verified Zenodo archive")
    parser.add_argument("--archive-cache", type=Path, help="Archive cache path used with --download")
    parser.add_argument("--ratio", default="0.5", help="Candidate disequality ratio using artifact f32 semantics")
    parser.add_argument("--output", type=Path, help="Generated fact directory")
    parser.add_argument("--archive-only", action="store_true", help="Only download and verify the archive")
    parser.add_argument("--extract-euf", type=Path, help="Extract the recorded uf.614981 input")
    parser.add_argument("--extract-native", type=Path, help="Extract the parameter-analysis native crates")
    parser.add_argument("--disegg-path", type=Path, help="Patched disegg checkout used by --extract-native")
    parser.add_argument("--force", action="store_true", help="Replace an existing output directory")
    parser.add_argument("--check", action="store_true", help="Compare generated bytes with an existing output")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if args.check and args.force:
        raise ValueError("--check and --force cannot be combined")
    actions = (
        args.output is not None,
        args.archive_only,
        args.extract_euf is not None,
        args.extract_native is not None,
    )
    if sum(actions) != 1:
        raise ValueError("select exactly one of --output, --archive-only, --extract-euf, or --extract-native")
    if (args.archive_only or args.extract_euf or args.extract_native) and not args.download:
        raise ValueError("archive extraction requires --download")
    if args.check and args.output is None:
        raise ValueError("--check applies only to --output")

    cache = args.archive_cache or Path.home() / ".cache/egglog-encoding/disequality/die-graph.zip"
    if args.archive_only:
        print(download_archive(cache))
        return 0
    if args.extract_euf is not None:
        archive = download_archive(cache)
        data = exact_member_bytes(archive, EUF_SOURCE_MEMBER, EUF_SOURCE_SHA256)
        write_exact_file(args.extract_euf, data, args.force)
        return 0
    if args.extract_native is not None:
        if args.disegg_path is None:
            raise ValueError("--extract-native requires --disegg-path")
        extract_native_sources(download_archive(cache), args.extract_native, args.disegg_path, args.force)
        return 0

    assert args.output is not None
    source = verified_source(args.input) if args.input is not None else source_from_archive(download_archive(cache))
    files = materialized_files(source, args.ratio)
    if args.check:
        compare_files(args.output, files)
    else:
        write_files(args.output, files, args.force)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
