"""Resolve and validate benchmark workload files shared by run and profile modes.

This module owns the default workload suite, invocation-relative file
resolution, content identities, and the rule that measured inputs do
not execute ``(prove ...)``. CLI parsing and endpoint selection belong in their
respective command modules.
"""

from __future__ import annotations

import glob
import json
import re
from collections.abc import Iterator, Sequence
from dataclasses import replace
from pathlib import Path

from .engines import TREATMENT_SPECS, TREATMENTS
from .models import Exclusion, FileSpec, validate_unique_file_identities
from .targets import sha256_file

DEFAULT_WORKLOADS = (
    "egglog-experimental/tests/math-microbenchmark-rational.egg",
    "egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg",
    "egglog/tests/hardboiled_conv1d_32.egg",
    "egglog/tests/luminal-llama.egg",
    "egglog/tests/web-demo/herbie.egg",
    "egglog/tests/papers/misaal-hvx-dot-product.egg",
    "egglog/tests/papers/churchroad-wide-multiply.egg",
    "egglog-experimental/tests/papers/dialegg-nmm40.egg",
    "egglog/tests/papers/speq-preserved-reference-suite.egg",
    "benchmarks/disequality/parameter-analysis.egg",
)
IGNORE_FILE = Path(__file__).resolve().parents[1] / "benchmarks/ignore.json"


def resolve_files(
    raw_files: Sequence[str],
    invocation_cwd: Path,
    *,
    ignore_file: Path = IGNORE_FILE,
) -> tuple[FileSpec, ...]:
    """Resolve selected or default workloads relative to the invocation directory."""

    chosen = raw_files or DEFAULT_WORKLOADS
    rules = json.loads(ignore_file.read_text())
    if not isinstance(rules, list):
        raise ValueError("benchmark ignore file must contain a list")
    matched_paths: dict[str, set[Path]] = {}
    for rule in rules:
        if (
            not isinstance(rule, dict)
            or not {"file", "kind", "reason", "evidence"} <= set(rule)
            or set(rule)
            - {
                "file",
                "kind",
                "reason",
                "evidence",
                "treatments",
                "memory_limit_bytes",
                "expected_table_sizes",
            }
            or any(not isinstance(rule[key], str) or not rule[key].strip() for key in ("file", "reason", "evidence"))
            or rule["kind"] not in ("resource", "unsupported", "expected-failure")
            or not isinstance(rule.get("treatments", []), list)
            or any(t not in TREATMENTS for t in rule.get("treatments", []))
            or (
                "memory_limit_bytes" in rule
                and (
                    type(rule["memory_limit_bytes"]) is not int
                    or rule["memory_limit_bytes"] < 1
                    or rule["kind"] != "resource"
                )
            )
        ):
            raise ValueError(f"invalid benchmark exclusion: {rule!r}")
        if rule["kind"] == "expected-failure":
            sizes = rule.get("expected_table_sizes")
            if (
                not isinstance(sizes, dict)
                or not sizes
                or any(not isinstance(name, str) or not name for name in sizes)
                or any(
                    not isinstance(pair, list)
                    or len(pair) != 2
                    or any(type(value) is not int or value < 0 for value in pair)
                    for pair in sizes.values()
                )
                or any(pair[0] == pair[1] for pair in sizes.values())
                or len(rule.get("treatments", [])) != 1
                or rule["treatments"][0] not in ("term", "proof-testing")
                or glob.has_magic(rule["file"])
            ):
                raise ValueError("expected failures require one exact file/treatment and recorded table-size pairs")
        elif "expected_table_sizes" in rule:
            raise ValueError("table-size failure expectations require kind expected-failure")
        if ".." in Path(rule["file"]).parts or Path(rule["file"]).is_absolute():
            raise ValueError("exclusion patterns must stay inside benchmarks/")
        matched_paths[rule["file"]] = {
            Path(path).resolve()
            for path in glob.glob(str(ignore_file.parent / rule["file"]), recursive=True)
            if Path(path).is_file()
        }
        if not matched_paths[rule["file"]]:
            raise ValueError(f"exclusion pattern matched nothing: {rule['file']}")
    files: list[FileSpec] = []
    for display_path in chosen:
        absolute_path = Path(display_path).expanduser()
        if not absolute_path.is_absolute():
            absolute_path = invocation_cwd / absolute_path
        absolute_path = absolute_path.resolve()
        if not absolute_path.is_file():
            raise FileNotFoundError(f"benchmark file does not exist: {display_path}")

        logical_path = absolute_path.with_suffix(".egg")
        if absolute_path.suffix not in (".ref", ".in") or not logical_path.is_file():
            logical_path = absolute_path
        files.append(
            FileSpec(
                display_path=display_path,
                absolute_path=absolute_path,
                sha256=sha256_file(absolute_path),
                exclusions=tuple(
                    Exclusion.from_json(rule) for rule in rules if logical_path in matched_paths[rule["file"]]
                ),
            )
        )
    for index, file in enumerate(files):
        representations = []
        for binary_name, specification in {spec.binary_name: spec for spec in TREATMENT_SPECS.values()}.items():
            suffix = specification.input_suffix
            if suffix == file.absolute_path.suffix:
                continue
            native_path = file.absolute_path.with_suffix(suffix)
            if not native_path.is_file():
                continue
            native = replace(
                file,
                display_path=str(Path(file.display_path).with_suffix(suffix)),
                absolute_path=native_path,
                sha256=sha256_file(native_path),
            )
            representations.append((binary_name, native))
        files[index] = replace(file, binary_inputs=tuple(representations))
    resolved = tuple(files)
    validate_workloads(resolved)
    return resolved


def exclusion_bindings(files: Sequence[FileSpec]) -> dict[str, tuple[Exclusion, ...]]:
    """Freeze the current policy for every excluded input, including later retargeting.

    Exclusions belong to the invocation's grouped snapshot, never synthetic raw
    observations. Hash only the small explicit ignore list beyond selected files.
    """
    # A browser can retarget to any cached input, including one outside the
    # current invocation, so embed all current hash-to-rule bindings.
    entries = [
        (physical.sha256, rule)
        for logical in files
        for physical in (logical, *(file for _, file in logical.binary_inputs))
        for rule in logical.exclusions
    ]
    suffixes = {specification.input_suffix for specification in TREATMENT_SPECS.values()}
    for rule in json.loads(IGNORE_FILE.read_text()):
        exclusion = Exclusion.from_json(rule)
        paths = glob.glob(str(IGNORE_FILE.parent / rule["file"]), recursive=True)
        physical = {Path(path).with_suffix(suffix) for path in paths for suffix in suffixes}
        entries.extend((sha256_file(path), exclusion) for path in sorted(physical) if path.is_file())
    bindings: dict[str, list[Exclusion]] = {}
    for identity, rule in dict.fromkeys(entries):
        bindings.setdefault(identity, []).append(rule)
    return {identity: tuple(rules) for identity, rules in bindings.items()}


def _egglog_tokens(source: str) -> Iterator[str]:
    """Yield raw parentheses, atoms and quoted strings, skipping comments."""

    index = 0
    while index < len(source):
        character = source[index]
        if character.isspace():
            index += 1
            continue
        if character == ";":
            newline = source.find("\n", index)
            index = len(source) if newline == -1 else newline + 1
            continue
        if character == '"':
            start = index
            index += 1
            while index < len(source):
                if source[index] == "\\":
                    index += 2
                elif source[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            yield source[start:index]
            continue
        if character in "()":
            yield character
            index += 1
            continue
        end = index
        while end < len(source) and not source[end].isspace() and source[end] not in ";()":
            end += 1
        yield source[index:end]
        index = end


def require_workload_unchanged(file_spec: FileSpec) -> None:
    """Reject an observation if its mutable inputs no longer match their cache identity."""

    try:
        file_sha256 = sha256_file(file_spec.absolute_path) if file_spec.absolute_path.is_file() else None
    except OSError as error:
        raise ValueError(f"workload changed during execution: {file_spec.display_path}") from error
    if file_sha256 != file_spec.sha256:
        raise ValueError(f"workload changed during execution: {file_spec.display_path}")


def validate_workloads(files: Sequence[FileSpec]) -> None:
    """Require self-contained programs without external input or include commands."""

    validate_unique_file_identities(files)
    for file in files:
        if file.absolute_path.suffix != ".egg":
            continue
        source = file.absolute_path.read_text(encoding="utf-8")
        # Includes and CSV inputs require strings; the large generated inputs have none.
        if '"' not in source:
            uncommented = re.sub(r";[^\n]*", "", source)
            if not any(word in uncommented for word in ("include", "input", "prove")):
                continue
        forms: list[list[str]] = []
        for token in _egglog_tokens(source):
            if token == "(":
                forms.append([])
            elif token == ")" and forms:
                form = forms.pop()
                if not form:
                    continue
                if form[0] in ("include", "input"):
                    raise ValueError(
                        f"{file.display_path}: benchmark inputs must be self-contained; expand {form[0]} commands first"
                    )
                if not forms and form[0] in ("prove", "prove-extract"):
                    raise ValueError(
                        f"{file.display_path} contains an explicit prove command; "
                        "benchmark files should use check or extract so the selected treatment "
                        "controls proof extraction"
                    )
            elif forms:
                forms[-1].append(token)
