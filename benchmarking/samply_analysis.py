"""Read, symbolicate, summarize, and present saved Samply profile artifacts.

Profile execution, caching, calibration, and viewer lifecycle belong in ``profile``.
"""

from __future__ import annotations

import gzip
import json
import os
import re
import shlex
import shutil
import subprocess
from collections import defaultdict
from collections.abc import Iterator, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal, cast

from rich import box
from rich.console import Console
from rich.table import Table
from rich.text import Text

ATOS_BATCH_SIZE = 512


@dataclass(frozen=True)
class ProfileFunctionCpu:
    name: str
    cpu_seconds: float


@dataclass(frozen=True)
class ProfileCpuSummary:
    observed_cpu_seconds: float
    application_cpu_seconds: float
    other_library_cpu_seconds: float
    unattributed_cpu_seconds: float
    symbolized_application_cpu_seconds: float
    functions: tuple[ProfileFunctionCpu, ...]
    warnings: tuple[str, ...]


@dataclass(frozen=True)
class ProfileReport:
    artifact: Path
    cache_status: Literal["hit", "recorded"]
    workload: str
    backend: str
    treatment: str
    top: int
    cpu_summary: ProfileCpuSummary | None


@dataclass(frozen=True)
class LeafSample:
    cpu_seconds: float
    library_index: int | None
    function_name: str | None
    relative_address: int | None


def read_artifact(path: Path) -> dict[str, Any]:
    try:
        if not path.is_file() or path.stat().st_size == 0:
            raise ValueError(f"profile artifact is missing or empty: {path}")
        with path.open("rb") as handle:
            if handle.read(2) != b"\x1f\x8b":
                raise ValueError(f"profile artifact is not gzip-compressed: {path}")
    except OSError as error:
        raise ValueError(f"could not read profile artifact {path}: {error}") from error
    try:
        with gzip.open(path, "rt", encoding="utf-8") as handle:
            value = json.load(handle)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError(f"could not parse profile artifact {path}: {error}") from error
    expected_sections = {"meta": dict, "libs": list, "threads": list}
    if not isinstance(value, dict) or not all(
        isinstance(value.get(key), expected) for key, expected in expected_sections.items()
    ):
        raise ValueError(f"profile artifact has an unsupported structure: {path}")
    return cast(dict[str, Any], value)


def _index(values: Sequence[Any], index: object) -> Any | None:
    if isinstance(index, bool) or not isinstance(index, int) or index < 0 or index >= len(values):
        return None
    return values[index]


def _cpu_seconds_scale(profile: Mapping[str, Any]) -> float:
    try:
        unit = profile["meta"]["sampleUnits"]["threadCPUDelta"]
    except (KeyError, TypeError) as error:
        raise ValueError("profile has no threadCPUDelta unit") from error
    scales = {
        "ns": 1e-9,
        "nanoseconds": 1e-9,
        "us": 1e-6,
        "\N{MICRO SIGN}s": 1e-6,
        "microseconds": 1e-6,
        "ms": 1e-3,
        "milliseconds": 1e-3,
        "s": 1.0,
        "seconds": 1.0,
    }
    if not isinstance(unit, str) or unit not in scales:
        raise ValueError(f"unsupported profile threadCPUDelta unit: {unit!r}")
    return scales[unit]


def _application_library(profile: Mapping[str, Any], binary: Path) -> tuple[int, str | None]:
    libraries = cast(list[Any], profile["libs"])
    binary_path = binary.resolve()
    exact_matches: list[tuple[int, Mapping[str, Any]]] = []
    name_matches: list[tuple[int, Mapping[str, Any]]] = []
    for index, value in enumerate(libraries):
        if not isinstance(value, dict):
            continue
        library = cast(Mapping[str, Any], value)
        path = library.get("path")
        name = library.get("name")
        if isinstance(path, str) and Path(path).resolve() == binary_path:
            exact_matches.append((index, library))
        if name == binary.name or (isinstance(path, str) and Path(path).name == binary.name):
            name_matches.append((index, library))
    matches = exact_matches if exact_matches else name_matches
    if len(matches) != 1:
        raise ValueError(f"could not identify application library for {binary}")
    index, library = matches[0]
    arch = library.get("arch")
    return (index, arch if isinstance(arch, str) and arch else None)


def _thread_leaf_samples(
    thread: Mapping[str, Any],
    scale: float,
) -> Iterator[LeafSample]:
    samples = thread["samples"]
    stacks = thread["stackTable"]
    frames = thread["frameTable"]
    functions = thread["funcTable"]
    resources = thread["resourceTable"]
    strings = thread["stringArray"]
    for stack, delta in zip(samples["stack"][1:], samples["threadCPUDelta"][1:], strict=False):
        if isinstance(delta, bool) or not isinstance(delta, (int, float)) or delta <= 0:
            continue
        frame = _index(stacks["frame"], stack)
        function = _index(frames["func"], frame)
        resource = _index(functions["resource"], function)
        library = _index(resources["lib"], resource)
        name = _index(strings, _index(functions["name"], function))
        address = _index(frames["address"], frame)
        yield LeafSample(
            cpu_seconds=float(delta) * scale,
            library_index=library if isinstance(library, int) and not isinstance(library, bool) else None,
            function_name=name if isinstance(name, str) else None,
            relative_address=(
                address if isinstance(address, int) and not isinstance(address, bool) and address >= 0 else None
            ),
        )


def _normalize_rust_name(name: str) -> str:
    for encoded, decoded in {
        "$SP$": "@",
        "$BP$": "*",
        "$RF$": "&",
        "$LT$": "<",
        "$GT$": ">",
        "$LP$": "(",
        "$RP$": ")",
        "$C$": ",",
    }.items():
        name = name.replace(encoded, decoded)

    def decode_unicode(match: re.Match[str]) -> str:
        try:
            return chr(int(match.group(1), 16))
        except (ValueError, OverflowError):
            return match.group(0)

    name = re.sub(r"\$u([0-9a-fA-F]+)\$", decode_unicode, name).replace("..", "::")
    return name[1:] if name.startswith("_<") else name


def _normalize_atos_symbol(value: str, image_name: str) -> str | None:
    name = value.strip().split(f" (in {image_name})", 1)[0]
    if not name or name == "<deduplicated_symbol>" or re.fullmatch(r"0x[0-9a-fA-F]+", name):
        return None
    return _normalize_rust_name(name)


def demangle_rust_v0_symbols(symbols: Mapping[int, str]) -> tuple[dict[int, str], tuple[str, ...]]:
    demangled = dict(symbols)
    raw_symbols = [(address, symbol) for address, symbol in symbols.items() if re.match(r"^_+R", symbol)]
    if not raw_symbols:
        return (demangled, ())
    xcrun = shutil.which("xcrun")
    if xcrun is None:
        for address, _ in raw_symbols:
            demangled.pop(address, None)
        return (demangled, ("llvm-cxxfilt is unavailable; Rust v0 symbols are incomplete",))
    try:
        completed = subprocess.run(
            [xcrun, "llvm-cxxfilt"],
            input="\n".join(symbol for _, symbol in raw_symbols) + "\n",
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        for address, _ in raw_symbols:
            demangled.pop(address, None)
        return (demangled, (f"Rust v0 symbol demangling failed: {error}",))
    for (address, raw_symbol), line in zip(raw_symbols, completed.stdout.splitlines(), strict=False):
        symbol = _normalize_rust_name(line.strip())
        if symbol and symbol != raw_symbol and not re.match(r"^_+R", symbol):
            demangled[address] = symbol
        else:
            demangled.pop(address, None)
    return (demangled, ())


def _symbolicate(
    binary: Path,
    arch: str | None,
    addresses: Sequence[int],
) -> tuple[dict[int, str], tuple[str, ...]]:
    unique_addresses = sorted(set(addresses))
    if not unique_addresses:
        return ({}, ())
    atos = shutil.which("atos")
    if atos is None:
        return ({}, ("atos is unavailable; application symbols are incomplete",))

    symbols: dict[int, str] = {}
    warnings: list[str] = []
    for start in range(0, len(unique_addresses), ATOS_BATCH_SIZE):
        batch = unique_addresses[start : start + ATOS_BATCH_SIZE]
        command = [atos, "-offset", "-o", str(binary)]
        if arch is not None:
            command.extend(["-arch", arch])
        command.extend(hex(address) for address in batch)
        try:
            completed = subprocess.run(command, check=True, capture_output=True, text=True)
        except (OSError, subprocess.CalledProcessError) as error:
            warnings.append(f"atos symbolication failed: {error}")
            continue
        for address, line in zip(batch, completed.stdout.splitlines(), strict=False):
            symbol = _normalize_atos_symbol(line, binary.name)
            if symbol is not None:
                symbols[address] = symbol
    symbols, demangle_warnings = demangle_rust_v0_symbols(symbols)
    warnings.extend(demangle_warnings)
    unresolved = len(unique_addresses) - len(symbols)
    if unresolved:
        warnings.append(f"could not resolve {unresolved} application frame address(es)")
    return (symbols, tuple(warnings))


def summarize(profile: Mapping[str, Any], binary: Path) -> ProfileCpuSummary:
    application_library, arch = _application_library(profile, binary)
    scale = _cpu_seconds_scale(profile)
    libraries = cast(list[Any], profile["libs"])
    threads = cast(list[Any], profile["threads"])
    observed_cpu = 0.0
    application_cpu = 0.0
    other_library_cpu = 0.0
    unattributed_cpu = 0.0
    named_cpu: defaultdict[str, float] = defaultdict(float)
    address_cpu: defaultdict[int, float] = defaultdict(float)
    warnings: list[str] = []

    for thread_index, value in enumerate(threads):
        if not isinstance(value, dict):
            warnings.append(f"profile thread {thread_index} is not an object")
            continue
        try:
            for sample in _thread_leaf_samples(value, scale):
                observed_cpu += sample.cpu_seconds
                if sample.library_index is None or not 0 <= sample.library_index < len(libraries):
                    unattributed_cpu += sample.cpu_seconds
                elif sample.library_index != application_library:
                    other_library_cpu += sample.cpu_seconds
                else:
                    application_cpu += sample.cpu_seconds
                    normalized_name = (
                        _normalize_atos_symbol(sample.function_name, binary.name)
                        if sample.function_name is not None
                        else None
                    )
                    if normalized_name is not None and not re.match(r"^_+R", normalized_name):
                        named_cpu[normalized_name] += sample.cpu_seconds
                    elif sample.relative_address is not None:
                        address_cpu[sample.relative_address] += sample.cpu_seconds
        except (KeyError, TypeError) as error:
            warnings.append(f"could not read profile thread {thread_index}: {error}")

    symbols, symbol_warnings = _symbolicate(binary, arch, tuple(address_cpu))
    warnings.extend(symbol_warnings)
    for address, cpu_seconds in address_cpu.items():
        if symbol := symbols.get(address):
            named_cpu[symbol] += cpu_seconds
    functions = tuple(
        ProfileFunctionCpu(name, cpu_seconds)
        for name, cpu_seconds in sorted(named_cpu.items(), key=lambda item: (-item[1], item[0]))
    )
    return ProfileCpuSummary(
        observed_cpu_seconds=observed_cpu,
        application_cpu_seconds=application_cpu,
        other_library_cpu_seconds=other_library_cpu,
        unattributed_cpu_seconds=unattributed_cpu,
        symbolized_application_cpu_seconds=sum(named_cpu.values()),
        functions=functions,
        warnings=tuple(warnings),
    )


def load_command(artifact: Path, *, os_name: str | None = None) -> str:
    command = ["samply", "load", str(artifact)]
    if (os.name if os_name is None else os_name) == "nt":
        return subprocess.list2cmdline(command)
    return shlex.join(command)


def _percentage(value: float, total: float) -> float:
    return 0.0 if total <= 0 else value * 100.0 / total


def _metadata_rows(report: ProfileReport) -> tuple[tuple[str, str], ...]:
    return (
        ("Artifact", str(report.artifact)),
        ("Cache", report.cache_status),
        ("Workload", report.workload),
        ("Backend", report.backend),
        ("Treatment", report.treatment),
    )


def _cpu_rows(summary: ProfileCpuSummary) -> tuple[tuple[str, str, str], ...]:
    observed = summary.observed_cpu_seconds
    application = summary.application_cpu_seconds
    return (
        ("Observed thread", f"{observed:.2f} s", "100.0%"),
        ("Application leaf", f"{application:.2f} s", f"{_percentage(application, observed):.1f}%"),
        (
            "Other library",
            f"{summary.other_library_cpu_seconds:.2f} s",
            f"{_percentage(summary.other_library_cpu_seconds, observed):.1f}%",
        ),
        (
            "Unattributed",
            f"{summary.unattributed_cpu_seconds:.2f} s",
            f"{_percentage(summary.unattributed_cpu_seconds, observed):.1f}%",
        ),
        (
            "Application symbols",
            "-",
            f"{_percentage(summary.symbolized_application_cpu_seconds, application):.1f}%"
            if application > 0
            else "n/a",
        ),
    )


def _function_rows(summary: ProfileCpuSummary, top: int) -> tuple[tuple[str, str, str], ...]:
    return tuple(
        (
            f"{function.cpu_seconds:.3f} s",
            f"{_percentage(function.cpu_seconds, summary.application_cpu_seconds):.1f}%",
            function.name,
        )
        for function in summary.functions[:top]
    )


def render_rich(
    console: Console,
    report: ProfileReport,
) -> None:
    summary = report.cpu_summary
    console.rule("CPU Profile Summary" if summary is not None else "Profile Ready")
    metadata = Table.grid(padding=(0, 1))
    metadata.add_column(style="bold")
    metadata.add_column(overflow="fold")
    for label, value in _metadata_rows(report):
        metadata.add_row(label, Text(value))
    console.print(metadata)
    if summary is not None:
        cpu_table = Table(title="CPU breakdown", box=box.SIMPLE_HEAD)
        cpu_table.add_column("Metric")
        cpu_table.add_column("CPU", justify="right")
        cpu_table.add_column("Share", justify="right")
        for row in _cpu_rows(summary):
            cpu_table.add_row(*row)
        console.print(cpu_table)

        function_rows = _function_rows(summary, report.top)
        if function_rows:
            functions = Table(title="Top functions by self CPU", box=box.SIMPLE_HEAD)
            functions.add_column("CPU", justify="right")
            functions.add_column("App %", justify="right")
            functions.add_column("Function", overflow="fold")
            for cpu, percentage, function in function_rows:
                functions.add_row(cpu, percentage, Text(function))
            console.print(functions)
        else:
            console.print("[dim]No resolved application functions.[/dim]")
    console.print("[bold]Visualize[/bold]")
    console.print(Text(load_command(report.artifact), style="cyan"))


def _markdown_cell(value: str) -> str:
    normalized = value.replace("\r\n", "\n").replace("\r", "\n")
    return (
        normalized.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace("\\", "\\\\")
        .replace("|", "\\|")
        .replace("\n", "<br>")
    )


def render_markdown(report: ProfileReport) -> str:
    summary = report.cpu_summary
    lines = [f"## {'CPU Profile Summary' if summary is not None else 'Profile Ready'}", ""]
    lines.extend(["| Field | Value |", "| --- | --- |"])
    for label, value in _metadata_rows(report):
        lines.append(f"| {_markdown_cell(label)} | {_markdown_cell(value)} |")
    if summary is not None:
        lines.extend(["", "### CPU Breakdown", "", "| Metric | CPU | Share |", "| --- | ---: | ---: |"])
        lines.extend(f"| {_markdown_cell(metric)} | {cpu} | {share} |" for metric, cpu, share in _cpu_rows(summary))
        lines.extend(["", "### Top Functions by Self CPU", ""])
        function_rows = _function_rows(summary, report.top)
        if function_rows:
            lines.extend(["| CPU | App % | Function |", "| ---: | ---: | --- |"])
            lines.extend(
                f"| {cpu} | {percentage} | {_markdown_cell(function)} |" for cpu, percentage, function in function_rows
            )
        else:
            lines.append("No resolved application functions.")
    lines.extend(["", "### Visualize", "", "```shell", load_command(report.artifact), "```"])
    return "\n".join(lines)
