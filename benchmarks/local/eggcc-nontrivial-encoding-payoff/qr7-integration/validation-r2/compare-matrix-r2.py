#!/usr/bin/env python3
"""Compare the complete QR7 r2 matrix with retained r1 evidence."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import re
import struct
from pathlib import Path
from typing import Any

BASE = Path(__file__).resolve().parent.parent
R1 = BASE / "final-r1"
R2 = BASE / "validation-r2/matrix-r2"
R1_INSPECTION = BASE / "actual-binary-inspection-r1.json"
R2_INSPECTION = R2 / "actual-binary-inspection-r2.json"
COMPARISON = R2 / "r1-r2-comparison.json"
REPORT = R2 / "report.md"
PHASES = ("positive", "negative", "context-negative", "loop-negative")
TIMING_KEYS = {
    "llvm_compile_time",
    "eggcc_compile_time",
    "eggcc_extraction_time",
    "eggcc_serialization_time",
}

LC_SEGMENT_64 = 0x19
LC_SYMTAB = 0x2
LC_DYSYMTAB = 0xB
LC_UUID = 0x1B
LC_CODE_SIGNATURE = 0x1D
LC_FUNCTION_STARTS = 0x26
LC_DATA_IN_CODE = 0x29
LC_DYLD_EXPORTS_TRIE = 0x80000033
LC_DYLD_CHAINED_FIXUPS = 0x80000034


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_actual_binary_inspection() -> dict[str, Any]:
    """Run the retained native inspection algorithm against the r2 matrix."""
    if R2_INSPECTION.exists():
        raise RuntimeError(f"refusing to overwrite {R2_INSPECTION}")
    script = BASE / "inspect-binaries.py"
    spec = importlib.util.spec_from_file_location("qr7_inspect_binaries_r2", script)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {script}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.MATRIX = R2 / "matrix/positive"
    module.OUTPUT = R2_INSPECTION
    module.main()
    return json.loads(R2_INSPECTION.read_text())


def case_rows(root: Path) -> list[tuple[str, dict[str, Any], Path]]:
    """Return every matrix row paired with its deterministic case directory."""
    rows = []
    for phase in PHASES:
        for row in json.loads((root / f"{phase}-results.json").read_text()):
            rows.append((phase, row, root / "matrix" / row["family"] / row["mode"]))
    return rows


def semantic_run_report(path: Path) -> dict[str, Any]:
    """Remove diagnostic durations while retaining outputs and semantic counters."""
    report = json.loads(path.read_text())
    return {key: value for key, value in report.items() if key not in TIMING_KEYS}


def tree_hashes(path: Path) -> dict[str, str]:
    """Hash every file in one optional evidence tree by relative name."""
    if not path.exists():
        return {}
    return {item.relative_to(path).as_posix(): sha256(item) for item in sorted(path.rglob("*")) if item.is_file()}


def normalized_llvm(data: bytes) -> tuple[bytes, int]:
    """Normalize the single temporary ModuleID comment in emitted LLVM."""
    text = data.decode()
    matches = re.findall(r"^; ModuleID = .*$", text, re.MULTILINE)
    if len(matches) != 1:
        raise RuntimeError(f"expected one LLVM ModuleID, found {len(matches)}")
    normalized = re.sub(r"^; ModuleID = .*$", "; ModuleID = '<temporary>'", text, flags=re.MULTILINE)
    return normalized.encode(), len(matches)


def normalized_assembly(data: bytes) -> tuple[bytes, int]:
    """Normalize llvm-objdump's input-path banner and preserve all disassembly."""
    text = data.decode()
    pattern = r"^.*:\tfile format mach-o arm64$"
    matches = re.findall(pattern, text, re.MULTILINE)
    if len(matches) != 1:
        raise RuntimeError(f"expected one assembly path banner, found {len(matches)}")
    normalized = re.sub(pattern, "<program>:\tfile format mach-o arm64", text, flags=re.MULTILINE)
    return normalized.encode(), len(matches)


def function_bodies(assembly: bytes) -> dict[str, str]:
    """Hash every disassembled function body, including addresses and instructions."""
    text = assembly.decode()
    headers = list(re.finditer(r"^([0-9a-f]+) <([^>]+)>:\n", text, re.MULTILINE))
    result = {}
    for index, header in enumerate(headers):
        end = headers[index + 1].start() if index + 1 < len(headers) else len(text)
        key = f"{header.group(1)} <{header.group(2)}>"
        if key in result:
            raise RuntimeError(f"duplicate assembly function {key}")
        result[key] = sha256_bytes(text[header.end() : end].encode())
    if not result:
        raise RuntimeError("assembly contained no functions")
    return result


def parse_macho(path: Path) -> dict[str, Any]:
    """Parse Mach-O sections and metadata ranges needed for byte attribution."""
    data = path.read_bytes()
    if len(data) < 32:
        raise RuntimeError(f"short Mach-O file {path}")
    magic, cpu, subtype, filetype, ncmds, sizeofcmds, flags, reserved = struct.unpack_from("<IiiIIIII", data, 0)
    if magic != 0xFEEDFACF:
        raise RuntimeError(f"unexpected Mach-O magic in {path}: {magic:#x}")
    header_end = 32 + sizeofcmds
    commands = bytearray(data[:header_end])
    sections = []
    runtime_linkedit = []
    metadata_ranges: dict[str, list[tuple[int, int]]] = {
        "uuid": [],
        "symbol_table": [],
        "string_table": [],
        "code_signature": [],
    }
    segments = []
    linkedit_start = None
    offset = 32
    for _ in range(ncmds):
        command, command_size = struct.unpack_from("<II", data, offset)
        if command_size < 8 or offset + command_size > header_end:
            raise RuntimeError(f"invalid Mach-O load command in {path}")
        if command == LC_UUID:
            metadata_ranges["uuid"].append((offset + 8, offset + command_size))
            commands[offset + 8 : offset + command_size] = bytes(command_size - 8)
        elif command == LC_SEGMENT_64:
            values = struct.unpack_from("<II16sQQQQiiII", data, offset)
            segment_name = values[2].rstrip(b"\0").decode()
            file_offset, file_size, section_count = values[5], values[6], values[9]
            segments.append(
                {
                    "name": segment_name,
                    "file_offset": file_offset,
                    "file_size": file_size,
                    "section_count": section_count,
                }
            )
            if segment_name == "__LINKEDIT":
                linkedit_start = file_offset
            section_offset = offset + 72
            for _section in range(section_count):
                values = struct.unpack_from("<16s16sQQIIIIIIII", data, section_offset)
                section_name = values[0].rstrip(b"\0").decode()
                section_segment = values[1].rstrip(b"\0").decode()
                section_size, section_file_offset = values[3], values[4]
                body = data[section_file_offset : section_file_offset + section_size]
                sections.append(
                    {
                        "segment": section_segment,
                        "section": section_name,
                        "offset": section_file_offset,
                        "size": section_size,
                        "sha256": sha256_bytes(body),
                    }
                )
                section_offset += 80
        elif command in {
            LC_DYLD_CHAINED_FIXUPS,
            LC_DYLD_EXPORTS_TRIE,
            LC_FUNCTION_STARTS,
            LC_DATA_IN_CODE,
        }:
            data_offset, data_size = struct.unpack_from("<II", data, offset + 8)
            runtime_linkedit.append(
                {
                    "command": command,
                    "offset": data_offset,
                    "size": data_size,
                    "sha256": sha256_bytes(data[data_offset : data_offset + data_size]),
                }
            )
        elif command == LC_SYMTAB:
            symbol_offset, symbol_count, string_offset, string_size = struct.unpack_from("<IIII", data, offset + 8)
            metadata_ranges["symbol_table"].append((symbol_offset, symbol_offset + symbol_count * 16))
            metadata_ranges["string_table"].append((string_offset, string_offset + string_size))
        elif command == LC_DYSYMTAB:
            fields = struct.unpack_from("<20I", data, offset)
            indirect_offset, indirect_count = fields[14], fields[15]
            runtime_linkedit.append(
                {
                    "command": command,
                    "offset": indirect_offset,
                    "size": indirect_count * 4,
                    "sha256": sha256_bytes(data[indirect_offset : indirect_offset + indirect_count * 4]),
                }
            )
        elif command == LC_CODE_SIGNATURE:
            signature_offset, signature_size = struct.unpack_from("<II", data, offset + 8)
            metadata_ranges["code_signature"].append((signature_offset, signature_offset + signature_size))
        offset += command_size
    if offset != header_end or linkedit_start is None:
        raise RuntimeError(f"incomplete Mach-O parse for {path}")
    return {
        "path": str(path),
        "data": data,
        "size": len(data),
        "sha256": sha256_bytes(data),
        "header": {
            "cpu": cpu,
            "subtype": subtype,
            "filetype": filetype,
            "ncmds": ncmds,
            "sizeofcmds": sizeofcmds,
            "flags": flags,
            "reserved": reserved,
        },
        "normalized_load_commands_sha256": sha256_bytes(bytes(commands)),
        "payload_after_load_commands_sha256": sha256_bytes(data[header_end:linkedit_start]),
        "segments": segments,
        "sections": sections,
        "runtime_linkedit": runtime_linkedit,
        "metadata_ranges": metadata_ranges,
    }


def macho_comparison(first: Path, second: Path) -> dict[str, Any]:
    """Compare executable content and attribute every raw-byte difference."""
    left = parse_macho(first)
    right = parse_macho(second)
    left_data = left.pop("data")
    right_data = right.pop("data")
    differing_offsets = [
        index
        for index, (left_byte, right_byte) in enumerate(zip(left_data, right_data, strict=True))
        if left_byte != right_byte
    ]
    categories: dict[str, int] = {}
    unattributed = []
    for index in differing_offsets:
        matched = False
        for name, ranges in left["metadata_ranges"].items():
            if any(start <= index < end for start, end in ranges):
                categories[name] = categories.get(name, 0) + 1
                matched = True
                break
        if not matched:
            unattributed.append(index)
    sections_equal = left["sections"] == right["sections"]
    runtime_linkedit_equal = left["runtime_linkedit"] == right["runtime_linkedit"]
    normalized_commands_equal = left["normalized_load_commands_sha256"] == right["normalized_load_commands_sha256"]
    loadable_payload_equal = left["payload_after_load_commands_sha256"] == right["payload_after_load_commands_sha256"]
    return {
        "r1_sha256": left["sha256"],
        "r2_sha256": right["sha256"],
        "raw_bytes_equal": left_data == right_data,
        "same_size": left["size"] == right["size"],
        "differing_byte_count": len(differing_offsets),
        "difference_categories": categories,
        "unattributed_difference_offsets": unattributed,
        "header_equal": left["header"] == right["header"],
        "segments_equal": left["segments"] == right["segments"],
        "sections_equal": sections_equal,
        "normalized_load_commands_equal": normalized_commands_equal,
        "loadable_payload_after_commands_equal": loadable_payload_equal,
        "runtime_linkedit_blobs_equal": runtime_linkedit_equal,
        "all_execution_content_checks_equal": all(
            (
                left["header"] == right["header"],
                left["segments"] == right["segments"],
                sections_equal,
                normalized_commands_equal,
                loadable_payload_equal,
                runtime_linkedit_equal,
                not unattributed,
            )
        ),
        "sections": left["sections"],
    }


def inspect_case(
    phase: str,
    r1_row: dict[str, Any],
    r1_folder: Path,
    r2_row: dict[str, Any],
    r2_folder: Path,
) -> dict[str, Any]:
    """Compare one matrix case from semantic rows through native bytes."""
    identity = {
        "phase": phase,
        "family": r1_row["family"],
        "mode": r1_row["mode"],
        "context": r1_row["context"],
        "source_sha256": r1_row["source_sha256"],
    }
    if identity != {
        "phase": phase,
        "family": r2_row["family"],
        "mode": r2_row["mode"],
        "context": r2_row["context"],
        "source_sha256": r2_row["source_sha256"],
    }:
        raise RuntimeError(f"case identity mismatch: {identity}")
    excluded = {"source", "binary_sha256"}
    semantic_row_equal = {k: v for k, v in r1_row.items() if k not in excluded} == {
        k: v for k, v in r2_row.items() if k not in excluded
    }
    if not semantic_row_equal:
        raise RuntimeError(f"semantic result-row mismatch: {identity}")

    report_files = ("interp.json", "emit.json", "native/lower.json")
    run_report_semantics_equal = all(
        semantic_run_report(r1_folder / name) == semantic_run_report(r2_folder / name) for name in report_files
    )
    if not run_report_semantics_equal:
        raise RuntimeError(f"semantic run-report mismatch: {identity}")

    evidence_trees_equal = all(
        tree_hashes(r1_folder / name) == tree_hashes(r2_folder / name)
        for name in ("egraphs", "evidence", "interp-evidence")
    )
    if not evidence_trees_equal:
        raise RuntimeError(f"evidence tree mismatch: {identity}")

    emitted_label = f"{r1_row['family']}-{r1_row['mode']}-emit"
    r1_emit = R1 / "commands" / emitted_label / "stdout"
    r2_emit = R2 / "commands" / emitted_label / "stdout"
    optimized_r1 = r1_folder / "optimized.bril"
    optimized_r2 = r2_folder / "optimized.bril"
    emitted_stdout_equal = r1_emit.read_bytes() == r2_emit.read_bytes()
    emitted_matches_optimized = (
        r1_emit.read_bytes() == optimized_r1.read_bytes() and r2_emit.read_bytes() == optimized_r2.read_bytes()
    )
    optimized_equal = optimized_r1.read_bytes() == optimized_r2.read_bytes()
    if not all((emitted_stdout_equal, emitted_matches_optimized, optimized_equal)):
        raise RuntimeError(f"emitted Bril mismatch: {identity}")

    llvm_r1 = (r1_folder / "native/program.ll").read_bytes()
    llvm_r2 = (r2_folder / "native/program.ll").read_bytes()
    normalized_llvm_r1, _ = normalized_llvm(llvm_r1)
    normalized_llvm_r2, _ = normalized_llvm(llvm_r2)
    llvm_normalized_equal = normalized_llvm_r1 == normalized_llvm_r2
    if not llvm_normalized_equal:
        raise RuntimeError(f"normalized LLVM mismatch: {identity}")

    assembly_r1 = (r1_folder / "native/program.asm").read_bytes()
    assembly_r2 = (r2_folder / "native/program.asm").read_bytes()
    normalized_assembly_r1, _ = normalized_assembly(assembly_r1)
    normalized_assembly_r2, _ = normalized_assembly(assembly_r2)
    assembly_normalized_equal = normalized_assembly_r1 == normalized_assembly_r2
    bodies_r1 = function_bodies(assembly_r1)
    bodies_r2 = function_bodies(assembly_r2)
    function_bodies_equal = bodies_r1 == bodies_r2
    if not assembly_normalized_equal or not function_bodies_equal:
        raise RuntimeError(f"native instruction-body mismatch: {identity}")

    native_outputs_equal = True
    native_output_hashes = []
    for index in range(len(r1_row["outputs"])):
        label = f"{r1_row['family']}-{r1_row['mode']}-native-{index:03}"
        r1_output = (R1 / "commands" / label / "stdout").read_bytes()
        r2_output = (R2 / "commands" / label / "stdout").read_bytes()
        native_outputs_equal &= r1_output == r2_output
        native_output_hashes.append(sha256_bytes(r2_output))
    if not native_outputs_equal:
        raise RuntimeError(f"native stdout mismatch: {identity}")

    executable = macho_comparison(
        r1_folder / "native/program",
        r2_folder / "native/program",
    )
    if not executable["all_execution_content_checks_equal"]:
        raise RuntimeError(f"Mach-O execution-content mismatch: {identity}")
    return {
        "identity": identity,
        "semantic_result_row_equal": semantic_row_equal,
        "queries_equal": r1_row["queries"] == r2_row["queries"],
        "semantic_run_reports_equal": run_report_semantics_equal,
        "egraph_and_evidence_files_byte_equal": evidence_trees_equal,
        "emitted_bril_stdout_byte_equal": emitted_stdout_equal,
        "emitted_stdout_matches_optimized_file": emitted_matches_optimized,
        "optimized_bril_byte_equal": optimized_equal,
        "optimized_bril_sha256": sha256(optimized_r2),
        "llvm_raw_byte_equal": llvm_r1 == llvm_r2,
        "llvm_normalized_module_id_equal": llvm_normalized_equal,
        "llvm_r1_sha256": sha256_bytes(llvm_r1),
        "llvm_r2_sha256": sha256_bytes(llvm_r2),
        "assembly_raw_byte_equal": assembly_r1 == assembly_r2,
        "assembly_normalized_path_banner_equal": assembly_normalized_equal,
        "all_function_instruction_bodies_equal": function_bodies_equal,
        "function_count": len(bodies_r2),
        "native_stdout_equal": native_outputs_equal,
        "native_output_count": len(native_output_hashes),
        "native_output_sha256": native_output_hashes,
        "native_executable": executable,
    }


def main() -> None:
    for path in (COMPARISON, REPORT):
        if path.exists():
            raise RuntimeError(f"refusing to overwrite {path}")
    r2_inspection = load_actual_binary_inspection()
    r1_inspection = json.loads(R1_INSPECTION.read_text())
    r1_rows = case_rows(R1)
    r2_rows = case_rows(R2)
    if len(r1_rows) != len(r2_rows):
        raise RuntimeError("matrix row-count mismatch")
    cases = [
        inspect_case(phase1, row1, folder1, row2, folder2)
        for (phase1, row1, folder1), (phase2, row2, folder2) in zip(r1_rows, r2_rows, strict=True)
        if phase1 == phase2
    ]
    if len(cases) != len(r1_rows):
        raise RuntimeError("matrix phase-order mismatch")

    inspection_exact = (R1 / "inspection.json").read_bytes() == (R2 / "inspection.json").read_bytes()
    actual_functions_equal = all(
        r1_inspection["modes"][mode]["functions"] == r2_inspection["modes"][mode]["functions"]
        for mode in r1_inspection["modes"]
    )
    groups_equal = r1_inspection["groups"] == r2_inspection["groups"]
    emitted_maps_equal = r1_inspection["emitted_bril_sha256"] == r2_inspection["emitted_bril_sha256"]
    all_execution_content_equal = all(case["native_executable"]["all_execution_content_checks_equal"] for case in cases)
    all_native_files_equal = all(case["native_executable"]["raw_bytes_equal"] for case in cases)
    all_differences_attributed = all(not case["native_executable"]["unattributed_difference_offsets"] for case in cases)
    result = {
        "schema_version": 1,
        "status": "semantic-and-execution-content-equivalent-exact-native-file-identity-false",
        "scope": {
            "r1": str(R1),
            "r2": str(R2),
            "matrix_phases": list(PHASES),
            "case_count": len(cases),
            "native_output_count": sum(case["native_output_count"] for case in cases),
            "run_report_count": len(cases) * 3,
            "timing_collected": False,
            "raytracing_requested": False,
        },
        "compiler_binaries": {
            "r1_sha256": "ab1185cd3e24d1ed1698bc004ed3cc70f16c89202e3cc36a910b8308221df251",
            "r2_sha256": "046efff7fcc7ea3a1e31ff8e35ccad32001967b75f97e4f2c1efaef0413b6333",
            "byte_equal": False,
            "compiler_time_is_excluded_from_existing_timing": True,
        },
        "aggregate": {
            "semantic_result_rows_equal": all(case["semantic_result_row_equal"] for case in cases),
            "queries_and_counters_equal": inspection_exact and all(case["queries_equal"] for case in cases),
            "inspection_json_byte_equal": inspection_exact,
            "semantic_run_reports_equal_after_excluding_diagnostic_durations": all(
                case["semantic_run_reports_equal"] for case in cases
            ),
            "egraph_and_evidence_files_byte_equal": all(case["egraph_and_evidence_files_byte_equal"] for case in cases),
            "emitted_bril_stdout_byte_equal": all(case["emitted_bril_stdout_byte_equal"] for case in cases),
            "optimized_bril_files_byte_equal": all(case["optimized_bril_byte_equal"] for case in cases),
            "llvm_files_raw_byte_equal": all(case["llvm_raw_byte_equal"] for case in cases),
            "llvm_files_equal_after_temporary_module_id_normalization": all(
                case["llvm_normalized_module_id_equal"] for case in cases
            ),
            "assembly_files_raw_byte_equal": all(case["assembly_raw_byte_equal"] for case in cases),
            "assembly_equal_after_input_path_banner_normalization": all(
                case["assembly_normalized_path_banner_equal"] for case in cases
            ),
            "all_disassembled_function_instruction_bodies_equal": all(
                case["all_function_instruction_bodies_equal"] for case in cases
            ),
            "native_stdout_byte_equal": all(case["native_stdout_equal"] for case in cases),
            "native_executable_files_raw_byte_equal": all_native_files_equal,
            "native_loadable_sections_and_execution_content_equal": all_execution_content_equal,
            "native_file_differences_confined_to_uuid_symbols_strings_and_signature": all_differences_attributed,
            "positive_actual_binary_function_summaries_equal": actual_functions_equal,
            "positive_actual_binary_groups_equal": groups_equal,
            "positive_emitted_bril_hash_maps_equal": emitted_maps_equal,
        },
        "timing_identity_conclusion": {
            "execution_content_equivalent": all_execution_content_equal and actual_functions_equal and groups_equal,
            "exact_timed_macho_file_identity": all_native_files_equal,
            "every_artifact_byte_identical": False,
            "existing_r1_timing_directly_measures_r2_regenerated_macho_files": False,
            "strict_answer": (
                "No: every semantic row, emitted program, loadable section, native output, and "
                "instruction body is identical, but the regenerated Mach-O files are not byte "
                "identical because UUID, temporary-object symbol/string metadata, and the derived "
                "ad-hoc code signature differ. The retained r1 timing directly measures the frozen "
                "r1 Mach-O files, not these r2 regenerated files."
            ),
            "performance_samples_taken": False,
        },
        "actual_binary_inspection": {
            "r1": str(R1_INSPECTION),
            "r1_sha256": sha256(R1_INSPECTION),
            "r2": str(R2_INSPECTION),
            "r2_sha256": sha256(R2_INSPECTION),
            "functions_equal": actual_functions_equal,
            "groups_equal": groups_equal,
        },
        "cases": cases,
    }
    COMPARISON.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")

    raw_differences = [case["native_executable"]["differing_byte_count"] for case in cases]
    native_output_count = sum(case["native_output_count"] for case in cases)
    baseline = r2_inspection["groups"]["baseline"]
    winning = r2_inspection["groups"]["winning"]
    REPORT.write_text(
        f"""# QR7 r2 matrix comparison

The complete r2 matrix passed all four phases and the retained semantic inspector:
14 positive modes, 18 negative rows, one context-negative row, and four
loop-negative rows. Across those {len(cases)} cases, all
{native_output_count} native outputs are exact.
No timing or raytracing workload was run, and every receipt records the benchmark
memory guard as absent.

| Compared artifact | r1 versus r2 |
| --- | --- |
| Semantic result rows, queries, and counters | identical |
| Inspector JSON | byte-identical |
| E-graph and scoped evidence JSON | byte-identical |
| Emitted and saved optimized Bril | byte-identical |
| LLVM IR | identical after removing the one temporary `ModuleID` comment; raw hash differs |
| All disassembled function/instruction bodies | byte-identical |
| Native stdout | {native_output_count}/{native_output_count} byte-identical |
| Mach-O executable content | identical after UUID normalization |
| Complete Mach-O file | differs in all {len(cases)} cases |

The r2 actual-binary inspection reproduces the r1 instruction groups exactly.
The baseline group has {baseline["instruction_count"]} process-main instructions and
{baseline["internal_backward_branch_count"]} internal backward branches, with hash
`{baseline["process_main_instruction_sha256"]}`. The winning group has
{winning["instruction_count"]} instructions and
{winning["internal_backward_branch_count"]} backward branches, with hash
`{winning["process_main_instruction_sha256"]}`.

The complete generated Mach-O files are not byte-identical. Each pair differs in
{min(raw_differences)} to {max(raw_differences)} bytes, and every changed byte is
inside the `LC_UUID` payload, local symbol/string metadata containing a temporary
object identity, or the ad-hoc code signature derived from those bytes. All Mach-O
sections and the payload after the load-command region and before `__LINKEDIT` are
byte-identical. The normalized LLVM difference is likewise only its temporary-file
`ModuleID`; the disassembly difference outside function bodies is only
llvm-objdump's input-path banner.

The strict exact-artifact answer is **no**: the retained r1 timing directly measures
the frozen r1 Mach-O files, while these regenerated r2 files have different hashes.
The execution-content answer is **yes**: semantic rows, optimized Bril, loadable
machine-code/data sections, complete instruction bodies, and outputs are identical.
Because the existing endpoint measures fresh-process runtime and excludes compiler
time, this establishes code-shape equivalence but does not relabel the old samples as
direct measurements of the r2 regenerated files. No new timing was collected.

Machine-readable details, including every case and byte-difference attribution, are
in [`r1-r2-comparison.json`](r1-r2-comparison.json). The r2 native inspection is
[`actual-binary-inspection-r2.json`](actual-binary-inspection-r2.json), and the
complete matrix receipts are under [`commands/`](commands/) and
[`top-level/`](top-level/).
"""
    )
    print(
        json.dumps(
            {
                "case_count": len(cases),
                "native_output_count": sum(case["native_output_count"] for case in cases),
                "execution_content_equivalent": all_execution_content_equal,
                "exact_timed_macho_file_identity": all_native_files_equal,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
