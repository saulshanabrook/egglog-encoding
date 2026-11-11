#!/usr/bin/env python3
"""Capture DialEgg and preserved SpEQ inputs with per-invocation evidence.

This writes a mapping for catalog integration, not the catalog itself. The
capture-only DialEgg frontend uses installed LLVM/MLIR; it never builds LLVM.
SpEQ artifact extraction streams through bounded buffers. Recorder inputs are
individually hash-verified; the optional complete index also saves small source
files for paper-case reconciliation and verifies the full archive checksum.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import http.client
import io
import json
import os
import re
import shutil
import sys
import tarfile
import time
import urllib.request
from collections import deque
from concurrent.futures import Future, ThreadPoolExecutor
from dataclasses import asdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from benchmarking.pilot import run_bounded_command  # noqa: E402
from scripts.hardboiled_replay import egglog_forms  # noqa: E402
from scripts.paper_benchmarks import materialize, record_speq  # noqa: E402

STORAGE = ROOT / "benchmarks/local"
DIALEGG_REVISION = materialize.DIALEGG_COMMIT
SPEQ_NAMES = tuple(record_speq.EXPECTED_KERNEL)
DIALEGG_INPUTS = {
    **{
        f"dialegg-{name}": f"bench/{name}/{name}.mlir"
        for name in ("image_conversion", "vector_norm", "polynomial", "2mm", "3mm")
    },
    **{f"dialegg-nmm-{size}": f"bench/nmm/{size}mm.mlir" for size in (10, 20, 40, 80, 160)},
}
# Frozen queries for calls with shape inference but no extracted optimization
# root. Hashes identify the original invocations; 2mm/3mm call 0 is identical.
DIALEGG_SHAPE_QUERIES = {
    "2c8960e5112d774678c559cd6c9dedeec7d25b57528519669493ab24854ace91": (
        "(check (= (nrows (type-of $op0)) -9223372036854775808))",
        "dynamic row-count sentinel copied from the original shape",
    ),
    "589ba424a5ff3cb1919d90a4f40e64f82f72204c7226d3c05b5fe86f3baaaefa": (
        "(check (= (nrows (type-of $op10)) 100))",
        "row count 100 for the original 100-by-10 tensor",
    ),
    "9077b9de13d3eba902b7a40d8d536cc8fc2ba34b62e564677978a9bbc26b37ac": (
        "(check (= (nrows (type-of $op13)) 200))",
        "row count 200 for the original 200-by-175 tensor",
    ),
}


class OracleSafetyStop(RuntimeError):
    """Carry negative-query evidence out of the nested capture loop on a safety stop."""

    def __init__(self, evidence: dict[str, Any]) -> None:
        super().__init__("negative-query resource guard stopped acquisition")
        self.evidence = evidence


def fetch_verified_source(url: str, destination: Path, expected: str | None = None) -> str:
    """Cache immutable source bytes and reject drift when a known digest exists."""
    if not destination.is_file():
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(urllib.request.urlopen(url, timeout=30).read())
    digest = hashlib.sha256(destination.read_bytes()).hexdigest()
    if expected is not None and digest != expected:
        raise ValueError(f"source digest mismatch at {destination}: {digest}, expected {expected}")
    return digest


def prepare_dialegg(prefix: Path) -> tuple[Path | None, dict[str, Any]]:
    """Build only the small pinned frontend with a per-invocation capture hook."""
    source = STORAGE / "sources/dialegg"
    evidence: dict[str, Any] = {"revision": DIALEGG_REVISION, "llvm_prefix": str(prefix), "builds": []}
    if not (source / "src/Egglog.cpp").exists():
        url = f"https://codeload.github.com/AzizZayed/dialegg-cgo-artifact/tar.gz/{DIALEGG_REVISION}"
        data = urllib.request.urlopen(url, timeout=30).read()
        evidence["source_archive_sha256"] = hashlib.sha256(data).hexdigest()
        with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as archive:
            for member in archive:
                if not member.isfile():
                    continue
                relative = Path(*Path(member.name).parts[1:])
                if ".." in relative.parts:
                    raise ValueError("unsafe source archive member")
                output = source / relative
                output.parent.mkdir(parents=True, exist_ok=True)
                handle = archive.extractfile(member)
                assert handle is not None
                output.write_bytes(handle.read())
    work = ROOT / "target/benchmark-acquisition/dialegg-capture"
    logs = STORAGE / "evidence/dialegg-build" / str(time.time_ns())
    shutil.copytree(source / "src", work / "src", dirs_exist_ok=True)
    pass_path = work / "src/EqualitySaturationPass.cpp"
    original = pass_path.read_text()
    adapted = materialize.replace_once(
        original,
        "std::ofstream eggFileOut(opsEggFilePath);",
        "static size_t captureIndex = 0;\n"
        '    const char* captureDirectory = std::getenv("DIALEGG_CAPTURE_DIR");\n'
        '    if (!captureDirectory) { throw std::runtime_error("DIALEGG_CAPTURE_DIR required"); }\n'
        '    opsEggFilePath = std::string(captureDirectory) + "/invocation-"\n'
        '        + std::to_string(captureIndex++) + ".egg";\n'
        "    std::ofstream eggFileOut(opsEggFilePath);",
        "per-invocation capture output",
    )
    adapted = materialize.replace_once(
        adapted, "eggFileOut.close();", "eggFileOut.close();\n    return;", "capture boundary"
    )
    adapted = materialize.replace_once(
        adapted,
        "runEgglog(egglog.eggifiedBlock, blockName); // Run egglog on the block",
        "runEgglog(egglog.eggifiedBlock, blockName);\n    return; // Capture before external engine/reconstruction.",
        "skip external engine and reconstruction",
    )
    pass_path.write_text(adapted)
    evidence["original_pass_sha256"] = hashlib.sha256(original.encode()).hexdigest()
    evidence["capture_pass_sha256"] = hashlib.sha256(adapted.encode()).hexdigest()
    objects: list[str] = []
    for name in ("egg-opt", "EqualitySaturationPass", "Egglog"):
        obj = work / f"{name}.o"
        command = [
            str(prefix / "bin/clang++"),
            "-std=c++17",
            "-O0",
            "-g0",
            f"-I{prefix / 'include'}",
            "-c",
            str(work / f"src/{name}.cpp"),
            "-o",
            str(obj),
        ]
        result = run_bounded_command(command, source, logs / f"build-{name}")
        evidence["builds"].append({"command": command, **asdict(result)})
        if result.status != "success":
            evidence["reason"] = result.message
            return None, evidence
        objects.append(str(obj))
    binary = work / "egg-opt-capture"
    command = [
        str(prefix / "bin/clang++"),
        *objects,
        f"-L{prefix / 'lib'}",
        "-lMLIROptLib",
        "-lMLIR",
        "-lLLVM",
        f"-Wl,-rpath,{prefix / 'lib'}",
        "-o",
        str(binary),
    ]
    result = run_bounded_command(command, source, logs / "link")
    evidence["builds"].append({"command": command, **asdict(result)})
    if result.status != "success":
        evidence["reason"] = result.message
        return None, evidence
    evidence["binary_sha256"] = hashlib.sha256(binary.read_bytes()).hexdigest()
    return binary, evidence


def modernize_dialegg_invocation(source: str, prelude: str, *, diagnostic_queries: bool = True) -> str:
    """Translate constructor/global/cost syntax while retaining the source schedule."""
    shape_query = DIALEGG_SHAPE_QUERIES.get(hashlib.sha256(source.encode()).hexdigest()) if diagnostic_queries else None
    source = materialize.replace_once(source, '(include "src/base.egg")', prelude, "shared prelude")
    source = source.replace("(function nrows (Type) i64)", "(function nrows (Type) i64 :merge old)")
    source = source.replace("(function ncols (Type) i64)", "(function ncols (Type) i64 :merge old)")
    source = source.replace("(unstable-cost ", "(set-cost ")
    source = materialize.constructors(source)
    if "(set-cost (linalg_matmul " in source:
        source = materialize.replace_once(
            source,
            "(constructor linalg_matmul (Op Op Op Type) Op)",
            "(with-dynamic-cost (constructor linalg_matmul (Op Op Op Type) Op))",
            "dynamic cost constructor",
        )
    globals_ = set(re.findall(r"^\(let ([^\s()]+)", source, re.MULTILINE))
    modern = materialize.prefix_atoms(source, globals_).rstrip() + "\n"
    if shape_query is not None:
        check, meaning = shape_query
        modern += f"\n;; Diagnostic query: {meaning}.\n{check}\n"
    return modern


def retain_derived_oracles(source: str, binary: Path, evidence_dir: Path) -> tuple[str, dict[str, Any]]:
    """Require each retained equality to fail specifically before the source schedule."""
    lines = source.splitlines()
    schedules = [line for line in lines if line.startswith("(run-schedule ")]
    if len(schedules) != 1 or not schedules[0].split(";", 1)[0].rstrip().endswith(")"):
        raise ValueError("expected one complete source run-schedule before testing derived oracles")
    checks = [line for line in lines if line.startswith("(check (= ")]
    body = "\n".join(line for line in lines if line not in checks and line not in schedules) + "\n"
    retained: list[str] = []
    evidence: dict[str, Any] = {"candidate_checks": len(checks), "retained_checks": 0, "negative_checks": []}
    for index, check in enumerate(checks):
        path = evidence_dir / f"no-schedule-{index}.egg"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body + check + "\n")
        process = run_bounded_command([str(binary), str(path)], ROOT, evidence_dir / f"no-schedule-{index}")
        stderr = process.stderr_path.read_text()
        is_derived = (
            process.status == "failure"
            and process.returncode == 1
            and re.search(r"(?m)^[ \t]*Check failed:", stderr) is not None
        )
        evidence["negative_checks"].append({"derived": is_derived, **asdict(process)})
        if process.status in ("resource-stopped", "memory-limit"):
            raise OracleSafetyStop(evidence)
        if is_derived:
            retained.append(check)
            evidence["retained_checks"] = len(retained)
        elif process.status != "success":
            raise ValueError(
                f"negative oracle {index} failed without an ordinary Check failed diagnostic: {process.message}"
            )
    filtered = "\n".join(line for line in lines if line not in checks or line in retained) + "\n"
    return filtered, evidence


def capture_dialegg(prefix: Path, egglog: Path | None) -> dict[str, Any]:
    binary, preparation = prepare_dialegg(prefix)
    results: dict[str, Any] = {}
    if preparation["builds"] and preparation["builds"][-1]["status"] in ("resource-stopped", "memory-limit"):
        return {"preparation": preparation, "cases": results, "operational_stop": preparation["builds"][-1]}
    source = STORAGE / "sources/dialegg"
    preparation["egglog_binary_sha256"] = (
        hashlib.sha256(egglog.read_bytes()).hexdigest() if egglog is not None else None
    )
    prelude = materialize.modernize_dialegg_base(
        materialize.read_verified(source / "src/base.egg", materialize.DIALEGG_BASE_SHA256)
    )
    for case_id, input_path in DIALEGG_INPUTS.items():
        print(f"Capturing {case_id}", file=sys.stderr, flush=True)
        evidence_dir = STORAGE / "evidence/capture" / case_id / f"attempt-{time.time_ns()}"
        evidence_dir.mkdir(parents=True, exist_ok=True)
        result: dict[str, Any] = {"source": input_path, "workloads": [], "invocations": [], "status": "blocked"}
        results[case_id] = result
        result["source_sha256"] = hashlib.sha256((source / input_path).read_bytes()).hexdigest()
        if binary is None:
            result["reason"] = "Pinned DialEgg capture frontend could not build against installed LLVM/MLIR: " + str(
                preparation["reason"]
            )
            continue
        capture_dir = evidence_dir / "original-invocations"
        capture_dir.mkdir(exist_ok=True)
        template = source / (
            "bench/nmm/nmm.egg" if case_id.startswith("dialegg-nmm-") else input_path.replace(".mlir", ".egg")
        )
        command = [
            str(binary),
            "--mlir-disable-threading",
            "--eq-sat",
            str(source / input_path),
            "--egg",
            str(template),
            "-o",
            str(evidence_dir / "unchanged.mlir"),
        ]
        previous = os.environ.get("DIALEGG_CAPTURE_DIR")
        os.environ["DIALEGG_CAPTURE_DIR"] = str(capture_dir)
        try:
            process = run_bounded_command(command, source, evidence_dir / "capture")
        finally:
            if previous is None:
                os.environ.pop("DIALEGG_CAPTURE_DIR", None)
            else:
                os.environ["DIALEGG_CAPTURE_DIR"] = previous
        result["capture_process"] = {"command": command, **asdict(process)}
        originals = sorted(capture_dir.glob("invocation-*.egg"), key=lambda p: int(p.stem.split("-")[-1]))
        if process.status != "success":
            result["reason"] = f"frontend {process.status}: {process.message}"
        elif not originals:
            result["reason"] = "frontend completed without emitting an Egglog invocation"
        if process.status in ("resource-stopped", "memory-limit"):
            result["raw_invocations"] = [str(path.relative_to(ROOT)) for path in originals]
            return {"preparation": preparation, "cases": results, "operational_stop": asdict(process)}
        for invocation, raw in enumerate(originals):
            captured: dict[str, Any] = {
                "index": invocation,
                "raw": str(raw.relative_to(ROOT)),
                "sha256": hashlib.sha256(raw.read_bytes()).hexdigest(),
            }
            result["invocations"].append(captured)
            try:
                modern = modernize_dialegg_invocation(raw.read_text(), prelude)
                shape_query = DIALEGG_SHAPE_QUERIES.get(captured["sha256"])
                probe = evidence_dir / f"invocation-{invocation}-probe.egg"
                probe.write_text(modern)
                extractions = [
                    modern[start:end] for start, end, tokens in egglog_forms(modern) if tokens[1] == "extract"
                ]
                if not extractions and shape_query is None:
                    raise ValueError("source invocation has no extracted root; no correctness oracle is available")
                if egglog is None:
                    raise ValueError("current Egglog executable is unavailable for a bounded extraction/check probe")
                phase = "query" if shape_query else "extraction"
                check = run_bounded_command(
                    [str(egglog), str(probe)],
                    ROOT,
                    evidence_dir / f"invocation-{invocation}-{'query' if shape_query else 'extract'}",
                )
                captured["query_validation" if shape_query else "extraction"] = asdict(check)
                if check.status in ("resource-stopped", "memory-limit"):
                    captured.update(status="blocked", reason=check.message)
                    result["reason"] = f"current-engine {phase} {check.status}: {check.message}"
                    return {"preparation": preparation, "cases": results, "operational_stop": asdict(check)}
                if check.status != "success":
                    raise ValueError(f"current-engine {phase} {check.status}: {check.message}")
                captured["extractions"] = extractions
                if shape_query is not None:
                    modern, oracle_evidence = retain_derived_oracles(
                        modern, egglog, evidence_dir / f"invocation-{invocation}-oracles"
                    )
                    captured["oracle_validation"] = oracle_evidence
                    captured["oracle"] = {
                        "kind": "shape-inference",
                        "check": shape_query[0],
                        "meaning": shape_query[1],
                    }
                    if not oracle_evidence["retained_checks"]:
                        raise ValueError("shape query holds before the source schedule; no derived oracle")
                output = STORAGE / "workloads/dialegg" / f"{case_id}-{invocation:03}.egg"
                output.parent.mkdir(parents=True, exist_ok=True)
                provenance = materialize.header(
                    (
                        f"DialEgg source revision: {DIALEGG_REVISION}",
                        f"Original MLIR: {input_path}",
                        f"Source SHA-256: {result['source_sha256']}",
                        f"Independent source invocation: {invocation}; generated SHA-256: {captured['sha256']}",
                        "Capture hook preserves each frontend call before engine execution and reconstruction.",
                        "Current constructor/global/cost syntax; original schedule and extraction commands retained.",
                        "Shape-analysis checks retain their separate no-schedule diagnostics.",
                        "Strict proof validation and resource admission are separate pilot gates.",
                    )
                )
                # Preserve identical shape-only source aliases as one measured
                # identity; their source provenance remains in the catalog.
                output.write_text(modern if shape_query else provenance + modern)
                captured["status"] = "captured"
                captured["workload"] = str(output.relative_to(ROOT))
                result["workloads"].append(str(output.relative_to(ROOT)))
            except OracleSafetyStop as error:
                captured.update(status="blocked", reason=str(error), oracle_validation=error.evidence)
                result["reason"] = str(error)
                return {
                    "preparation": preparation,
                    "cases": results,
                    "operational_stop": error.evidence["negative_checks"][-1],
                }
            except (OSError, ValueError) as error:
                captured.update(status="blocked", reason=str(error))
        failures = [item["reason"] for item in result["invocations"] if item["status"] != "captured"]
        if originals and process.status == "success" and not failures:
            result["status"] = "captured"
        elif failures:
            result["reason"] = "; ".join(failures)
    return {"preparation": preparation, "cases": results}


def stream_speq_artifact(byte_limit: int | None, *, complete_index: bool = False) -> dict[str, Any]:
    """Extract only small recorder inputs without saving the multi-GB archive."""
    artifact = STORAGE / "sources/speq/artifact"
    wanted = {
        "parseIR.py": record_speq.PARSE_IR_SHA256,
        "run_benchmark.py": record_speq.RUN_BENCHMARK_SHA256,
        **{f"analysis/{name}.ll": digest for name, digest in record_speq.REFERENCE_ANALYSIS_SHA256.items()},
        **{f"benchmarks/{name}.c": digest for name, digest in record_speq.APPLICATION_C_SHA256.items()},
    }
    cached: dict[str, str] = {}
    for name, expected in wanted.items():
        path = artifact / name
        if path.is_file():
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            if digest != expected:
                raise ValueError(f"cached artifact member digest mismatch: {name}: {digest}")
            cached[name] = digest
    if len(cached) == len(wanted) and not complete_index:
        return {
            "archive_record": record_speq.SPEQ_RECORD,
            "declared_archive_md5": record_speq.SPEQ_ARCHIVE_MD5,
            "selected": cached,
            "missing": [],
            "reused_verified_members": True,
            "compressed_bytes_read": 0,
        }
    evidence: dict[str, Any] = {"compressed_byte_limit": byte_limit, "selected": {}, "last_member": None}
    metadata_url = f"https://zenodo.org/api/records/{record_speq.SPEQ_RECORD}"
    metadata = json.loads(urllib.request.urlopen(metadata_url, timeout=30).read())
    entry = next(item for item in metadata["files"] if item["checksum"] == "md5:" + record_speq.SPEQ_ARCHIVE_MD5)
    evidence["archive"] = entry
    evidence["full_archive_index_examined"] = False
    evidence["mapping_files"] = {}
    evidence["member_count"] = 0
    index_path = STORAGE / "evidence/speq-artifact-members.jsonl"
    index_path.parent.mkdir(parents=True, exist_ok=True)
    evidence["member_index"] = str(index_path)
    mapping_bytes = 0
    transfer_size = min(byte_limit or entry["size"], entry["size"])
    started = time.monotonic()

    class ProgressReader(io.RawIOBase):
        """Read ordered ranges with at most eight prefetched 8-MiB chunks."""

        def __init__(self) -> None:
            super().__init__()
            self.received = 0
            self.reported = 0
            self.chunk_size = 8 * 1024**2
            self.pool = ThreadPoolExecutor(max_workers=8)
            self.pending: deque[Future[bytes]] = deque()
            self.next_start = 0
            self.current = b""
            self.offset = 0
            self.md5 = hashlib.md5()
            for _ in range(8):
                if self.next_start < transfer_size:
                    self.pending.append(self.pool.submit(self.fetch, self.next_start))
                    self.next_start += self.chunk_size

        def fetch(self, start: int) -> bytes:
            end = min(start + self.chunk_size, transfer_size) - 1
            request = urllib.request.Request(entry["links"]["self"], headers={"Range": f"bytes={start}-{end}"})
            for attempt in range(5):
                try:
                    with urllib.request.urlopen(request, timeout=30) as response:
                        expected_range = f"bytes {start}-{end}/{entry['size']}"
                        if response.status != 206 or response.headers.get("Content-Range") != expected_range:
                            raise ValueError(f"artifact server did not honor requested range {expected_range}")
                        data: bytes = response.read(end - start + 2)
                        if len(data) != end - start + 1:
                            raise OSError(f"artifact range {start}-{end}: received only {len(data)} bytes")
                        return data
                except (OSError, http.client.HTTPException) as error:
                    if attempt == 4:
                        raise
                    print(f"Retrying SpEQ range {start}-{end}: {error}", file=sys.stderr, flush=True)
                    time.sleep(2**attempt)
            raise AssertionError("unreachable range retry state")

        def read(self, size: int = -1) -> bytes:
            if size < 0:
                raise ValueError("archive reader requires bounded reads")
            output = bytearray()
            while len(output) < size:
                if self.offset == len(self.current):
                    if not self.pending:
                        break
                    self.current = self.pending.popleft().result()
                    self.offset = 0
                    if self.next_start < transfer_size:
                        self.pending.append(self.pool.submit(self.fetch, self.next_start))
                        self.next_start += self.chunk_size
                take = min(size - len(output), len(self.current) - self.offset)
                output.extend(self.current[self.offset : self.offset + take])
                self.offset += take
            data = bytes(output)
            self.md5.update(data)
            self.received += len(data)
            if self.received - self.reported >= 64 * 1024**2:
                self.reported = self.received
                elapsed = time.monotonic() - started
                print(
                    f"SpEQ stream: {self.received / 1024**2:.0f} MiB, "
                    f"{self.received / 1024**2 / elapsed:.1f} MiB/s; "
                    f"{len(evidence['selected'])}/{len(wanted)} required files verified",
                    file=sys.stderr,
                    flush=True,
                )
                progress = STORAGE / "evidence/speq-stream-progress.json"
                progress.parent.mkdir(parents=True, exist_ok=True)
                progress.write_text(
                    json.dumps(
                        {**evidence, "compressed_bytes_read": self.received, "elapsed_seconds": elapsed}, indent=2
                    )
                    + "\n"
                )
            return data

        def close(self) -> None:
            self.pool.shutdown(wait=True, cancel_futures=True)
            super().close()

    reader = ProgressReader()
    try:
        with reader, index_path.open("w") as index, tarfile.open(fileobj=reader, mode="r|gz") as archive:
            for member in archive:
                relative = member.name.removeprefix("lleq-artifact/")
                evidence["last_member"] = member.name
                evidence["member_count"] += 1
                index.write(json.dumps({"name": member.name, "size": member.size, "type": member.type.decode()}) + "\n")
                index.flush()
                path_parts = Path(relative).parts
                if Path(relative).is_absolute() or ".." in path_parts:
                    raise ValueError(f"unsafe artifact member: {relative}")
                mapping_source = (
                    complete_index
                    and member.isfile()
                    and member.size <= 1_000_000
                    and (
                        re.search(r"tpal|tsvc", relative, re.IGNORECASE) is not None
                        or (
                            path_parts[0] in {"benchmarks", "analysis", "ll", "figures"}
                            and (
                                Path(relative).suffix
                                in {".c", ".cc", ".cpp", ".h", ".py", ".sh", ".md", ".txt", ".csv"}
                                or Path(relative).name.lower().startswith(("readme", "makefile"))
                            )
                        )
                        or (
                            len(path_parts) == 1
                            and (
                                Path(relative).suffix in {".py", ".md", ".txt", ".sh"}
                                or Path(relative).name.lower().startswith("readme")
                            )
                        )
                    )
                )
                if (relative in wanted and member.isfile()) or (mapping_source and mapping_bytes < 64 * 1024**2):
                    if member.size > 10_000_000:
                        raise ValueError("unexpected large recorder input")
                    handle = archive.extractfile(member)
                    assert handle is not None
                    data = handle.read()
                    digest = hashlib.sha256(data).hexdigest()
                    if relative in wanted and digest != wanted[relative]:
                        raise ValueError(f"artifact member digest mismatch: {relative}: {digest}")
                    path = artifact / relative
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(data)
                    if relative in wanted:
                        evidence["selected"][relative] = digest
                    else:
                        mapping_bytes += len(data)
                        evidence["mapping_files"][relative] = digest
                if len(evidence["selected"]) == len(wanted) and not complete_index:
                    break
            else:
                while reader.read(1024**2):
                    pass
                evidence["computed_archive_md5"] = reader.md5.hexdigest()
                if reader.received == entry["size"]:
                    if reader.md5.hexdigest() != record_speq.SPEQ_ARCHIVE_MD5:
                        raise ValueError("complete artifact MD5 differs from the pinned Zenodo record")
                    evidence["full_archive_index_examined"] = True
    except (OSError, tarfile.TarError, EOFError) as error:
        evidence["stream_end"] = str(error)
    evidence["compressed_bytes_read"] = reader.received
    evidence["member_index_sha256"] = hashlib.sha256(index_path.read_bytes()).hexdigest()
    evidence["elapsed_seconds"] = time.monotonic() - started
    evidence["missing"] = [name for name in wanted if not (artifact / name).is_file()]
    return evidence


def reconcile_speq_paper_cases() -> dict[str, dict[str, Any]]:
    """Attribute missing paper cases only from a verified, complete archive index."""
    cases: dict[str, dict[str, Any]] = {
        f"speq-{name}": {
            "status": "blocked",
            "workloads": [],
            "reason": (
                "Paper case is outside the eight preserved REVTest inputs; run --index-artifact-only "
                "to reconcile its source against the complete artifact."
            ),
        }
        for name in ("tpal", "tsvc2")
    }
    index_evidence_path = STORAGE / "evidence/speq-artifact-index.json"
    if not index_evidence_path.is_file():
        return cases
    evidence = json.loads(index_evidence_path.read_text())
    if not evidence.get("full_archive_index_examined"):
        return cases
    if evidence.get("computed_archive_md5") != record_speq.SPEQ_ARCHIVE_MD5:
        raise ValueError("paper reconciliation requires the pinned complete archive checksum")
    mapping_name = "figures/table3/draw_table3.py"
    mapping_path = STORAGE / "sources/speq/artifact" / mapping_name
    mapping_bytes = mapping_path.read_bytes()
    if hashlib.sha256(mapping_bytes).hexdigest() != evidence["mapping_files"][mapping_name]:
        raise ValueError("artifact paper-name mapping changed after extraction")
    assignments = {
        node.targets[0].id: ast.literal_eval(node.value)
        for node in ast.parse(mapping_bytes).body
        if isinstance(node, ast.Assign)
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id in ("names", "benchmarks")
    }
    index_bytes = (STORAGE / "evidence/speq-artifact-members.jsonl").read_bytes()
    if hashlib.sha256(index_bytes).hexdigest() != evidence["member_index_sha256"]:
        raise ValueError("complete artifact member index changed after extraction")
    members = {json.loads(line)["name"].removeprefix("lleq-artifact/") for line in index_bytes.splitlines()}
    for case_id, paper_name in (("speq-tpal", "TPAL"), ("speq-tsvc2", "TSVC2")):
        artifact_name = next(key for key, value in assignments["names"].items() if value == paper_name)
        expected_members = [f"benchmarks/{artifact_name}.c", f"ll/{artifact_name}.ll", f"analysis/{artifact_name}.ll"]
        present = [name for name in expected_members if name in members]
        cases[case_id].update(
            artifact_name=artifact_name,
            artifact_mapping=mapping_name,
            artifact_mapping_sha256=hashlib.sha256(mapping_bytes).hexdigest(),
            expected_artifact_members=expected_members,
            present_artifact_members=present,
            selected_by_artifact_table=artifact_name in assignments["benchmarks"],
            archive_member_count=evidence["member_count"],
            archive_md5=evidence["computed_archive_md5"],
            reason=(
                f"Artifact maps {paper_name} to {artifact_name}, but its named source and LLVM IR are absent from the "
                f"complete {evidence['member_count']:,}-member, MD5-verified archive."
                if not present
                else f"Artifact input {artifact_name} is outside the preserved REVTest recorder; "
                "a separate frontend capture and result oracle are required."
            ),
        )
    return cases


def capture_speq(artifact: Path | None, python: Path, llvm_config: Path, byte_limit: int | None) -> dict[str, Any]:
    preparation: dict[str, Any] = {}
    if artifact is None:
        preparation = stream_speq_artifact(byte_limit)
        artifact = STORAGE / "sources/speq/artifact"
    lleq = STORAGE / "sources/speq/lleq"
    for source_path, expected in (
        ("llvm/unittests/Transforms/REV/REVTest.cpp", record_speq.REV_TESTS_SHA256),
        ("llvm/lib/Analysis/REVPass.cpp", record_speq.REV_PASS_SHA256),
        ("llvm/include/llvm/Analysis/REVPass.h", record_speq.REV_PASS_HEADER_SHA256),
        # The pinned frontend makes MemoryAccess::getID public for FIR names.
        ("llvm/include/llvm/Analysis/MemorySSA.h", record_speq.REV_MEMORY_SSA_SHA256),
    ):
        fetch_verified_source(
            f"https://raw.githubusercontent.com/avery-laird/lleq/{record_speq.LLEQ_COMMIT}/{source_path}",
            lleq / source_path,
            expected,
        )
    wrapper = STORAGE / "toolchains/speq-record-with-trace.py"
    wrapper.parent.mkdir(parents=True, exist_ok=True)
    wrapper.write_text(
        "import sys\n"
        "from pathlib import Path\n"
        f"sys.path.insert(0, {str(ROOT)!r})\n"
        "from scripts.paper_benchmarks import record_speq\n"
        "trace_path = Path(sys.argv[1])\n"
        "loaded = []\n"
        "original_import = record_speq.import_parse_ir\n"
        "def retain_module(path):\n"
        "    module = original_import(path)\n"
        "    loaded.append(module)\n"
        "    return module\n"
        "record_speq.import_parse_ir = retain_module\n"
        "try:\n"
        "    record_speq.main(sys.argv[2:])\n"
        "finally:\n"
        "    for index, module in enumerate(loaded):\n"
        "        path = trace_path.with_name(f'{trace_path.stem}-{index:03d}.egg')\n"
        "        path.write_text(module.egraph.as_egglog_string)\n"
    )
    results: dict[str, Any] = {}
    for name in SPEQ_NAMES:
        case_id = f"speq-{name}"
        print(f"Recording {case_id}", file=sys.stderr, flush=True)
        evidence_dir = STORAGE / "evidence/capture" / case_id / f"attempt-{time.time_ns()}"
        evidence_dir.mkdir(parents=True, exist_ok=True)
        fir = record_speq.extract_rev_test(lleq / "llvm/unittests/Transforms/REV/REVTest.cpp", name)
        (evidence_dir / "preserved.fir").write_text(fir)
        output = STORAGE / "workloads/speq" / f"{case_id}-recorded.egg"
        command = [
            str(python),
            str(wrapper),
            str(evidence_dir / "native-invocation.egg"),
            "--artifact",
            str(artifact),
            "--rev-tests",
            str(lleq / "llvm/unittests/Transforms/REV/REVTest.cpp"),
            "--lleq",
            str(lleq),
            "--llvm-config",
            str(llvm_config),
            "--benchmark",
            name,
            "--output",
            str(output),
        ]
        source_evidence = evidence_dir / "source-frontend"
        if name in record_speq.APPLICATION_C_SHA256:
            command.extend(["--source-evidence", str(source_evidence)])
        process = run_bounded_command(command, ROOT, evidence_dir / "record")
        reason = process.message
        if process.status == "failure":
            match = re.search(
                r"^ValueError: (.+ did not extract to [^:]+):",
                process.stderr_path.read_text(),
                re.MULTILINE,
            )
            if match:
                reason = match.group(1) + "; full extracted expression retained in stderr evidence"
        raw_invocations = sorted(evidence_dir.glob("native-invocation-*.egg"))
        source_manifest_path = source_evidence / name / "manifest.json"
        source_manifest = json.loads(source_manifest_path.read_text()) if source_manifest_path.is_file() else None
        recorded_fir_sha256: str | None = hashlib.sha256(fir.encode()).hexdigest()
        if name in record_speq.APPLICATION_C_SHA256:
            chunks = source_manifest["chunks"] if source_manifest is not None else []
            recorded_fir_sha256 = chunks[0]["sha256"] if len(chunks) == 1 else None
        results[case_id] = {
            "status": "captured" if process.status == "success" else "blocked",
            "workloads": [str(output.relative_to(ROOT))] if process.status == "success" else [],
            "raw_invocations": [str(path.relative_to(ROOT)) for path in raw_invocations],
            "raw_invocation_sha256": {
                str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in raw_invocations
            },
            "fir_sha256": recorded_fir_sha256,
            **({"source_frontend": source_manifest} if name in record_speq.APPLICATION_C_SHA256 else {}),
            "command": command,
            "process": asdict(process),
            "reason": reason,
        }
        if process.status in ("resource-stopped", "memory-limit"):
            return {"preparation": preparation, "cases": results, "operational_stop": asdict(process)}
    results.update(reconcile_speq_paper_cases())
    return {"preparation": preparation, "cases": results}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=("all", "dialegg", "speq"), default="all")
    parser.add_argument("--llvm18-prefix", type=Path, default=Path("/opt/homebrew/opt/llvm@18"))
    parser.add_argument("--llvm17-config", type=Path, default=Path("/opt/homebrew/opt/llvm@17/bin/llvm-config"))
    parser.add_argument("--egglog", type=Path)
    parser.add_argument(
        "--complete", action="store_true", help="Complete native parents and validate standalone outputs"
    )
    parser.add_argument("--case", action="append", help="Exact complete-mode parent ID; repeat to select several")
    parser.add_argument("--timeout-sec", type=float, default=300, help="Complete-mode per-stage guarded deadline")
    parser.add_argument("--output", type=Path, help="Fresh complete-mode evidence directory")
    parser.add_argument("--dialegg-source", type=Path, default=STORAGE / "sources/dialegg")
    parser.add_argument("--native-egglog", type=Path, help="DialEgg's original cost-action backend executable")
    parser.add_argument(
        "--speq-frontend-flag",
        action="append",
        default=[],
        help="Explicit complete-mode original-C compiler flag (repeat; use --speq-frontend-flag=-DNAME)",
    )
    parser.add_argument(
        "--speq-phi-polarity-repair",
        action="store_true",
        help="Opt in to the recorded REV PHI repair and rebuild its plugin in complete mode",
    )
    parser.add_argument(
        "--speq-c99-frontend-repair",
        choices=("polybench-gemm-address-v1",),
        help="Opt in to scoped original-C GEMM repair; requires PHI and pinned frontend flags",
    )
    parser.add_argument("--speq-lleq", type=Path, default=STORAGE / "sources/speq/lleq")
    parser.add_argument("--speq-rev-plugin", type=Path, help="Optional already-built pinned REV analysis plugin")
    parser.add_argument(
        "--list-cases", action="store_true", help="List complete-mode parent IDs without running anything"
    )
    parser.add_argument("--speq-artifact", type=Path)
    parser.add_argument("--speq-python", type=Path, default=Path(sys.executable))
    parser.add_argument("--artifact-byte-limit", type=int, help="optional compressed-byte transfer limit")
    parser.add_argument(
        "--index-artifact-only",
        action="store_true",
        help="stream the complete SpEQ member index and verify archive MD5",
    )
    args = parser.parse_args()
    if args.timeout_sec <= 0:
        parser.error("--timeout-sec must be positive")
    if args.complete or args.list_cases:
        from scripts.dialegg_speq_complete import complete_capture, complete_case_ids

        if args.list_cases:
            print("\n".join(complete_case_ids(args.family)))
            return 0
        if args.index_artifact_only or args.output is None or args.egglog is None:
            parser.error("--complete requires --output and --egglog and cannot index/download the artifact")
        if args.family in ("all", "dialegg") and args.native_egglog is None:
            parser.error("complete DialEgg requires --native-egglog (the original cost-action backend)")
        if args.family in ("all", "speq") and args.speq_artifact is None:
            parser.error("complete SpEQ requires --speq-artifact; preparation/downloads are a separate stage")
        return complete_capture(args)
    if (
        args.case
        or args.output
        or args.native_egglog
        or args.speq_frontend_flag
        or args.speq_phi_polarity_repair
        or args.speq_c99_frontend_repair
    ):
        parser.error("case/output/backend/frontend flags and PHI repair require --complete")
    if args.artifact_byte_limit is not None and args.artifact_byte_limit <= 0:
        parser.error("--artifact-byte-limit must be positive")
    if args.index_artifact_only:
        result = stream_speq_artifact(args.artifact_byte_limit, complete_index=True)
        (STORAGE / "evidence/speq-artifact-index.json").write_text(json.dumps(result, indent=2) + "\n")
        (STORAGE / "evidence/speq-artifact-paper-cases.json").write_text(
            json.dumps(reconcile_speq_paper_cases(), indent=2) + "\n"
        )
        return 0 if result["full_archive_index_examined"] else 1
    for family in ("dialegg", "speq") if args.family == "all" else (args.family,):
        if family == "dialegg":
            result = capture_dialegg(args.llvm18_prefix.resolve(), args.egglog.resolve() if args.egglog else None)
        else:
            result = capture_speq(
                args.speq_artifact.resolve() if args.speq_artifact else None,
                args.speq_python.absolute(),
                args.llvm17_config.resolve(),
                args.artifact_byte_limit,
            )
        path = STORAGE / "evidence" / f"{family}-capture-results.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(result, indent=2, default=str) + "\n")
        for case_id, case in result["cases"].items():
            print(f"{case_id}: {case['status']}, {len(case['workloads'])} invocations")
        if result.get("operational_stop"):
            print("Resource guard stopped acquisition; remaining cases are pending.", file=sys.stderr)
            return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
