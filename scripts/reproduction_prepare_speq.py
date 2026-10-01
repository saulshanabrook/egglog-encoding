"""Prepare SpEQ's original inputs, LLVM 17 REV plugin and egglog-python 13.2 port.

Run as ``python -m scripts.reproduction_prepare_speq``. Acquisition and native
commands run only when explicitly invoked, under the ordinary guard and CLI lock.
An explicit scoped C99 mode additionally gates fresh paired source repairs;
complete optimization and device execution remain outside preparation.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import platform
import re
import shutil
import sys
import tarfile
import urllib.request
from dataclasses import asdict
from functools import partial
from pathlib import Path, PurePosixPath
from typing import Any

from benchmarking.memory_guard import GROUP_LIMIT_BYTES
from benchmarking.pilot import PilotProcessResult, run_bounded_command
from benchmarking.targets import sha256_file
from scripts.paper_benchmarks import record_speq
from scripts.reproduction_process import exclusive_job

ROOT = Path(__file__).resolve().parents[1]
LLVM_VERSION = "17.0.6"
PYTHON_VERSION = "3.11.11"
SETUPTOOLS_VERSION = "80.9.0"  # z3-solver 4.12.2.0 imports the retired pkg_resources API.
ARCHIVE_BYTES = 6_259_975_347
DOCKERFILE_BYTES = 1893
ARTIFACT_HASHES = {
    "parseIR.py": record_speq.PARSE_IR_SHA256,
    "run_benchmark.py": record_speq.RUN_BENCHMARK_SHA256,
    "requirements.txt": "fbba60f4c8dcf962814f470028534a52258cab17004b949d346066ffa4f6bad5",
    "driver.py": "f890ec4f0852ff3dd9e52812fa6a5888eb31f8ab916c8594a0e4ebe9a849fb4b",
    "run_table3.sh": "6c15c3043e765fca0a1848e5eb75d60d78214f9f46c98a966ea53581642f02d6",
    "figures/table3/draw_table3.py": "ecc1d6b16764a2621bc4ed8d8712aa7bc13c670d48528fa1193ab145a9780c26",
    **{f"analysis/{name}.ll": digest for name, digest in record_speq.REFERENCE_ANALYSIS_SHA256.items()},
    **{f"benchmarks/{name}.c": digest for name, digest in record_speq.COMPLETE_APPLICATION_C_SHA256.items()},
    **{f"benchmarks/{name}": digest for name, digest in record_speq.APPLICATION_HEADER_SHA256.items()},
}
REV_HASHES = {
    "llvm/lib/Analysis/REVPass.cpp": record_speq.REV_PASS_SHA256,
    "llvm/include/llvm/Analysis/REVPass.h": record_speq.REV_PASS_HEADER_SHA256,
    "llvm/include/llvm/Analysis/MemorySSA.h": record_speq.REV_MEMORY_SSA_SHA256,
    "llvm/unittests/Transforms/REV/REVTest.cpp": record_speq.REV_TESTS_SHA256,
}
PYTHON_REQUIREMENTS = (
    f"egglog=={record_speq.EGGLOG_PYTHON_VERSION}\nlark==1.1.7\nz3-solver==4.12.2.0\nsetuptools=={SETUPTOOLS_VERSION}\n"
)


def acquire_artifact(destination: Path) -> dict[str, Any]:
    """Stream the pinned archive, retaining exact inputs plus its formerly omitted Dockerfile.

    This child entry point is launched by prepare_speq's guard. No cached source or
    index is overwritten, no archive code executes, and no unrequested member is extracted.
    """
    destination.mkdir(parents=True, exist_ok=False)
    metadata_url = f"https://zenodo.org/api/records/{record_speq.SPEQ_RECORD}"
    with urllib.request.urlopen(metadata_url, timeout=30) as response:
        metadata = json.load(response)
    (destination / "zenodo-record.json").write_text(json.dumps(metadata, indent=2) + "\n")
    matches = [row for row in metadata["files"] if row["checksum"] == "md5:" + record_speq.SPEQ_ARCHIVE_MD5]
    if len(matches) != 1 or matches[0]["size"] != ARCHIVE_BYTES:
        raise ValueError("Zenodo archive identity or length differs from the pinned artifact")
    entry = matches[0]
    url = f"https://zenodo.org/api/records/{record_speq.SPEQ_RECORD}/files/speq-artifact.tar.gz/content"
    selected: dict[str, str] = {}
    artifact = destination / "artifact"
    artifact.mkdir()
    index_path = destination / "members.jsonl"
    wanted = set(ARTIFACT_HASHES) | {"Dockerfile"}
    count = 0

    class ArchiveReader(io.RawIOBase):
        """Hash ordered compressed bytes without buffering the multi-GB archive."""

        def __init__(self, response: Any) -> None:
            self.response = response
            self.md5 = hashlib.md5()
            self.received = 0

        def read(self, size: int = -1) -> bytes:
            if size < 0:
                raise ValueError("unbounded archive read refused")
            data: bytes = self.response.read(size)
            self.md5.update(data)
            self.received += len(data)
            if self.received > ARCHIVE_BYTES:
                raise ValueError("artifact exceeds its pinned compressed length")
            return data

    with urllib.request.urlopen(url, timeout=60) as response, index_path.open("x") as index:
        reader = ArchiveReader(response)
        with tarfile.open(fileobj=reader, mode="r|gz") as archive:
            for member in archive:
                path = PurePosixPath(member.name)
                if path.is_absolute() or ".." in path.parts:
                    raise ValueError(f"unsafe artifact member: {member.name}")
                count += 1
                index.write(json.dumps({"name": member.name, "size": member.size, "type": member.type.decode()}) + "\n")
                relative = member.name.removeprefix("lleq-artifact/")
                if member.name != "lleq-artifact/" + relative or relative not in wanted:
                    continue
                if not member.isfile() or relative in selected or member.size > 1_000_000:
                    raise ValueError(f"duplicate, non-regular or oversized selected member: {relative}")
                if relative == "Dockerfile" and member.size != DOCKERFILE_BYTES:
                    raise ValueError("root Dockerfile differs from the previously verified archive index")
                handle = archive.extractfile(member)
                assert handle is not None
                data = handle.read(member.size + 1)
                digest = hashlib.sha256(data).hexdigest()
                if len(data) != member.size or (relative in ARTIFACT_HASHES and digest != ARTIFACT_HASHES[relative]):
                    raise ValueError(f"artifact member digest/size mismatch: {relative}")
                target = artifact / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
                selected[relative] = digest
        while reader.read(1024**2):
            pass
    if reader.received != ARCHIVE_BYTES or reader.md5.hexdigest() != record_speq.SPEQ_ARCHIVE_MD5:
        raise ValueError("complete archive checksum or length mismatch; extracted files are not admitted")
    if missing := wanted - selected.keys():
        raise ValueError(f"missing required artifact members: {sorted(missing)}")
    record = {
        "archive_record": record_speq.SPEQ_RECORD,
        "archive": entry,
        "full_archive_index_examined": True,
        "computed_archive_md5": reader.md5.hexdigest(),
        "compressed_bytes_read": reader.received,
        "member_count": count,
        "member_index_sha256": sha256_file(index_path),
        "selected": selected,
    }
    (destination / "artifact-receipt.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def prepare_speq(
    output: Path,
    engine: Path,
    *,
    llvm_config: Path = Path("/opt/homebrew/opt/llvm@17/bin/llvm-config"),
    artifact_source: Path | None = None,
    artifact_receipt: Path | None = None,
    lleq_source: Path | None = None,
    acquire_archive: bool = False,
    timeout_sec: float = 1800,
    c99_frontend_repair: str | None = None,
) -> dict[str, Any]:
    """Prepare immutable dependencies and publish settings after source/tool/reference gates."""
    if c99_frontend_repair not in (None, "polybench-gemm-address-v1"):
        raise ValueError("unknown C99 frontend repair scope")
    output, engine, llvm_config = output.resolve(), engine.resolve(), llvm_config.resolve()
    durable = (ROOT / "benchmarks/local/reproduction").resolve()
    if not output.is_relative_to(durable) or output.exists():
        raise ValueError(f"preparation requires a fresh directory below {durable}")
    if not engine.is_file() or not llvm_config.is_file() or timeout_sec <= 0:
        raise ValueError("existing ordinary engine, LLVM 17 llvm-config, and positive timeout are required")
    if acquire_archive and (artifact_source is not None or artifact_receipt is not None):
        raise ValueError("choose archive acquisition or an existing verified artifact source/receipt")
    output.mkdir(parents=True)
    evidence = output / "evidence"
    evidence.mkdir()
    receipt = output / "preparation.json"
    record: dict[str, Any] = {
        "status": "blocked",
        "reason": None,
        "steps": [],
        "device_execution": False,
        "benchmark_execution": False,
        "lleq_revision": record_speq.LLEQ_COMMIT,
        "python_version": PYTHON_VERSION,
        "egglog_python_version": record_speq.EGGLOG_PYTHON_VERSION,
        "setuptools_version": SETUPTOOLS_VERSION,
        "missing_paper_inputs": ["speq-tpal", "speq-tsvc2"],
        "implementation_sha256": sha256_file(Path(__file__)),
        "recorder_sha256": sha256_file(ROOT / "scripts/paper_benchmarks/record_speq.py"),
        "plugin_wrapper_sha256": sha256_file(ROOT / "scripts/paper_benchmarks/speq_rev_plugin.cpp"),
    }
    environment = {
        "PYTHONNOUSERSITE": "1",
        "PYTHONPATH": str(ROOT),
        "UV_CACHE_DIR": str(output / "uv-cache"),
        "UV_PYTHON_INSTALL_DIR": str(output / "python-runtimes"),
        "UV_CONCURRENT_BUILDS": "1",
        "CMAKE_BUILD_PARALLEL_LEVEL": "1",
        "MAKEFLAGS": "-j1",
        "PIP_DISABLE_PIP_VERSION_CHECK": "1",
    }

    def step(name: str, command: list[str], *, memory_limit_bytes: int = GROUP_LIMIT_BYTES) -> PilotProcessResult:
        """Retain intent and guarded outcome; no dependent step runs after any failure."""
        argv = ["env", *(f"{key}={value}" for key, value in environment.items()), *command]
        row: dict[str, Any] = {"name": name, "command": argv, "cwd": str(ROOT), "status": "running"}
        record["steps"].append(row)
        receipt.write_text(json.dumps(record, indent=2, default=str) + "\n")
        try:
            result = run_bounded_command(
                argv,
                ROOT,
                evidence / f"{len(record['steps']):03}-{name}",
                timeout_sec=timeout_sec,
                memory_limit_bytes=memory_limit_bytes,
                require_guard=True,
                disk_reserve_bytes=10 * 1024**3,
                allow_warning_pressure=True,
            )
        except ValueError as error:
            row.update(status="resource-stopped" if "guard refused" in str(error) else "blocked", message=str(error))
            record.update(status=row["status"], reason=f"{name}: {error}")
            raise
        row.update(asdict(result))
        receipt.write_text(json.dumps(record, indent=2, default=str) + "\n")
        if result.status != "success":
            record.update(status=result.status, reason=f"{name}: {result.message or result.status}")
            raise ValueError(record["reason"])
        return result

    try:
        uv = shutil.which("uv")
        if not uv:
            raise ValueError("uv is required to prepare an isolated Python runtime and hashed dependency lock")
        version = step("llvm-version", [str(llvm_config), "--version"]).stdout_path.read_text().strip()
        if version != LLVM_VERSION:
            raise ValueError(f"this inspected recipe requires LLVM {LLVM_VERSION}; observed {version!r}")
        bindir = Path(step("llvm-bindir", [str(llvm_config), "--bindir"]).stdout_path.read_text().strip())
        libraries = step("llvm-libraries", [str(llvm_config), "--libfiles"]).stdout_path.read_text().split()
        tools = [llvm_config, bindir / "clang", bindir / "clang++", bindir / "opt", Path(uv)]
        tools.extend(Path(path) for path in libraries)
        if not libraries or any(not path.is_file() for path in tools):
            raise ValueError("LLVM development libraries or compiler/optimizer executables are missing")
        record["native_tools"] = {str(path.resolve()): sha256_file(path) for path in tools}
        clang_version = step("clang-version", [str(bindir / "clang"), "--version"]).stdout_path.read_text()
        opt_version = step("opt-version", [str(bindir / "opt"), "--version"]).stdout_path.read_text()
        if f"clang version {LLVM_VERSION}" not in clang_version or f"LLVM version {LLVM_VERSION}" not in opt_version:
            raise ValueError("Clang/opt versions do not match the LLVM development installation")
        if acquire_archive:
            acquisition = output / "archive"
            step(
                "artifact-acquisition",
                [
                    sys.executable,
                    "-c",
                    "from pathlib import Path; from scripts.reproduction_prepare_speq import "
                    "acquire_artifact; import sys; acquire_artifact(Path(sys.argv[1]))",
                    str(acquisition),
                ],
            )
            artifact_source = acquisition / "artifact"
            artifact_receipt = acquisition / "artifact-receipt.json"
        artifact_source = artifact_source or ROOT / "benchmarks/local/sources/speq/artifact"
        artifact_receipt = artifact_receipt or ROOT / "benchmarks/local/evidence/speq-artifact-index.json"
        receipt_bytes = artifact_receipt.read_bytes()
        archive_record = json.loads(receipt_bytes)
        if (
            archive_record.get("computed_archive_md5") != record_speq.SPEQ_ARCHIVE_MD5
            or not archive_record.get("full_archive_index_examined")
            or archive_record.get("compressed_bytes_read") != ARCHIVE_BYTES
        ):
            raise ValueError("artifact source requires a complete pinned archive verification receipt")
        index_path = Path(archive_record.get("member_index", artifact_receipt.parent / "members.jsonl"))
        if not index_path.is_file():
            # The historical receipt retains its old temporary path. Its exact
            # index was relocated alongside the receipt, under the same name.
            index_path = artifact_receipt.parent / index_path.name
        index_bytes = index_path.read_bytes()
        index_digest = hashlib.sha256(index_bytes).hexdigest()
        if index_digest != archive_record.get("member_index_sha256", "").removeprefix("sha256:"):
            raise ValueError("artifact member index differs from the complete archive receipt")
        member_count = 0
        dockerfile_members = []
        for line in index_bytes.splitlines():
            member = json.loads(line)
            member_count += 1
            if member.get("name") == "lleq-artifact/Dockerfile":
                dockerfile_members.append(member)
        if member_count != archive_record.get("member_count"):
            raise ValueError("artifact member count differs from the complete archive receipt")
        if len(dockerfile_members) != 1 or any(
            dockerfile_members[0].get(key) != value for key, value in {"size": DOCKERFILE_BYTES, "type": "0"}.items()
        ):
            raise ValueError("artifact index requires the original regular root Dockerfile")
        member_hashes = {**archive_record.get("mapping_files", {}), **archive_record.get("selected", {})}
        dockerfile = artifact_source / "Dockerfile"
        retain_dockerfile = "Dockerfile" in member_hashes
        if retain_dockerfile != (dockerfile.exists() or dockerfile.is_symlink()):
            raise ValueError("retained root Dockerfile and archive receipt disagree")
        (evidence / "artifact-receipt.json").write_bytes(receipt_bytes)
        retained_index = evidence / index_path.name
        retained_index.write_bytes(index_bytes)
        record["artifact_provenance"] = {
            "receipt": str(evidence / "artifact-receipt.json"),
            "receipt_sha256": hashlib.sha256(receipt_bytes).hexdigest(),
            "member_index": str(retained_index),
            "member_index_sha256": index_digest,
            "dockerfile": {
                "status": "retained" if retain_dockerfile else "not-retained",
                "archive_member": "lleq-artifact/Dockerfile",
                "size": DOCKERFILE_BYTES,
                "sha256": member_hashes.get("Dockerfile"),
                "used_by_native_preparation": False,
                "reason": None if retain_dockerfile else "historical extraction omitted this unused provenance file",
            },
        }
        sources = output / "sources"
        artifact, lleq = sources / "artifact", sources / "lleq"
        retained: dict[str, str] = {}
        for relative in [*ARTIFACT_HASHES, *(["Dockerfile"] if retain_dockerfile else [])]:
            original = artifact_source / relative
            with original.open("rb") as handle:
                data = handle.read(1_000_001)
            if len(data) > 1_000_000:
                raise ValueError(f"oversized artifact source: {relative}")
            digest = hashlib.sha256(data).hexdigest()
            if digest != member_hashes.get(relative) or (
                relative in ARTIFACT_HASHES and digest != ARTIFACT_HASHES[relative]
            ):
                raise ValueError(f"artifact source or receipt changed: {relative}")
            if relative == "Dockerfile" and len(data) != DOCKERFILE_BYTES:
                raise ValueError("root Dockerfile has unexpected length")
            target = artifact / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            retained[relative] = digest
        record["artifact_members"] = retained
        lleq_source = lleq_source or ROOT / "benchmarks/local/sources/speq/lleq"
        for relative, digest in REV_HASHES.items():
            target = lleq / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            cached = lleq_source / relative
            if cached.is_file():
                record_speq.read_verified(cached, digest)
                shutil.copyfile(cached, target)
            else:
                url = f"https://raw.githubusercontent.com/avery-laird/lleq/{record_speq.LLEQ_COMMIT}/{relative}"
                step(
                    "rev-source-" + target.name,
                    [
                        sys.executable,
                        "-c",
                        "import pathlib,sys,urllib.request; "
                        "pathlib.Path(sys.argv[2]).write_bytes(urllib.request.urlopen(sys.argv[1],timeout=30).read())",
                        url,
                        str(target),
                    ],
                )
                record_speq.read_verified(target, digest)
        record["rev_sources"] = REV_HASHES
        python = output / "python/bin/python"
        step(
            "python-environment",
            [uv, "venv", "--seed", "--managed-python", "--python", PYTHON_VERSION, str(python.parent.parent)],
        )
        requirements = evidence / "requirements.in"
        requirements.write_text(PYTHON_REQUIREMENTS)
        lock = evidence / "requirements.lock"
        step(
            "python-lock",
            [
                uv,
                "pip",
                "compile",
                "--python",
                str(python),
                "--generate-hashes",
                "--only-binary",
                ":all:",
                str(requirements),
                "--output-file",
                str(lock),
            ],
        )
        wheels = evidence / "wheels"
        wheels.mkdir()
        step(
            "python-download",
            [
                str(python),
                "-m",
                "pip",
                "download",
                "--require-hashes",
                "--only-binary=:all:",
                "--dest",
                str(wheels),
                "-r",
                str(lock),
            ],
        )
        step(
            "python-install",
            [
                str(python),
                "-m",
                "pip",
                "install",
                "--no-index",
                "--find-links",
                str(wheels),
                "--require-hashes",
                "-r",
                str(lock),
            ],
        )
        step("python-freeze", [str(python), "-m", "pip", "freeze", "--all"])
        record["python_wheels"] = {path.name: sha256_file(path) for path in sorted(wheels.glob("*.whl"))}
        if not record["python_wheels"] or not lock.is_file():
            raise ValueError("resolved Python lock and downloaded wheels were not retained")
        adapted = evidence / "adapted/parseIR.py"
        adapted.parent.mkdir()
        adapted.write_text(record_speq.adapt_parse_ir((artifact / "parseIR.py").read_text()))
        probe = step(
            "python-import",
            [
                str(python),
                "-c",
                "import importlib.metadata as m,json,sys,pkg_resources; "
                "from pathlib import Path; from scripts.paper_benchmarks import record_speq as r; "
                f"assert m.version('setuptools') == {SETUPTOOLS_VERSION!r}; "
                "r.import_parse_ir(Path(sys.argv[1])); "
                "assert m.version('egglog') == r.EGGLOG_PYTHON_VERSION; "
                "print(json.dumps({'python':sys.version,'executable':sys.executable,'egglog':m.version('egglog'),"
                "'setuptools':m.version('setuptools'),'pkg_resources':pkg_resources.__file__}))",
                str(adapted),
            ],
        )
        record["python_probe"] = probe.stdout_path.read_text().strip()
        plugin = output / "rev-plugin.so"
        step(
            "rev-build",
            [
                str(python),
                "-c",
                "from pathlib import Path; import sys; "
                "from scripts.paper_benchmarks.record_speq import build_rev_plugin; "
                "print(build_rev_plugin(*map(Path,sys.argv[1:])))",
                str(lleq),
                str(llvm_config),
                str(plugin),
            ],
        )
        if not plugin.is_file() or not plugin.stat().st_size:
            raise ValueError("REV plugin build did not retain a nonempty shared library")
        references = evidence / "reference-fir"
        references.mkdir()
        for name in record_speq.REFERENCE_ANALYSIS_SHA256:
            step(
                "reference-" + name,
                [
                    str(python),
                    "-c",
                    "from pathlib import Path; import sys; "
                    "from scripts.paper_benchmarks.record_speq import reference_fir; "
                    "fir=reference_fir(Path(sys.argv[1]),Path(sys.argv[2]),Path(sys.argv[3]),sys.argv[4]); "
                    "Path(sys.argv[5]).write_text(fir)",
                    str(bindir / "opt"),
                    str(plugin),
                    str(artifact / f"analysis/{name}.ll"),
                    name,
                    str(references / f"{name}.fir"),
                ],
            )
        for name, digest in record_speq.REFERENCE_FIR_SHA256.items():
            record_speq.read_verified(references / f"{name}.fir", digest)
        c99_paths: list[str] = []
        if c99_frontend_repair:
            from scripts.speq_c99_gates import run_gates

            c99_directory = output / "c99-gates"
            gates = run_gates(lleq, artifact, llvm_config, c99_directory, partial(step, memory_limit_bytes=5 * 1024**3))
            if gates.get("status") != "success" or gates.get("contract") != c99_frontend_repair:
                raise ValueError("fresh C99 gates did not complete successfully")
            record["c99_gates"] = gates
            c99_paths = [str(c99_directory), *gates["artifacts"]]
        linked: dict[str, str] = {}
        inspector = "otool" if platform.system() == "Darwin" else "ldd"
        for name, binary in [("plugin", plugin), ("clang", bindir / "clang"), ("opt", bindir / "opt")]:
            args = [inspector, "-L", str(binary)] if inspector == "otool" else [inspector, str(binary)]
            observed = step("linked-" + name, args).stdout_path.read_text()
            for path in re.findall(r"(?:=>\s+|^\s*)(/[^\s]+)\s+\(", observed, re.M):
                if Path(path).is_file():
                    linked[path] = sha256_file(Path(path))
        record["linked_libraries"] = linked
        record["artifacts"] = {str(path): sha256_file(path) for path in (plugin, lock, adapted, python.resolve())}
        settings = {
            "speq": {
                "revision": record_speq.LLEQ_COMMIT,
                "paths": {
                    "speq_artifact": str(artifact),
                    "speq_lleq": str(lleq),
                    "speq_python": str(python),
                    "speq_rev_plugin": str(plugin),
                    "llvm17_config": str(llvm_config),
                    "egglog": str(engine),
                },
                "timeout_sec": 300,
                "frontend_flags": ["-D_FORTIFY_SOURCE=0", "-DPOLYBENCH_USE_C99_PROTO"],
                "phi_polarity_repair": True,
                **({"c99_frontend_repair": c99_frontend_repair} if c99_frontend_repair else {}),
                "identity_paths": [
                    str(sources),
                    str(evidence),
                    str(output / "python"),
                    str(output / "python-runtimes"),
                    str(python.resolve()),
                    str(plugin),
                    str(Path(__file__).resolve()),
                    str(ROOT / "scripts/paper_benchmarks/record_speq.py"),
                    str(ROOT / "scripts/paper_benchmarks/speq_rev_plugin.cpp"),
                    *c99_paths,
                    *record["native_tools"],
                    *linked,
                ],
            }
        }
        settings_path = output / "settings.json"
        settings_path.write_text(json.dumps(settings, indent=2) + "\n")
        record.update(
            status="success",
            settings=str(settings_path),
            settings_sha256=sha256_file(settings_path),
            reason="Prerequisites prepared; eight native optimization parents remain unrun, two paper inputs missing",
        )
    except (OSError, ValueError) as error:
        if record["reason"] is None:
            record.update(status="blocked", reason=str(error))
    finally:
        receipt.write_text(json.dumps(record, indent=2, default=str) + "\n")
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--egglog", type=Path, default=ROOT / "target/release/egglog-experimental")
    parser.add_argument("--llvm-config", type=Path, default=Path("/opt/homebrew/opt/llvm@17/bin/llvm-config"))
    parser.add_argument("--artifact-source", type=Path)
    parser.add_argument("--artifact-receipt", type=Path)
    parser.add_argument("--lleq-source", type=Path)
    parser.add_argument("--acquire-archive", action="store_true", help="Stream and verify the full 6.26-GB artifact")
    parser.add_argument("--timeout-sec", type=float, default=1800)
    parser.add_argument("--c99-frontend-repair", choices=("polybench-gemm-address-v1",))
    args = parser.parse_args()
    with exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        result = prepare_speq(
            args.output,
            args.egglog,
            llvm_config=args.llvm_config,
            artifact_source=args.artifact_source,
            artifact_receipt=args.artifact_receipt,
            lleq_source=args.lleq_source,
            acquire_archive=args.acquire_archive,
            timeout_sec=args.timeout_sec,
            c99_frontend_repair=args.c99_frontend_repair,
        )
    print(json.dumps({key: result.get(key) for key in ("status", "reason", "settings")}, indent=2))
    return 0 if result["status"] == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
