"""Prepare isolated MISAAL packages, source API gates, and capture requests.

The public CLI owns the shared heavy-job lock and guards every acquisition and
native child. Internal child modes are implementation details, not entrypoints.
Raw package preparation emits blocked candidates. The coordinator's complete
recipe adds the reviewed ABI gates and runtime seal before publishing requests.
No source optimization, LLVM build, or Cargo build runs here.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import time
import urllib.parse
import urllib.request
import zipfile
from contextlib import nullcontext
from dataclasses import asdict
from pathlib import Path, PurePosixPath
from typing import Any

from benchmarking.pilot import run_bounded_command
from scripts.misaal_reproduction import verified_request
from scripts.reproduction_prepare_misaal import HYDRIDE_REVISION, MISAAL_REVISION, sha256_file, write_json
from scripts.reproduction_process import DISK_RESERVE_BYTES, exclusive_job

ROOT = Path(__file__).resolve().parents[1]
RACKET = Path("/Applications/Racket v9.2/bin/racket")
RACKET_SHA256 = "5cd73913bd9ee3da9745fdecb6bfbc4516b39888f2fcd060b5d1282ee8c0d2d0"
RACO_SHA256 = "03a77daf7c01a94f2021d5aa9760cbe753272792a53b2984779fbac49bba678c"
Z3_ARCHIVE_SHA256 = "c53f9513283ce96ffd442fa134e48c1c67e4de486953f965a3b61a407144a255"
Z3_ARCHIVE_BYTES = 8_002_399
Z3_BYTES = 20_730_655
DSL_UTILS_SHA256 = "e385eaa17a81bbcb8106ad33cbbe1ac2ed4307879b0f366f3b72219744b43bdb"
MAX_PACKAGE_BYTES = 32 * 1024**2
MAX_FILE_BYTES = 4 * 1024**2
MAX_TREE_BYTES = 2 * 1024**2
MAX_FILES = 1600
SCHEMA = "misaal-racket-candidate-v1"
SERVER_SHA256 = "2b58d9207e8d505c196468af160a6275b71fe0ddffe0691c901316cf8b66231e"

# package: (tree hash, API tree URL, pinned raw-file prefix)
PACKAGES = {
    "custom-load": (
        "7a450084d7d94893c54037c41a7a5e865f62fd92",
        "https://api.github.com/repos/rmculpepper/custom-load/git/trees/"
        "7a450084d7d94893c54037c41a7a5e865f62fd92?recursive=1",
        "https://raw.githubusercontent.com/rmculpepper/custom-load/142b32a0381d271f4bc6efbbcf3d306a0ee55566/",
    ),
    "rfc6455": (
        "f30d7e5a1e1d91e32b03116806e238afec7461ae",
        "https://git.leastfixedpoint.com/api/v1/repos/tonyg/racket-rfc6455/git/trees/"
        "e3a87e914e25841a6e1bb996aa001aeb178284bf?recursive=true",
        "https://git.leastfixedpoint.com/tonyg/racket-rfc6455/raw/commit/e3a87e914e25841a6e1bb996aa001aeb178284bf/",
    ),
    "rosette": (
        "d722c2d7f8d7f26612752230b04e3b7ef830ce42",
        "https://api.github.com/repos/akothen/Hydride/git/trees/d722c2d7f8d7f26612752230b04e3b7ef830ce42?recursive=1",
        f"https://raw.githubusercontent.com/akothen/Hydride/{HYDRIDE_REVISION}/rosette/",
    ),
    "hydride": (
        "71f6b3960f3707b632a1a595f19ec01f8ea54d34",
        "https://api.github.com/repos/akothen/Hydride/git/trees/71f6b3960f3707b632a1a595f19ec01f8ea54d34?recursive=1",
        f"https://raw.githubusercontent.com/akothen/Hydride/{HYDRIDE_REVISION}/code-synthesizer/hydride/",
    ),
    "misaal": (
        "25a09c474bf212ff8e49100abc8633193766d678",
        "https://api.github.com/repos/RafaeNoor/MISAAL/git/trees/25a09c474bf212ff8e49100abc8633193766d678?recursive=1",
        f"https://raw.githubusercontent.com/RafaeNoor/MISAAL/{MISAAL_REVISION}/misaal/",
    ),
}

HEADER = """#lang rosette
(require rosette/lib/synthax rosette/lib/angelic racket/pretty
         rosette/lib/destruct hydride misaal
         rosette/solver/smt/boolector rosette/solver/smt/z3)
(current-bitwidth 16)
(unless (eq? (subprocess-group-enabled) #f)
  (error 'misaal-smoke "subprocess group default changed"))
"""
SOLVE = """(current-solver (z3 #:path (getenv "MISAAL_Z3_PATH")))
(define-symbolic x (bitvector 8))
(define result (solve (assert (bveq (bvadd x (bv 1 8)) (bv 3 8)))))
(unless (and (sat? result) (equal? (evaluate x result) (bv 2 8)))
  (error 'misaal-smoke "solver result mismatch"))
(displayln "MISAAL_TINY_SOLVER_OK")
(flush-output)
(read-line)
(solver-shutdown (current-solver))
"""
PARAMETER_SMOKE = """(current-solver (z3 #:path (getenv "MISAAL_Z3_PATH")))
(define cases (list (TESTS 6 (vector 5))
                    (TESTS 10 (vector 9))
                    (TESTS 16 (vector 15))))
(define-values (found? expr) (synthesize-param-expression cases 2 0 (list)))
(unless found? (error 'misaal-smoke "parameter synthesis failed"))
(for ([tc cases])
  (unless (equal? (param_abstract:interpret expr (TESTS-input-values tc))
                  (TESTS-output-value tc))
    (error 'misaal-smoke "selected expression fails source test case")))
(printf "MISAAL_PARAM_SYNTH_OK ~v\\n" expr)
(solver-shutdown (current-solver))
"""


def fetch_bytes(url: str, limit: int) -> bytes:
    """Bound every response, reject off-origin redirects, and never send credentials."""
    request = urllib.request.Request(url, headers={"User-Agent": "egglog-misaal-prerequisite-audit"})
    with urllib.request.urlopen(request, timeout=30) as response:
        if urllib.parse.urlsplit(response.url)[:2] != urllib.parse.urlsplit(url)[:2]:
            raise ValueError("source response redirected to an unexpected origin")
        data: bytes = response.read(limit + 1)
    if len(data) > limit:
        raise ValueError("source response exceeds its byte bound")
    return data


def verify_tree(metadata: dict[str, Any], expected: str) -> list[dict[str, Any]]:
    """Reconstruct the pinned Git tree before trusting its paths or advertised blobs."""
    rows = metadata["tree"]
    if metadata.get("truncated") or not rows or len(rows) > MAX_FILES:
        raise ValueError("incomplete or oversized package tree")
    entries: dict[str, dict[str, Any]] = {}
    total = 0
    for row in rows:
        name = row["path"]
        path = PurePosixPath(name)
        if path.is_absolute() or str(path) != name or any(p in ("", ".", "..") for p in name.split("/")):
            raise ValueError("unsafe package tree path")
        if name in entries or re.fullmatch(r"[0-9a-f]{40}", row["sha"]) is None:
            raise ValueError("duplicate path or invalid Git identity")
        if (row["type"], row["mode"]) not in (("tree", "040000"), ("blob", "100644"), ("blob", "100755")):
            raise ValueError("package contains a symlink, submodule, or unsupported member")
        if row["type"] == "blob":
            size = row["size"]
            if not isinstance(size, int) or not 0 <= size <= MAX_FILE_BYTES:
                raise ValueError("package file exceeds its byte bound")
            total += size
        entries[name] = row
    if total > MAX_PACKAGE_BYTES:
        raise ValueError("package exceeds its aggregate byte bound")
    children: dict[str, list[dict[str, Any]]] = {"": []}
    for name, row in entries.items():
        parent = str(PurePosixPath(name).parent)
        parent = "" if parent == "." else parent
        if parent and (parent not in entries or entries[parent]["type"] != "tree"):
            raise ValueError("package tree omits a parent directory")
        children.setdefault(parent, []).append(row)
        if row["type"] == "tree":
            children.setdefault(name, [])
    for directory in sorted(children, key=lambda p: len(PurePosixPath(p).parts), reverse=True):
        body = b""
        for row in sorted(
            children[directory], key=lambda r: PurePosixPath(r["path"]).name + "/" * (r["type"] == "tree")
        ):
            body += f"{row['mode'].lstrip('0')} {PurePosixPath(row['path']).name}\0".encode() + bytes.fromhex(
                row["sha"]
            )
        digest = hashlib.sha1(f"tree {len(body)}\0".encode() + body).hexdigest()
        if digest != (entries[directory]["sha"] if directory else expected):
            raise ValueError("package tree differs from its pinned Git identity")
    return [row for row in rows if row["type"] == "blob"]


def acquire_packages(directory: Path) -> None:
    """Child-only bounded acquisition; verify every blob against the pinned tree."""
    directory.mkdir()
    for name, (tree, api, raw) in PACKAGES.items():
        metadata = json.loads(fetch_bytes(api, MAX_TREE_BYTES))
        rows = verify_tree(metadata, tree)
        destination = directory / name
        destination.mkdir()
        files = {}
        for row in rows:
            data = fetch_bytes(raw + urllib.parse.quote(row["path"], safe="/"), row["size"])
            actual = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
            if len(data) != row["size"] or actual != row["sha"]:
                raise ValueError(f"source blob differs from pin: {name}/{row['path']}")
            path = destination / row["path"]
            path.parent.mkdir(parents=True, exist_ok=True)
            with path.open("xb") as output:
                output.write(data)
            path.chmod(int(row["mode"], 8) & 0o777)
            files[row["path"]] = hashlib.sha256(data).hexdigest()
        write_json(directory / f"{name}.json", {"tree": tree, "api": api, "raw": raw, "files": files})


def unpack_z3(archive: Path, output: Path) -> dict[str, Any]:
    """Admit only the exact retained native asset and its single regular member."""
    if archive.stat().st_size != Z3_ARCHIVE_BYTES or sha256_file(archive) != Z3_ARCHIVE_SHA256:
        raise ValueError("Z3 archive differs from its pinned bytes")
    with zipfile.ZipFile(archive) as bundle:
        members = bundle.infolist()
        if len(members) != 1:
            raise ValueError("Z3 archive must contain exactly one member")
        member = members[0]
        if member.filename != "z3" or member.file_size != Z3_BYTES or not stat.S_ISREG(member.external_attr >> 16):
            raise ValueError("Z3 archive member is not the expected regular executable")
        output.parent.mkdir(parents=True, exist_ok=True)
        with bundle.open(member) as source, output.open("xb") as target:
            shutil.copyfileobj(source, target, 1024**2)
    output.chmod(0o755)
    return {"path": str(output), "sha256": sha256_file(output), "archive_sha256": Z3_ARCHIVE_SHA256}


def audit_sources(directory: Path) -> dict[str, Any]:
    """Scan all acquired source files, keeping unknown escape/FFI sites as a stop."""
    suspect = re.compile(r"subprocess-group-enabled|setsid|setpgid|ffi/unsafe|ffi-lib|get-ffi-obj")
    launch = re.compile(r"\bsubprocess\b|\(system(?:\s|\*|/)|\(process(?:\s|\*|/)")
    findings, launchers = [], []
    count = 0
    for package in PACKAGES:
        for path in sorted((directory / package).rglob("*")):
            if not path.is_file() or path.suffix not in (
                ".rkt",
                ".rktl",
                ".ss",
                ".scm",
                ".sch",
                ".sls",
                ".sps",
                ".scrbl",
                ".py",
                ".sh",
            ):
                continue
            count += 1
            for number, line in enumerate(path.read_text().splitlines(), 1):
                row = {"path": str(path.relative_to(directory)), "line": number, "text": line}
                if suspect.search(line):
                    findings.append(row)
                if launch.search(line):
                    launchers.append(row)
    server = directory / "rosette/rosette/solver/smt/server.rkt"
    if sha256_file(server) != SERVER_SHA256:
        raise ValueError("unreviewed Rosette solver launcher identity")
    return {
        "status": "review-required" if findings else "no-escape-patterns-found",
        "files_scanned": count,
        "findings": findings,
        "launch_sites": launchers,
        "limitation": "Text scan of complete acquired packages; runtime PGID observation remains required.",
    }


def process_snapshot() -> dict[int, dict[str, Any]]:
    """Read one bounded process inventory, preserving executable paths with spaces."""
    snapshot = subprocess.run(
        ["/bin/ps", "-axo", "pid=,ppid=,pgid=,comm=", "-ww"],
        check=True,
        capture_output=True,
        text=True,
        timeout=1,
    )
    rows = {}
    for line in snapshot.stdout.splitlines():
        pid, parent, group, executable = line.strip().split(None, 3)
        rows[int(pid)] = {
            "pid": int(pid),
            "ppid": int(parent),
            "pgid": int(group),
            "executable": str(Path(executable).resolve()),
        }
    return rows


def observe_solver(racket: Path, script: Path, solver: Path, receipt: Path) -> None:
    """Observe the held real pair; always release it and audit child drain before returning."""
    record: dict[str, Any] = {"status": "failure", "expected_pgid": os.getpgrp(), "processes": []}
    process = subprocess.Popen([str(racket), str(script)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    problem: BaseException | None = None
    selected_solver = str(solver.resolve())
    try:
        assert process.stdout is not None
        for line in process.stdout:
            print(line, end="", flush=True)
            if line.strip() == "MISAAL_TINY_SOLVER_OK":
                break
        else:
            raise ValueError("solver exited before producing a verified model")
        rows = process_snapshot()
        descendants = {process.pid}
        while True:
            children = {pid for pid, row in rows.items() if row["ppid"] in descendants}
            if children <= descendants:
                break
            descendants |= children
        if process.pid not in rows:
            raise ValueError("Racket disappeared before process-group observation")
        record["processes"] = [rows[pid] for pid in sorted(descendants)]
        if any(row["pgid"] != record["expected_pgid"] for row in record["processes"]):
            raise ValueError("Racket or solver detached from the guarded process group")
        if not any(row["executable"] == selected_solver for row in record["processes"]):
            raise ValueError("the pinned solver was not observed as a live descendant")
    except BaseException as error:
        record["reason"] = str(error)
        problem = error
    finally:
        cleanup: dict[str, Any] = {"status": "failure", "release": "not-attempted", "snapshots": []}
        record["cleanup"] = cleanup
        observed = {row["pid"] for row in record["processes"]}
        try:
            # The smoke owns solver-shutdown after read-line. Do this even after
            # detachment/telemetry failure; killing its parent first skips cleanup.
            cleanup["release"] = "attempted"
            stdout, _ = process.communicate("\n", timeout=10)
            print(stdout, end="", flush=True)
            cleanup.update(release="sent", racket_returncode=process.returncode)
            if process.returncode != 0:
                raise ValueError("Racket failed while releasing the held solver")
            for attempt in range(10):
                rows = process_snapshot()
                remaining = [
                    row
                    for pid, row in rows.items()
                    if pid in observed or row["executable"] == selected_solver or row["ppid"] == process.pid
                ]
                cleanup["snapshots"].append({"remaining": remaining})
                if not remaining:
                    break
                if attempt < 9:
                    time.sleep(0.1)
            else:
                raise ValueError("observed solver processes did not drain after release")
            if not any(row["executable"] == selected_solver for row in record["processes"]):
                cleanup["status"] = "unverified"
                raise ValueError("initial solver observation missing; child drain cannot be fully verified")
            cleanup["status"] = "drained"
        except BaseException as error:
            cleanup["reason"] = str(error)
            if problem is None:
                record["reason"] = str(error)
                problem = error
        if problem is None:
            record["status"] = "observed-same-group"
        # Never signal a numeric child/group recovered from a stale snapshot.
        # Ambiguous cleanup stays a failed guard-owned attempt, with this receipt.
        write_json(receipt, record)
    if problem is not None:
        raise problem


def candidate_request(original: Path, runtime: Path, environment: dict[str, str]) -> dict[str, Any]:
    """Preserve native identities and expose augmented data only as a non-executable candidate."""
    request = verified_request(original)
    launcher = Path(request["checkout"]) / "lib/utils/DSLInstructionUtils.py"
    if sha256_file(launcher) != DSL_UTILS_SHA256:
        raise ValueError("candidate requires the reviewed Python Racket launcher")
    receipt = json.loads(runtime.read_text())
    gates = receipt["gates"]
    if (
        receipt["status"] != "source-api-blocked"
        or any(gates.get(key, {}).get("status") != "success" for key in ("imports", "tiny_solver", "source_four_args"))
        or gates.get("captured_five_args", {}).get("status") != "expected-api-failure"
        or receipt["pgid_observation"]["status"] != "observed-same-group"
        or receipt["pgid_observation"].get("cleanup", {}).get("status") != "drained"
    ):
        raise ValueError(
            "candidate requires separate real import, solver, source, API-negative, PGID, and drain evidence"
        )
    return {
        "schema": SCHEMA,
        "status": "source-api-blocked",
        "promoted": False,
        "workflow_ready": False,
        "original_request": {"path": str(original), "sha256": sha256_file(original)},
        "runtime": {"path": str(runtime), "sha256": sha256_file(runtime)},
        # Nesting prevents this artifact from being accepted as an ordinary request.
        "candidate_request": {
            **request,
            "racket": str(RACKET),
            "racket_sha256": RACKET_SHA256,
            "racket_group_containment": "misaal-racket-lease-v1",
            "source_hashes": {**request["source_hashes"], "lib/utils/DSLInstructionUtils.py": DSL_UTILS_SHA256},
            "environment": {**request["environment"], **environment},
            "environment_unset": sorted(set(request.get("environment_unset", [])) | {"PLTCOLLECTS", "PLTCONFIGDIR"}),
            "racket_runtime": {"path": str(runtime), "sha256": sha256_file(runtime), "status": "source-api-blocked"},
        },
    }


def prepare(
    output: Path,
    requests: list[Path],
    archive: Path,
    captured: Path,
    captured_sha256: str,
    *,
    lock_owned: bool = False,
) -> dict[str, Any]:
    """Own one immutable, sequential diagnostic; never publish settings or workflow readiness."""
    output = output.resolve()
    durable = (ROOT / "benchmarks/local/reproduction").resolve()
    if not output.is_relative_to(durable) or output.exists() or not requests:
        raise ValueError("require existing requests and a fresh output beneath benchmarks/local/reproduction")
    if re.fullmatch(r"[0-9a-f]{64}", captured_sha256) is None or sha256_file(captured) != captured_sha256:
        raise ValueError("captured source operation differs from the supplied identity")
    original_bytes = {str(path.resolve()): path.read_bytes() for path in requests}
    inputs = [verified_request(path) for path in requests]
    checkouts = {request["checkout"] for request in inputs}
    if len(checkouts) != 1 or any(
        request["revision"] != MISAAL_REVISION or request["hydride_revision"] != HYDRIDE_REVISION for request in inputs
    ):
        raise ValueError("all requests must share the pinned MISAAL/Hydride checkout")
    if sha256_file(RACKET) != RACKET_SHA256 or sha256_file(RACKET.with_name("raco")) != RACO_SHA256:
        raise ValueError("Racket installation differs from the reviewed executable identities")
    if archive.stat().st_size != Z3_ARCHIVE_BYTES or sha256_file(archive) != Z3_ARCHIVE_SHA256:
        raise ValueError("Z3 archive differs from its pinned bytes")
    with nullcontext() if lock_owned else exclusive_job(durable / "stages/.heavy-job.lock"):
        output.mkdir(parents=True)
        (output / "steps").mkdir()
        record: dict[str, Any] = {
            "schema": SCHEMA,
            "status": "blocked",
            "promoted": False,
            "workflow_ready": False,
            "reason": None,
            "steps": [],
            "gates": {},
            "implementation_sha256": sha256_file(Path(__file__)),
            "racket": {"path": str(RACKET), "sha256": RACKET_SHA256, "raco_sha256": RACO_SHA256},
            "original_requests": {path: hashlib.sha256(data).hexdigest() for path, data in original_bytes.items()},
        }
        for name in ("user", "addon", "tmp", "bin", "smokes", "candidates"):
            (output / name).mkdir()
        environment = {
            "PLTUSERHOME": str(output / "user"),
            "PLTADDONDIR": str(output / "addon"),
            "TMPDIR": str(output / "tmp"),
            "HYDRIDE_ROOT": str(Path(next(iter(checkouts))) / "Hydride"),
            "MISAAL_Z3_PATH": str(output / "bin/z3"),
            "PATH": f"{output / 'bin'}:{RACKET.parent}:/usr/bin:/bin:/usr/sbin:/sbin",
        }
        record["environment"] = environment

        def step(name: str, command: list[str], *, native: bool = False, expected_failure: bool = False) -> str:
            prefix = output / "steps" / f"{len(record['steps']) + 1:03}-{name}"
            argv = (
                ["/usr/bin/env", "-i", *[f"{k}={v}" for k, v in environment.items()], *command] if native else command
            )
            row: dict[str, Any] = {"name": name, "command": argv, "cwd": str(output)}
            write_json(prefix.with_suffix(".request.json"), row)
            record["steps"].append(row)
            try:
                result = run_bounded_command(
                    argv,
                    output,
                    prefix,
                    timeout_sec=600,
                    memory_limit_bytes=5 * 1024**3,
                    require_guard=True,
                    allow_warning_pressure=False,
                    disk_reserve_bytes=DISK_RESERVE_BYTES,
                )
            except (OSError, ValueError) as error:
                record["status"] = "resource-stopped" if "guard" in str(error).lower() else "blocked"
                row.update(status="launch-refused", reason=str(error))
                write_json(prefix.with_suffix(".result.json"), row)
                raise
            row.update(asdict(result))
            write_json(prefix.with_suffix(".result.json"), row)
            if result.status != "success" and not (
                expected_failure and result.status == "failure" and result.returncode == 1
            ):
                record["status"] = result.status
                raise RuntimeError(f"{name}: {result.status}; see {prefix}.result.json")
            stdout, stderr = result.stdout_path.read_text(), result.stderr_path.read_text()
            if expected_failure and (
                result.status == "success"
                or not all(
                    text in stderr
                    for text in ("synthesize-param-expression", "arity mismatch", "expected: 4", "given: 5")
                )
            ):
                raise ValueError("unchanged captured operation did not exhibit the exact expected 5/4 API failure")
            return stdout

        child = [
            sys.executable,
            "-c",
            f"import runpy,sys; sys.path.insert(0,{str(ROOT)!r}); "
            f"runpy.run_path({str(Path(__file__).resolve())!r}, run_name='__main__')",
        ]
        try:
            step("acquire-pinned-packages", [*child, "_acquire", str(output / "sources")])
            audit = audit_sources(output / "sources")
            write_json(output / "source-scan.json", audit)
            record["source_scan"] = {
                "path": str(output / "source-scan.json"),
                "sha256": sha256_file(output / "source-scan.json"),
            }
            if audit["status"] != "no-escape-patterns-found":
                raise ValueError("package source scan requires review before native execution")
            record["solver"] = unpack_z3(archive, output / "bin/z3")
            version = step("racket-version", [str(RACKET), "--version"], native=True)
            if version.strip() != "Welcome to Racket v9.2 [cs].":
                raise ValueError("unexpected Racket version")
            version = step("z3-version", [str(output / "bin/z3"), "--version"], native=True)
            if not version.strip().startswith("Z3 version 4.8.8"):
                raise ValueError("unexpected solver version")
            step(
                "installation-packages",
                [str(RACKET.with_name("raco")), "pkg", "show", "--all", "--long", "--dir"],
                native=True,
            )
            for name in PACKAGES:
                step(
                    f"install-{name}",
                    [
                        str(RACKET.with_name("raco")),
                        "pkg",
                        "install",
                        "--scope",
                        "user",
                        "--batch",
                        "--deps",
                        "fail",
                        "--copy",
                        "--no-setup",
                        "--name",
                        name,
                        str(output / "sources" / name),
                    ],
                    native=True,
                )
            step(
                "isolated-packages",
                [str(RACKET.with_name("raco")), "pkg", "show", "--all", "--long", "--dir"],
                native=True,
            )
            imports = output / "smokes/imports.rkt"
            imports.write_text(
                HEADER + '(require json (only-in pkg/lib pkg-directory))\n(display "MISAAL_IMPORTS_JSON ")\n'
                "(write-json (hash\n"
                '  \'modules (for/hash ([name (list "rosette" "hydride" "misaal")])\n'
                '    (values (string->symbol name) (path->string (collection-file-path "main.rkt" name))))\n'
                '  \'packages (for/hash ([name (list "custom-load" "rfc6455" "rosette" "hydride" "misaal")])\n'
                "    (values (string->symbol name) (path->string (pkg-directory name))))\n"
                '  \'racket (path->string (find-executable-path "racket"))\n'
                '  \'z3 (path->string (find-executable-path "z3"))))\n(newline)\n'
            )
            step("compile-imports", [str(RACKET.with_name("raco")), "make", str(imports)], native=True)
            text = step("imports", [str(RACKET), str(imports)], native=True)
            resolved = json.loads(
                next(
                    line.removeprefix("MISAAL_IMPORTS_JSON ")
                    for line in text.splitlines()
                    if line.startswith("MISAAL_IMPORTS_JSON ")
                )
            )
            modules = resolved["modules"]
            if set(modules) != {"rosette", "hydride", "misaal"} or any(
                not Path(path).resolve().is_relative_to(output / "addon") for path in modules.values()
            ):
                raise ValueError("active packages escaped the isolated addon tree")
            if resolved["racket"] != str(RACKET) or Path(resolved["z3"]).resolve() != output / "bin/z3":
                raise ValueError("PATH does not resolve the exact selected Racket and Z3")
            if set(resolved["packages"]) != set(PACKAGES):
                raise ValueError("package resolution omitted a pinned dependency")
            installed = {}
            for name, location in resolved["packages"].items():
                directory = Path(location).resolve()
                if not directory.is_relative_to(output / "addon"):
                    raise ValueError("package installation escaped the managed addon tree")
                manifest = json.loads((output / "sources" / f"{name}.json").read_text())
                for relative, expected in manifest["files"].items():
                    path = directory / relative
                    if (
                        path.is_symlink()
                        or not path.resolve().is_relative_to(directory)
                        or sha256_file(path) != expected
                    ):
                        raise ValueError("installed package bytes differ from their pinned source")
                installed[name] = {"path": str(directory), **manifest}
            bundled_z3 = Path(resolved["packages"]["rosette"]) / "bin/z3"
            if bundled_z3.exists() or bundled_z3.is_symlink():
                raise ValueError("unexpected bundled Z3 overrides the selected solver")
            record["installed_packages"] = installed
            record["gates"]["imports"] = {"status": "success", "module_paths": modules}
            solver = output / "smokes/solver.rkt"
            solver.write_text(HEADER + SOLVE)
            step(
                "tiny-solver-pgid",
                [*child, "_observe", str(RACKET), str(solver), str(output / "bin/z3"), str(output / "pgids.json")],
                native=True,
            )
            record["pgid_observation"] = json.loads((output / "pgids.json").read_text())
            record["gates"]["tiny_solver"] = {"status": "success", "pgids_sha256": sha256_file(output / "pgids.json")}
            smoke = output / "smokes/parameter-four-args.rkt"
            smoke.write_text(HEADER + PARAMETER_SMOKE)
            text = step("parameter-four-args", [str(RACKET), str(smoke)], native=True)
            if "MISAAL_PARAM_SYNTH_OK " not in text:
                raise ValueError("source operation did not validate its selected expression")
            record["gates"]["source_four_args"] = {
                "status": "success",
                "sha256": sha256_file(smoke),
                "workflow_evidence": False,
            }
            negative = output / "smokes/captured-five-args.rkt"
            negative.write_bytes(captured.read_bytes())
            if sha256_file(negative) != captured_sha256:
                raise ValueError("captured source changed during preparation")
            step("captured-five-args", [str(RACKET), str(negative)], native=True, expected_failure=True)
            record["gates"]["captured_five_args"] = {
                "status": "expected-api-failure",
                "sha256": captured_sha256,
                "modified": False,
            }
            for path, data in original_bytes.items():
                if Path(path).read_bytes() != data:
                    raise ValueError("an original request changed during preparation")
            record["packages"] = {
                name: json.loads((output / "sources" / f"{name}.json").read_text()) for name in PACKAGES
            }
            record["status"] = "source-api-blocked"
            record["reason"] = (
                "Pinned packages work; unchanged source caller supplies five arguments to a four-argument API."
            )
        except BaseException as error:
            record["reason"] = str(error)
            write_json(output / "runtime.json", record)
            raise
        write_json(output / "runtime.json", record)
        candidates = []
        for index, request in enumerate(requests):
            # Restore the trusted original PATH suffix needed by the existing native products.
            original = inputs[index]
            augmented = {**environment, "PATH": f"{output / 'bin'}:{RACKET.parent}:{original['environment']['PATH']}"}
            path = output / "candidates" / f"{index:03}.candidate.json"
            write_json(path, candidate_request(request.resolve(), output / "runtime.json", augmented))
            candidates.append({"path": str(path), "sha256": sha256_file(path)})
        write_json(
            output / "candidates.json", {"status": "source-api-blocked", "promoted": False, "candidates": candidates}
        )
        return record


def augment_requests(requests: list[Path], seal_path: Path, output: Path) -> dict[str, Path]:
    """Publish fresh requests against one verified runtime, preserving native products.

    This is data preparation only. The runtime has already passed its native
    diagnostic gates; source optimization and standalone replay are still due.
    Original requests and historical candidate receipts remain untouched.
    """
    from scripts.reproduction_misaal_patterns import PARAMETER_ABI_CONTRACT, PARAMETER_ABI_SOURCE_SHA256
    from scripts.reproduction_misaal_runtime import verify_runtime

    if output.exists() or not requests:
        raise ValueError("Runtime request publication requires inputs and a fresh output directory")
    seal_path = seal_path.resolve()
    seal = json.loads(seal_path.read_text())
    runtime_ref = {"path": str(seal_path), "sha256": sha256_file(seal_path)}
    identities = [str(seal_path), *(row["path"] for row in seal["code_trees"].values())]
    prepared: dict[str, dict[str, Any]] = {}
    sources: dict[str, str] = {}
    for source in requests:
        before = source.read_bytes()
        request = verified_request(source)
        case_id = request["case_id"]
        if case_id in prepared or re.fullmatch(r"[A-Za-z0-9_.-]+", case_id) is None or case_id in {".", ".."}:
            raise ValueError("Runtime request publication requires unique safe case identities")
        if any(request.get(key) != value for key, value in seal["source"].items() if key != "source_hashes"):
            raise ValueError("Native request does not share the validated runtime source checkout/revision")
        required_sources = {**PARAMETER_ABI_SOURCE_SHA256, "lib/utils/DSLInstructionUtils.py": DSL_UTILS_SHA256}
        if any(sha256_file(Path(request["checkout"]) / name) != digest for name, digest in required_sources.items()):
            raise ValueError("Native request source differs from the validated ABI/containment implementation")
        environment = {**request["environment"], **seal["environment"]}
        environment["PATH"] = os.pathsep.join(
            [*seal["environment"]["PATH"].split(os.pathsep)[:2], request["environment"]["PATH"]]
        )
        if any(key in environment for key in seal["required_unset"]) or any(
            key.startswith("PLT") and key not in seal["environment"] for key in environment
        ):
            raise ValueError("Native request environment conflicts with the isolated Racket runtime")
        augmented = {
            **request,
            "racket": seal["executables"]["racket"]["path"],
            "racket_sha256": seal["executables"]["racket"]["sha256"],
            "racket_group_containment": seal["racket_group_containment"],
            "parameter_abi": PARAMETER_ABI_CONTRACT,
            "source_hashes": {**request["source_hashes"], **required_sources},
            "environment": environment,
            "environment_unset": sorted(set(request.get("environment_unset", [])) | set(seal["required_unset"])),
            "racket_runtime": runtime_ref,
            "identity_paths": list(dict.fromkeys([*request.get("identity_paths", []), *identities])),
        }
        # Packages are shared across this publication. Rehash the complete
        # runtime once; each request's distinct native/source identities were
        # verified above and remain unchanged in the augmented payload.
        if not prepared:
            verify_runtime(augmented)
        if source.read_bytes() != before:
            raise ValueError("Native request changed during runtime publication")
        sources[str(source.resolve())] = hashlib.sha256(before).hexdigest()
        prepared[case_id] = augmented
    output.mkdir(parents=True)
    published = {}
    for case_id, request in prepared.items():
        path = output / f"{case_id}.json"
        write_json(path, request)
        published[case_id] = path
    write_json(output / "publication.json", {"runtime": runtime_ref, "original_requests": sources})
    return published


def prepare_source_runtime(output: Path, requests: list[Path], *, lock_owned: bool = False) -> dict[str, Any]:
    """Run the complete prerequisite/ABI recipe, then publish capture requests.

    Native generator builds remain separate and reusable. A failed phase keeps
    its own logs and stops publication; no source optimization runs here.
    """
    from scripts.reproduction_misaal_abi_gate import CAPTURED_FIXTURE, CAPTURED_SHA256, run_gates
    from scripts.reproduction_misaal_runtime import seal_runtime
    from scripts.reproduction_preparation import preparation_stop
    from scripts.reproduction_prepare_misaal import Preparation

    output = output.resolve()
    if output.exists() or not requests:
        raise ValueError("Source runtime preparation requires native requests and a fresh directory")
    record: dict[str, Any] = {"status": "blocked", "requests": {}, "reason": None}
    with nullcontext() if lock_owned else exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        output.mkdir(parents=True)
        driver = Preparation(output)
        runtime_path = output / "runtime/runtime.json"
        try:
            archive = output / "z3.zip"
            driver.step(
                "download-pinned-z3",
                [
                    "curl",
                    "--fail",
                    "--location",
                    "--max-filesize",
                    str(Z3_ARCHIVE_BYTES),
                    "--output",
                    str(archive),
                    "https://github.com/emina/rosette/releases/download/4.1/z3-4.8.8-aarch64-osx-13.3.1.zip",
                ],
            )
            prepare(output / "runtime", requests, archive, CAPTURED_FIXTURE, CAPTURED_SHA256, lock_owned=True)
            checkout = Path(json.loads(requests[0].read_text())["checkout"])
            gates = run_gates(runtime_path, checkout, output / "abi-gates", lock_owned=True)
            if gates["status"] != "success":
                raise ValueError("MISAAL source ABI gates did not complete successfully")
            seal_path = output / "runtime-seal.json"
            seal_runtime(
                runtime_path,
                Path(gates["abi_gate"]["path"]),
                seal_path,
                captured_gate_path=Path(gates["captured_gate"]["path"]),
            )
            published = augment_requests(requests, seal_path, output / "requests")
            record.update(
                status="success",
                requests={key: str(path) for key, path in published.items()},
                runtime_seal={"path": str(seal_path), "sha256": sha256_file(seal_path)},
            )
        except (OSError, ValueError, RuntimeError) as error:
            # Inspect only this attempt's diagnostic receipts. A safety stop
            # must survive wrapping, so the coordinator starts no later job.
            evidence = [json.loads(path.read_text()) for path in output.rglob("*.result.json")]
            evidence.extend(
                json.loads(path.read_text())
                for path in (runtime_path, output / "abi-gates/result.json")
                if path.is_file()
            )
            record.update(status=preparation_stop({"phases": evidence}, output) or "blocked", reason=str(error))
        write_json(output / "result.json", record)
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="mode", required=True)
    public = subparsers.add_parser("prepare")
    public.add_argument("--output", type=Path, required=True)
    public.add_argument("--request", type=Path, action="append", required=True)
    public.add_argument("--z3-archive", type=Path, required=True)
    public.add_argument("--captured-script", type=Path, required=True)
    public.add_argument("--captured-sha256", required=True)
    acquire = subparsers.add_parser("_acquire", help=argparse.SUPPRESS)
    acquire.add_argument("output", type=Path)
    observe = subparsers.add_parser("_observe", help=argparse.SUPPRESS)
    for name in ("racket", "script", "solver", "receipt"):
        observe.add_argument(name, type=Path)
    args = parser.parse_args()
    if args.mode == "_acquire":
        acquire_packages(args.output)
    elif args.mode == "_observe":
        observe_solver(args.racket, args.script, args.solver, args.receipt)
    else:
        prepare(args.output, args.request, args.z3_archive, args.captured_script, args.captured_sha256)


if __name__ == "__main__":
    main()
