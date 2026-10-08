"""Prepare isolated MISAAL packages, source API gates, and capture requests.

The public CLI owns the shared heavy-job lock and guards every acquisition and
native child. Internal child modes are implementation details, not entrypoints.
Raw package preparation emits blocked candidates. The coordinator's complete
recipe adds the reviewed ABI gates and runtime seal before publishing requests.
No source optimization, LLVM build, or Cargo build runs here.
"""

from __future__ import annotations

import hashlib
import json
import re
import shutil
import stat
import urllib.parse
import urllib.request
import zipfile
from pathlib import Path, PurePosixPath
from typing import Any

from scripts.reproduction_prepare_misaal import HYDRIDE_REVISION, MISAAL_REVISION, sha256_file, write_json

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
