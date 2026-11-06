"""Apply the checked-in bridge to an exact LMFAO revision and record its provenance."""

import argparse
import json
import shutil
import subprocess
from pathlib import Path
from typing import Any

from benchmarking.lmfao.model import COMMIT
from benchmarking.targets import sha256_file

ADAPTER = Path(__file__).resolve().parent
PATCHES = ("optimizer-bridge.patch", "dependent-output.patch")
HEADERS = ("ImportPlan.hpp", "OptimizerBridge.hpp")


def adapter_hashes() -> dict[str, str]:
    return {name: sha256_file(ADAPTER / name) for name in (*PATCHES, *HEADERS)}


def patched_checkout(source: Path, output: Path) -> Path:
    """Create a detached pinned worktree; reject patch drift before building."""
    checkout = output / "source"
    subprocess.run(["git", "-C", str(source), "worktree", "add", "--detach", str(checkout), COMMIT], check=True)
    actual = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    if actual != COMMIT:
        raise ValueError("LMFAO checkout does not match the pinned revision")
    for patch in PATCHES:
        args = ["git", "-C", str(checkout), "apply"]
        subprocess.run([*args, "--check", str(ADAPTER / patch)], check=True)
        subprocess.run([*args, str(ADAPTER / patch)], check=True)
    for header in HEADERS:
        shutil.copy2(ADAPTER / header, checkout / "src/compiler" / header)
    return checkout


def verify_backend(binary: Path) -> dict[str, Any]:
    """Require the pinned revision, current adapters and the prepared binary hash."""
    path = binary.parent.parent / "provenance.json"
    if not path.is_file():
        raise ValueError("missing LMFAO provenance.json; run benchmarks.reproduction.lmfao.prepare")
    manifest = json.loads(path.read_text())
    if (
        manifest["lmfao_commit"] != COMMIT
        or manifest["adapter_sha256"] != adapter_hashes()
        or manifest["binary_sha256"] != sha256_file(binary)
    ):
        raise ValueError("LMFAO backend provenance differs; prepare a new pinned backend")
    return dict(manifest)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True, help="Existing LMFAO git checkout")
    parser.add_argument("--output", type=Path, required=True, help="New checkout/build directory")
    parser.add_argument("--boost", type=Path)
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    out = args.output.resolve()
    if out.exists():
        parser.error("--output must be a new directory")
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    out.mkdir(parents=True)
    source = patched_checkout(args.source.resolve(), out)
    cmake = ["cmake", "-S", str(source), "-B", str(out / "build")]
    if args.boost:
        boost = args.boost.resolve()
        cmake += [
            f"-DBOOST_ROOT={boost}",
            f"-DBOOST_LIBRARYDIR={boost}/lib/x86_64-linux-gnu",
            "-DBoost_NO_SYSTEM_PATHS=ON",
            "-DBoost_NO_BOOST_CMAKE=ON",
            f"-DCMAKE_CXX_FLAGS=-I{boost}/include",
        ]
    subprocess.run(cmake, check=True)
    subprocess.run(["cmake", "--build", str(out / "build"), f"-j{args.jobs}"], check=True)
    (out / "provenance.json").write_text(
        json.dumps(
            {
                "lmfao_commit": COMMIT,
                "adapter_sha256": adapter_hashes(),
                "binary_sha256": sha256_file(out / "build/multifaq"),
            },
            indent=2,
        )
        + "\n"
    )


if __name__ == "__main__":
    main()
