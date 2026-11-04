#!/usr/bin/env python3
"""Bounded future capture commands. Diagnostic durations are not performance samples."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

BASE = Path(__file__).resolve().parent
ROOT = Path(os.environ.get("PACK32_OUTPUT_ROOT", str(BASE / "probe-01")))
HOST = Path("/private/tmp/eggcc-pack32-candidate")
ENGINE = Path("/private/tmp/encoding-pack32-candidate")
ENV = dict(os.environ)
ENV.update(EGGCC_ROOT=str(HOST), RUSTUP_TOOLCHAIN="1.91.0", CARGO_BUILD_JOBS="4",
           RUST_TEST_THREADS="4", RAYON_NUM_THREADS="1", LLVM_SYS_180_PREFIX="/opt/homebrew/opt/llvm@18",
           LIBRARY_PATH="/opt/homebrew/lib", PATH="/opt/homebrew/opt/llvm@18/bin:" + os.environ["PATH"],
           CARGO_TARGET_DIR=str(ENGINE / "target"), PYTHONDONTWRITEBYTECODE="1")
for name in ("EGGLOG_BENCH_MEMORY_GUARD", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "RUSTFLAGS",
             "CARGO_ENCODED_RUSTFLAGS", "INSTA_UPDATE", "INSTA_FORCE_PASS", "MAKEFLAGS"):
    ENV.pop(name, None)


def run(label, argv, timeout=180, cwd=None, check=True):
    folder = ROOT / "commands" / label
    folder.mkdir(parents=True, exist_ok=False)
    argv = list(map(str, argv))
    started = time.monotonic()
    process = subprocess.Popen(argv, cwd=cwd or HOST, env=ENV, start_new_session=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
    (folder / "stdout").write_bytes(stdout)
    (folder / "stderr").write_bytes(stderr)
    receipt = dict(argv=argv, cwd=str(cwd or HOST), timeout_s=timeout,
                   diagnostic_elapsed_s=time.monotonic() - started,
                   exit_code=process.returncode, timed_out=timed_out,
                   environment={key: ENV[key] for key in ENV if key in {
                       "EGGCC_ROOT", "RUSTUP_TOOLCHAIN", "CARGO_BUILD_JOBS", "RUST_TEST_THREADS",
                       "RAYON_NUM_THREADS", "LLVM_SYS_180_PREFIX", "LIBRARY_PATH", "PATH",
                       "CARGO_TARGET_DIR", "PYTHONDONTWRITEBYTECODE", "EGGCC_SCOPED_MODE",
                       "EGGCC_SCOPED_EVIDENCE", "UV_CACHE_DIR", "UV_PYTHON", "UV_OFFLINE"}},
                   absent_environment=["EGGLOG_BENCH_MEMORY_GUARD", "INSTA_UPDATE", "INSTA_FORCE_PASS"],
                   files=[dict(path=arg, sha256=hashlib.sha256(Path(arg).read_bytes()).hexdigest())
                          for arg in argv if Path(arg).is_file()],
                   stdout_sha256=hashlib.sha256(stdout).hexdigest(), stderr_sha256=hashlib.sha256(stderr).hexdigest())
    (folder / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(label, process.returncode, flush=True)
    if check:
        assert not timed_out and process.returncode == 0, stderr.decode(errors="replace")[-6000:]
    return stdout


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cwd", type=Path, default=HOST)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("label")
    parser.add_argument("argv", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    assert args.argv and args.timeout > 0
    run(args.label, args.argv, timeout=args.timeout, cwd=args.cwd)
