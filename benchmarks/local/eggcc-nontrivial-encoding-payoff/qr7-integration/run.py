#!/usr/bin/env python3
"""Capture bounded commands; importing this module never launches a process."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

BASE = Path(__file__).resolve().parent
ROOT = Path(os.environ.get('QR7_OUTPUT_ROOT', str(BASE)))
HOST = Path('/private/tmp/eggcc-qr7-candidate')
ENGINE = Path('/private/tmp/encoding-qr7-candidate')
ENV = dict(os.environ)
ENV.update(EGGCC_ROOT=str(HOST), RUSTUP_TOOLCHAIN='1.91.0', CARGO_BUILD_JOBS='4',
           RUST_TEST_THREADS='4', RAYON_NUM_THREADS='1',
           LLVM_SYS_180_PREFIX='/opt/homebrew/opt/llvm@18', LIBRARY_PATH='/opt/homebrew/lib',
           PATH='/opt/homebrew/opt/llvm@18/bin:' + os.environ['PATH'],
           CARGO_TARGET_DIR=str(ENGINE / 'target'), PYTHONDONTWRITEBYTECODE='1')
for name in ['EGGLOG_BENCH_MEMORY_GUARD', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER',
             'RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS', 'INSTA_UPDATE', 'INSTA_FORCE_PASS', 'MAKEFLAGS']:
    ENV.pop(name, None)


def run(label, argv, timeout=180, cwd=HOST, check=True):
    folder = ROOT / 'commands' / label
    folder.mkdir(parents=True, exist_ok=False)
    argv = [str(argument) for argument in argv]
    start = time.monotonic()
    launch_error = None
    timed_out = False
    try:
        process = subprocess.Popen(argv, cwd=cwd, env=ENV, start_new_session=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except OSError as error:
        launch_error = repr(error)
        stdout, stderr, exit_code = b'', str(error).encode(), None
    else:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
        exit_code = process.returncode
    (folder / 'stdout').write_bytes(stdout)
    (folder / 'stderr').write_bytes(stderr)
    executable = shutil.which(argv[0], path=ENV['PATH'])
    files = []
    for argument in argv:
        candidate = Path(argument)
        if not candidate.is_absolute():
            candidate = Path(cwd) / candidate
        if candidate.is_file():
            files.append(dict(path=str(candidate), sha256=hashlib.sha256(candidate.read_bytes()).hexdigest()))
    receipt = dict(argv=argv, cwd=str(cwd), timeout_s=timeout, exit_code=exit_code,
                   launch_error=launch_error,
                   timed_out=timed_out, elapsed_s_diagnostic=time.monotonic() - start,
                   diagnostic_elapsed_is_performance_evidence=False,
                   environment={key: ENV[key] for key in ['EGGCC_ROOT', 'RUSTUP_TOOLCHAIN',
                       'CARGO_BUILD_JOBS', 'RUST_TEST_THREADS', 'RAYON_NUM_THREADS',
                       'LLVM_SYS_180_PREFIX', 'LIBRARY_PATH', 'PATH', 'CARGO_TARGET_DIR',
                       'PYTHONDONTWRITEBYTECODE']},
                   scoped_mode=ENV.get('EGGCC_SCOPED_MODE'),
                   scoped_evidence=ENV.get('EGGCC_SCOPED_EVIDENCE'),
                   absent_environment=['EGGLOG_BENCH_MEMORY_GUARD'],
                   files=files, executable=executable,
                   executable_sha256=hashlib.sha256(Path(executable).read_bytes()).hexdigest() if executable else None,
                   stdout_sha256=hashlib.sha256(stdout).hexdigest(),
                   stderr_sha256=hashlib.sha256(stderr).hexdigest())
    (folder / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'{label}: exit={exit_code} timeout={timed_out}', file=sys.stderr, flush=True)
    if check and (launch_error is not None or timed_out or exit_code):
        raise RuntimeError(f'{label} failed; see {folder}')
    return stdout


def freeze():
    folder = BASE / 'bin'
    folder.mkdir(exist_ok=False)
    rows = []
    for name, source in [('eggcc', ENGINE / 'target/release/eggcc'),
                         ('tiger', BASE.parent / 'admission/bin/tiger')]:
        target = folder / name
        shutil.copy2(source, target)
        rows.append(dict(path=str(target), source=str(source),
                         sha256=hashlib.sha256(target.read_bytes()).hexdigest()))
    (BASE / 'binary-identities.json').write_text(json.dumps(rows, indent=2) + '\n')


if __name__ == '__main__':
    if sys.argv[1:] == ['freeze']:
        freeze()
    else:
        label, *argv = sys.argv[1:]
        run(label, argv, timeout=1800 if argv[0] in {'cargo', 'make'} else 180)
