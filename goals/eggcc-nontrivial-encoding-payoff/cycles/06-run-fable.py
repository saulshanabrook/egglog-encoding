from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
from datetime import UTC, datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PROMPT = HERE / "06-fable-prompt.md"
OUTPUT = HERE / "06-fable-audit.md"
STDERR = HERE / "06-fable-stderr.log"
RECEIPT = HERE / "06-fable-receipt.json"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


for path in (OUTPUT, STDERR, RECEIPT):
    if path.exists():
        raise SystemExit(f"refusing to overwrite {path}")

claude = shutil.which("claude")
if claude is None:
    raise SystemExit("claude is not on PATH")

prompt = PROMPT.read_bytes()
argv = [
    claude,
    "--print",
    "--model",
    "fable",
    "--effort",
    "max",
    "--restricted",
    "--safe-mode",
    "--disable-slash-commands",
    "--allowedTools",
    "Read,Grep,Glob",
    "--permission-mode",
    "dontAsk",
    "--permission-prompts",
    "none",
    "--no-session-persistence",
    "--output-format",
    "text",
    "--add-dir",
    "/private/tmp/eggcc-nontrivial-encoding-payoff-u0",
]
started = datetime.now(UTC)
try:
    completed = subprocess.run(
        argv,
        cwd=ROOT,
        input=prompt,
        capture_output=True,
        timeout=1800,
        check=False,
        env={**os.environ, "CLAUDE_CODE_ENABLE_TELEMETRY": "0"},
    )
    timed_out = False
except subprocess.TimeoutExpired as error:
    completed = subprocess.CompletedProcess(
        argv,
        124,
        stdout=error.stdout or b"",
        stderr=error.stderr or b"",
    )
    timed_out = True
finished = datetime.now(UTC)

OUTPUT.write_bytes(completed.stdout)
STDERR.write_bytes(completed.stderr)
receipt = {
    "argv": argv,
    "cwd": str(ROOT),
    "started_utc": started.isoformat().replace("+00:00", "Z"),
    "finished_utc": finished.isoformat().replace("+00:00", "Z"),
    "timeout_s": 1800,
    "timed_out": timed_out,
    "exit_code": completed.returncode,
    "prompt_sha256": sha256(prompt),
    "stdout_sha256": sha256(completed.stdout),
    "stderr_sha256": sha256(completed.stderr),
    "allowed_tools": ["Read", "Grep", "Glob"],
    "read_only": True,
}
RECEIPT.write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps(receipt, indent=2))
raise SystemExit(completed.returncode)
