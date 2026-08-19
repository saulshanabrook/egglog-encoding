#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 7 ]]; then
  cat >&2 <<'USAGE'
usage: benchmark_term_languages.sh BASELINE_PROPEL CANDIDATE_PROPEL BASELINE_EUF CANDIDATE_EUF EUF_SMALL EUF_LARGE OUTPUT_DIR

The baseline executables must come from commit 5069c43. Candidate executables
must be built from the revision under test. EUF_SMALL and EUF_LARGE are the
published uf.815405.smt2 and uf.614981.smt2 inputs from the Zenodo artifact.
USAGE
  exit 2
fi

export BASELINE_PROPEL="$1"
export CANDIDATE_PROPEL="$2"
export BASELINE_EUF="$3"
export CANDIDATE_EUF="$4"
export EUF_SMALL="$5"
export EUF_LARGE="$6"
OUTPUT_DIR="$7"

ROOT="$(git rev-parse --show-toplevel)"
export PROPEL_GSET="$ROOT/benchmarks/disequality/inductive-prover/benchmarks/propel/gset_comm.propel"
export PROPEL_MEDIUM="$ROOT/benchmarks/disequality/inductive-prover/benchmarks/propel/tip_bin_plus_assoc.propel"
mkdir -p "$OUTPUT_DIR"
export OUTPUT_DIR ROOT

python3 - <<'PY'
from __future__ import annotations

import hashlib
import json
import os
import platform
import subprocess
from datetime import UTC, datetime
from pathlib import Path


root = Path(os.environ["ROOT"])
revision = subprocess.run(
    ["git", "rev-parse", "HEAD"],
    cwd=root,
    check=True,
    stdout=subprocess.PIPE,
    text=True,
).stdout.strip()
status = subprocess.run(
    ["git", "status", "--short", "--untracked-files=all"],
    cwd=root,
    check=True,
    stdout=subprocess.PIPE,
    text=True,
).stdout.splitlines()
binary_paths = {
    "baseline_propel": os.environ["BASELINE_PROPEL"],
    "candidate_propel": os.environ["CANDIDATE_PROPEL"],
    "baseline_euf": os.environ["BASELINE_EUF"],
    "candidate_euf": os.environ["CANDIDATE_EUF"],
}
input_paths = {
    "propel_gset_comm": os.environ["PROPEL_GSET"],
    "propel_tip_bin_plus_assoc": os.environ["PROPEL_MEDIUM"],
    "euf_uf_815405": os.environ["EUF_SMALL"],
    "euf_uf_614981": os.environ["EUF_LARGE"],
}
provenance = {
    "schema_version": 1,
    "generated_at": datetime.now(UTC).isoformat(),
    "platform": platform.platform(),
    "baseline_source_revision": "5069c4317492d9a3c8d0d1da4265d59e556bbaeb",
    "candidate_source_revision": revision,
    "candidate_source_status": status,
    "binary_sha256": {
        name: hashlib.sha256(Path(path).read_bytes()).hexdigest()
        for name, path in binary_paths.items()
    },
    "input_sha256": {
        name: hashlib.sha256(Path(path).read_bytes()).hexdigest()
        for name, path in input_paths.items()
    },
}
output = Path(os.environ["OUTPUT_DIR"]) / "provenance.json"
output.write_text(json.dumps(provenance, indent=2, sort_keys=True) + "\n")
PY

hyperfine --warmup 1 --runs 5 --export-json "$OUTPUT_DIR/propel-gset-forward.json" \
  --command-name baseline-vec-cold '"$BASELINE_PROPEL" -f "$PROPEL_GSET" --variant egglog-de' \
  --command-name candidate-vec-cold '"$CANDIDATE_PROPEL" -f "$PROPEL_GSET" --variant egglog-de --term-language vec --no-template-cache' \
  --command-name candidate-vec-cached '"$CANDIDATE_PROPEL" -f "$PROPEL_GSET" --variant egglog-de --term-language vec' \
  --command-name candidate-direct-cold '"$CANDIDATE_PROPEL" -f "$PROPEL_GSET" --variant egglog-de --term-language direct --no-template-cache' \
  --command-name candidate-direct-cached '"$CANDIDATE_PROPEL" -f "$PROPEL_GSET" --variant egglog-de --term-language direct'

hyperfine --warmup 1 --runs 5 --export-json "$OUTPUT_DIR/propel-gset-reverse.json" \
  --command-name candidate-direct-cached '"$CANDIDATE_PROPEL" -f "$PROPEL_GSET" --variant egglog-de --term-language direct' \
  --command-name candidate-direct-cold '"$CANDIDATE_PROPEL" -f "$PROPEL_GSET" --variant egglog-de --term-language direct --no-template-cache' \
  --command-name candidate-vec-cached '"$CANDIDATE_PROPEL" -f "$PROPEL_GSET" --variant egglog-de --term-language vec' \
  --command-name candidate-vec-cold '"$CANDIDATE_PROPEL" -f "$PROPEL_GSET" --variant egglog-de --term-language vec --no-template-cache' \
  --command-name baseline-vec-cold '"$BASELINE_PROPEL" -f "$PROPEL_GSET" --variant egglog-de'

hyperfine --warmup 1 --runs 3 --export-json "$OUTPUT_DIR/propel-medium-forward.json" \
  --command-name baseline-vec-cold '"$BASELINE_PROPEL" -f "$PROPEL_MEDIUM" --variant egglog-de' \
  --command-name candidate-vec-cold '"$CANDIDATE_PROPEL" -f "$PROPEL_MEDIUM" --variant egglog-de --term-language vec --no-template-cache' \
  --command-name candidate-vec-cached '"$CANDIDATE_PROPEL" -f "$PROPEL_MEDIUM" --variant egglog-de --term-language vec' \
  --command-name candidate-direct-cached '"$CANDIDATE_PROPEL" -f "$PROPEL_MEDIUM" --variant egglog-de --term-language direct'

hyperfine --warmup 1 --runs 3 --export-json "$OUTPUT_DIR/propel-medium-reverse.json" \
  --command-name candidate-direct-cached '"$CANDIDATE_PROPEL" -f "$PROPEL_MEDIUM" --variant egglog-de --term-language direct' \
  --command-name candidate-vec-cached '"$CANDIDATE_PROPEL" -f "$PROPEL_MEDIUM" --variant egglog-de --term-language vec' \
  --command-name candidate-vec-cold '"$CANDIDATE_PROPEL" -f "$PROPEL_MEDIUM" --variant egglog-de --term-language vec --no-template-cache' \
  --command-name baseline-vec-cold '"$BASELINE_PROPEL" -f "$PROPEL_MEDIUM" --variant egglog-de'

hyperfine --warmup 2 --runs 5 --export-json "$OUTPUT_DIR/euf-small-forward.json" \
  --command-name baseline-vec '"$BASELINE_EUF" "$EUF_SMALL" --backend egglog-de' \
  --command-name candidate-vec '"$CANDIDATE_EUF" "$EUF_SMALL" --backend egglog-de --term-language vec' \
  --command-name candidate-direct '"$CANDIDATE_EUF" "$EUF_SMALL" --backend egglog-de --term-language direct'

hyperfine --warmup 2 --runs 5 --export-json "$OUTPUT_DIR/euf-small-reverse.json" \
  --command-name candidate-direct '"$CANDIDATE_EUF" "$EUF_SMALL" --backend egglog-de --term-language direct' \
  --command-name candidate-vec '"$CANDIDATE_EUF" "$EUF_SMALL" --backend egglog-de --term-language vec' \
  --command-name baseline-vec '"$BASELINE_EUF" "$EUF_SMALL" --backend egglog-de'

hyperfine --warmup 2 --runs 3 --export-json "$OUTPUT_DIR/euf-large-forward.json" \
  --command-name baseline-vec '"$BASELINE_EUF" "$EUF_LARGE" --backend egglog-de' \
  --command-name candidate-vec '"$CANDIDATE_EUF" "$EUF_LARGE" --backend egglog-de --term-language vec' \
  --command-name candidate-direct '"$CANDIDATE_EUF" "$EUF_LARGE" --backend egglog-de --term-language direct'

hyperfine --warmup 2 --runs 3 --export-json "$OUTPUT_DIR/euf-large-reverse.json" \
  --command-name candidate-direct '"$CANDIDATE_EUF" "$EUF_LARGE" --backend egglog-de --term-language direct' \
  --command-name candidate-vec '"$CANDIDATE_EUF" "$EUF_LARGE" --backend egglog-de --term-language vec' \
  --command-name baseline-vec '"$BASELINE_EUF" "$EUF_LARGE" --backend egglog-de'

(cd "$OUTPUT_DIR" && shasum -a 256 ./*.json > SHA256SUMS)
