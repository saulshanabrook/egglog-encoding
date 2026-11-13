#!/usr/bin/env bash
# Compare the slotted specification with the Rust slotted reference on the paper's corpus.
#
# Each file under egglog-experimental/tests/slotted/paper asserts the outcome of every
# check with `check` and `fail`. The reference is run on each file: a zero exit status
# means every asserted outcome holds in it. `difftest slotted-bounded` then runs every
# check with the bounded evaluator of the slotted specification and compares the outcome
# with the asserted one. A check the evaluator cannot decide within its fuel is reported
# and does not fail the gate; a disagreement does. SLOTTED_FILES overrides the file list.
set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
reference="${EGGLOG_EXPERIMENTAL_BIN:-$root/target/release/egglog-experimental}"
per_file_timeout="${DIFFTEST_TIMEOUT:-600}"

if [[ ! -x "$reference" ]]; then
  echo "slotted-difftest: no egglog-experimental binary at $reference" >&2
  echo "slotted-difftest: build one with 'cargo build --release -p egglog-experimental'" >&2
  exit 1
fi

export PATH="$HOME/.elan/bin:$PATH"
cd "$root/semantics" || exit 1
lake build difftest >/dev/null || exit 1

if [[ -n "${SLOTTED_FILES:-}" ]]; then
  read -r -a files <<<"$SLOTTED_FILES"
else
  mapfile -t files < <(find "$root/egglog-experimental/tests/slotted/paper" -name '*.egg' | sort)
fi

fail=0
for egg in "${files[@]}"; do
  if ! RAYON_NUM_THREADS=1 "$reference" --slotted "$egg" >/dev/null 2>&1; then
    echo "FAIL $egg: the reference rejects the file's asserted outcomes"
    fail=$((fail + 1))
  fi
done

timeout "$per_file_timeout" .lake/build/bin/difftest slotted-bounded "${files[@]}" || fail=$((fail + 1))
[[ $fail -eq 0 ]]
