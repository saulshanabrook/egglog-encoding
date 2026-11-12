#!/usr/bin/env bash
# Compile every parser-accepted slotted file and compare all asserted outcomes.
# Unsupported syntax and the restricted-aliasing execution policy are explicit rejections.
# Reference failures, crashes, timeouts, exhausted fuel and disagreements fail the gate.
set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
reference="${EGGLOG_EXPERIMENTAL_BIN:-$root/target/release/egglog-experimental}"
per_file_timeout="${DIFFTEST_TIMEOUT:-600}"
if [[ ! -x "$reference" ]]; then
  echo "slotted-compile: no egglog-experimental binary at $reference" >&2
  exit 1
fi

cd "$root/semantics" || exit 1
read -r -a lake_cmd <<< "${LAKE:-lake --no-cache}"
"${lake_cmd[@]}" build difftest >/dev/null || exit 1
logs="$(mktemp -d)" || exit 1
trap 'rm -rf "$logs"' EXIT

if [[ -n "${SLOTTED_FILES:-}" ]]; then
  read -r -a files <<< "$SLOTTED_FILES"
else
  mapfile -t files < <(find "$root/egglog-experimental/tests/slotted" \
    "$root/semantics/tests/slotted" -name '*.egg' ! -name '*.slotted.egg' | sort)
fi

accepted=0 compiled=0 rejected=0 skipped=0 agree=0 disagree=0 undecided=0 errors=0
for egg in "${files[@]}"; do
  egg="$(realpath "$egg")" || exit 1
  .lake/build/bin/difftest slotted-plan "$egg"
  status=$?
  if [[ $status -eq 2 ]]; then
    skipped=$((skipped + 1))
    continue
  elif [[ $status -ne 0 ]]; then
    echo "ERROR $egg: preflight exited $status"
    errors=$((errors + 1))
    continue
  fi
  accepted=$((accepted + 1))
  flags=(--slotted)
  restricted=0
  if [[ "$egg" == */tests/slotted/nested/* ]]; then
    restricted=1
    flags+=(--slotted-no-aliasing)
  fi
  (cd "$root" && timeout "$per_file_timeout" "$reference" "${flags[@]}" "$egg") \
    >"$logs/reference" 2>&1
  status=$?
  if [[ $status -ne 0 ]]; then
    echo "REFERENCE-FAIL $egg: exit $status"
    cat "$logs/reference"
    errors=$((errors + 1))
    continue
  fi
  echo "REFERENCE-OK $egg: ${flags[*]}"
  if [[ $restricted -eq 1 ]]; then
    echo "REJECT $egg: requires --slotted-no-aliasing; the pass implements unrestricted paper matching"
    rejected=$((rejected + 1))
    continue
  fi
  timeout "$per_file_timeout" .lake/build/bin/difftest slotted-compile "$egg" \
    >"$logs/compiled" 2>&1
  status=$?
  cat "$logs/compiled"
  agree=$((agree + $(grep -c '^AGREE ' "$logs/compiled")))
  disagree=$((disagree + $(grep -c '^DISAGREE ' "$logs/compiled")))
  undecided=$((undecided + $(grep -c '^UNDECIDED ' "$logs/compiled")))
  if grep -q '^REJECT ' "$logs/compiled"; then
    rejected=$((rejected + 1))
  elif grep -q '^COMPILED ' "$logs/compiled"; then
    compiled=$((compiled + 1))
  else
    echo "ERROR $egg: no complete-file result"
    errors=$((errors + 1))
  fi
  if [[ $status -ne 0 ]]; then
    echo "ERROR $egg: compiler/interpreter exited $status (124 means timeout)"
    errors=$((errors + 1))
  fi
done
echo "slotted-compile: ${#files[@]} files, $accepted parser-accepted, $compiled compiled, $rejected rejected, $skipped parser-skipped; $agree agree, $disagree disagree, $undecided undecided, $errors errors"
[[ $errors -eq 0 && $disagree -eq 0 && $undecided -eq 0 && $agree -gt 0 && \
   $((compiled + rejected)) -eq $accepted ]]
