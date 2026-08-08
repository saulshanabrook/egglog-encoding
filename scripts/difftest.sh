#!/usr/bin/env bash
# Differentially test the Lean semantics against egglog.
#
# `difftest` (semantics/DiffTest.lean) writes one .egg file and one .expected file per
# case; each .expected holds the per-constructor row counts the Lean interpreter predicts.
# This runs egglog on the .egg file and diffs its `(print-size)` output against that.
#
# Row counts are the same quantity egglog/tests/files.rs snapshots: one row per distinct
# canonical argument tuple, which on the Lean side is one per congruence class of
# argument lists.
#
# Cases come in four kinds. The curated ones are the Redex test.rkt programs plus
# variations, and are only as good as whoever chose them; likewise the curated :merge ones
# for M9. The two random families remove that bias -- rand-* over the constructor fragment
# (RANDOM_CASES) and mrand-* over M9's :merge functions (MERGE_CASES). See DiffTest.lean
# for why every generated merge is a join and why merge functions are written but never
# read.
set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
out="${DIFFTEST_OUT:-$root/.difftest}"
egglog="${EGGLOG_BIN:-$root/target/release/egglog}"
random_cases="${RANDOM_CASES:-60}"
merge_cases="${MERGE_CASES:-30}"
# A generated program can blow up in either engine; cap both rather than hang the run. The
# binding constraint is the Lean side, whose matcher is |terms| ^ |vars| by construction,
# so this is a budget for the reference interpreter rather than a pathology detector.
per_case_timeout="${DIFFTEST_TIMEOUT:-40}"

if [[ ! -x "$egglog" ]]; then
  echo "difftest: no egglog binary at $egglog" >&2
  echo "difftest: build one with 'cargo build --release -p egglog', or set EGGLOG_BIN" >&2
  exit 1
fi

export PATH="$HOME/.elan/bin:$PATH"
cd "$root/semantics" || exit 1
lake build difftest >/dev/null || exit 1
gen=".lake/build/bin/difftest"

rm -rf -- "$out"
mkdir -p -- "$out"

"$gen" "$out" curated >/dev/null || exit 1
"$gen" "$out" merge >/dev/null || exit 1
skipped=0
fail=0
pass=0
# A generated case may time out, which is a skip. Anything else -- notably the generator
# refusing to emit a program egglog would reject -- is a defect in the generator, and its
# message must not be swallowed, so stderr is kept and reported as a failure.
generate() { # <mode> <seed> <case-name>
  local status=0
  timeout "$per_case_timeout" "$gen" "$out" "$1" "$2" >/dev/null 2>"$out/$3.genlog" ||
    status=$?
  if [[ $status -ne 0 ]]; then
    if [[ $status -ne 124 && -s "$out/$3.genlog" ]]; then
      echo "FAIL $3: generator refused to emit the case"
      sed 's/^/      /' "$out/$3.genlog"
      fail=$((fail + 1))
    fi
    rm -f -- "$out/$3".*
    skipped=$((skipped + 1))
  fi
  rm -f -- "$out/$3.genlog"
}
for ((i = 0; i < random_cases; i++)); do generate seed "$i" "rand-$i"; done
for ((i = 0; i < merge_cases; i++)); do generate mergeseed "$i" "mrand-$i"; done

for egg in "$out"/*.egg; do
  name="$(basename "$egg" .egg)"
  # `(print-size)` prints `((Add 2)\n (One 1))`; reduce to sorted `name count` lines.
  if ! timeout "$per_case_timeout" "$egglog" "$egg" >"$out/$name.raw" 2>"$out/$name.err"; then
    echo "FAIL $name: egglog failed or timed out"
    sed 's/^/      /' "$out/$name.err" | head -5
    fail=$((fail + 1))
    continue
  fi
  tr -d '()' <"$out/$name.raw" | awk 'NF==2 {print $1, $2}' | sort >"$out/$name.actual"
  sort <"$out/$name.expected" >"$out/$name.want"
  if diff -q "$out/$name.want" "$out/$name.actual" >/dev/null; then
    pass=$((pass + 1))
  else
    echo "FAIL $name: row counts differ (want = Lean, actual = egglog)"
    sed 's/^/      /' "$egg"
    diff -u --label want --label actual "$out/$name.want" "$out/$name.actual" |
      sed 's/^/      /' | tail -n +3
    fail=$((fail + 1))
  fi
done

# Report how much work the random cases actually did: a case whose rules never fire has
# only its seeded terms, and tests little beyond action evaluation. Per family, because a
# pooled number would hide one family's distribution collapsing behind the other's spread.
profiles() { # <label> <glob-prefix>
  compgen -G "$out/$2-*.want" >/dev/null || return 0
  echo "difftest: $1 total row counts:"
  for w in "$out/$2"-*.want; do awk '{s += $2} END {print s}' "$w"; done |
    sort -n | uniq -c | awk '{printf "    %3d rows: %d cases\n", $2, $1}'
  echo "difftest: $(for w in "$out/$2"-*.want; do tr '\n' ' ' <"$w"; echo; done |
    sort -u | wc -l) distinct $1 profiles"
}
profiles "random-case" rand
profiles "random-merge-case" mrand
echo "difftest: $pass passed, $fail failed, $skipped skipped (not generated)"
[[ $fail -eq 0 ]]
