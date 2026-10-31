#!/usr/bin/env bash
# Run the congruence compiler's output in egglog and compare row counts with the Lean
# interpreter's prediction for the same compiled program.
#
# `difftest <dir> compiled` writes one `.egg` and one `.expected` per in-domain corpus case:
# the compiled program with `min` on ids spelled `ordering-min`, and the per-table row
# counts the interpreter predicts for it. egglog's `(print-size)` is reduced to the same
# lines. Only the census (`<constructor>:live`, one row per canonical e-node: a held
# application joined with the live union-find edges of its children) is compared. Those
# counts are independent of which representative either engine picks; the raw tables hold
# every spelling a run built plus the subsumed stale edges, and egglog's `ordering-min`
# (earliest id) and the model's structural order pick different representatives, so a
# source rule head can build a different spelling of the same class on the two sides.
set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
out="${DIFFTEST_OUT:-$root/.difftest-compiled}"
egglog="${EGGLOG_BIN:-$root/target/release/egglog}"
per_case_timeout="${DIFFTEST_TIMEOUT:-120}"

if [[ ! -x "$egglog" ]]; then
  echo "compiled-difftest: no egglog binary at $egglog" >&2
  exit 1
fi

export PATH="$HOME/.elan/bin:$PATH"
cd "$root/semantics" || exit 1
lake build difftest >/dev/null || exit 1
gen=".lake/build/bin/difftest"

rm -rf -- "$out"
mkdir -p -- "$out"
"$gen" "$out" compiled || exit 1

pass=0
fail=0
for egg in "$out"/*.egg; do
  name="$(basename "$egg" .egg)"
  if ! timeout "$per_case_timeout" "$egglog" "$egg" >"$out/$name.raw" 2>"$out/$name.err"; then
    echo "FAIL $name: egglog failed or timed out"
    sed 's/^/      /' "$out/$name.err" | head -5
    fail=$((fail + 1))
    continue
  fi
  tr -d '()' <"$out/$name.raw" | awk 'NF==2 && $1 ~ /:live$/ {print $1, $2}' |
    sort >"$out/$name.actual"
  awk '$1 ~ /:live$/' <"$out/$name.expected" | sort >"$out/$name.want"
  if diff -q "$out/$name.want" "$out/$name.actual" >/dev/null; then
    pass=$((pass + 1))
  else
    echo "FAIL $name: row counts differ (want = Lean, actual = egglog)"
    diff -u --label want --label actual "$out/$name.want" "$out/$name.actual" |
      sed 's/^/      /' | tail -n +3
    fail=$((fail + 1))
  fi
done
echo "compiled-difftest: $pass passed, $fail failed"
[[ $fail -eq 0 ]]
