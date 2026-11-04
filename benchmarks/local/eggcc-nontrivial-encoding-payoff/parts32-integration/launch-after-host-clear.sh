#!/bin/zsh
set -euo pipefail

cd /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration
exec >> timing-launch-after-host-clear.log 2>&1

echo "waiting for competing PID 38360 at $(date -u +%Y-%m-%dT%H:%M:%SZ)"
while /bin/ps -p 38360 >/dev/null 2>&1; do
  sleep 15
done

echo "competing PID exited at $(date -u +%Y-%m-%dT%H:%M:%SZ); settling host"
sleep 30

unset EGGLOG_BENCH_MEMORY_GUARD
echo "preflight starting at $(date -u +%Y-%m-%dT%H:%M:%SZ)"
python3 -B prepare-timing.py
echo "session 1 starting at $(date -u +%Y-%m-%dT%H:%M:%SZ)"
python3 -B timing.py 1
echo "session 2 starting at $(date -u +%Y-%m-%dT%H:%M:%SZ)"
python3 -B timing.py 2
echo "verification starting at $(date -u +%Y-%m-%dT%H:%M:%SZ)"
python3 -B verify-timing.py
echo "compiler diagnostic starting at $(date -u +%Y-%m-%dT%H:%M:%SZ)"
python3 -B compile-diagnostic-final/run.py run --acknowledge-diagnostic-only
echo "campaign completed at $(date -u +%Y-%m-%dT%H:%M:%SZ)"
