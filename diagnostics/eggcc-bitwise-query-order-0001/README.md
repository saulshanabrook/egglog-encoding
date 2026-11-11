# Eggcc bitwise third-check ordering diagnostic

Prepared only. No native probe has been run by this handoff.

The driver reads the exact retained session-002 optimization replay and its capture
receipt from the earlier `eggcc-bitwise-stage-boundary-0001` intent. It pins those
three files and the engine by SHA-256. The recorded source-parent capture remains
the input identity; this diagnostic is not a new capture or an admitted workload.

Only the third check changes. In its original zero-based fact order, fact 376 is
the existing 20-argument `@GeneratedFreshTable4` context constraint and fact 1109
is the existing native-root equality. They move to positions 0 and 1, respectively.
All other facts keep their relative order. The driver asserts:

- Exactly six checks, with the third at command index 1000 and containing 1,110 facts.
- The expected context constraint and root equality are still present.
- The full fact-token multiset, including duplicate multiplicities, is identical.
- Every other command and the complete prefix/suffix bytes are unchanged.
- No actions, new terms, or constraints are added.

This tests whether variable introduction order improves query planning. It does not
assume that order controls the final plan or that this will resolve the timeout.
The source schedules and original type/context constraints remain intact.

## Invocation, only after the heavy-process slot is released

Run from the live root. The output directory must not already exist. Do not use
Python `-O` or `PYTHONOPTIMIZE`; the driver explicitly refuses disabled assertions.

```sh
cd /Users/saul/p/egglog-encoding
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python \
  /Users/saul/p/wt/egglog-encoding/reproduction-eggcc-churchroad/diagnostics/eggcc-bitwise-query-order-0001/run.py \
  --root /Users/saul/p/egglog-encoding \
  --output /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/diagnostics/eggcc-bitwise-query-order-0001
```

The driver takes the existing exclusive heavy-job lock and launches exactly one
ordinary replay through `run_bounded_command`, with one job, a 60-second timeout,
a 5-GiB process-group RSS cap, required host memory supervision, a 10-GiB disk
reserve, and authorized warning-pressure tolerance. The logging configuration
matches the prior unchanged diagnostic. There is no automatic retry.

## Retained evidence and interpretation

Before launching, the fresh output retains `original.egg`, `reordered.egg`, the
source capture and previous diagnostic intent, and the diagnostic driver source.
`intent.json` records both input hashes, helper/engine hashes, the entire fact
permutation, the multiset hash, the exact command, and guard settings.
`result.json` retains the guarded process receipt and log paths.

`interpretation.json` reports success only if the process exits successfully and
all six check-completion messages appear. Exit status is 0 for that result, 2 for
a guard refusal/timeout/resource stop, or 1 for another incomplete result. Input
identity or assertion failures stop before launching. Every interpretation keeps
`admitted: false`; even success requires reviewed adapter changes and normal
complete-parent validation before corpus admission. No catalog, settings, index,
or production adapter is changed.

## Lightweight preparation checks

Ruff passes. An in-memory transformation of the pinned replay passes the full
preservation assertions. Two negative checks reject a changed fresh-context table
and an added constraint. Those checks never called `main`, acquired the heavy-job
lock, wrote a replay, or launched the engine.

- Original replay SHA-256: `ced29250ea65acb944aba02f05d92070c7aa0431017e85e26c3431ecf06f7768`
- Adapted replay SHA-256: `83ad5cc8e312b4c12d183b8fb0e7ffcc04f28dd8da325c2e8bd1ff055baccd45`
- Fact-token multiset SHA-256: `7a8fcc49f3cce179cc8c72ea1e56667a4d1d4a3f79ad57223890506b22262c8c`
- Driver SHA-256: `08bf515c30d3f61a8e65ff9be542f6a73fb72f45e951f098d70249eef3528dfc`
