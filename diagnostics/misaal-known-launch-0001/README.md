# MISAAL known-launch containment handoff

This is a prepared, **unrun** safety diagnostic. It is not an optimizer run,
Racket/Rosette readiness evidence, or corpus admission. The production patch is
`MISAAL-KNOWN-LAUNCH.patch` in the isolated mirror; this ignored directory is
copied separately into durable diagnostic evidence.

## Narrow production scope

The exact pinned `lib/utils/DSLInstructionUtils.py` launcher is the only wrapped
native detach site. It retains its original command (`racket`, source filename),
source streams, session, and 180-second source timeout. The original function
still performs its local `killpg` and returns its original fallback. Its process
handle now names a lightweight, standard-library-only Python `-I -S` supervisor
that holds the same session, reserves before fork, and cannot start Racket until
the outer guard acknowledges both the parent PID receipt and the kernel-authenticated
supervisor connection. Racket and its inherited-group solver descendants remain
in that registered group. This does not claim arbitrary process-tree isolation.

The outer guard samples root plus known reserved/registered groups once each.
It retains the unreaped root PID with `waitid(WNOWAIT)`, signals root work before
potentially slow detached drain, and always performs the final kill/wait even if
a callback fails or is interrupted. The supervisor stays alive through actual
Racket completion and confirmed group drain. EOF triggers self-group SIGKILL;
source SIGTERM enters that same cleanup so TERM-resistant descendants cannot
outlive it. The guard allows up to one second to observe signal drain; persistent
or ambiguous survivors fail closed. Retired numeric group IDs are not reused
for accounting, and the guard never signals a stale detached numeric PGID.

Reservations and pending bootstrap wrappers have a bounded refusal/drain phase
(up to six seconds) during shutdown. They cannot start Racket without a live
acknowledgment. Unresolved reservations, failed monitoring, or failed cleanup
are failures, never success. This is sampled operational containment, not a hard
allocation guarantee. The private control socket lives under a short `/tmp`
directory, and its protocol/ownership receipt remains in the durable attempt.

Known Python source detach audit for MISAAL revision
`44ff893445d664cd87f52b08a138260ed2015ba8`:

- `lib/utils/DSLInstructionUtils.py:117`: exact hash-gated Racket launcher.
- `lib/compiler/EggLogCompiler.py:230`: existing scoped `sb` helper observer
  refuses unexpected `Popen` before spawning; optimizer calls use the already
  captured inherited-group replacement.
- Other inspected `lib` subprocess calls (`pgrep`, cleanup, and LLVM helpers)
  inherit the existing group; no other `start_new_session`/`setsid` appears.

The package preparation slice must separately inspect the actual vendored
Rosette/Hydride solver launch code for further explicit detachment. No generic
upstream package or arbitrary newer source is silently covered by this claim.
Public complete capture rejects missing contract or Racket pins before launch.
The request bytes, actual Racket executable, group helper and existing adapter
hashes participate in the capture identity. No performance-cache schema changes.

## Prepared real gates

`run.py` uses the actual pinned launcher function code and production supervisor,
with a clearly labeled Python executable named `racket`. It retains original
source/helper/runner/tool hashes, per-case process receipts, group receipts, and
remaining-process observations. Cases are serial under the existing heavy-job
lock, normal host guard, 10 GiB disk reserve, and at most the existing 5 GiB cap:

1. Exact normal return code through the original source helper.
2. Detached child + grandchild aggregate-only 256 MiB cap: each process remains
   individually below that cap; the combined registered scope exceeds it.
3. Outer timeout and complete owned-group cleanup.
4. Fast source-parent exit after launch reservation/PID receipt.
5. Interruption between reserved fork and PID receipt: no Racket work allowed.
6. Original source-local timeout with TERM-resistant child/grandchild, leaving
   the source parent alive with its original fallback result.
7. Deliberate monitoring failure after real work begins.
8. Death of the lease owner itself: the detached group must drain within the
   separately recorded two-second crash-response bound.

A separate small bystander must survive every case. Any unexpected stop, live
owned process, changed source identity, or harmed bystander halts the diagnostic.
Mock tests additionally cover immediate root exit before first sampling, reused
PID ambiguity, unsupported exit-observation APIs, callback exceptions/interrupts,
and unrecognized/swallowed launcher errors. No native fixture has been run by
the implementing agent.

After the production patch is integrated and this directory is copied to
`benchmarks/local/reproduction/diagnostics/misaal-known-launch-0001`, root may run:

```sh
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python \
  benchmarks/local/reproduction/diagnostics/misaal-known-launch-0001/run.py \
  --source benchmarks/local/reproduction/prerequisites/misaal-44ff/attempt-20260925T051740Z-ef4010cc/sources/MISAAL/lib/utils/DSLInstructionUtils.py \
  --output benchmarks/local/reproduction/diagnostics/misaal-known-launch-0001/results
```

For preparation-only inspection, use `--materialize-only` and a different fresh
output directory. Never reuse a result directory or overwrite failed evidence.

## Independent readiness gap

Root's actual `misaal-racket-prerequisite-0001` smoke found Racket 9.2 at
`/Applications/Racket v9.2/bin/racket`, but the tiny solver program failed because
Rosette is absent. Hydride/MISAAL packages are also not installed. The artifact
uses modified vendored Rosette, followed by its Hydride and MISAAL packages.
The separate preparer must hydrate/pin those exact trees, prove solver/package
readiness, address its independently reviewed source API blocker, and emit fresh
requests. These guard fixtures alone do not authorize a 3600-second source run.
