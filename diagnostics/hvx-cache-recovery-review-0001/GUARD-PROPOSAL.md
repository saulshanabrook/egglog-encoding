# Separate proposal: reproduction-only detached-descendant guard

Proposal only. No implementation or real process fixture ran in this slice. The timeout-policy patch does not fix this prerequisite.

## Confirmed gap

The pinned MISAAL `lib/utils/DSLInstructionUtils.py115–134` launches Racket with `start_new_session=True`, waits up to180 seconds, and signals that child's group on timeout/interruption. The reproduction guard samples only the initial PGID (`benchmarking/memory_guard.py73–81`) and kills only that PGID (`benchmarking/pilot.py` cleanup). Racket/solver descendants can thus escape the5 GiB sum and outer cleanup. Preserve native local `killpg` behavior; simply removing `start_new_session` could kill the source parent.

## Recommended boundary

Use a separate, opt-in **reproduction process-family guard**, leaving ordinary benchmark defaults/cache/schema unchanged. The process receipt must say whether RSS is root-group-only or full registered-family accounting. Keep the same5 GiB aggregate ceiling, host-pressure and10 GiB disk gates, one-heavy-slot discipline, and stop-on-monitor-failure behavior.

A process snapshot should contain PID, PPID, PGID, process start identity and RSS. Starting with the guarded root, compute the transitive PPID closure and retain every discovered process birth identity and detached PGID. Sum each live process once even if it appears through both a retained group and PPID closure. Reparenting does not remove ownership; continue tracking retained groups until conclusively empty. Never adopt an unrelated process solely because its PID/PGID numerically matches an old record. Start identity needs better than a seconds-resolution wall-clock timestamp. Record monitoring/cleanup receipts independently of the source parent's status.

**Polling ancestry alone is insufficient for a strong safety claim.** A child can detach, spawn a solver, exit and reparent that solver between snapshots. The first observation after root exit cannot recover the missing lineage. There is also a spawn-versus-outer-cleanup race. A test that sleeps long enough for polling to discover a child does not prove these races safe.

For the current known Racket launcher, add a narrow source-hash-gated launch registration/supervision contract instead of attempting a general arbitrary-process sandbox. A reproduction-owned launcher should establish/register its new group and stable birth identity before allowing real Racket work, wait for guard acknowledgment, and refuse/exit if the guard owner has died. Keep a lightweight group-lifetime supervisor so the group identity cannot be recycled while native descendants remain. The source still receives a waitable child with the real Racket result, and its `killpg(child)` targets only that child's supervised group. Native argument list, script bytes, local180-second timeout/result behavior and cache/rule generation must remain unchanged. This is observational/safety instrumentation, separate from pattern semantics. Do not silently return a successful helper result on a guard stop.

This startup handshake closes the important fast-orphan gap for the **known** detached launcher; PPID discovery remains defense in depth for ordinary descendants. A narrowly pinned scope must reject unknown detached-launch mechanisms, or adopt a platform-native containment mechanism before claiming coverage for arbitrary descendants. Full general containment across uncooperative grandchildren is not established by this proposal.

## Cleanup and monitor failure

On source-root exit, success, timeout, cancellation, memory/disk/pressure stop or monitoring error: first prevent any registered launcher from starting new work; terminate all still-owned groups, including detached groups after their original parent exits; resnapshot until no owned process remains within a short bounded cleanup deadline. Escalate to SIGKILL if necessary. Never silently report successful cleanup if enumeration, group identity verification or signaling fails. If a group leader is absent but verified retained members remain, retain ownership; avoid PID-only signaling or killing a reused unrelated group. The supervising group lifetime makes this identity check simpler. The single-heavy-job policy does not make unrelated user processes safe to kill.

Root-group cleanup must also occur if startup registration fails. A lightweight unacknowledged launcher must not proceed into Racket, and must exit when the owning guard disappears. Receipt evidence should include discovered/registered groups, their birth identities, peak aggregate RSS, stop cause and terminal cleanup result.

## Discriminating real fixtures required before3600 seconds

Run under the real native guard in the sole heavy slot, using tiny local Python processes rather than MISAAL:

1. Root starts a new-session child that consumes more than a deliberately tiny aggregate cap while root RSS remains small; assert memory stop and no surviving child/grandchild.
2. Detached child and ordinary grandchild sleep beyond a short outer timeout; assert timeout cleanup reaches both.
3. Source root exits successfully immediately after spawning detached work; guard must clean descendants and report cleanup, not leave work behind merely because the root exited0.
4. An intermediate detached launcher exits before a normal polling interval, leaving its grandchild; startup registration/supervision must still account for and clean it. Include a variant that kills the root during launch registration.
5. Simulated PID/PGID reuse plus distinct process-birth identity must never signal the unrelated replacement. Inject snapshot/parser failures and require fail-closed cleanup/error status.
6. Native local timeout behavior: a supervised Racket-shaped child/group is signaled by its source parent; verify only that child group dies, the source parent survives, and the returned failure result is preserved.

Only after these pass should the new request-pinned3600-second cold HVX parent run. The historical4.795 GiB measurement remains explicitly root-group-only; never relabel it as full-family RSS.
