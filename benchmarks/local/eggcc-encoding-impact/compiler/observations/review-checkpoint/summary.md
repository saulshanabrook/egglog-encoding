# First full-host observation checkpoint

Development-v2 implements the approved restricted checker and passes its first focused/full-CLI correctness slice. This is diagnostic translation validation of a confirmed bug, with an equivalent manual control. No optimization speedup, all-input verifier, unique logical power over that control or final-gate completion is claimed. **Repeated static evidence paths remain a known cost-integration blocker**, and the narrow real source-corrected specificity control is pending.

The [manifest](manifest.json) verifies the complete 28-file compiler source identity, source patch, frozen compiler/Tiger, all587 files under development-v2, all37 CLI results and the authoritative five-file E1 source package. The ad-hoc development-v2 engine.patch is only a four-tracked-file diff; complete E1 authority is the copied encoding-reviewable-1.patch/json plus encoding-final-source-checkpoint.json, including the untracked oracle and its completed full gate. All old C1/C2, previous study worktrees and frozen evidence are preserved.

## Implemented boundary

Both root and standalone DAG dependency graphs resolve experimental3.0.0/core2.0.0 from `/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding`; locked metadata is retained. No old local-address feature was imported. Compiler base is15ee7cbabe70d3b2e72d796bcf81cc2604626e7b in `/Users/saul/p/wt/eggcc/encoding-impact`. The only source optimization changes remain **none**: the two diagnosed multiplication rules are unchanged.

`dag_in_context/src/observations.rs` checks a positive Int/Bool/tuple grammar, actual argument types/contexts, one call-free function and selected If paths. Mul wraps i64; LessThan is signed; boolean And/Or/Not are total supported operators. Calls, loops, memory, floats, Div/shifts, partial unary operations and other grammar reject when reached. A per-region Rc memo preserves sharing. Print is traversed structurally; it is never detached-interpreted. Root input includes the host StateV; selected regions receive their actual evaluated input tuples. Only checked pure Bool fragments reach the existing interpreter helper. Dead regions produce explicit skipped records with zero observations.

The same contextual pre-pass TreeToEgglog/cache prints optimizer Exprs and matching literals. Opaque primitive point tokens separate inputs, actual region invocations and passes. CommonSeed/Manual/Injective have identical logical observations, literals, seed IDs, points, region inputs and initialization except the literal annotation: all32 applicable case/pass/mode comparisons match. `EvalBoolAt(Expr,i64)->ObservationValue` is unmarked; only `ObservedBool(bool)` is injective in Injective mode. No Expr annotation, Expr union or Expr disequality is added by observation seeding.

Initialization, actual source schedule, witness capture and audit are separate. Both checked modes find the same committed `(ObservationConflict 5 2 1 true false)` on MAX: observation5 is the reached branch comparison under actual region tuple `[StateV,0,MAX,2]`; observation2 is its matching false literal at that point. Manual rejects directly. Injective reports `injectivity violation in constructor ObservedBool: unequal primitive argument0`. Both abort before the serialization-entry receipt and before any Tiger egraph is emitted. CommonSeed records that conflict and continues without audit, preserving the real wrong output; it does not trigger the existing Const guard.

CLI controls are `--observations off|common-seed|manual|injective`, `--observation-evidence-dir PATH`, and separate `--observation-prepass-probe`. Enabled CLI use requires Optimize, actual contexts, no CLI ablation, and an evidence directory; probe requires Injective. Root arguments come from the actual file header, not ignored trailing CLI args. Off avoids collection/declarations/seeding/audit. Context, pass schedule, non_weakly_linear=true and default native greedy Tiger/reconstruction remain common for CLI and the new root host tests.

## Executed evidence

| Check | Result |
|---|---|
| Locked root and DAG metadata | both passed; same new E1 source |
| Focused DAG tests |10 passed,0 failed |
| Focused full-host root tests |3 passed,0 failed; actual bug rejection, three native control round trips and configuration rejection |
| Source interpreter oracles |7/7 parse/interpreter invocations, non-null expected outputs |
| Mode/case matrix plus two separate probes |30 optimizer invocations, all expected statuses |
| Successful full native invocations |24, each non-null outputs and passes0/1/2 plus three native egraph snapshots |
| Expected actual bug detector aborts |3: Manual, Injective, separate Injective-probe MAX |
| Expected unsupported-domain aborts |3 enabled modes on selected Div, before emitting seeds |
| Initialized old/E1 replay |4 expected statuses, identical input bytes/flags percase; not a full old-query compiler endpoint |

MAX source prints true; Off/CommonSeed optimize to false and finish all three passes. Manual/Injective reject that same invalid class merge at the named observer stage. x=1 prints false in all four modes; x=0/-1 return empty non-null output in all four modes. The contradictory dead branch and the dead-Div fixture print true in all four modes. Selected Div at x=-2 is valid source (`-2/2=-1`, prints true), passes Off, and is explicitly unsupported before seeding in every enabled mode. These domain rejections are not detector successes or semantic miscompilations.

The first-pass designated product-sign probe count is1/1/0/0 for MAX/1/0/-1, with true/false payloads for the reached cases. The contradictory branch's designated product-sign probe count is0. Full identities/counts are retained in [diagnostics.json](diagnostics.json), including per-pass source observations, logical seed rows, actual inputs, skipped-region counts and Print visits. These are defined host/seed counts, not optimizer match/firing/time counts.

Independent-oracle coverage is tied to `goals/eggcc-encoding-impact/findings/observation-oracle-cases.md`: synthetic tests assert7→14 and3→6→12 actual region inputs, selected false values and both dead-probe zero counts; exact shared contextual Rc under3/20 gives true/false at distinct points and both audits accept; the state carrier test visits one Print structurally, limits detached calls to its two pure Bool observations and separately verifies normal execution's single `7` log event. Synthetic root tuples include the approved trailing StateV. Actual frontend point counts/slot order come from the real receipts, rather than assumptions from Bril text. The actual selected/dead Div commands provide case5's explicit eligibility boundary.

The separate actual-host E1 probe runs before source rules: MAX knows the product-sign Expr differs from matching false; fresh x=1 is unknown. Identical initialized replay bytes produce MAX old-unary exit1/E1 exit0 and x=1 both exit1. The otherwise witness-free different-point query-unknown negative is prepared but **not executed yet**; audits accepting distinct points alone do not satisfy that remaining query condition.

## Preserved failures and limits

The first focused development run had7 passed/2 failed because sort and constructor shared `ObservedBool`; renamed only the sort to ObservationValue and retained the failed receipt. The green source was hash-frozen before v2 DAG/root tests and CLI build; no source changed during those green commands or capture. Two sign-rule correction, final full EggCC gates and release/cost collection have not run. Prior baseline arithmetic endpoint panics and the ineffective CLI ablation remain separate C1 evidence and were not “fixed” here.

The current evidence directory is fresh-per-invocation by caller convention; a static repeated arm path collides at pass-00. This leaves the37-command correctness matrix valid but blocks repeated-cost use. The [next-slice proposal](next-slice-proposal.md) specifies a compiler-owned atomic persistent invocation child, normal receipt directory/index plus early abort locator, matched output cost, exact two-rule temporary source correction/restore and final restored-source gates. No such follow-up change has been applied.

All commands use the bounded process-group runner with exact argv/cwd/env/exit/stdout/stderr receipts. Build/test timeout was1200s; CLI/replay timeout120s. Rust1.91, jobs4, Rayon1, LLVM18 and CBC library path are recorded. Frozen debug compiler SHA is8e8d8eb9e5ffcf8653d1e49f19540940458cd6e7c89f3d92b3f7c2851cad1488; its active sibling Tiger SHA isbd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a. Receipt wall times are diagnostic bookkeeping, not a performance cohort. No native adapter, timing cohort, commit or push ran.

All owned compiler builds, tests and workload processes are terminal. The build slot was released to the parent/harness. The four tiny replay calls launched just before the defer instruction, were already terminal in under2s when authoritative state was checked, and were retained without rerun. Subsequent work only read/hash-verified source and wrote new summary/proposal artifacts.
