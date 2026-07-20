# Causal Slice v0 Design Validation

Status: active experiment, 2026-07-20.

## Steering frame

- Mission: falsify or establish the smallest sound instance of one traced
  native run, one backward causal slice, and one unchanged proof-mode replay.
- Non-goals: global minimum slicing, OR alternatives, delta debugging,
  differential-dataflow support, proof/checker redesign, speculative epochs,
  per-column provenance, or general mutation/container support before Bronze.
- Exact base: PR #23 head
  `4940be37429e7adf16cc43283b38508e692cf045`.
- Worktree: `/Users/saul/p/wt/egglog-encoding/causal-slice-arena-v0`.
- Branch: `agent/causal-slice-arena-v0`.
- Current frontier: validate the proposed native evidence hooks, then import
  only the already demonstrated relation-only Bronze slice as the passing
  comparison.
- Stop rule: after a hook is disproved by a reduced canary, record the exact
  missing evidence and do not replace it with final-state guessing.

## Competing hypotheses

| ID | Hypothesis | Confirming prediction | Disconfirming prediction | Status |
|---|---|---|---|---|
| H1 | PR #23 is a sufficient guarded replay leaf for fully grounded positive relation rules | a captured two-step transcript replays in ordinary and unchanged strict proof modes | a fully bound leaf cannot reproduce the captured grounding or complete head | pending |
| H2 | final native join expansion exposes enough evidence for exact whole-row body support and complete replay bindings | every final grounding carries every logical variable plus stable source row identities or equivalent dependencies | an existential variable or source row identity is projected away before the action leaf | falsified on unmodified PR #23: the planner drops single-use, non-RHS variables, and final expansion drops `TaggedRowBuffer` tags |
| H3 | one current dependency pointer per mutable row identity is viable | row identity survives commit/rekey/delete lifecycle without unsafe reuse | replacement, canonicalization, deletion, or slot reuse changes the identity without a repair hook | pending |
| H4 | successful-union endpoint edges form a recoverable explanation forest without epochs | endpoints and the earlier unique path remain queryable after later canonicalization/rebuild | canonicalization destroys endpoint identity or makes an earlier path unrecoverable | pending |
| H5 | replay witnesses can be captured once at match time and printed lazily | each supported binding has immutable syntax plus availability dependencies at the firing | witness syntax is only discoverable by later extraction/final inverse search | pending |
| H6 | sequential `run-rule` is sound for fully grounded insert-only set relations | same-wave canaries retain original observations and do not gain uncaptured groundings | current-state re-query changes a captured grounded firing | pending |
| H7 | sequential leaves preserve general shared-wave semantics | delete/write/subsume/lookups behave like one original wave | an earlier replay head changes a later captured firing or RHS read | expected to be falsified |

## Invariant validation table

`Confirmed` means direct code plus a focused run/test. `Falsified` requires a
reduced witness. `Uncertain` is not permission to implement around the gap.

| Proposed invariant | Initial status | Required evidence | Final status / evidence |
|---|---|---|---|
| PR #23 exact guard is atomic before head effects | uncertain | existing `run_rule` test and implementation | pending |
| complete match bindings exist at the final native action leaf | uncertain | free-join path audit and trace canary | falsified: `free_join/plan.rs` intentionally omits a single-use variable not needed by the RHS; `CapturedBinding` only copies the resulting dense map |
| exact source `RowId`s survive factorized final match expansion | uncertain | `TaggedRowBuffer` to `push_bindings` dataflow | falsified at the action leaf: `expand_binding_sets` consumes the tag while expanding the match and passes only bindings onward |
| decomposed intermediate rows can carry one shadow `DepId` | uncertain | materialization representation and projection audit | pending |
| action lanes can carry a `PendingFireId` through every proposal | uncertain | action-buffer and mutation-buffer audit | pending |
| commit can attribute effective insert/update/no-op to one origin | uncertain | table/merge commit boundary audit | pending |
| `RowId` is stable across commit/replacement/rekey/delete/reuse | uncertain | table lifecycle audit plus canaries | pending |
| RHS lookup hits/misses expose current row/tombstone evidence | uncertain | action execution and lookup hooks | pending |
| successful union exposes pre-canonical endpoints and outcome | uncertain | union-find/write path audit plus canary | pending |
| successful-union forest needs no epochs | uncertain | direct, redundant, later-union, congruence/rebuild canaries | pending |
| scalar binding syntax is available without per-match extraction | uncertain | match-time base-value reconstruction canary | pending |
| container same-ID rebuild is version distinguishable | uncertain | container rebuild identity canary | pending |
| matched all-no-op firings can be discarded | uncertain | complete-head mixed no-op/effective canary | pending |
| positive conjunctive check exposes one actual environment | uncertain | traced check query canary | pending |
| sequential replay is sound for the declared Bronze fragment | uncertain | enabling and same-wave multi-fire canaries | pending |
| general replay requires a shared-pre-state batch | uncertain | delete/write/subsume/RHS-read counterexamples | pending |

## Circle roster

| Agent | Domain | Aim | Authority | Expected output | Stop |
|---|---|---|---|---|---|
| coordinator | implementation and synthesis | own the only code edits, experiments, integration, gates, and handoff | may implement within the prompt; no remote writes | sound vertical slice or minimal blocker | hard criteria pass or architecture assumption is reduced and falsified |
| native-hooks | native joins, rows, action origins, commit/rebuild | classify H2/H3 and exact hook availability | read-only; no broad gates | path/line evidence and minimal missing-interface canaries | every assigned invariant is confirmed, falsified, or explicitly uncertain |
| equality-witness | equality forest and replay witnesses | classify H4/H5 without speculative epochs | read-only; no code edits | endpoint/path/rekey analysis and focused canary designs | first decisive counterexample or all assumptions supported |
| wave-source-review | wave batching, state canaries, source replay | independently falsify H6/H7 and review output contract | read-only; no code edits | reduced counterexamples and Bronze soundness criteria | monotone boundary and smallest batch requirement are precise |

## Experiment ledger

| ID | Question | Smallest repro / command | Expected discriminator | Result |
|---|---|---|---|---|
| E0 | Does the exact PR head pass its focused replay tests and baseline gates? | `cargo test -p egglog --test run_rule`; `make proof-tests`; `make check` | 4 guarded-run tests and both repository gates pass | passed: 4/4 focused; 192 reference plus 8 experimental proof fixtures; full `make check` passed |
| E1 | Can one captured transcript replay in ordinary and proof modes? | two-rule/two-grounding relation chain | every leaf has complete bindings and `:expect 1` | pending |
| E2 | Can one check-rooted backward slice remove an irrelevant branch? | Bronze relation fixture | 6 matched applications become 2 retained | pending |
| E3 | Is sequential replay adequate for the monotone fragment? | same-wave enabling with fully bound fires | no new uncaptured grounding fires | pending |
| E4 | Does mutation falsify sequential shared-wave replay? | delete/read and write/lookup canaries | sequential replay diverges from original wave | pending |
| E5 | Does `:expect` count successful logical matches after primitive filters? | one relation candidate plus false equality filter | guard must fail if it counts logical matches | pending |
| E6 | Are equality-forest endpoints/path stable? | direct/redundant/later union and rekey canaries | earlier path remains recoverable without final-class guessing | pending |
| E7 | Are row IDs stable enough for current-state sidecars? | insert/overwrite/rekey/delete/reinsert probes | row sidecar identity remains valid or failure is localized | pending |
| E8 | Is output deterministic and proof-checkable? | two independent slicer processes plus strict replay | byte-identical source and unchanged checker pass | pending |

## Validation commands

```bash
cargo test -p egglog --test run_rule
cargo test -p egglog --test causal_slice
make check
make proof-tests
cargo fmt --all -- --check
git diff --check
```
