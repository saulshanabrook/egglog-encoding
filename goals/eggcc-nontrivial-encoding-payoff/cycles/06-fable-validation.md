# Independent validation of cycle 06 Fable

Read-only source/evidence review of `06-fable-audit.md`; no compiler, tests,
timing, network, or evidence regeneration was run. The 771 files in
`benchmarks/local/eggcc-nontrivial-encoding-payoff/admission/source-files.json`
still match pinned U0. Below, `U/` means
`/private/tmp/eggcc-nontrivial-encoding-payoff-u0/`, and `B/` means
`benchmarks/local/eggcc-nontrivial-encoding-payoff/`. Line references to Fable
refer to `06-fable-audit.md`.

## Confirmed

- **QR7 mechanism and added consumer (lines 7–9).**
  `B/qr7-integration/scoped_qr7.rs:540–669` constructs unmarked `Q7`, `R7`,
  `Pair`, and `Addr`, marks only unary `K7`, seeds the two component equalities,
  supplies the representation unions, saturates injectivity, and checks pair,
  key, word, and address equality. There is no disequality seed or witness
  query. The total signed-i64 law is sound: fixed positive division by 7 and
  its reconstructed remainder identify the original word without overflow.
  `eggcc-candidate-r1.patch:544–554` adds `Qr7MustAlias`/`Qr7ForwardEnabled`
  and copies the value/state actions of
  `U/dag_in_context/src/optimizations/mem_simple.egg:107–113`. This is an added bridge; the evidence does not show
  untouched U0's same-address rule doing the QR7 forwarding. Historical ledger
  line 12 is a proposal, superseded by line 42, rather than a current result.
  `PrimitiveOnly` shares `seed_only` with `SeedOnly` at sidecar line 543; its
  empty marked-primitive-field receipt is constructed at 664–665. Thus the
  null executes, but a distinct primitive-comparison algorithm does not.
  `TransportOff` only suppresses export at 650–651; it does not ablate the
  transport calculation. Both qualifications already appear in the report.
- **QR7 measured and executed endpoint (lines 10–17).** The confirmation
  `timing-r1/independent-verification.json` records hot Encoding/U0
  `0.5505494231 [0.5471011571,0.5575021727]` and zero-trip
  `0.9892585012 [0.9836729081,1.0003275615]`, with all declared gates true.
  In `final-r1/matrix/positive/u0/native/program.asm:5351–5442`, `x19` and
  `x20` receive the first two parsed inputs; `cmp x19,x20` at line 5382
  implements the second guard after the quotient comparison. The executed
  loops at 5414–5433 contain arithmetic and branches, with no load/store.
  Encoding's corresponding `_main` at
  `matrix/positive/encoding/native/program.asm:5336–5391` instead computes an
  acyclic sum. The backend has therefore reduced this guarded case to input
  equality and removed its executed memory operations already in U0. QR7 does
  not establish a uniquely unavailable LLVM law or hot-load-removal payoff.
- **Parts32 law, chain, exact union, and measurement (lines 19–24).**
  `B/parts32-integration/eggcc-final.patch:1024–1085` confirms unmarked
  metadata-carrying Low/High, marked Parts32, unmarked Pair, word-disequality
  and low-equality seeds, representation unions, marked forward reasoning,
  and the sibling-guarded `known-disequal?` query. The arithmetic law is total:
  for low remainder `r`, `x-r` lies in `[-2^63,2^63-2^32]` and is divisible by
  `2^32`. Patch line 561 is the exact contextual predicate/false union, and
  its consumer-off gate is decisive. The retained
  `final-reviewed/matrix/positive/u0/native/main.ll:36–44` contains XOR, low-part testing, and the
  remaining unsigned-XOR `< 2^32` test selecting 99/7; the Encoding diff
  `final-reviewed/u0-encoding-main.ll.diff:25–123,134–143` removes that target
  and introduces vector operations. The tested backend failed to perform
  this combination unaided. All three timing verifier booleans Fable names
  are true, and the six Encoding/U0 estimates range from `0.9139833514` to
  `0.9250432355`. The separate compile diagnostic is non-acceptance evidence.
- **Validation is still unmet (lines 17,24,26).** QR7's retained root-test,
  DAG-test, and nits receipts have the recorded exit codes 1, 0, and 2; their
  hashes and stdout/stderr hashes were checked. Its root result includes one
  filtered raytrace test, 13 unaccepted snapshots, and the inherited root
  Clippy failure; DAG passes 70 tests. Parts32 `validation.json` records root
  exit 2 with 13 pending snapshots and DAG Clippy exit 101 with two unchanged
  U0 sites and zero new sidecar warnings. The dependency-only attribution in
  QR7 `validation-r1/independent-attribution.json` distinguishes the 13 actual
  program-output differences from clean U0 and from QR7-specific changes.
  Same-mask, Affine, Route, and Sort reports retain the same snapshot limit;
  Affine additionally records 17 new sidecar Clippy diagnostics. These facts
  support measured/mechanism results with an explicitly failed full-validation
  gate, not unconditional completion of `facts.md:18`.
- **A1's U0 rules, schedule, and retained opportunity (lines 44,46,48).**
  `U/dag_in_context/src/optimizations/mem_simple.egg:8–62,71–81,107–113`
  has precisely the declared relation, If transport, interval-based producers,
  symmetry, commute consumer, and same-address forward consumer; no loop
  NoAlias rule exists. `schedule.rs:46–112` saturates mem-simple in helpers;
  both sequential and parallel schedules run helpers before loop inversion
  (`164–180`, `217–237`), whose rule subsumes the old loop at `ivt.egg:184`.
  `B/alias-screen/reachability/transport.json` confirms the listed graph-local
  IDs, both invariant pointer slots, exact consumer, and non-execution flags.
  The baseline native opportunity is distinct: the screen and actual A1
  inspection retain a store–store–load loop. The Mask reverse step with a
  shared mask, fixed wrapping translation, and live same-allocation cell
  identity are sound under the documented bounds/lifetime restrictions;
  literal mask 1 does not by itself decide the dynamic child disequality.
- **Shift typing gap (line 69).** The source locations cited for Bril import,
  interpretation, Rust operand/result types, and missing egglog table entries
  are correct. `type_analysis.egg:283–310` has no Shl/Shr entry or dedicated
  typing rule. `B/parts32-screen/failure-inspection.json` and
  `findings/parts32-screen.md:42–67` retain the actual untyped Shr failure.
  No Shl/Shr use was found in U0's test/benchmark inputs. More precisely, the
  table cannot derive their result type; an e-class already merged with some
  separately typed expression could inherit HasType. This adjacent baseline
  defect was found without the generic encoding and fails the material-
  discovery requirement at `facts.md:14`; it is not this goal's bug payoff.

## Corrected or rejected conclusions

- **Specific LLVM pass causality is unestablished (line 10).** Final assembly
  establishes the equality guard, memory elimination, cyclic-versus-acyclic
  endpoints, and iteration-dependent work. It does not reveal whether GVN,
  indvars, exit-value rewriting, or a particular pass order caused the
  difference. Treat that pass attribution as a hypothesis. “Earlier EggCC
  forwarding exposes a different optimization opportunity to the fixed LLVM
  pipeline” is supported; robustness to other pipelines and iteration counts
  remains untested. Linear versus acyclic computation also does not make the
  measured percentage a transferable performance constant.
- **Wrong Parts32 false-If ablation location (line 22); reject “nothing …
  overstated” (line 23).** `eggcc-final.patch:523–529` gates
  `optimizations/non_weakly_linear.egg:12–17`, not
  `interval_analysis.egg:284–290`. The latter remains active via
  `interval-rewrite` (`schedule.rs:116–125`). Thus the capture establishes
  non-essentiality of the non-weakly-linear rule, not of interval-based If
  elimination, and does not isolate extraction/LLVM as the exclusive consumer.
  The exact Eq=false union remains the supported causal endpoint.
- **Context panic is not a lifetime proof (lines 45,47,49).**
  `U/dag_in_context/src/utility/context_of.egg:15–21` detects two still-unequal
  contexts on one expression class during error checking. It does not reject
  every unsafe fact transport, retire branch-dependent relations, or prove
  safety through context merges/substitution. QR7's host `transport`,
  `loop_bindings`, `resolve_slot`, and `address` (sidecar 128–238,385–423)
  demonstrate reusable checked structural transport, not an already executed
  A1 import/transport/lifetime certificate. Fable's two-missing-premises
  “collapse” is therefore rejected. Direct persistent NoAlias export into
  the initial program and “untouched U0 consumer” remain a proposal needing
  their own lifetime/consumer justification. The actual attempt instead uses
  a new demand-scoped copy of U0's commute action, with untouched store forward:
  `/private/tmp/eggcc-alias-actual/dag_in_context/src/optimizations/scoped_alias.egg:1–16`,
  `scoped_alias.rs:804–869`. It revalidates the
  certificate and clears the token before further rules run. QR7 alone also
  does not prove Fable's claim that A1 unions will survive extraction copies.
- **Exhaustive census is not supported (lines 55–65).** The `!=`-site summary
  matches U0: the only scheduled semantic NoAlias consumer is the commute
  rule; CICM's `!= e1 e2` is e-class nonidentity, and general memory is absent
  from the schedule. But the equality-consumer list is incomplete:
  `peepholes.egg:38–45` consumes the repeated dynamic `a` in `(a*x)+a`, and
  `hackers_delight.egg:9–15,20–40` joins repeated dynamic expressions to
  recognize parity/NTZ loops. These are omitted equality-dependent matches.
  This supplies no new eligible lead: no novel producer, knockout, primitive
  null, surviving backend endpoint, or payoff is demonstrated for them.
  Retain “this pass found no new source-backed eligible lead,” without the
  exhaustive-search claim or a blanket source-only proof of LLVM coverage.
  The other rejections remain screens rather than impossibility results.
  In particular, interval refinement driven solely by primitive bounds fails
  the primitive-null criterion; direct Eq-to-NoAlias is the shorter A1 family;
  generic compile-time benefit has no measured bottleneck. No valid Bril
  multi-way Switch producer was established: although `to_dag.rs:168–188`
  handles Gamma, Bril branches and `restructure::branch_if` use Bool
  (`src/cfg/mod.rs:501–537`, `restructure.rs:70–85`), and the Bool importer
  requires two outputs (`from_cfg.rs:466–497`). Presence of a Switch/Gamma API
  alone is not an admitted trigger.
- **Validation attribution is not a waiver (line 26).** Recording
  `unmet, attributed` is appropriate. Snapshot differences alone do not prove
  all 13 are compiler defects, and `facts.md:13` excludes counting such defects
  as the payoff rather than authorizing a weakened validation criterion.
  An editorial classification cannot turn failed required checks green.

## Superseded proposals and remaining disposition

- **P1 supersession is justified at the mechanism level (lines 30–40).**
  `findings/pack32-screen.md:9–36` and `B/pack32-screen/source.bril:73–80`
  confirm bounded binary packing, domain-preserving updates, cancellation,
  equal-sibling reverse disequality, equality transport, fixed-shift forward
  propagation, and the final false predicate. Affine, Route, and Sort reports
  establish binary cancellation followed by unmarked Add reverse reasoning
  and marked odd-multiply propagation; Parts32 supplies a measured lossless
  32-bit decomposition with unmarked Pair reverse reasoning; same-mask has
  measured Shift7 propagation. P1's exact producer and bounded loop-invariant
  import have not been implemented by these cases, but no distinct generic
  mechanism remains. A terminal superseded disposition may preserve its
  native opportunity and explicitly state this limit. It is not an executed
  P1 result or evidence that P1's implementation/performance must succeed.
- **The proposed A1 probe is now historical (lines 42–51,71).** Fable started
  at `2026-10-20T03:49:48Z` (`06-fable-receipt.json:25–26`), before the
  actual attempt completed at `04:05:12Z`.
  `B/alias-integration/actual-r0/report.md:7–19`, `summary.json`, `acceptance.json`, and `inspection.json`
  now record the initial allocation-type failure, one functional revision,
  and final whitelist rejection of auxiliary `TupleRemoveAt`/`to-hoist` rows
  before a positive certificate (`positive-rejection.json`;
  `scoped_alias.rs:390–395`). Six revised focused tests have three failures;
  the complete host library suite has the same three new failures. All 18
  positive modes, 13 negative arms, 31 interpreter pairs, and 233 native
  checks agree because the actual import fails closed: zero queries/exports,
  identical emitted Bril and process-main instructions, one hot load/two
  stores, no timing. This is an unsuccessful bounded implementation, terminal
  under the initial-plus-one-revision budget at `facts.md:10`, not a refuted
  NoAlias law or a demonstrated redesign requirement. Standalone causal and
  action-parity tests cannot establish actual-host knockout/rescue causality.
- Fable's instructions to run A1 and correct QR7 wording are superseded by
  current evidence: A1 has run, and `B/qr7-integration/report.md` already calls
  its consumer an added bridge and states baseline LLVM load elimination and
  the workload/pipeline limits. The remaining source-backed work is to record
  the P1/A1 dispositions, preserve failed full-validation status, and avoid
  the unsupported LLVM-pass and census assertions above. Nothing in this
  validation establishes global impossibility or waives accepted facts.
