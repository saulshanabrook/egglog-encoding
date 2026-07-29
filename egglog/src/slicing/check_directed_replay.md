# Check-directed replay slicing

Check-directed replay slicing answers a historical question:

> Which events from this particular execution are sufficient to make its
> successful checks succeed again on a fresh e-graph?

The answer is an ordinary egglog program. It contains selected source state,
grounded instances of selected rule firings, and the successful checks that
made those events relevant. That makes the result an *executable causal
explanation*: it can be inspected as source and run by an independent egglog
configuration.

This is different from asking whether an equality is provable. The capture
trace describes what happened in one ordinary execution. A proof, when
requested, is reconstructed by the proof subsystem while the generated
program runs on a fresh graph. Keeping those roles separate is central to the
design.

## The three-stage model

The implementation is easiest to understand as three deliberately separate
stages:

```text
ordinary execution
  + causal-event capture
              |
              v
successful checks -- backward closure --> closed historical support
                                                |
                                                v
                                     graph-neutral grounded replay
                                                |
                                                v
                                      ordinary egglog source
                                         /              \
                                  normal replay       proof replay
```

Each stage exists because the next one cannot safely reconstruct its input
from final e-graph state.

### Capture preserves the past

The final e-graph says which values and rows remain equivalent, but it has
discarded the order in which they were created, merged, rekeyed, removed, and
observed. It also cannot distinguish two deleted-and-recreated occurrences
that have identical source syntax. Capture therefore attaches compact causal
records at the engine points that already know an operation's exact result.

The trace records selected source effects, immutable logical fact identities,
observed grounded firings and their exact premises and bindings, applied
equality edges and their causes, rekeys, replay-observable removals, and the
first successful witness for each check. Static source and structural-term
recipes are shared rather than copied into every event.

Capture is intentionally not eager explanation production. It does not store
one proof tree per equality, elaborate every rule match into a source tree, or
record a conservative prefix of the run. The expensive part of earlier
designs was materializing and repeatedly projecting those representations,
not observing native events. The current trace keeps a shared causal DAG and
enough typed history to recover one actual witness on demand.

Only replay-observable events become durable. A no-op proposal does not become
causal support. Conversely, when a selected source command or firing owns one
relevant effect, replay preserves its whole visible action bundle. Replaying
only one action from a multi-action head would no longer replay the event that
actually occurred.

### Backward closure selects one actual history

Every successful check is a slicing criterion. Its record identifies the
matched facts, typed equality endpoints, occurrence identities, and the exact
historical cutoff at which the check succeeded. A mixed worklist then follows
facts to causes, causes to source commands or firings, firings to their
premises and bindings, and equality obligations to the earlier applied edges,
facts, and rekeys that support them.

The closure also accounts for replay semantics that are not direct positive
evidence for the check:

- Selecting an owner exposes all of that source command's or firing's visible
  effects.
- Native maintenance equalities are retained when selected state would induce
  them again.
- A removal is retained when omitting it would leave a stale keyed row able to
  collide with a later selected row.
- Every selected equality carrier closes over the earlier history that made
  its source-level endpoints denote the native edge that was actually applied.

These passes iterate until they add no support. Typed work items make each
dependency rule explicit, while strict-replay and permutation tests exercise
the resulting closure invariant. The result is a sound support cone for the
observed execution. It deliberately makes no claim of global minimality, and
it is not a proof object.

### Grounded replay checks the account

Replay lowering copies the selection into an owned, graph-neutral
intermediate representation. Backend IDs, recording-graph values, trace
handles, and borrows do not cross into the fresh graph. Literal values remain
source literals; constructor-valued bindings are re-established through
checked `let-check` aliases.

Selected firings are emitted as grounded `run-rule` configurations. Firings
from the same captured wave are placed in one list-form schedule, so they see
the same pre-wave state instead of being accidentally enabled by one another's
replay effects. The original checks are then placed after the waves whose
state they observed.

This use of ordinary syntax avoids a second evaluator for historical events.
The egglog engine remains the authority for rule execution, rebuilding,
merges, and checks. If the recorded account cannot be reconstructed as an
ordinary program, slicing fails closed instead of searching for a different
derivation.

## Three coordinates of historical time

One timestamp is not enough to describe an equality-saturation execution.
The trace uses three related coordinates:

| Coordinate | Meaning | Why replay needs it |
| --- | --- | --- |
| `Wave` | A synchronous execution or rebuild unit whose effects share a pre-wave state | Groups grounded firings without introducing false within-wave dependencies |
| `HistoryPosition` | A total order across facts, firings, equalities, rekeys, removals, and checks | Places cross-kind events and bounds exact row lifetimes |
| `EdgeHorizon` | The dense prefix of applied equality edges visible at an event | Prevents a later union from explaining an earlier read or endpoint spelling |

A wave alone is too coarse: several equalities, row changes, and removals can
occur within it. A history position orders those different event streams, but
an equality explanation also needs an explicit edge high-water mark.
Historical equality queries therefore use the position and equality horizon
recorded at the observation, never the final equality relation.

## Syntax is not occurrence identity

A structural replay term such as `(A 1)` identifies syntax in a shared term
DAG. It does not identify one native occurrence of that syntax. A constructor
row can be deleted and later recreated with the same spelling but a different
native value and causal history.

`FactId` provides the missing occurrence identity. It remains stable when a
live logical row is merely rekeyed by canonicalization. A tombstone ends that
fact's lifetime; recreation receives another fact identity. Rekey records make
the changing key addressable at the correct historical point, while
tombstones provide explicit kill semantics for non-monotone state.

Ordered containers add another version boundary. A rebuilt container may have
the same apparent call shape while its child denotations belong to a refreshed
version. A freshness floor prevents a replay alias for the new container from
collapsing back to an alias established for an older version.

For every structural call used by a grounded binding, replay consequently
tracks four independent constraints:

- **Availability:** the exact producer has been created, or a pure call is
  recomputable.
- **Key readiness:** child aliases, equalities, facts, and rekeys needed to
  address that producer's key are already present.
- **Liveness:** if the producer's selected tombstone is replayed, the alias is
  captured strictly before that removal.
- **Freshness:** a refreshed container and its descendants do not reuse an
  alias from an earlier version.

An alias is scheduled only at a retained pre-wave point satisfying all four.
There is no fallback to a syntactically identical occurrence outside that
window.

## Why equality carriers need strict pre-event closure

The smallest counterexample has seven commands:

```lisp
(datatype E (A) (B) (C))
(A)
(B)
(C)
(union (A) (B))
(union (B) (C))
(check (= (A) (C)))
```

Suppose constructors are allocated in `A`, `B`, `C` order. The first union
connects `B` to `A`. When the second source action is applied, it is still
spelled `(union (B) (C))`, but its left structural endpoint already denotes
`A`; the native edge connects `C` to `A`.

Selecting only the owner of that second edge appears plausible and can render
this program:

```lisp
(datatype E (A) (B) (C))
(A)
(C)
(union (B) (C))
(check (= (A) (C)))
```

It fails. Grounded replay faithfully applies the emitted proposal, but the
fresh `(B)` no longer denotes `A`. Retaining the owner of a native applied edge
is therefore insufficient; replay also needs the historical state that made
the owner's structural proposal denote that edge.

The closure law is strict and pre-event. For every replay-visible applied
equality, both structural endpoints are resolved immediately before that
event: at the preceding `EdgeHorizon` and preceding `HistoryPosition`. Their
representatives must match the recorded native parent and child, and the
earlier occurrence and equality support for those denotations is added to the
slice. The equality being explained cannot justify its own precondition. This
both fixes the example and prevents circular explanations.

## Why output support and producer liveness are different

A later counterexample combines deletion, recreation, and an alias used after
its constructor row is gone. Its essential timeline is:

```text
old (A 1) occurrence
  -> delete it
  -> create a new (A 1) occurrence
  -> establish the child/key bridge used to create H(new A)
  -> delete H(new A) and its child row
  -> establish a later equality bridge
  -> consume the value that was stored before deletion
```

The two `(A 1)` occurrences have the same syntax but are not interchangeable.
The alias for the selected `H` occurrence must be checked after its exact
producer exists and after the *new* child's key is addressable, but before the
selected deletion of `H`. A bridge involving the dead old child cannot be used
to move that lower bound past the deletion.

At the same time, an alias established while a constructor row is live remains
a valid name for its e-class after that row is removed. Equality support that
relates the already-captured output to a later consumer may therefore occur
after the deletion. Requiring the output bridge to fit inside the producer's
lifetime would reject valid replays; allowing child/key support after the
deletion would select an occurrence that could never have been addressed.

This is why key readiness deliberately excludes the current call's output
bridge, and why liveness is an exclusive upper bound rather than another
causal dependency. If no retained pre-wave point lies between readiness and
the selected kill, replay construction reports an error.

## Preserving source carriers

The capture engine normalizes rewrites into rules, but the replay artifact
preserves retained `rewrite` and `birewrite` commands as those source forms.
Deterministic replay names identify the exact normalized direction used by a
grounded firing, while the original birewrite orientation and source globals
remain intact. This matters even when only one direction of a birewrite enters
the slice: replacing its carrier with an ad hoc normalized rule would change
the program being replayed and can lose source-level dependencies.

The same principle governs all lowering: declarations and selected sources
come from the capture catalog, runtime values are reconstructed from typed
structural recipes, and whole action bundles retain their ordinary semantics.
The replay artifact is a smaller egglog program, not a serialization of
backend operations.

## Trace evidence and proof are independent

Trace evidence answers “what made this check succeed in the recorded run?” A
proof answers “what certificate does the proof-enabled engine construct for
this proposition?” Those questions overlap at equalities, but their data
structures and correctness checks are independent.

Capture always runs on an ordinary, non-proof graph. The generated source can
then run normally or on a fresh graph configured for proofs, proof testing,
term encoding, or proof extraction. Proof mode therefore consumes the replay
program exactly as it consumes any other egglog program; it does not interpret
recording-graph values or trust the trace as a certificate. Successful proof
replay is strong validation of the artifact, but it does not turn the slice
into a minimal proof.

## Where recording cost comes from

The exact replay contract records an observed firing together with its ordered
premise facts and source-order bindings. Most capture work therefore comes from
carrying witnesses through matching and commit, not from later explanation or
rendering. Backward closure and replay are cold operations whose cost follows
the retained cone; capture pays for every observed firing whether or not that
firing eventually supports a check.

That tradeoff is deliberate. An exact witness lets replay reconstruct the
historical firing without searching for another derivation. A different design
could annotate each first-produced fact with a rule identity and derivation
wave, then re-run that rule at slice time to recover premises. Zhao, Subotić,
and Scholz use this shape for scalable Datalog provenance in
[*Provenance for Large-scale
Datalog*](https://arxiv.org/abs/1907.05045).

Annotation-only capture is not a drop-in storage optimization here. It changes
the contract from replaying a recorded match to re-deriving one, so it needs a
bounded search, a deterministic tie-break that recovers the original witness,
and new evidence for mutable denotations, rekeys, and deletion. It is a useful
future option if always-on recording cost becomes the priority; the current
design chooses direct historical evidence and keeps that cost visible.

## Supported boundary and publication contract

The current command-line boundary is intentionally narrow: one input file,
one execution thread, the main backend, and trace capture enabled on an
ordinary graph before user declarations, rules, or input are installed.
Successful `check` commands are the replay roots. `extract` and
`multi-extract` output are not retained.

Unsupported behavior remains fail-closed. Some constructs, such as push/pop
state and nested `fail`, are rejected before that command is resolved or can
mutate captured state. Static typed `Unsupported` structural-origin selectors
are allowed to remain dormant, but an effective merge or rebuild that reaches
one is rejected while the capture transaction is still abortable. Unsupported
scheduler, source, literal, container, or mutation shapes similarly produce an
error at the relevant capture or selection boundary. An unsupported path is
never replaced by a prefix or by the original program.

Source-authored `run-rule` schedules are one deliberate current boundary.
Replay uses grounded `run-rule` for already-recorded ordinary firings, but
capturing a source-authored grounded firing would also need its exact premise
`FactId`s to publish atomically with the grounded mutation transaction. The
existing grounded executor does not expose that commit-time carrier, so trace
capture rejects the schedule instead of synthesizing premise identities or
recording its effects as source facts.

`--slice-output PATH` captures and slices, then writes the rendered source
directly to `PATH`. By itself it does not replay the artifact. The write is an
ordinary direct filesystem write: there is no production replay-validation
pass and no atomic temporary-file-and-rename publication protocol.

`--slice` requests execution of the generated program on a fresh graph. Replay
mode is independent, so proof and other execution-mode flags can be combined
with slicing. If output and replay are both requested, writing still precedes
replay and is not made transactional by it.

Strict replay is instead a corpus and CI invariant: supported generated
artifacts are executed there, and a replay failure fails the test. Code that
publishes an artifact outside that workflow must therefore decide whether to
run its own validation and atomic-publication protocol. The existence of an
output file alone is not a validation claim.

## A practical design guide

When extending capture or replay, work from the semantic obligation rather
than from a desired output shape:

1. **Name the observation.** Decide which successful check fact or equality is
   being preserved and at which historical cutoff.
2. **Keep exact occurrence identity.** If deletion, recreation, rebuild, or
   repeated syntax can distinguish two values, a structural term alone is not
   a sufficient key.
3. **Record at the effective commit point.** Persist the smallest stable cause,
   premise, endpoint, or version receipt that the engine already knows. Do not
   eagerly unfold it into a proof or replay tree.
4. **State the temporal law.** Specify the wave, cross-stream position, equality
   horizon, and any availability, readiness, liveness, or freshness bound.
5. **Close over executable semantics.** Include whole owner effects,
   pre-event endpoint denotation, induced maintenance, and interfering kills,
   not only the positive edge found by backward reachability.
6. **Choose an ordinary source carrier.** The owned replay form must reconstruct
   typed values and execute through the normal engine without recording-graph
   handles or a second evaluator.
7. **Falsify with strict replay.** Test allocation-order changes, same-syntax
   delete/recreate cases, same-wave effects, container refresh, and proof replay.
   A missing capability should end in a precise error, never a conservative
   prefix.

This discipline keeps capture bounded and its costs explicit, keeps historical
queries exact, and makes the fresh engine an independent oracle for the final
artifact.

## Research lineage

This design combines established ideas from several research traditions. The
particular composition is project-specific; this document makes no claim that
the combination, or any individual mechanism, establishes research novelty or
priority.

- Database and Datalog provenance motivate shared derivation DAGs, one
  selected witness, and lazy reconstruction. See Deutch, Gilad, and
  Moskovitch, [*Selective Provenance for Datalog using Top-k
  Queries*](https://amirgilad.github.io/publication/vldb15/VLDB15.pdf), and
  Green, Karvounarakis, and Tannen, *Provenance Semirings*.
- Annotation-based Datalog provenance demonstrates the alternative of retaining
  compact rule/height labels and reconstructing derivations on demand: Zhao,
  Subotić, and Scholz, [*Provenance for Large-scale
  Datalog*](https://arxiv.org/abs/1907.05045) and *Debugging Large-scale
  Datalog: A Scalable Provenance Evaluation Strategy*.
- Dynamic slicing supplies the criterion-and-backward-reachability model and
  the limited-preprocessing point between eager graphs and repeated
  re-execution. See Zhang, Gupta, and Zhang,
  [*Precise Dynamic Slicing
  Algorithms*](https://www.cs.purdue.edu/homes/xyzhang/Comp/icse03.pdf) and
  [*Cost Effective Dynamic Program
  Slicing*](https://www.cs.ucr.edu/~gupta/research/Publications/Comp/pldi04.pdf).
- Delayed trace interpretation and the forward/backward consistency law are
  developed by Perera, Acar, Cheney, and Levy in
  [*Functional Programs that Explain their
  Work*](https://www.mpi-sws.org/tr/2012-003.pdf).
- Timestamped trace storage and record/replay systems motivate compact capture
  followed by offline queries: Zhang et al., [*Whole Execution
  Traces*](https://microarch.org/micro37/papers/10_Zhang-WholeExecutionTraces.pdf);
  Devecsery et al., [*Eidetic
  Systems*](https://www.usenix.org/conference/osdi14/technical-sessions/presentation/devecsery);
  and [rr](https://rr-project.org/).
- Reason-labeled equality forests and on-demand explanation follow the
  proof-producing congruence-closure line, especially Nieuwenhuis and
  Oliveras, *Proof-Producing Congruence Closure*, and Flatt et al., *Small
  Proofs from Congruence Closure*.
- Explicit tombstones reflect the operational treatment required by deletion
  and kill semantics; compact typed sidecars follow the same systems lesson as
  Kemerlis et al., [*libdft*](https://nsl.cs.columbia.edu/papers/2012/libdft.vee12.pdf).
