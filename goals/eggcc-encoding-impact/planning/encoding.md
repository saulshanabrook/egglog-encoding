# Encoding discovery: remaining-child disequality and closure

Status: **planning evidence only**. No implementation, builds, tests, benchmarks,
commits, or changes to the previous study's frozen evidence were performed.
The only authored file in this slice is this planning note. EggCC consumers and
measurement infrastructure are owned by the other planning circles and were not
scanned here.

## Source identity and commands

Primary encoding implementation inspected:
`/Users/saul/p/wt/egglog-encoding/injectivity`, branch `codex/injectivity`, HEAD
`392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`. The inspected implementation/test/
scheduler paths have no tracked changes. The last commit touching the query and
its tests is `e9d91839422a09e63986d730c85fe8fd4002c156`, “Document injectivity
encodings and inference boundaries.”

The primary `/Users/saul/p/egglog-encoding` checkout is at
`fdd4eac12c1318c578badbf5d1299e0e3eb4e6c0` with extensive unrelated author work.
It does not contain the feature worktree's `egglog-experimental/src/disequality.rs`.
Use an isolated implementation checkout after plan approval; do not reconstruct
the feature in that dirty primary tree or alter the completed study's inputs.

Read-only commands used, from the feature worktree unless stated otherwise:

```sh
git rev-parse --show-toplevel
git rev-parse --abbrev-ref HEAD
git rev-parse HEAD
git status --porcelain=v1 --untracked-files=no -- egglog-experimental/src/disequality.rs egglog-experimental/src/injectivity.rs egglog-experimental/tests/injectivity_disequality.rs egglog/src/exec_state.rs egglog/src/lib.rs egglog-experimental/src/scheduling.rs Makefile Cargo.toml
git log -1 --format='%H %s' -- egglog-experimental/src/disequality.rs egglog-experimental/tests/injectivity_disequality.rs
nl -ba egglog-experimental/src/disequality.rs | sed -n '208,415p'
nl -ba egglog-experimental/src/injectivity.rs | sed -n '219,291p'
nl -ba egglog-experimental/tests/injectivity_disequality.rs | sed -n '1,116p'
nl -ba egglog-experimental/tests/injectivity.rs | sed -n '1,88p'
nl -ba egglog-experimental/tests/disequality.rs | sed -n '1,190p'
nl -ba egglog-experimental/tests/injectivity/injectivity-disequality.egg | sed -n '1,90p'
nl -ba egglog-experimental/tests/disequality/congruence.egg
nl -ba egglog/src/exec_state.rs | sed -n '338,615p'
nl -ba egglog/src/lib.rs | sed -n '1350,1406p'
nl -ba egglog-experimental/src/scheduling.rs | sed -n '265,350p'
nl -ba egglog-experimental/tests/files.rs | sed -n '365,440p'
cat egglog-experimental/Cargo.toml
cat rust-toolchain.toml
nl -ba Makefile | sed -n '22,79p'
```

Additional adjacent `nl`/`sed -n` reads covered the ranges cited below; source
discovery used `rg -n` for `known-disequal`, `unary`, `reverse`, `saturate`,
`constructor_enodes_for_eclass`, and `function_entries`. Root reads were accepted
`facts.md`, `STATUS.md`, root revision/status, and workspace/Makefile paths.
The Rust pin is 1.91.0. All validation commands later in this note are proposed,
not executed during setup.

## Laws: separate congruence from injectivity

For an ordinary congruent constructor `f : S₀ × … × Sₙ₋₁ → T`, the requested
binary law is sound without an injectivity annotation:

```text
f(a,b) ≠ f(c,d)  ∧  a = c   ⇒   b ≠ d.
```

More generally, for each position `i`:

```text
f(a₀,…,aₙ₋₁) ≠ f(b₀,…,bₙ₋₁)
  ∧  ∀j ≠ i. aⱼ = bⱼ
  ⇒  aᵢ ≠ bᵢ.
```

Assuming equality at the remaining position would make all inputs equal and
therefore the results equal by congruence, contradicting the premise. Unary
reverse reasoning is this rule with no sibling premises. Nullary constructors
have no child conclusion. If two or more positions remain unresolved, parent
disequality alone does not choose which position differs. Unequal siblings are
not a substitute for equal siblings.

Keep this direction separate from the existing opt-in laws:

| Direction | Required assumption |
| --- | --- |
| Equal outputs imply equal corresponding inputs | Injectivity of that constructor. |
| One known-unequal input implies unequal outputs | Injectivity of that constructor. |
| Unequal outputs plus equality of all other inputs imply unequal remaining inputs | Ordinary congruence; no injectivity annotation. |

This new direction can therefore apply to a noninjective constructor without
reusing the previous study's rejected blanket Concat/Const/Bop/Top annotations.
It does not validate any unsound equality or parent-disequality premise supplied
by a compiler consumer; those still require the consumer's semantic argument.

## Verified implementation state

Paths below are relative to the clean feature worktree.

| Current behavior | Primary evidence |
| --- | --- |
| `disequal` stores same-sort unionable equality-sort constraints; direct primitive operands are rejected. | `egglog-experimental/src/disequality.rs:7-16,191-194,722-737`; invalid-input tests in `tests/disequality.rs:99-125`. |
| Query returns `Unit` for a finite witness and remains undefined for unknown. It does not add rows, applications, unions, or a persistent pair cache. | `src/disequality.rs:33-54,123-127,231-244`; row/table-count assertions in `tests/injectivity_disequality.rs:16-40`. |
| Forward structural disequality already works at every argument position of marked constructors, including primitive mismatches and recursive equality-sort witnesses. | `src/disequality.rs:311-331`; tests `explicit_eq_fields_propagate_at_each_position_and_respect_opt_in` at `tests/injectivity_disequality.rs:44-70`. |
| The constructor list is read exclusively from `@injectivity-constructors`. | `src/disequality.rs:276-295`; annotation metadata installation in `src/injectivity.rs:176-201`. |
| Reverse search explicitly accepts only a one-input equality-sort constructor, and that constructor must already be on the marked-only list. | `src/disequality.rs:333-345`. |
| N-ary reverse with equal siblings has no implementation path. Unmarked unary reverse is also absent despite needing only congruence. | The only reverse branch above, plus documented boundary in `README.md:65-70` and `src/disequality.rs:47-52`. This is a source finding, not an executed missing-case receipt. |
| Existing negative tests intentionally encode the old limits. | `reverse_witnesses_are_unary_only_and_cross_sort`, `tests/injectivity_disequality.rs:73-95`; unmarked `Other` has asserted unequal outputs but its children remain unknown. The `.egg` example at `tests/injectivity/injectivity-disequality.egg:35-49` distinguishes unary congruence from ambiguous binary reverse. |
| Equal-output injectivity is ordinary generated rules, scheduled explicitly, including subsumed rows. Equality-sort fields union; primitive disagreement panics. | `src/injectivity.rs:219-289`; `tests/injectivity.rs:15-85`. Containers are rejected for marked constructors at declaration. |
| Queries support ordinary execution only. Existing term/proof use must continue rejecting them. | `src/disequality.rs:191-194`; `tests/injectivity_disequality.rs:250-275`. |

The existing assertion encodings already detect contradiction after all inputs
of unequal parent applications become equal: ordinary congruence merges those
parent results, and the stored constraint becomes inconsistent. The unmarked
unary example in `tests/disequality/congruence.egg:4-8` exercises exactly this
path. Remaining-child querying adds usable intermediate reasoning; do not call
that existing contradiction case a newly found baseline bug.

## Recommended first vertical slice

Implement the binary case as the first red/green test, but use one n-ary
remaining-child mechanism rather than special-casing arity two. Keep the public
API and read-only-query contract intact initially.

1. Add an ordinary-mode test with an **unmarked** binary constructor, distinct
   input/output equality sorts, asserted parent disequality, and equal first
   children. Require the second-child query to succeed. Include the converse
   position and an unmarked unary case.
2. Separate the schema collections used by query search: marked constructors
   supply the existing forward-injectivity edges; supported ordinary
   constructors supply reverse-congruence edges. Do not remove the forward
   annotation gate. Include relevant unmarked input sorts in root-goal seeding;
   currently sort discovery also comes only from marked schemas/assertion tables
   (`src/disequality.rs:258-299`). A cross-sort unmarked test catches this trap.
3. For a queried child pair at position `i`, locate existing rows of the same
   constructor with those respective children, match equality of every sibling
   column, and enqueue their result pair as a witness goal. Only the remaining
   parent-disequality premise is another search goal, so a finite per-call
   reachability search remains sufficient; sibling equality is a guard against
   the committed graph, not another disequality alternative.
4. Keep missing applications absent. Preserve subsumed rows, `push`/`pop`,
   failed-declaration behavior, canonical committed IDs, and no graph growth.
   The existing old-limit test must be updated deliberately: unmarked unary
   `Other` should now supply reverse witnesses, while ambiguous binary pairs
   must still stay unknown. The existing unmarked **forward** negative must
   continue passing unchanged.
5. Update the README, module explanation, and executable query example to state
   the new direction and remaining boundaries. Stop this slice at a reviewable
   correctness/coverage change before adding materialization, a new command,
   persistent indexes, or any proof support.

Suggested initial supported fragment: constructor tables with unionable
equality-sort outputs, a unionable equality-sort focused child, and primitive or
unionable equality-sort siblings. Ordinary `function` tables, container-aware
reasoning, nonunionable focused children, and primitive query operands remain
explicitly outside this first slice. The mathematical law is broader than that
implementation fragment; document the difference.

Existing read APIs support a minimal implementation without a runtime redesign:
`Read::tables`, `table_subtype`, `constructor_schema`, and `is_sort_unionable`
in `egglog/src/exec_state.rs:404-460`, plus `constructor_enodes[_while]` at
`:463-495`. The latter exposes children, output, and subsumed status. There is
currently an output-indexed lookup at `:498-527`, but no read API here indexed
by arbitrary child position. Start with a transient per-query index or a
bounded straightforward scan grouped by constructor/position/sibling tuple;
retain current unary direct lookup when useful. Measure before proposing a
persistent index or core read API change. A per-query row cross-product can be
expensive and must not be described as free.

Scan only the appropriate table subtype and output-sort contract. Relations
desugar to nonunionable constructor outputs (`exec_state.rs:453-460`), custom
functions have a separate subtype, and EE introduces internal constructor tables.
Decide and document whether the reverse fragment includes representation-internal
tables; do not accidentally rely on their presence for user-level NEE/EE parity
or silently exclude user `:internal-hidden` constructors by presentation status.

## Primitive and equality-sort obligations

- Equality-sort siblings require actual committed equality, not failure to find
  a disequality witness. Different current class IDs are not disequality.
  Read APIs expose raw stored IDs and the output-indexed lookup warns about
  merged-but-not-canonical rows (`exec_state.rs:498-504`); test after real union
  and rebuild rather than assuming ID comparisons remain valid at every stage.
- Primitive siblings use the existing native equality/value representation
  convention. Initially cover integers, booleans, and strings. A different
  primitive sibling must prevent inferring the focused equality-sort mismatch.
- For a primitive focused position, native `!=` already answers two distinct
  concrete primitive values. Equal focused values plus all equal siblings make
  the asserted parent disequality contradictory through congruence. Do not try
  to insert `(disequal 1 2)` or widen `known-disequal?` to primitive operands as
  an incidental part of this change.
- Marked equal-parent primitive conflicts still panic when `injectivity` runs.
  An unmarked constructor must not acquire primitive cancellation merely because
  reverse congruence became available.

## Query closure, storage, and schedules

The current BFS uses a per-call visited set over typed unordered pairs
(`src/disequality.rs:247-348`). It already closes its supported witness edges
over the current committed graph. A new reverse edge should be answered on
demand without scheduling a query ruleset or writing an asserted child pair.
Asserted NE storage / EE equality terms and their contradiction normalization
remain a distinct mechanism (`src/disequality.rs:351-383,722-737,824-883`).

This distinction affects integration:

1. A sibling equality supplied by another rule is unavailable until that rule
   runs and rebuilding commits it. Equality-injectivity still requires an
   explicit `injectivity` schedule; the query does not perform those unions.
2. A `:naive` consumer must rerun when a hidden parent witness or sibling equality
   changes, even if its explicit request/input rows do not change. Core context
   enforcement is documented at `egglog/src/exec_state.rs:64-81` and
   `egglog/src/lib.rs:1525-1538`.
3. `check-contradiction` saturates **only** private `@disequality`, then checks
   for a contradiction (`src/disequality.rs:415-453`). It does not run
   `injectivity`, consumer rules, or remaining-child materialization. EE's
   private rules can union user values (`:824-861`), so a one-time check after
   consumer saturation is not a general joint fixed point.
4. Core `saturate` stops on `RunReport.updated` (`egglog/src/lib.rs:1374-1394`);
   the default extended scheduler stops on `can_stop`
   (`egglog-experimental/src/scheduling.rs:268-289`). Existing query Rust tests
   use the core-schedule graph (`tests/injectivity_disequality.rs:6-8`), while
   ordinary CLI construction enables extended scheduling (`src/main.rs:15-22`).
   Exercise both on the bounded closure regressions.

First establish a bounded concrete pipeline's required order, then specify its
fixed-point contract. Do not claim that existing public commands provide a
general joint closure API, or publish private `@disequality` names as a stable
user API. If a real consumer needs explicit stored child constraints or a public
joint-closure command, make that a separately reviewed second slice. It must
account for equality producer → injectivity → query/materialization → consumer
→ encoding-normalization dependencies and report updates correctly.

For generative pipelines, no finite convergence follows just from these laws.
Retain fail-fast audits **inside** any generative propagation saturation, before
consumers, as established by the preceding study. Do not saturate an unbounded
producer and plan to audit only afterward.

## Automated acceptance matrix proposed for execution

Use the existing `for_encodings` helper in
`egglog-experimental/tests/injectivity_disequality.rs:6-14` for ordinary NEE/EE
parity. These are planned checks, not claimed results:

| Check family | Positive target / required negative |
| --- | --- |
| Requested binary rule | Unmarked cross-sort `f(A,B) ≠ f(A,D)` gives `B ≠ D`; symmetric orientation and the other focus position work. |
| No invented injectivity | An unmarked constructor's known-unequal children alone do not prove its outputs unequal; equal unmarked outputs do not cancel arguments. |
| Ambiguity | Parent disequality with two unknown positions yields neither individual child disequality; a known-unequal sibling does not permit selecting another child. Different constructor names give no residual inference. |
| Ternary/general arity | For each of three positions, all other siblings equal gives that child's witness; equality of only one sibling leaves two unresolved positions unknown. Include repeated argument positions and arity zero/one boundaries. |
| Mixed primitive siblings | Equal integer/bool/string siblings allow an equality-sort focus; differing primitive siblings block selecting that focus. Primitive direct query/assertions remain rejected; all-equal-argument parent contradiction remains detected. |
| Late union | Parent NE exists before sibling equality: query is initially undefined, then succeeds after an explicit sibling union. Repeat when sibling equality is exposed only by scheduled injectivity. No stale negative cache. |
| Delayed rule body | A `:naive` consumer's explicit request rows remain unchanged while an external sibling equality or parent witness appears; the next consumer iteration derives its result. Test core and extended schedules to a bounded common fixed point. |
| Contradiction | Materialized parent NE plus subsequent equality of the final children makes `check-contradiction` succeed in NEE/EE. Seeded bad axioms stay labeled; structural query truth alone is not asserted-pair materialization. |
| Read-only/lifecycle | Tuple and table-name counts are unchanged by direct queries; no missing applications are created. Subsumed rows, canonical IDs after unions, pop/redeclaration/failed declarations, and recursive cycles retain coverage. |
| Mode boundary | New query uses still reject term/proof encoding; existing assertion/injectivity mode regressions pass. No validator/proof extension is included. |

After hand examples, use a small independent finite closure oracle as a meaningful
cross-check: fix a finite set of existing typed applications, the current equality
partition, asserted NE seeds, marked forward rules, and reverse rules guarded by
all-other-input equality. Compare all supported pair queries against an iterative
least-fixed-point reference. Cover cycles and row ordering without mirroring the
implementation's BFS/index algorithm. This checks the stated fragment; it does
not prove unrestricted completeness or validate compiler semantics.

Proposed validation entrypoints, after implementation permission and in its
isolated encoding workspace root:

```sh
cargo +1.91.0 test -p egglog-experimental --test injectivity_disequality --test injectivity --test disequality
cargo +1.91.0 test -p egglog-experimental --test files injectivity
make check
```

The new Rust tests belong in the existing `injectivity_disequality` integration
target; the file harness discovers `tests/**/*.egg` and uses sanitized file stems
(`tests/files.rs:163-179,373-430`). Add/update the ordinary query example under
`tests/injectivity/`; proof compatibility is auto-filtered, not assumed. Require
nonzero selected test counts and inspect expected-error diagnostics. Once full
`make check` passes, do not rerun `make proof-tests` redundantly unless a new
proof-specific concern exists. CLI smoke checks should use both NEE/EE on the
same new ordinary example to cover the extended scheduler separately.

## Claims, ordering, and stop terms

Order the execution plan as: freeze current source in an isolated checkout;
write the minimal missing unmarked-binary test; implement n-ary query reverse
congruence; pass the acceptance matrix/reference fragment; review the scoped
API/documentation boundary; then integrate only with a consumer identified by
the consumer circle. Storage/closure API work is conditional on a concrete
consumer mechanism, not a prerequisite redesign.

The strongest initial claim is “sound additional read-only witnesses for the
specified finite constructor fragment.” Undefined remains unknown. There is no
claim of completeness for arbitrary equational theories, arbitrary function or
container semantics, all class disequalities, constructor disjointness, runtime
nonaliasing, mutable analysis records, proof modes, or term-generating schedules.
Even fragment completeness requires a precisely specified graph and oracle
evidence; the source scan alone establishes no such theorem.

Stop the first implementation slice for review when the target changes from
unknown to a witness, meaningful negative cases stay unknown, lifecycle/mode
regressions pass, and direct query storage remains unchanged. Stop and revise if
correctness needs an unjustified constructor annotation, unknown-as-unequal
reasoning, a primitive-assertion API change, or an unbounded schedule. Encoding
coverage, fewer rows, and a removed operation alone do not satisfy the accepted
impact objective. An eventual negative impact conclusion must come from the
shared evidence-backed candidate/exhaustion review, not this bounded encoding
slice or an arbitrary prototype count.
