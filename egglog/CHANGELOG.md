# Changes

## [Unreleased] - ReleaseDate

- **Breaking reporting formats.** `--save-report` now stores each iteration with its ruleset name and timing responsibility, and no longer serializes the redundant `ruleset_timings` or `search_and_apply_time_per_rule` aggregates. `--timing-summary` now emits the typed version-4 timing partition used by the benchmark runner; the runner's JSONL schema is also version 4, so older disposable benchmark caches must be recomputed.
- **Proof mode is substantially faster and uses less memory.** The term/proof encoding no longer writes each proof's `Congr`/`Trans`/`Sym` steps as rows while rules run; it records what justified a fact and rebuilds the steps when a proof is asked for. A flat `(rewrite (Add a b) (Add b a))` firing writes 2 proof rows where it wrote 13. Across the benchmark suite that is 0.73–0.75x wall time, and peak memory on `math-microbenchmark` goes from 2.3 GiB to 1.1 GiB. Proof semantics are unchanged by this work; the proof snapshots that do move in this release move for the separate fixes and the now-deterministic extraction order below.
- Fix `set-if-empty` in the term/proof encoding looking its key up in the committed table while staging its insert, so two calls with the same key in one action batch both missed and both inserted, minting two e-classes for one term — leaving the encoding one iteration behind ordinary execution on programs that do not saturate. It now reads through the batch's predicted rows, as `lookup_or_insert` already did.
- **Declared indexes.** `(index <name> <function> (any <column>*))` declares a read-only relation over the rows of `<function>`: each value appearing in *any* of the listed columns, followed by the whole row. It answers "which rows mention this value", which no ordinary atom expresses — repeating a variable across those columns instead constrains them to be equal. Purely physical: it changes no results, only the cost of finding those rows. The database maintains it and creates it on demand, so the declaration binds a name and nothing more. An atom is probed rather than scanned, so a *variable* indexed value must be bound elsewhere in the query by a function's rows — a body primitive runs after the join, so it cannot bind one — while a literal is already known and needs no binder. Over a single indexed column the occurrence is an ordinary equality and the atom is lowered to a plain one, which is also what lets the indexed value sit at another of the row's columns; over several columns that combination is a per-row disjunction and is rejected. A *user-written* declaration is not yet supported under the term/proof encoding, which rewrites a function into a view whose columns differ, so the declaration would name the wrong ones; the encoder's own declarations, written against its views, are unaffected. `(any …)` is an extractor over the row, leaving room for others (e.g. the elements of a container column).
- The term/proof encoding rebuilds a view's eq-sort columns through a declared index: one rule per child eq-sort, driven by a `UF` edge joined against the index, canonicalizing the whole row in its action. This replaces the per-column fan-out and folds the separate e-class rule into it.
- Add a `(begin <action>*)` command and a `(let <var> (begin <action>* <expr>))` form that run a block of actions once, immediately, with a shared *local* scope (`let`s bind local variables, not global functions); `let`-begin additionally binds the global `<var>` to the block's trailing value. In the term/proof encoding, each top-level action's minted temporaries now run inside one such block instead of as separate top-level `let`s, so a temporary no longer becomes its own global function/table. This removes the per-proof-node table blow-up that made building a large static graph under the encoding slow (dominant cost on graphs with many top-level terms). A *user-written* `begin` block is reported unsupported under the term/proof encoding for now (proof checking models top-level actions individually, so a block's local bindings have no checkable representation); the encoding's own generated blocks are unaffected.
- In the term/proof encoding, when a `union` operand is a freshly-built constructor term, build it directly into the other operand's e-class instead of minting a fresh id and unioning it away: a plain view `set` points the constructor's children at the other operand's (target) e-class, and the view's congruence `:merge` handles the case where the term already exists. This reuses ids and drops the corresponding `@UF` rows (union-heavy workloads run substantially faster and use less memory in both term and proof mode). In proof mode the view row carries the equality proof `target = f(children)` as the dropped union's rule justification, with the built-in operand's term kept on its own id so proof reconstruction stays unambiguous.
- Fix unsound container rebuild proofs for reordering containers (`Set`, `MultiSet`, `Map`): rebuilds identified changed elements by their position in the container's value-order element list, which need not match the proof term's canonical child order. Rebuild proofs now use a new element-matching `CongrAll` proof constructor, desugared into positional `Congr` steps during proof conversion (the user-facing proof format is unchanged).
- Fix `file_supports_proofs` wrongly rejecting programs whose `(push)`-scoped globals are read in actions: the whole-program check ran against the final (popped) scope, so scoped globals looked like unsupported function lookups. Six corpus files (herbie, array, bdd, cyk, math, typeinfer) now run under the term/proof encoding tests. Also accept a reflexive `Fiat` proof over a termified base value: base sorts whose values termify as applications rather than literals (BigInt's `(from-string …)`, BigRat's `(bigrat …)`) declare their canonical value term form via a new `prim_value_constructor` sort hook (the base-sort analogue of `rebuild_container_normalizer`), which the proof checker uses to re-evaluate such terms. `from-string` also gains a primitive validator.
- Fix the term/proof encoding dropping rebuilds of a custom function's container-valued *output*: elements unioned after the value was stored kept the stale container. The FD view's value column now canonicalizes through the container rebuild primitive (delete-then-reinsert, so the user merge does not rerun), with the row proof composed by `Congr` at the output position.
- In proof mode, build every container over its elements' *natural* (as-built) ids, recording each `natural -> deduped` equality in the element's union-find so the standard container rebuild canonicalizes it. This keeps a container's term-proof anchored on the shape the rule wrote, even when the deduped e-class extracts as a different member of the class (e.g. a birewrite partner).
- The term/proof encoding supports `:no-merge` functions with a primitive or `Unit` output (encoded as an FD view declared `:no-merge` with an identity-column guard on the output), but no longer supports `:no-merge` functions with an eq-sort output (whose conflict check needs union-find leaders). Such a program must run without term/proof encoding, or give the function a `:merge` (e.g. `:merge old`). This removes the rule/`current`-helper machinery the encoding previously used to emulate `:no-merge`.
- `(fail <command>+)` now accepts multiple commands, running them in order and succeeding if any one fails (previously it wrapped a single command). Desugaring, global removal, and proof encoding keep the whole expansion of a wrapped command inside the `fail`, so `fail` now works over commands that expand to several — including `(fail (set …))` under the term/proof encoding.
- In the term/proof encoding, load `(input …)` for custom functions (with or without `:merge`, including `:no-merge` `Unit`-output ones) natively via `EGraph::native_input`, the same path already used for constructors and relations. This removes the per-input bodyless "loader rule" (and its fresh ruleset) that custom-function inputs used to compile to.
- Make proof extraction deterministic by choosing rows independently of storage iteration order.
- Speed up proof extraction, which was quadratic: it rescanned every candidate function's rows once per extracted node. Each function's rows are now read once per extraction run and grouped by output value. The extracted term is unchanged.
- Speed up `core-relations`' `merge_all` by resetting only the tables that changed during the call instead of every table.
- Desugar global variables as functions instead of constructor + `union` in the term/proof encoding, and skip rebuilding after non-`union` top-level actions (removing a per-definition rebuild cost).
- Fix user-defined primitives (registered through the Rust API after construction) being reported as unbound under term encoding / proofs: primitive registration now also reaches the term-encoding typechecker, so the encoder can typecheck the encoded program. Previously callers had to manually register the primitive on `proof_state.original_typechecking` as well.
- Fix a build failure when egglog is compiled without default features (as a library dependency). The `egglog-add-primitive` proc macro parses full Rust expressions and now declares `syn`'s `full` feature directly, instead of relying on another crate (`clap_derive`, via the `bin` feature) to unify it onto our `syn`. This surfaced when `clap_derive` moved to `syn` 3.x. A CI job now builds `-p egglog --no-default-features` to catch regressions.
- Convert many reachable `panic!`/`unwrap`/`expect`/`todo!` sites into recoverable errors, so malformed or edge-case programs report an error instead of aborting the process. Examples now returning `Error`/`TypeError`/`ParseError`/`ProveExistsError`: malformed sort-constructor declarations like `(sort S (Vec))` or `(sort S (UnstableFn))`; negative `extract` variant counts; duplicate rule names; `unstable-fn` referencing an unknown, non-literal, or mis-typed target; `(fail ...)` wrapping `include` or an empty expansion; subsuming a non-call rewrite; running `prove`/`prove-exists` without proofs enabled; and missing/unreadable files for `input`, `print-function`, `print-overall-statistics`, and the CLI. Several primitives became partial (returning no result instead of panicking) on out-of-range input: `vec-set`/`vec-remove` indices, `multiset-pick` on an empty multiset, count overflow in `multiset` operations, and the numeric primitives `bigint <<`/`>>`, `bigrat`, and `log2`. A few scheduler edge cases (unknown ruleset, rules with no free variables) no longer panic; variable-free rules now correctly apply their actions when scheduled. Primitive resolution now returns `TypeError::AmbiguousPrimitive`/`TypeError::UnresolvedPrimitive` instead of panicking when duplicate same-signature registrations are indistinguishable or nothing resolves; both direct calls and `unstable-fn` primitive targets report the same variants. `step_rules_with_scheduler` now restores its `rulesets`/`schedulers` on every fallible path, so an error during scheduled rule compilation no longer leaves the `EGraph` in a corrupted state.
- **Breaking:** `EGraph::print_function` now takes its output sink as `Option<(File, PathBuf)>` plus a `Span`, so write failures return `Error::IoError` instead of panicking.
- Speed up query evaluation by building on-the-fly per-subset column indexes as sorted arrays (`SortedColumnIndex`) instead of hash maps. These indexes are typically iterated once and probed a bounded number of times over high-cardinality columns, so skipping hash-table construction is a large win (e.g. ~33% faster on the `gemma` benchmark).
- Share trie roots (and their cached sub-indexes and child nodes) across query plans within a single `run_rule_set` instead of rebuilding a fresh trie per plan. Plans that scan the same table under the same header (fast) constraints reuse one root, so on-the-fly per-subset index builds happen once rather than per plan; only roots that more than one plan uses are shared, so workloads that would not benefit keep the per-plan behavior. Large speedups on transformer workloads (e.g. ~15% faster on `whisper`, ~12% on `gemma`, ~8% on `qwen3_moe`).
- Add `make nightly` and `scripts/nightly_bench.py`, a hyperfine-based benchmark harness that measures every `tests/**/*.egg` program at 1/2/4/8 threads and (where supported) in proof-testing mode, caps each run at a 2-minute timeout, skips sub-50ms programs, and emits an HTML dashboard (one row per benchmark, one column per configuration) for nightly.cs.washington.edu. The dashboard uses [eval-live](https://github.com/oflatt/eval-live) for interactive filtering and sorting.
- Rework the term/proof encoding's union-find and congruence maintenance,
  substantially reducing proof-mode time and memory.
- In the term/proof encoding, run a custom function's `:merge` in its
  functional-dependency view's own `:merge` (like constructor congruence) instead
  of a separate rule plus a `current` helper table. This computes the merge once
  rather than twice, so encoded runs no longer mint over-merged extra term rows,
  and the merged value is justified by a proper merge-function proof.
- **Tuple-output functions.** A function may declare more than one output sort, e.g.
  `(function interval (Math) (i64 i64) :merge (values (max old0 new0) (min old1 new1)))`. Such a
  function stores its outputs as separate value columns; the functional dependency is
  `keys -> (value0, value1, ...)`. Outputs are destructured in queries with
  `(= (values lo hi) (interval x))`, written with `(set (interval x) (values 0 100))`, and merged
  with a `(values ...)` clause whose `i`-th element merges column `i` using the bound variables
  `old0`, `new0`, `old1`, `new1`, .... Tuple outputs are only allowed for plain functions (not
  constructors, relations, or view tables) and are not supported by the term/proof encoding.
- **`:merge` action blocks.** A `:merge` may be a value-producing action block
  `:merge (<action>* <result-expr>)`: the actions run first (with `old`/`new` bound), then the
  trailing expression is the merged value. Actions may be `let` (bind an intermediate value used by
  later actions or the result), `set` (write another function), or `union` (unify two eclasses). A
  bare `:merge <expr>` (no actions) is unchanged.
- Built-in keywords (most command, action, and schedule heads such as `function`, `set`, `union`,
  `rule`, `run`, ..., plus the tuple constructor `values`) are now reserved and may no longer be
  used as user identifiers (function/sort/constructor/relation/variant names or variables). Names
  starting with `:` may not be used as identifiers (definition names), since that prefix marks
  option keywords (`:merge`, `:cost`, ...); it is still accepted in expression position so command
  macros can consume their own option markers (e.g. `:until`). The common-word commands `input` and
  `output` are only partially reserved: they remain usable as variables, but not as definition names
  or as the head of a call expression.
- Add typed `EGraph` extension state that clones with `EGraph` and is restored by `push`/`pop`.
- Fix custom scheduler queries so subsumed rows are not offered as fresh matches.
- Replace the global Rayon thread pool with an `egglog-concurrency` scoped `ThreadPool`; configure parallelism per `EGraph` via `with_num_threads` / `set_num_threads`.
- Report full source file paths in egglog span and error messages.
- Fix seminaive matching after nested containers rebuild in place by propagating dirty container ids through parent containers.
- Fix multi-column secondary index rebuilds so each value's rows come back sorted by row id, and make all rebuild paths (serial, parallel, and bulk) record a row once even when its value repeats across covered columns (#914).
- Render nullary AST calls without a trailing space, e.g. (foo) instead of (foo ).
- Escape `"` and `\` when displaying string literals so printed/serialized programs round-trip through the parser.
- Add a BigRat to-i64 primitive for integral rationals.
- Add f64 exp, log, and sqrt primitives.
- Add `RunReport::can_stop` so scheduler progress can be reported separately from database updates.
- Add `EGraph::typecheck_expr_with_bindings_and_output`, `Core::eval_resolved_expr`, and `Core::apply_primitive` for body-defined primitive support, including normal command-path global rewrites for expressions typechecked through the helper.
- Allow `unstable-fn` function containers to target primitive overloads.
- Desugar `relation`s to `constructor`s to simplify the language and implementation. Relations no longer return unit `()` values.
- Refactored API to use [`TermId`] more consistently instead of `Term` where possible, simplifying egglog code.
- **Typed primitive surface for seminaive safety (#772).** Custom primitives now pick one of `PurePrim` / `ReadPrim` / `WritePrim` / `FullPrim` based on what the body needs, and register via the matching `add_*_primitive`. Rust enforces capability bounds via the state wrapper passed to the body; the egglog typechecker enforces context bounds. See the `egglog::exec_state` module docs and the `*Prim` trait docs for the full picture. Migration: `rust_rule` callbacks now take `&mut WriteState` (replacing `RustRuleContext`); a new `rust_rule_full` gives action callbacks read access. Higher-order primitives over `unstable-fn` values dispatch via `state.apply_function(&fc, args)`.
- Expose `Read::table_size(name)` and `Read::table_sizes()` so read-capable primitives can inspect row counts without raw execution-state access, while avoiding an all-table scan when only one table is needed.
- **`:naive` and `:unsafe-seminaive` rule options** (mutually exclusive). Both compile a rule under the permissive `Read`/`Full` contexts so its RHS can read the database (read-primitives and function-table lookups). `:naive` matches the whole database every iteration; `:unsafe-seminaive` keeps seminaive (delta) matching, which is faster but **unsafe** — an RHS read observes the database mid-iteration, so results can depend on evaluation order. `:unsafe-seminaive` is rejected by the term/proof encoding.
- **Name-indexed e-graph access from primitives and `rust_rule` callbacks (#745, #751).** New `Read` / `Write` capability traits on the state wrappers let primitive bodies and rule callbacks read/write tables by name (`fs.lookup`, `fs.set`, `fs.add`, `fs.union`, `fs.function_entries`, `fs.constructor_enodes`, etc.) instead of through raw `FunctionId` + `&[Value]`; `EGraph::update(|fs| ...)` gives the same surface outside a rule, and `EGraph::function_entries` / `EGraph::constructor_enodes` expose the table scans directly at the top level. Misuse (wrong subtype, wrong arity, unknown table) surfaces as `Error::ApiError`.
- **Container support in the term/proof encoding.** Programs using container sorts (`Vec`, `Set`, `Map`, `MultiSet`, `Pair`) now work under the term/proof encoding (previously rejected), including containers read (`vec-get`, `map-get`, …) or constructed (`vec-of`, `set-of`, …) in a rule body (`set-get` excepted: it indexes an internal runtime order that proofs cannot reproduce). A container built in the body is a *side condition* with no carryable proof: it is marked with an `Eval` proof step and re-evaluated against the typed rule when checked, so it can be read or matched in the query but not carried into an action (that is rejected). Two user-visible extraction changes: container terms extract in a deterministic, reproducible order rather than value-id order, and maps extract in a flat `(map-of k0 v0 …)` form (new `map-of` constructor) instead of nested `map-insert`s.

## [2.0.0] - 2026-02-11

Bigger changes

- Index catalog optimized for small set of indices (#719)
- Warn when globals lack the $ prefix; require globals to use the `$` prefix; missing prefixes now log a warning by default and can be upgraded to errors with `--strict-mode` or `EGraph::set_strict_mode`. (#722)
- Rename global vars in tests (#792, #800)
- Make interactive mode a delimiter (#729)
- Enable type-aware macros for fresh! sugar (#741)
- Proof preparation and term encoding (#742, #743, #765, #789)
- Export let bindings in the serialized format so they are visualized; Renames `ignore_viz` to `let_binding` (#701)
- Add snapshot tests (#778)

Bug fixes

- Fix Incorrect Unstable Function Behavior (#739)
- Run all tests in the workspace in CI (#776)

Performance improvements

- Low-level optimization for rebuilding (#754)
- Improve merge performance by being precise (#766)
- Avoid excessive cross-crate monomorphization (#773)
- Remove duplicate variables using functional dependency (#777)
- Memcpy for parallel writes and fix compilation failures (#779)

Misc. improvements

- Pin cargo codspeed version to fix CI (#734)
- Expose type constraints related APIs (#747)
- Remove lazy_static (#714)
- Simplify extract option handling (#759)
- Add longer extraction benchmark (#760)
- Specify that extractor does not support DAG costs (#763)
- Helpers for getting table sizes in primitives (#752)
- Refactor query planning (#780)
- Disable tracing tests (#787)
- Add initial early stopping support and use it for panic functions (#788)
- Update links in README for egglog resources (#798)


## [1.0.0] - 2025-10-18

This is the first release of egglog that is based on our new database-first, highly parallel backend.

**Abandoned features**

- `extract` is now a command instead of an action, which means calling `extract` within a rule is not allowed.
  Instead, the user is encouraged to use `print-function`.

Features

- Cost trait (#605)
- A new set of Rust APIs in `egglog::prelude` (#586)
- User-defined commands (#597)
- Scheduler interface for custom scheduling (#587)

Misc. Improvements

- Improves usability of `print-function` (#640)
- Desugar `rewrite`s to use `set`s when possible (#626)
- Grounded-ness check for ungrounded variables (#635)
- Don't panic when extracting nonexistent term (#629) 
- Documentation improvements (#634)
- Add parallelism flag and remove nondeterminism flag (#640, #642)
- Emit prompt and debug info when running from REPL (#672)
- Add support for the :unextractable flag for datatype variants (#712)
- Move egglog ast into its own crates (#670)

## [0.5.0] - 2025-6-9

This is the last major release before we switch to a database-first, highly parallel new backend.

Improvements

- Make `EGraph` thread-safe (#517)
- Support for egglog-python (#522)
- Throws type errors when unioning non-EqSort values (#561)
- Improvements to tests (#529)
- Improvements to error messages (#555)
- Makes union-find struct externally accessible (for container implementation) (#560)
- Disallow shadowing and interpret underscores as wildcards (#565)
- Faster `(push)` implementation

Bug fixes

- Fix value generations when `subsume`-ing a tuple in a relation (#569)
- Fixes to the new parser (#559)
- Rebuild after running commands instead of before (#573)

Benchmarks, serialization, and web demo

- Improvements to serialization (#520)
- Added eggcc benchmarks (#527)
- Fixes web demo escaping (#564, #566)
- Moves webdemo into a separate repository (#591)
- Fixes to Codspeed (#572)

## [0.4.0] - 2025-1-20

Semantic change (BREAKING)

- Split `function` into `constructor` and `functions` with merge functions. (#461)
- Remove `:default` keyword. (#461)
- Disallow lookup functions in the right hand side. (#461)
- Remove `:on_merge`, `:cost`, and `:unextractable` from functions, require `:no-merge` (#485)

Language features

- Add multi-sets (#446, #454, #471)
- Recursive datatypes with `datatype*` (#432)
- Add `BigInt` and `BigRat` and move `Rational` to `egglog-experimental` (#457, #475, #499)

Command-line interface and web demo

- Display build info when in binary mode (#427)
- Expose egglog CLI (#507, #510)
- Add a new interactive visualizer (#426)
- Disable build script for library builds (#467)

Rust interface improvements

- Make the type constraint system user-extensible (#509)
- New extensible parser (#435, #450, #484, #489, #497, #498, #506)
- Remove `Value::tag` when in release mode (#448)

Extraction

- Remove unused 'serde-1' attribute (#465)
- Extract egraph-serialize features  (#466)
- Expose extraction module publicly (#503)
- Use `set-of` instead of `set-insert` for extraction result of sets. (#514)

Bug fixes

- Fix the behavior of i64 primitives on overflow (#502)
- Fix memory blowup issue in `TermDag::to_string`
- Fix the issue that rule names are ignored (#500)

Cleanups and improvements

- Allow disabling messages for performance (#492)
- Determinize egglog (#438, #439)
- Refactor sort extraction API (#495)
- Add automated benchmarking to continuous integration (#443)
- Improvements to performance of testing (#458)
- Other small cleanups and improvements (#428, #429, #433, #434, #436, #437, #440, #442, #444, #445, #449, #453, #456, #469, #474, #477, #490, #491, #494, #501, #504, #508, #511)

## [0.3.0] - 2024-10-02

Cleanups

- Remove `declare` and `calc` keywords (#418, #419)
- Fix determinism bug from new combined ruleset code (#406)
- Fix performance bug in typechecking containers (#395)
- Minor improvements to the web demo (#413, #414, #415)
- Add power operators to i64 and f64 (#412)

Error reporting

- Report the source locations for errors (#389, #398, #405)

Serialization

- Include subsumption information in serialization (#424)
- Move splitting primitive nodes into the serialize library (#407)
- Support omitted nodes (#394)
- Support Class ID <-> Value conversion (#396)

REPL

- Evaluate multiple lines at once (#402)
- Show build information in the REPL (#427)

Higher-order functions (UNSTABLE)

- Infer types of function values based on names (#400)

Import relation from files

- Accept f64 function arguments #384

## [0.2.0] - 2024-05-24

Usability

- Improve statistics for runs (#284)
- Improve user-defined primitive support (#280, #288)
- Improve serialization (#293)
- Add more container primitives (#306)

Web demo

- Add slidemode in the web demo (#302)
- Fix box shadowing problem (#372)

Refactor

- Big refactoring to the intermediate representation (#320)
- Make global variables a syntactic sugar (#338)
- Drop experimental implementation for proofs and terms (#320, #342)

New features

- Support Subsumptions (#301)
- Add basic support for first-class, higher-order functions (UNSTABLE) (#348)
- Support combined rulesets (UNSTABLE) (#362)

Others

- Numerous bug fixes

## [0.1.0] - 2023-10-31

This is egglog's first release! Egglog is ready for use, but is still fairly experimental. Expect some significant changes in the future.

- Egglog is better than [egg](https://github.com/egraphs-good/egg) in many ways, including performance and new features.
- Egglog now includes cargo documentation for the language interface.

As of yet, the rust interface is not documented or well supported. We recommend using the language interface. Egglog also lacks proofs, a feature that egg has.


[Unreleased]: https://github.com/egraphs-good/egglog/compare/v2.0.0...HEAD
[0.1.0]: https://github.com/egraphs-good/egglog/tree/v0.1.0
[0.2.0]: https://github.com/egraphs-good/egglog/tree/v0.2.0
[0.3.0]: https://github.com/egraphs-good/egglog/tree/v0.3.0
[0.4.0]: https://github.com/egraphs-good/egglog/tree/v0.4.0
[0.5.0]: https://github.com/egraphs-good/egglog/tree/v0.5.0
[1.0.0]: https://github.com/egraphs-good/egglog/tree/v1.0.0
[2.0.0]: https://github.com/egraphs-good/egglog/tree/v2.0.0


See release-instructions.md for more information on how to do a release.
