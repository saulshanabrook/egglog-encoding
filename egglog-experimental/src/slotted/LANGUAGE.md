# Slotted language reference

The slotted language represents terms with free variables and binders.
Equality respects bound-variable alpha-equivalence. Free-variable names are
significant unless a query explicitly compares terms modulo renaming.

## Slotted features

With `--slotted`, the following syntax is added to vanilla egglog:

| Feature | Syntax | Meaning |
| --- | --- | --- |
| [Slots](#slots-and-terms) | `$a`, `$a0` | Variable terms in any equality sort; names in rewrites are rule-local |
| [Binders](#binder-columns) | `:binder i ...` | Constructor columns that bind slots in the following term child |
| [Equality modulo renaming](#equality) | `(renaming-= a b)`, `(renaming-!= a b)` | Equality or inequality allowing renaming of free variables |
| [Free names](#free-names) | `(free $x a ...)` | `$x` is free in at least one listed term |
| [Free names](#free-names) | `(not-free $x a ...)` | `$x` is free in none of the listed terms |
| [Exact free names](#free-names) | `(free-names-are a $x ...)` | The term's live free names are exactly the listed set; no names means closed |
| [Nested-matcher compatibility](#nested-matcher-compatibility) | `--slotted-no-aliasing` | Restrict matching to the reference nested matcher's aliasing policy |

Existing egglog forms have these slotted semantics:

| Form | Behavior in slotted mode |
| --- | --- |
| [Sorts and constructors](#sorts-and-constructors) | Every equality sort accepts slots; a constructor's term children must use its result sort |
| [`let`](#let) | Globals in rewrite patterns expand to their defining source terms |
| [`union`](#union), [`=` and `!=`](#equality) | Equality respects bound-variable alpha-equivalence and known symmetries while preserving free-variable identities |
| [`rewrite`](#rewrite) | Pattern slots are rule-local; distinct names match distinct slots, and RHS-only slots are implicitly fresh |
| [`run`](#run) | Slotted maintenance surrounds each round of user rewrites |
| [`extract`](#extract) | Returns an encoded tree from the class leader, including renamings and binder markers |

Pattern variables, `:name`, and `:when` use egglog's existing syntax. The
[multipattern](#multipatterns) section describes how constructor patterns in
`rewrite` and `:when` match slotted terms together.

Slotted mode supports a subset of vanilla egglog. General `rule` and `birewrite`
commands, named rulesets, `run-schedule`, and `run-report` are unsupported.
Constructor payloads are limited to `i64` and `String`; cross-sort term edges,
containers, and payload computations are unsupported. The sections below give
the restrictions for each declaration, command, and predicate.

The rest of this guide describes these features in more detail, including
their syntax, constraints, and examples.

## Invocation

```text
egglog-experimental --slotted [OPTIONS] [FILE ...]
```

| Option | Behavior |
| --- | --- |
| `--slotted` | Evaluate slotted source |
| `--mode desugar` | Print the compiled egglog program |
| `--slotted-no-aliasing` | Restrict rewrite matching to the reference nested matcher's aliasing policy; requires `--slotted` |

With no files, the executable reads commands from stdin. Successive inputs
share declarations, globals, rewrites, and graph state. Include paths are
relative to the invocation directory. A failed complete REPL input restores
both compiler and graph state, including changes from earlier commands in that
input. `--slotted` cannot be combined with term or proof encoding.

## Sorts and constructors

```text
(sort Expr)
(constructor Lam (Expr Expr) Expr :binder 0)
(constructor Let (Expr Expr Expr) Expr :binder 1)
(constructor App (Expr Expr) Expr)
(constructor Num (i64) Expr)
```

The equivalent datatype declaration is:

```text
(datatype Expr
  (Lam Expr Expr :binder 0)
  (Let Expr Expr Expr :binder 1)
  (App Expr Expr)
  (Num i64))
```

Every equality sort is a **carrier** for slotted terms and accepts slot
literals. Several carriers may be declared, including through `datatype*`.
A constructor's term children must have the same carrier as its result.
All patterns in a rewrite must also use one carrier, as must the terms
in a union or comparison. Cross-carrier operations are rejected.

Constructor columns are either term columns or payload columns. Payloads
support `i64` and `String` and carry no slots. Container-valued columns and
constructor options `:cost`, `:unextractable`, and
`:internal-term-constructor` are unsupported.

### Binder columns

`:binder` lists zero-based positions among the term columns; payload columns
do not count. Binder positions must be distinct, contiguous, and immediately
precede the term child they bind. Multiple binder columns act as nested
binders around that child. Other children remain outside their scope.

A binder argument must be a slot literal of the constructor's carrier.
Compound terms, globals, and pattern variables are rejected in binder
positions. In `(Let initializer $x body)`, `$x` binds occurrences in `body`
and has no scope over `initializer`.

## Slots and terms

| Form | Meaning |
| --- | --- |
| `$a`, `$a0`, `$outer_var` | A variable term, or a binding occurrence in a binder column |
| `(Ctor arg ...)` | A constructor application; nullary constructors also require parentheses |
| `name` | A previously declared global, or a pattern variable in a rewrite |

Identifiers retain their spelling: `x` and `?x` are different names.

Slot names contain letters, digits, or underscores. Every carrier accepts
slots without a variable declaration, even if it has no user constructors.
The carrier is inferred from context; a bare slot is ambiguous when several
carriers are declared and no constructor determines its sort.

Free slot names have the following meanings:

| Context | Meaning of `$a` |
| --- | --- |
| Ground terms, including `let`, `union`, and `check` | The concrete slot named `a`, with the same identity across commands and inputs |
| Rewrite pattern or `:when` guard | A rule-local slot matched against the graph |
| Rewrite RHS, when `$a` occurs in the pattern | The slot selected by that match |
| Rewrite RHS, when `$a` is absent from the pattern | A fresh slot, distinct from the slots in that match |

`check` introduces no pattern-slot scope. Its free slots refer to concrete
names, just as they do in `let`. In a rewrite, spelling a slot `$a` does not
refer to the concrete slot named `a`. A pattern slot can match a concrete
slot regardless of its name.

Binders introduce a scope for their bound occurrences in every context.
Bound names may change under alpha-equivalence; free names remain significant.

```slotted
(datatype Expr (Lam Expr Expr :binder 0))
(let id (Lam $a $a))
(let constant (Lam $a $a0))
(run 0)
(check (= id (Lam $renamed $renamed)))
(check (!= id constant))
(check (free-names-are constant $a0))
```

## Commands

### `let`

```text
(let name term)
```

Constructs `term` and binds a global to it. Global names cannot start with `$`
or be rebound. A bare slot cannot be stored as a global, so `(let v $x)` is
rejected. Globals in rewrite patterns expand to their defining source terms;
slots in those patterns have rule-local scope.

### `union`

```text
(union a b)
```

Asserts equality while preserving the free-variable identities written in
`a` and `b`. A union can introduce symmetries or remove dependence on a slot.
For example, unioning `(F $a $b)` with `(F $b $a)` introduces a swap symmetry;
unioning it with `(F $b $c)` makes both slots redundant.

### `rewrite`

```text
(rewrite lhs rhs :name "name" :when (fact ...))
```

Asserts `lhs = rhs` for each match. Options are optional. `:name` assigns the
rule name. `:when` takes one list of facts; repeated `:when` clauses or facts
without the surrounding list are rejected.

The left side is a constructor pattern or a variable bound by the multipattern.
The right side is a matched variable or a constructed term. Literal payloads
and payload pattern variables are supported; payload computations and
primitive calls are unsupported. Only the default ruleset is supported.
`:ruleset`, `rule`, and `birewrite` are rejected. Two `rewrite` commands express
a bidirectional equation.

#### Multipatterns

A multipattern combines the rewrite's left-hand pattern with additional
patterns introduced by `:when`. A `:when` fact can be a
[query predicate](#query-predicates), an equality
`(= v (Ctor ...))` that binds a constructor pattern to `v`, or a constructor
pattern `(Ctor ...)` whose presence is required. Patterns may nest. Variables
bound by the multipattern may be used on the right-hand side.

Shared pattern variables join the patterns' matches and require equal term
invocations, including their free-variable identities. In this example, `m`
identifies the stored memory and `p` requires the same address:

```slotted
(datatype Expr (Num i64) (Mem0) (Store Expr Expr Expr) (LoadFrom Expr Expr))
(rewrite (LoadFrom m p) v
         :when ((= m (Store m0 p v))) :name "load-after-store")
(let m1 (Store (Mem0) (Num 7) (Num 42)))
(let got (LoadFrom m1 (Num 7)))
(let other (LoadFrom m1 (Num 8)))
(run 4)
(check (= got (Num 42)))
(fail (check (= other (Num 42))))
```

An unbound left-hand variable is rejected. The multipattern can bind it:

```slotted
(datatype Expr (F Expr Expr) (G Expr) (N))
(let start (F (N) (N)))
(rewrite child (G child) :when ((= parent (F child other))))
(run 1)
(check (= (N) (G (N))))
```

#### Fresh slots

A slot appearing on the right-hand side but absent from the multipattern is
implicitly fresh with respect to the match, including free slots inside matched
terms.

Here `$binder` names the fresh slot in the rewrite, and `$free` is a concrete
slot in the input. The rewrite wraps that input in a lambda without capturing
its free slot:

```slotted
(datatype Expr (Wrap Expr) (Lam Expr Expr :binder 0))
(rewrite (Wrap e) (Lam $binder e))
(let result (Wrap $free))
(run 1)
(check (= result (Lam $bound $free)))
(check (free-names-are result $free))
(fail (check (= result (Lam $bound $bound))))
```

The checks use the same concrete `$free` as the input. `$bound` is bound by
`Lam`; its spelling need not match the rewrite's `$binder`. The last check
rejects the identity lambda, whose body would refer to the binder instead of
the input's free slot.

#### Slot constraints and capture

Different explicit slot names in a rewrite must match distinct slots:
`(F $x $y)` does not match `(F $a $a)`. A pattern slot may coincide with a free
slot inside a matched term. Repeating a slot name in independent binder
columns does not require the binders' bodies to be equal; sharing a body
pattern variable imposes that relationship.

Capture avoidance is a rule condition. When a rewrite moves an independently
matched term under a binder, a `not-free` guard can exclude captures:

```text
(rewrite (Pair (Lam $y body) e) (Lam $y (Pair body e))
         :when ((not-free $y e)))
```

Without the guard, occurrences of `$y` free in `e` can become bound.

**Scope limitation:** reusing one pattern slot name for a free occurrence and
a binder can cause a missed match. For example, `(Let $x $x $x)` uses `$x` in
both roles. `(Let $free $bound $bound)` distinguishes them. See
[issue #81](https://github.com/saulshanabrook/egglog-encoding/issues/81).

#### Nested-matcher compatibility

`--slotted-no-aliasing` restricts aliasing between slots not explicitly named
in the pattern, preserving sharing already present in child edges. It requires
one nested left-hand pattern and rejects side conditions that introduce
additional constructor patterns. Predicates over already matched variables
remain available. This option does not change ground checks.

### `run`

```text
(run N)
```

Performs `N` rounds of user rewrites. Each round matches against a snapshot
before applying actions, with slotted maintenance saturated around the round.
`N` must be a nonnegative integer. `(run 0)` performs maintenance without
applying user rewrites. `run-schedule` and `run-report` are unsupported.

### `check` and `fail`

```text
(check predicate)
(fail (check predicate))
```

`check` queries the current graph without adding terms or applying user
rewrites. It fails if the predicate does not hold. Each slotted assertion
requires its own `check`. `fail` succeeds when its enclosed check fails.
Terms in a check are ground: globals must already be defined, and free slot
names denote concrete slots. A check cannot introduce pattern variables or
rule-local slots.

### `push` and `pop`

```text
(push)
(pop)
```

`push` saves the declarations, globals, rewrites, and graph state. `pop` restores
the most recent saved state. Both commands take no arguments. A `pop` without
a matching `push` is an error.

### `extract`

```text
(extract term)
```

Returns an encoded tree from the term's class leader. The output contains
renamings and binder-marker children and uses the leader's slot frame, which
may differ from the requested term's frame. The cost is egglog's encoded-tree
cost. Conversion back to slotted source syntax is unsupported.

## Query predicates

These predicates are available in `check` and rewrite `:when` clauses. Checks
accept ground terms and globals. Comparisons in guards take bound pattern
variables; `=` can also add a constructor pattern to the multipattern. Free-name
predicates accept matched variables or constructor patterns. Slot arguments in
guards refer to rule-local pattern slots.

### Equality

`=` respects bound-variable alpha-equivalence and known class symmetries while
preserving free-variable identities. `renaming-=` compares the underlying
slotted classes and permits renaming free variables. Within one carrier, all
bare slots are equal modulo renaming.

```slotted
(datatype Expr (Lam Expr Expr :binder 0))
(let id (Lam $bound $bound))
(let p (Lam $bound $c))
(let q (Lam $bound $d))
(run 0)
(check (= id (Lam $other $other)))
(check (renaming-= p q))
(check (!= p q))
(check (renaming-!= p id))
(check (renaming-= $c $d))
(check (!= $c $d))
```

The same distinctions apply to comparisons between matched variables:

```slotted
(datatype Expr (Pair Expr Expr) (Related Expr Expr))
(let pair (Pair $a $b))
(rewrite (Pair a b) (Related a b) :when ((renaming-= a b)))
(run 1)
(check (= pair (Related $a $b)))
```

Here `a` and `b` are equal modulo renaming. A guard `(= a b)` or the repeated
pattern variable in `(Pair a a)` would require the same free-variable identity.

Known symmetries can make terms equal despite different written slot orders:

```slotted
(datatype Expr (F Expr Expr))
(rewrite (F x y) (F y x) :name "comm")
(let a (F $a $b))
(let b (F $b $a))
(run 1)
(check (= a b))
```

Disequality is non-monotonic: terms that differ at query time may be unioned
later. Consequences of an earlier rewrite match are not withdrawn.

### Free names

Free-name predicates inspect the term's live dependencies, excluding bound
slots and slots made redundant by equations. `free` and `not-free` require at
least one term. `free-names-are` takes one term and zero or more slot names.

```slotted
(datatype Expr (Lam Expr Expr :binder 0) (Mult Expr Expr) (Null))
(let k (Lam $bound $c))
(let id (Lam $bound $bound))
(let m (Mult $a (Null)))
(run 0)
(check (free-names-are k $c))
(check (free-names-are id))
(check (free $a m))
(check (not-free $a k id))
```

## Rust API

[`Compiler`] translates slotted source into an egglog program.
[`new_egraph()`] constructs a graph that can evaluate that program.

```rust
use egglog_experimental::slotted::{Compiler, new_egraph};

let mut compiler = Compiler::default();
let program = compiler.compile(None, r#"
    (datatype Expr (Lam Expr Expr :binder 0))
    (let id (Lam $a $a))
    (run 0)
    (check (= id (Lam $b $b)))
"#)?;
let mut egraph = new_egraph();
egraph.parse_and_run_program(None, &program)?;
# Ok::<(), Box<dyn std::error::Error>>(())
```

The compiler and graph form a stateful pair for successive inputs. A
compilation error leaves the compiler unchanged. If evaluation fails,
embedding applications are responsible for restoring both states.
[`Options::no_aliasing`] selects nested-matcher compatibility.

The [encoding description](ENCODING.md) covers the representation and its
invariants.
