# Slotted language reference

The slotted language represents terms with free variables and binders.
Equality respects bound-variable alpha-equivalence. Free-variable names are
significant unless a query explicitly compares terms modulo renaming.

## Slotted features

With `--slotted`, the following syntax is added to vanilla egglog:

| Feature | Syntax | Meaning |
| --- | --- | --- |
| [Slots](#slots-and-terms) | `$a`, `$a0` | Variable terms in any equality sort; names in queries are local to the query |
| [Binders](#binder-columns) | `:binder i ...` | Constructor columns that bind slots in the following term child |
| [Equality modulo renaming](#equality) | `(renaming-= a b)`, `(renaming-!= a b)` | Equality or inequality allowing renaming of free variables |
| [Free names](#free-names) | `(free $x a ...)` | `$x` is free in at least one listed term |
| [Free names](#free-names) | `(not-free $x a ...)` | `$x` is free in none of the listed terms |
| [Exact free names](#free-names) | `(free-names-are a $x ...)` | The term's live free names are exactly the listed set; no names means closed |
| [Substitution](#substitution) | `(subst body $x replacement)` | Capture-avoiding substitution on a rewrite's right-hand side |
| [Nested-matcher compatibility](#nested-matcher-compatibility) | `--slotted-no-aliasing` | Restrict matching to the reference nested matcher's aliasing policy |

Existing egglog forms have these slotted semantics:

| Form | Behavior in slotted mode |
| --- | --- |
| [Sorts and constructors](#sorts-and-constructors) | Every equality sort accepts slots; a constructor's term children must use its result sort |
| [`let`](#let) | Binds a term or concrete slot; references preserve its free-slot identities |
| [`union`](#union), [`=` and `!=`](#equality) | Equality respects bound-variable alpha-equivalence and known symmetries while preserving free-variable identities |
| [`rewrite`](#rewrite) | Pattern slots are rule-local; distinct names match distinct slots, and RHS-only slots are implicitly fresh |
| [`check`](#check-and-fail) | Facts form an existential query, with the same local slots and matching semantics as rewrite queries |
| [`extract`](#extract) | Returns a source term with named slots, preserving free names and avoiding capture |

Pattern variables, `:name`, and `:when` use egglog's existing syntax. The
[multipattern](#multipatterns) section describes how constructor patterns in
`rewrite` and `:when` match slotted terms together.

Slotted mode supports a subset of vanilla egglog. General `rule` and `birewrite`
commands, named rulesets, `run-schedule`, and `run-report` are unsupported.
Constructor payloads are limited to `i64` and `String`; cross-sort term edges,
containers, and payload computations are unsupported.

The rest of this reference describes these features in more detail, including
their syntax, constraints, and examples.

## Invocation

```text
egglog-experimental --slotted [OPTIONS] [FILE ...]
```

| Option | Behavior |
| --- | --- |
| `--slotted` | Evaluate slotted source |
| `--mode desugar` | Print the compiled egglog program |
| `--slotted-no-aliasing` | Restrict matching to the reference nested matcher's aliasing policy; requires `--slotted` |

With no files, the executable reads commands from stdin. Successive inputs
share declarations, globals, rewrites, and graph state. Include paths are
relative to the invocation directory. A failed complete REPL input restores
both compiler and graph state, including changes from earlier commands in that
input. `--slotted` cannot be combined with `--term-encoding`, `--proof-testing`,
or `--proof-extraction`.

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
All patterns in a query must also use one carrier, as must the terms
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
| `name` | A previously declared global, or a pattern variable in a query |

Identifiers retain their spelling: `x` and `?x` are different names.

Slot names contain letters, digits, or underscores; signed 64-bit numeric names
such as `$0` and `$-1` are also accepted. Every carrier accepts slots without a
variable declaration, even if it has no user constructors.
The carrier is inferred from context; a bare slot is ambiguous when several
carriers are declared and no constructor determines its sort.

Free slot names have the following meanings:

| Context | Meaning of `$a` |
| --- | --- |
| Ground terms in `let`, `union`, and `extract` | The concrete slot named `a`, with the same identity across commands and inputs |
| `check`, rewrite pattern, or `:when` guard | A slot local to that query, matched against the graph |
| Rewrite RHS, when `$a` occurs in the pattern | The slot selected by that match |
| Rewrite RHS, when `$a` is absent from the pattern | A fresh slot, distinct from the slots in that match |

Each `check` and rewrite has its own pattern-slot scope. Writing `$a` in a
query does not refer to a concrete slot named `a`. To query a specific slot,
bind it with `(let concrete_a $a)` and use `concrete_a` in the query. A pattern
slot can match a concrete slot regardless of its name.

Binders introduce a scope for their bound occurrences in every context.
Bound names may change under alpha-equivalence; free names remain significant.

```slotted
(datatype Expr (Lam Expr Expr :binder 0))
(let id (Lam $a $a))
(let free_a0 $a0)
(let constant (Lam $a free_a0))
(check (= id (Lam $renamed $renamed)))
(check (!= id constant))
(check (free-names-are constant free_a0))
```

## Commands

Slotted invariants are maintained automatically before queries and extraction,
between rewrite iterations, and at the end of each input. `run` controls user
rewrites.

### `let`

```text
(let name term)
```

Constructs `term` and binds a global to it. Global names cannot start with `$`
or be rebound. `(let v $x)` binds the concrete slot named `x`; a slot global
gets its carrier from the context where it is used, like a slot literal.
References to a global preserve its free-slot identities and follow its
e-class through subsequent unions and maintenance. This applies in both
checks and rewrites.

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

Asserts `lhs = rhs` for each match. `:name` and `:when` are optional. `:name`
assigns the rule name. `:when` takes one list of facts; repeated `:when` clauses
or facts without the surrounding list are rejected.

The left side is a constructor pattern, slot, global, or variable bound by the
multipattern. The right side is a matched variable, global, slot, constructed
term, or [substitution](#substitution). Literal payloads and payload pattern
variables are supported; payload computations and other primitive calls are
unsupported. Only the default ruleset is supported.
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

Here `$binder` names the fresh slot in the rewrite. The global `free_slot`
refers to a concrete slot in the input. The rewrite wraps that input in a
lambda without capturing its free slot:

```slotted
(datatype Expr (Wrap Expr) (Lam Expr Expr :binder 0))
(let free_slot $free)
(rewrite (Wrap e) (Lam $binder e))
(let result (Wrap free_slot))
(run 1)
(check (= result (Lam $bound free_slot)) (not-free $bound free_slot))
(check (free-names-are result free_slot))
(fail (check (= result (Lam $bound $bound))))
```

The checks use the global `free_slot` to refer to the input's concrete slot.
`$bound` is a pattern slot in a binder column; its spelling need not match the
rewrite's `$binder`. The `not-free` guard keeps it distinct from `free_slot`.
The last check rejects the identity lambda, whose body would refer to the
binder instead of the input's free slot.

#### Substitution

```text
(subst body $x replacement)
```

Replaces free occurrences of `$x` in `body` with `replacement`, avoiding
capture by binders. It must be the complete right-hand side of a rewrite.
`body` and `replacement` must be matched variables or globals of the rewrite's
carrier; the middle argument must be a slot literal.

Substitution uses a minimum-size tree representative from the start of the
round, with deterministic tie-breaking. It can fail if a class requiring
substitution has no finite tree representative.

```slotted
(datatype Expr (Let Expr Expr Expr :binder 1) (Num i64))
(rewrite (Let value $x body) (subst body $x value))
(let result (Let (Num 7) $bound $bound))
(run 1)
(check (= result (Num 7)))
```

#### Slot constraints and capture

Different explicit slot names in a query must match distinct slots:
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
in the pattern, preserving sharing already present in child edges. Rewrites
must use one nested left-hand pattern; additional constructor patterns in
`:when` are rejected. Predicates over already matched variables remain
available. Checks use the same aliasing restriction.

### `run`

```text
(run N)
```

Performs `N` rounds of user rewrites. `N` must be a nonnegative integer.
`run-schedule` and `run-report` are unsupported.

### `check` and `fail`

```text
(check fact ...)
(fail (check fact ...))
```

`check` succeeds when one match satisfies all its facts. It uses the same
patterns, shared variables, slot constraints, and predicates as rewrite
queries. It does not add terms or apply user rewrites. `fail` asserts that
there is no matching assignment.

```slotted
(datatype Expr (Pair Expr Expr))
(let a $a)
(let b $b)
(let pair (Pair a b))
(check (= pair (Pair $x body)) (not-free $x body))
(check (= a $local))
(check (= b $local))
(fail (check (= a $shared) (= b $shared)))
(check (!= a b))
```

The two `$local` occurrences belong to separate checks. Within the single
check using `$shared`, both facts must use the same slot, so it has no match.
Pattern variables must be bound by a constructor pattern, slot, or global
in the query; `(check (= x y))` alone does not bind `x` or `y`.

Disequality filters each candidate match. For example,
`(check (Pair x y) (!= x y))` requires a pair with unequal children.
`(fail (check (Pair x y) (= x y)))` requires that no pair have equal children.

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

Returns a minimum-size tree using the source constructors and `$name` slots.
Free names are preserved. Binders and other slots private to the chosen
representative receive fresh names such as `$0` and `$1`.

```slotted
(datatype Expr (Lam Expr Expr :binder 0) (Pair Expr Expr))
(let term (Lam $bound (Pair $bound $free)))
(extract term)
```

Output:

```text
(Lam $0 (Pair $0 $free))
```

The result can be read back as a slotted term. In the Rust output, slots use
[`egglog::Term::Var`] nodes in the [`egglog::TermDag`].

Tree size counts constructor and variable occurrences; payloads and binder
declarations contribute no additional cost. A missing finite tree is an error.
Only the single-term form is supported; a variant count is rejected.

## Query predicates

These predicates are available in `check` and rewrite `:when` clauses.
Comparisons accept matched variables, globals, and constructor patterns;
`=` can bind a variable to a pattern. Free-name predicates accept matched
variables, globals, or constructor patterns. A slot argument must be bound
by a pattern or be a global bound to a concrete slot.

### Equality

`=` respects bound-variable alpha-equivalence and known class symmetries while
preserving free-variable identities. `renaming-=` compares the underlying
slotted classes and permits renaming free variables. Within one carrier, all
bare slots are equal modulo renaming.

```slotted
(datatype Expr (Lam Expr Expr :binder 0))
(let c $c)
(let d $d)
(let id (Lam $bound $bound))
(let p (Lam $bound c))
(let q (Lam $bound d))
(check (= id (Lam $other $other)))
(check (renaming-= p q))
(check (!= p q))
(check (renaming-!= p id))
(check (renaming-= c d))
(check (!= c d))
```

The same distinctions apply to comparisons between matched variables:

```slotted
(datatype Expr (Pair Expr Expr) (Related Expr Expr))
(let pair (Pair $a $b))
(rewrite (Pair a b) (Related a b) :when ((renaming-= a b)))
(run 1)
(check (= pair (Related $left $right)))
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
(let a $a)
(let c $c)
(let k (Lam $bound $c))
(let id (Lam $bound $bound))
(let m (Mult $a (Null)))
(check (free-names-are k c))
(check (free-names-are id))
(check (free a m))
(check (not-free a k id))
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

## Getting proofs

```text
egglog-experimental --slotted --proofs source.egg
```

For supported `=` and `renaming-=` checks, this prints a checked proof using
source terms and original rewrites, including their `:when` clauses.
Other predicates use ordinary checks.
See [the proof guide](PROOFS.md) for supported forms, Rust API usage, and examples.
