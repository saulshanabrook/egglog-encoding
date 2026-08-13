import EgglogSemantics.Proofs.Step

/-!
# The proof encoding, as a program transformation

M11. `encode : Program → Program` rewrites a source program so that built-in
congruence disappears and every equality is an entry some rule wrote. Designed in
`egglog/src/proofs/proof_encoding.md` and implemented in `egglog/src/proofs/`.

**Parked.** The encoder below is all that survives: the theorems it was written for are
deleted, and `ENCODING.md` records what they said and the two defects that sank them.

The fragment is `PLAN.md`'s: **constructors only, no containers, no delete/subsume,
no schedules**. `Program.EncodeDomain` states it.

## What the encoding does

Three tables per source constructor `f`, plus one union-find for the (single) sort:

| target table | shape | role |
| --- | --- | --- |
| `@UF` | `(t) ↦ parent` | `t`'s parent, identity on miss |
| `@fView` | `(children) ↦ eclass` | the functional dependency; its `:merge` *is* congruence |
| `@fTerm` | `(children, id) ↦ ()` | every application ever built; write-only |

`@UF` and `@fView` share one `:merge` body — keep the smaller side and `set` the
larger's `@UF` edge to it — so a view collision on congruent children unions the two
e-classes and no congruence rule is needed. Both are `.merge` functions, so the encoded
program has **no** constructor table at all: it asserts no equation but the reflexive one
`addTerm` records, so `Cong` on the target is the identity relation on the terms it holds
and congruence there is entirely simulated.

## Two deviations forced by the modelled language

**Proofs are off, but no longer because the language cannot say them.** egglog's `@UF`
and `@fView` carry a parent/e-class *and* a proof. That column used to be inexpressible:
`Action.set` took a single output expression and so could write only one column.
`Action.set` now takes a `List Expr`, `evalAction`'s `set` case records the whole entry
as the term `.app f (args ++ out)`, and `Pattern.values` — egglog's entry atom, and now
the only read the language has — binds every value column. So what remains between this
file and a proofs-on encoding is *encoder* work: emitting a `@Proof` sort, the
`@Rule_<k>` and `@Congr` node families, and a second column on every `set` and every view
read. `encode` here still emits one-column entries, so anything said about the proof
column is vacuous for that reason — a shape the encoder does not yet write, rather than
one the language cannot express. `Lit` still wants `.unit` and `.str`, which is what the
proof column's `Unit` and `@Rule_<k>`'s rule name need.

**No disequality.** `Pattern` has no `!=`, so the `(!= b c)` guards on path compression
and on the rebuild rule are dropped; they only suppressed no-op firings.

**One flat rebuild ruleset.** The maintenance rules join `rebuildRuleset` and every encoded
run is followed by `Cmd.saturate rebuildRuleset`. egglog nests three rulesets in a
`run-schedule`; one flat ruleset run to a fixpoint is exactly as strong, since a fixpoint of
a union of rulesets is a fixpoint of each. `Rebuilt` is that command's postcondition
(`saturateReach_rebuilt`).

## Fresh ids

`get-fresh!` has no counterpart in the source semantics, and it cannot be added to the
target *configuration* either: `Database` is fixed, and no `Expr` in the fragment can
depend on a counter. Freshness is instead **structural** — the id minted for `f` over
already-canonical children `cs` is the term `.app f cs`, a skolem id. This is what a
Datalog encoding of `get-fresh!` always does, and it is what the term relation's
`f(children, id)` entry records anyway.

Two consequences, both recorded in `CHECKER.md`:

* Source terms and target ids inhabit one type, so the simulation theorem can compare
  them directly instead of carrying a source-to-target correspondence relation.
* egglog mints a *new* id per construction and lets the view merge dedup them; here the
  second construction of one shape reuses the id, so the merge does not fire. The
  induced equivalence is the same; the entry counts are not.

The id supply that remains is over *variable names*, `@v0`, `@v1`, …, threaded through
`encode` at encode time — egglog's `@pv0`, `@pv1`, ….
-/

namespace Egglog
/-! ### Names -/
/-- The union-find table. The modelled language has one eq-sort, so where egglog emits
`@UF_<Sort>` per sort there is one table here. -/
def ufName : FnName := "@UF"

/-- The ruleset the maintenance rules join, and the one every emitted `Cmd.saturate` runs.

**One flat ruleset, one `saturate`.** egglog's rebuild schedule nests three
(`egglog/src/proofs/proof_encoding.rs:1928-1943`); this is exactly as strong, because a
fixpoint of the union of rulesets is a fixpoint of each, and `Cmd.saturate` runs to a
fixpoint. -/
def rebuildRuleset : RulesetName := "@rebuild"

/-- `f`'s view: the functional dependency `children ↦ eclass`. All queries read it. -/
def viewName (f : FnName) : FnName := "@" ++ f ++ "View"

/-- `f`'s term relation. egglog names it `f`; here `f` is needed as the skolem-id
constructor, so the relation is renamed. Nothing reads it — it exists because proof
extraction does, and because "nothing is ever removed from it" is what lets a proof
mention a term after it leaves the e-graph. -/
def termName (f : FnName) : FnName := "@" ++ f ++ "Term"

/-- The `n`th generated variable. -/
def freshVar (n : Nat) : Var := "@v" ++ toString n

/-- `()`. A stand-in until `Lit` gains `.unit` (`MERGE.md`, "Constraint (5)"); the term
relation's output is the only place it appears, and nothing reads it. -/
def unitE : Expr := .lit (.int 0)

/-- `(ordering-max x y)`, egglog's tie-break, resolved by `Prim.ofName`. -/
def maxE (x y : Expr) : Expr := .app "ordering-max" [x, y]

/-- `(ordering-min x y)`. -/
def minE (x y : Expr) : Expr := .app "ordering-min" [x, y]

/-! ### Declarations

The `:merge` body shared by `@UF` and every view: keep the smaller side, and `set` the
larger side's union-find edge to it. With one value column `mergeEnv` binds `old`/`new`,
which is egglog's naming for a single-column function. -/
/-- The body both `:merge`s run. -/
def mergeBody : List Action :=
  [.set ufName [maxE (.var "old") (.var "new")] [minE (.var "old") (.var "new")]]

/-- The value both `:merge`s settle on. -/
def mergeResult : List Expr := [minE (.var "old") (.var "new")]

/-- `(function @UF (S) (S) :merge …)`. A term with no entry is its own representative, so
the lookup is identity on miss — which the model expresses by there simply being no
`@UF(t, p)` term to read. -/
def ufDecl : FnDecl :=
  { arity := 1, outArity := 1, merge := some (.merge mergeBody mergeResult) }

/-- `(function @fView (S…) (S) :merge …)` for a constructor of arity `k`. Two entries
colliding on one key are congruent, and the merge resolves that by unioning them. -/
def viewDecl (k : Nat) : FnDecl :=
  { arity := k, outArity := 1, merge := some (.merge mergeBody mergeResult) }

/-- `(function @fTerm (S… S) Unit :no-merge)`. Keyed on children *and* id, so distinct
constructions never collide. -/
def termDecl (k : Nat) : FnDecl :=
  { arity := k + 1, outArity := 1, merge := some .noMerge }

/-- `(constructor f (S…) S)`: the source name, kept as the **skolem-id** constructor.

Declaration is required, so this is a command the prelude has to emit — `.app f es` is
what `encodeBuild` mints an id with, and `Expr.eval` has no rule for an undeclared name.
egglog uses the source name for the *term relation* instead; `termName` is the rename that
frees it. -/
def skolemDecl (k : Nat) : FnDecl :=
  { arity := k, outArity := 1, merge := none }

/-! ### The constructors a program mentions

Read off the syntax rather than off the signature: the source is in the constructor
fragment, so a name's *arity* is only ever visible in its uses, and the prelude needs one
table triple — and one skolem declaration — per name however the source came by it. -/
mutual

/-- The `(name, arity)` pairs an expression applies. -/
def Expr.ctors : Expr → List (FnName × Nat)
  | .lit _ => []
  | .var _ => []
  | .app f args => (f, args.length) :: Expr.ctorsList args

/-- `Expr.ctors` over an argument list. -/
def Expr.ctorsList : List Expr → List (FnName × Nat)
  | [] => []
  | e :: es => e.ctors ++ Expr.ctorsList es

end

/-- `Expr.ctors` over a pattern. -/
def Pattern.ctors : Pattern → List (FnName × Nat)
  | .expr e => e.ctors
  | .eq e₁ e₂ => e₁.ctors ++ e₂.ctors
  | .values vs _ as => Expr.ctorsList vs ++ Expr.ctorsList as

/-- `Expr.ctors` over an action. A `set`'s own function counts: it names a view. -/
def Action.ctors : Action → List (FnName × Nat)
  | .expr e => e.ctors
  | .letBind _ e => e.ctors
  | .union e₁ e₂ => e₁.ctors ++ e₂.ctors
  | .set f args out => (f, args.length) :: (Expr.ctorsList args ++ Expr.ctorsList out)

/-- `Expr.ctors` over a command. A declaration counts even if nothing applies it. -/
def Cmd.ctors : Cmd → List (FnName × Nat)
  | .action a => a.ctors
  | .rule r => (r.query.flatMap Pattern.ctors) ++ (r.actions.flatMap Action.ctors)
  | .run _ => []
  | .saturate _ => []
  | .decl f d => [(f, d.arity)]

/-- Every function the program mentions, deduplicated. One table triple is emitted per
entry. -/
def Program.ctors (P : Program) : List (FnName × Nat) := (P.flatMap Cmd.ctors).dedup

/-! ### Queries

A source pattern becomes one view read per subterm, joined on e-class variables — the
`check` expansion of `proof_encoding.md`, "Queries". The reads bind ids, so the outer
`(= e₁ e₂)` of a source equality pattern becomes id equality, which is egglog's own
`(= e3 e6)` and is why the rebuild has to have canonicalized the entries first. -/
mutual

/-- Flatten `e` into view reads. Returns the expression naming `e`'s e-class, the reads,
and the next variable number.

A view read is a `Pattern.values` atom, which is what egglog lowers `(= e (@fView c…))` to
and the only form the model admits: `Expr.eval` does not read, so a non-constructor
application is not an expression here. -/
def encodeQueryExpr : Expr → Nat → Expr × List Pattern × Nat
  | .lit l, n => (.lit l, [], n)
  | .var v, n => (.var v, [], n)
  | .app f args, n =>
      match encodeQueryArgs args n with
      | (es, ps, n₁) =>
          (.var (freshVar n₁),
           ps ++ [.values [.var (freshVar n₁)] (viewName f) es],
           n₁ + 1)

/-- `encodeQueryExpr` over an argument list. -/
def encodeQueryArgs : List Expr → Nat → List Expr × List Pattern × Nat
  | [], n => ([], [], n)
  | e :: es, n =>
      match encodeQueryExpr e n with
      | (e', ps, n₁) =>
          match encodeQueryArgs es n₁ with
          | (es', ps', n₂) => (e' :: es', ps ++ ps', n₂)

end

/-- Encode one source pattern. `.expr e` is "`e` is present", which the reads already
say; `.eq` adds the id equality. -/
def encodePattern : Pattern → Nat → List Pattern × Nat
  | .values vs f as, n => ([.values vs f as], n)
  | .expr e, n => match encodeQueryExpr e n with | (_, ps, n₁) => (ps, n₁)
  | .eq e₁ e₂, n =>
      match encodeQueryExpr e₁ n with
      | (x₁, ps₁, n₁) =>
          match encodeQueryExpr e₂ n₁ with
          | (x₂, ps₂, n₂) => (ps₁ ++ ps₂ ++ [.eq x₁ x₂], n₂)

/-- `encodePattern` over a query. -/
def encodeQuery : Query → Nat → Query × Nat
  | [], n => ([], n)
  | p :: ps, n =>
      match encodePattern p n with
      | (qs, n₁) => match encodeQuery ps n₁ with | (qs', n₂) => (qs ++ qs', n₂)

/-! ### Building a term

`proof_encoding.md`, "Building a term": mint an id, write the term-relation entry, intern
the application into its view, and read back the view's e-class. A parent is built over
its children's canonical ids, which is what keeps views canonical.

egglog interns with `set-if-empty-<View>!`, which returns the *existing* e-class when
the shape was already there and **discards** the id it just minted. There is no such
action here, so the encoding `set`s and then reads the view back. The difference is one
extra union: where egglog drops the minted id, the plain `set` collides with the
existing entry and the view's `:merge` unions the two. Both terms denote the same
application, so the equalities are the same and only the entry count differs.

**The read-back is a shape egglog rejects, and this is the reason `set-if-empty` exists.**
`(let x (@fView c…))` in a rule head is a lookup, and
`check_no_function_lookups_in_actions` refuses one: "Value lookup of non-constructor
function function in rule is disallowed". egglog gets around it by registering
`set-if-empty-<View>!` as a **primitive** (`src/proofs/proof_fresh.rs`), and
`expr_has_function_lookup` flags only `ResolvedCall::Func`. So `encode` as written emits
rule heads the real system would refuse, and `Impl/Check.lean`'s `Program.noLookup` is the
transcribed check that rejects them. The fix is the same one egglog made — a `Prim`-style
get-or-insert, which is a write and not a read — and it is M11 work, so it is recorded
here rather than done. Nothing downstream depends on the read-back stepping — the
theorems that would have are deleted (`ENCODING.md`). -/
mutual

/-- Build `e` in the target. Returns the expression naming `e`'s e-class, the actions
that create it, and the next variable number. -/
def encodeBuild : Expr → Nat → Expr × List Action × Nat
  | .lit l, n => (.lit l, [], n)
  | .var v, n => (.var v, [], n)
  | .app f args, n =>
      match encodeBuildArgs args n with
      | (es, as, n₁) =>
          (.var (freshVar n₁),
           as ++ [.set (termName f) (es ++ [.app f es]) [unitE],
                  .set (viewName f) es [.app f es],
                  .letBind (freshVar n₁) (.app (viewName f) es)],
           n₁ + 1)

/-- `encodeBuild` over an argument list. -/
def encodeBuildArgs : List Expr → Nat → List Expr × List Action × Nat
  | [], n => ([], [], n)
  | e :: es, n =>
      match encodeBuild e n with
      | (e', as, n₁) =>
          match encodeBuildArgs es n₁ with
          | (es', as', n₂) => (e' :: es', as ++ as', n₂)

end

/-! ### Heads

A `union` becomes one `@UF` edge from the larger endpoint to the smaller. egglog's
construct-into optimization — building a freshly constructed operand directly into the
other operand's e-class, dropping the union — is deliberately **not** modelled: its
stated effect is "exactly the edge the explicit union would have produced"
(`proof_encoding.md`, "Union in a rule"), so it changes which entries are written and not
which equalities hold. -/
/-- Encode one head action. -/
def encodeAction : Action → Nat → List Action × Nat
  | .expr e, n => match encodeBuild e n with | (_, as, n₁) => (as, n₁)
  | .letBind v e, n =>
      match encodeBuild e n with | (x, as, n₁) => (as ++ [.letBind v x], n₁)
  | .union e₁ e₂, n =>
      match encodeBuild e₁ n with
      | (x₁, as₁, n₁) =>
          match encodeBuild e₂ n₁ with
          | (x₂, as₂, n₂) =>
              (as₁ ++ as₂ ++ [.set ufName [maxE x₁ x₂] [minE x₁ x₂]], n₂)
  | .set f args out, n =>
      match encodeBuildArgs args n with
      | (es, as, n₁) =>
          match encodeBuildArgs out n₁ with
          | (xs, as', n₂) => (as ++ as' ++ [.set (viewName f) es xs], n₂)

/-- `encodeAction` over an action list. -/
def encodeActions : List Action → Nat → List Action × Nat
  | [], n => ([], n)
  | a :: as, n =>
      match encodeAction a n with
      | (bs, n₁) => match encodeActions as n₁ with | (bs', n₂) => (bs ++ bs', n₂)

/-- Encode a rule: view reads for the body, builds and `@UF` edges for the head. -/
def encodeRule (r : Rule) (n : Nat) : Rule × Nat :=
  match encodeQuery r.query n with
  | (q, n₁) =>
      match encodeActions r.actions n₁ with
      | (as, n₂) => ({ query := q, actions := as, ruleset := r.ruleset }, n₂)

/-! ### Maintenance

`proof_encoding.md`, "Rebuilding". Two families, both ordinary rules. -/
/-- Path compression, `a → b → c` to `a → c`. egglog guards it with `(!= b c)`; without
disequality the unguarded rule additionally re-`set`s edges it already holds, which
changes nothing. -/
def pathCompressRule : Rule :=
  { query := [.values [.var "@b"] ufName [.var "@a"],
              .values [.var "@c"] ufName [.var "@b"]],
    actions := [.set ufName [.var "@a"] [.var "@c"]],
    ruleset := rebuildRuleset }

/-- `@c0 … @c(k-1)`, a rebuild rule's column variables. -/
def rebuildVars (k : Nat) : List Expr :=
  (List.range k).map fun i => .var ("@c" ++ toString i)

/-- The rebuild rules for a constructor of arity `k`: one per child column, moving that
column to its union-find leader, and one for the e-class column.

egglog emits **one** rule per eq-sort occurring in the view, not one per column: its
body joins a `@UF` delta against the rebuild index, and its action re-canonicalizes
every column at once through `@UF_<Sort>_canon` (identity on miss) before deleting the
stale entry. Neither piece is available here — there is no index, no `delete`, and no
identity-on-miss read, since "no entry" is not a matchable fact. Neither is needed for
the equalities: entries are never removed in this model, so a half-rewritten entry is an
extra entry rather than a lost one, and `Database.Out` reads any of them. What egglog
buys with the one-firing form is entry count. -/
def rebuildRules (f : FnName) (k : Nat) : List Rule :=
  let cs := rebuildVars k
  let view : Pattern := .values [.var "@e"] (viewName f) cs
  let eclassRule : Rule :=
    { query := [view, .values [.var "@x"] ufName [.var "@e"]],
      actions := [.set (viewName f) cs [.var "@x"]],
      ruleset := rebuildRuleset }
  eclassRule :: (List.range k).map fun i =>
    { query := [view, .values [.var "@x"] ufName [.var ("@c" ++ toString i)]],
      actions := [.set (viewName f) (cs.set i (.var "@x")) [.var "@e"]],
      ruleset := rebuildRuleset }

/-- Every maintenance rule the encoding of `P` emits. `Rebuilt` is stated over it. -/
def maintenanceRules (P : Program) : List Rule :=
  pathCompressRule :: P.ctors.flatMap fun fk => rebuildRules fk.1 fk.2

/-! ### The transformation -/
/-- The declarations and maintenance rules, emitted once at the top. -/
def encodePrelude (P : Program) : Program :=
  .decl ufName ufDecl ::
    (P.ctors.flatMap fun fk =>
      [.decl fk.1 (skolemDecl fk.2), .decl (viewName fk.1) (viewDecl fk.2),
       .decl (termName fk.1) (termDecl fk.2)]) ++
    (maintenanceRules P).map .rule

/-- Encode one command. A source declaration is dropped: the prelude has already declared
its function as the skolem-id constructor and emitted its table triple, and re-emitting it
would be a redeclaration (`Cmd.DeclFresh`). -/
def encodeCmd : Cmd → Nat → Program × Nat
  | .action a, n => match encodeAction a n with | (as, n₁) => (as.map .action, n₁)
  | .rule r, n => match encodeRule r n with | (r', n₁) => ([.rule r'], n₁)
  | .run R, n => ([.run R, .saturate rebuildRuleset], n)
  | .saturate R, n => ([.saturate R, .saturate rebuildRuleset], n)
  | .decl _ _, n => ([], n)

/-- `encodeCmd` over a program. -/
def encodeCmds : Program → Nat → Program × Nat
  | [], n => ([], n)
  | c :: cs, n =>
      match encodeCmd c n with
      | (p, n₁) => match encodeCmds cs n₁ with | (p', n₂) => (p ++ p', n₂)

/-- **The encoding.** -/
def encode (P : Program) : Program := encodePrelude P ++ (encodeCmds P 0).1

/-! ### The source programs `encode` is defined for

`PLAN.md`'s fragment. `MERGE.md`, "Restrictions on `encode`'s domain", records the one
restriction that is permanent rather than a gap: egglog refuses to encode a function
with a `:merge` action block. -/
/-- No `set` action. `Action.set` is what a `:merge` function and an encoded rule head
need; the constructor fragment has neither, and under `EncodeDomain.ctorsOnly` a `set`
could only name a constructor or an undeclared function — which is exactly what
`Action.SetLegal` refuses. -/
def Action.NoSet : Action → Prop
  | .set _ _ _ => False
  | _ => True

/-- No entry atom. `Pattern.values` reads an entry of a non-constructor function, which
the constructor fragment has none of — so like `Action.NoSet` this is a fragment
restriction rather than a limitation, and it is why `encodePattern` leaves the case alone
instead of encoding it. The encoding's *own* queries are all entry atoms; this constrains
the source. -/
def Pattern.NoValues : Pattern → Prop
  | .values _ _ _ => False
  | _ => True

/-- `Action.NoSet` over a command, together with `Pattern.NoValues` over its query. -/
def Cmd.NoSet : Cmd → Prop
  | .action a => a.NoSet
  | .rule r => (∀ a ∈ r.actions, a.NoSet) ∧ ∀ p ∈ r.query, p.NoValues
  | _ => True

/-- The variables a pattern mentions. -/
def Pattern.varsOf : Pattern → List Var := Pattern.vars

/-- The variables an action mentions, binders included. -/
def Action.vars : Action → List Var
  | .expr e => e.vars
  | .letBind v e => v :: e.vars
  | .union e₁ e₂ => e₁.vars ∪ e₂.vars
  | .set _ args out => Expr.varsList args ∪ Expr.varsList out

/-- `Action.vars` over a command. -/
def Cmd.vars : Cmd → List Var
  | .action a => a.vars
  | .rule r => r.query.vars ∪ (r.actions.flatMap Action.vars)
  | .run _ => []
  | .saturate _ => []
  | .decl _ _ => []

/-- Every variable the program mentions. -/
def Program.vars (P : Program) : List Var := (P.flatMap Cmd.vars).dedup

/-- Constructors only, and no name that would collide with a generated one. -/
structure Program.EncodeDomain (P : Program) : Prop where
  /-- Every declared function is a constructor. -/
  ctorsOnly : ∀ c ∈ P, ∀ f d, c = Cmd.decl f d → d.merge = none
  /-- No `set` action anywhere. -/
  noSet : ∀ c ∈ P, c.NoSet
  /-- No source function shadows a primitive, so every application builds. -/
  noPrim : ∀ fk ∈ P.ctors, Prim.ofName fk.1 = none
  /-- No source function is in the generated namespace. -/
  noAt : ∀ fk ∈ P.ctors, ¬ "@".isPrefixOf fk.1
  /-- Nor any source variable: the generated `@v0`, `@v1`, … are numbered from one
  supply for the whole program, so they collide with nothing but a source `@` name. -/
  noAtVar : ∀ v ∈ P.vars, ¬ "@".isPrefixOf v

/-! ### Reading the target

The three notions the deleted M11 theorems were stated over. None of them is `Cong`: the
encoded program's tables are `.merge` functions and it asserts no equation but the
reflexive one `addTerm` records, so `Cong` on the target is the identity relation on the
terms it holds. Equality on the target side is *only* what `@UF` and the views record.

Source-side equality is `Spec/Congruence.lean`'s `CongOn`, not `Cong`: the rebuild re-keys
a view entry to its children's leaders, so the encoded database ends up holding entries
about applications the source never built — `@AddView [1,1] ↦ Add[1,2]` after `(Add 1 2)`
and `(union 1 2)`. Those entries are still *true*, but only in that sense. `ENCODING.md`
records why `CongOn` is nevertheless too weak to state a theorem over unmodified. -/
/-- A union-find edge that moves. The `:merge` writes `@UF (ordering-max p p) ↦
ordering-min p p` on a self-collision, so reflexive self-loops are ordinary entries and a
leader is "no edge that moves" rather than "no entry". -/
def UFEdge (d : Database) (t p : Term) : Prop := d.Out ufName [t] [p] ∧ p ≠ t

/-- `l` is `t`'s representative: reachable along edges, and itself at the end of one.

A relation rather than a function because `Database.Out` reads *any* recorded output —
the model keeps the entries a merge displaces (`MERGE.md`, "Constraint (3): monotonicity"),
so a term can have several recorded parents, every one genuinely equal to it. -/
def UFLeader (d : Database) (t l : Term) : Prop :=
  Relation.ReflTransGen (UFEdge d) t l ∧ ∀ p, ¬ UFEdge d l p

mutual

/-- The e-class the encoded database gives a source term: one view read per subterm,
joined on ids. This is what `check` compiles to (`proof_encoding.md`, "Queries"), and it
is the source-to-target correspondence the simulation theorem needs.

A literal is its own id — it has no view, since only an application does. -/
inductive ViewRepr (d : Database) : Term → Term → Prop where
  | lit {l : Lit} : Term.lit l ∈ d.terms → ViewRepr d (.lit l) (.lit l)
  | app {f : FnName} {as es : List Term} {e : Term} :
      ViewReprList d as es → d.Out (viewName f) es [e] → ViewRepr d (.app f as) e

/-- `ViewRepr` over an argument list. -/
inductive ViewReprList (d : Database) : List Term → List Term → Prop where
  | nil : ViewReprList d [] []
  | cons {a e : Term} {as es : List Term} :
      ViewRepr d a e → ViewReprList d as es → ViewReprList d (a :: as) (e :: es)

end

/-- Two source terms are in one e-class of the encoded database: their view reads land
on ids with a common union-find leader.

Existential in the reads because `ViewRepr` is, and because that is the direction both
halves of the simulation want — a match exists iff the equality holds. -/
def SameClass (d : Database) (a b : Term) : Prop :=
  ∃ ea eb l, ViewRepr d a ea ∧ ViewRepr d b eb ∧ UFLeader d ea l ∧ UFLeader d eb l

/-- The rebuild schedule has run out: no maintenance rule adds anything, and no merge
step changes anything. It is the hypothesis the completeness half of simulation needs —
until the views are re-keyed to leaders, a collision that congruence would find has not yet
happened.

`ENCODING.md`, finding 1, was that no state `encode` ran to satisfied this, because
`Cmd.run` carried no ruleset and the number of rounds needed to re-key grows with term
depth. `encode` now emits `Cmd.saturate rebuildRuleset` after every run, and
`saturateReach_rebuilt` below is the repair: this is that command's *postcondition*. -/
def Rebuilt (P : Program) (d : Database) : Prop :=
  (∀ r ∈ maintenanceRules P, ∀ d' ∈ RuleResults d r, Database.Contained d' d) ∧
    MergeSaturated d

/-- **`Rebuilt` is `RunSaturated rebuildRuleset`.** The only bookkeeping is `hR`: the
rules of `d` in the rebuild ruleset are the maintenance rules `encode` emitted. -/
theorem rebuilt_iff_runSaturated {P : Program} {d : Database}
    (hR : ∀ r, (r ∈ d.rules ∧ r.ruleset = rebuildRuleset) ↔ r ∈ maintenanceRules P) :
    RunSaturated rebuildRuleset d ↔ Rebuilt P d := by
  rw [RunSaturated, runRules_eq_self_iff]
  exact and_congr_left' ⟨fun h r hr => h r ((hR r).mpr hr).1 ((hR r).mpr hr).2,
    fun h r hr hRr => h r ((hR r).mp ⟨hr, hRr⟩)⟩

/-- **And `Cmd.saturate rebuildRuleset` delivers it**, with no extra hypothesis. This is
what the ruleset bought: `Rebuilt` went from a condition nothing reachable satisfied to the
postcondition of a command the encoding emits. -/
theorem saturateReach_rebuilt {P : Program} {db d : Database}
    (hR : ∀ r, (r ∈ d.rules ∧ r.ruleset = rebuildRuleset) ↔ r ∈ maintenanceRules P)
    (h : SaturateReach rebuildRuleset db d) : Rebuilt P d :=
  (rebuilt_iff_runSaturated hR).mp h.2

/-- Read through `CmdStep`: whatever the encoded program's rebuild command steps to is
rebuilt. `cmdStep_saturate_iff` is what makes the trailing merge phase neutral here. -/
theorem cmdStep_rebuilt {P : Program} {db d : Database}
    (hR : ∀ r, (r ∈ d.rules ∧ r.ruleset = rebuildRuleset) ↔ r ∈ maintenanceRules P)
    (h : CmdStep db (.saturate rebuildRuleset) d) : Rebuilt P d :=
  saturateReach_rebuilt hR (cmdStep_saturate_iff.mp h)

/-! ### Proof nodes

`encode` writes none of these — the proof column is what the one-value-column
restriction blocks (see the header). The vocabulary is fixed here so the M11 proof
theorems would have something to quantify over, and so the shape is reviewable now.

egglog declares each as a *relation* whose last input column is a `get-fresh! "@Proof"`
id, deliberately so that two structurally equal proofs are never merged into one. With
structural freshness there is no id to mint and a proof node simply *is* its own term;
the two coincide except that equal proofs are equal here. -/
/-- `@Fiat`: a top-level action asserted `a = b`. -/
def pFiat (a b : Term) : Term := .app "@Fiat" [a, b]

/-- `@Trans`. -/
def pTrans (p q : Term) : Term := .app "@Trans" [p, q]

/-- `@Sym`. -/
def pSym (p : Term) : Term := .app "@Sym" [p]

/-- `@Congr`: `p` proves `t = t'`, `q` proves the `i`th child's step. -/
def pCongr (p : Term) (i : Nat) (q : Term) : Term := .app "@Congr" [p, .lit (.int i), q]

/-- `@Rule_<k>`: the rule named by `nm`, fired on the premises `prems`. Which of the
head's conclusions this is — layer 2's *column* — is the last argument. -/
def pRule (nm : Term) (prems : List Term) (col : Nat) : Term :=
  .app "@Rule" (nm :: prems ++ [.lit (.int col)])

end Egglog
