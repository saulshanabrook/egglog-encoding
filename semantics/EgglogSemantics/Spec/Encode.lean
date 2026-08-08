import EgglogSemantics.Spec.Merge

/-!
# The proof encoding, as a program transformation

M11. `encode : Program → Program` rewrites a source program so that built-in
congruence disappears and every equality is a row some rule wrote. Designed in
`egglog/src/proofs/proof_encoding.md` and implemented in `egglog/src/proofs/`.

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
program has **no** `.union` function at all and `MCong` on the target degenerates to
syntactic equality: congruence there is entirely simulated.

## Two deviations forced by the modelled language

**Proofs are off, but no longer because the language cannot say them.** egglog's `@UF`
and `@fView` carry a parent/e-class *and* a proof. That column used to be inexpressible:
`Action.set` took a single output expression and so could write only one column.
`Action.set` now takes a `List Expr`, `ActionStep.set` writes `db.addRow f ts vs`, and
`Pattern.values` — egglog's tuple destructure `(= (values v…) (f a…))` — reads a column
other than the first. So what remains between this file and a proofs-on encoding is
*encoder* work: emitting a `@Proof` sort, the `@Rule_<k>` and `@Congr` node families, and
a second column on every `set` and every view read. `encode` here still emits one-column
rows, and `Proofs/Encode.lean`'s `encode_proof_rows_check` is still vacuous for that
reason — a statement about a row shape the encoder does not yet write, rather than one the
language cannot express. `Lit` still wants `.unit` and `.str`, which is what the proof
column's `Unit` and `@Rule_<k>`'s rule name need.

**No disequality and no rulesets.** `Pattern` has no `!=`, so the `(!= b c)` guards on
path compression and on the rebuild rule are dropped; they only suppressed no-op
firings. `Cmd.run` has no ruleset argument, so the maintenance rules are ordinary rules
that fire in every round rather than a `run-schedule`, and "the rebuild schedule has
saturated" becomes the predicate `Rebuilt` rather than a command.

## Fresh ids

`get-fresh!` has no counterpart in the source semantics, and it cannot be added to the
target *configuration* either: `Database` is fixed, and no `Expr` in the fragment can
depend on a counter. Freshness is instead **structural** — the id minted for `f` over
already-canonical children `cs` is the term `.app f cs`, a skolem id. This is what a
Datalog encoding of `get-fresh!` always does, and it is what the term relation's
`f(children, id)` row records anyway.

Two consequences, both recorded in `CHECKER.md`:

* Source terms and target ids inhabit one type, so the simulation theorem can compare
  them directly instead of carrying a source-to-target correspondence relation.
* egglog mints a *new* id per construction and lets the view merge dedup them; here the
  second construction of one shape reuses the id, so the merge does not fire. The
  induced equivalence is the same; the row counts are not.

The id supply that remains is over *variable names*, `@v0`, `@v1`, …, threaded through
`encode` at encode time — egglog's `@pv0`, `@pv1`, ….
-/

namespace Egglog
/-! ### Names -/
/-- The union-find table. The modelled language has one eq-sort, so where egglog emits
`@UF_<Sort>` per sort there is one table here. -/
def ufName : FnName := "@UF"

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

/-- `(function @UF (S) (S) :merge …)`. A term with no row is its own representative, so
the lookup is identity on miss — which the model expresses by there simply being no row
to read. -/
def ufDecl : FnDecl := { arity := 1, outArity := 1, merge := .merge mergeBody mergeResult }

/-- `(function @fView (S…) (S) :merge …)` for a constructor of arity `k`. Two rows
colliding on one key are congruent, and the merge resolves that by unioning them. -/
def viewDecl (k : Nat) : FnDecl :=
  { arity := k, outArity := 1, merge := .merge mergeBody mergeResult }

/-- `(function @fTerm (S… S) Unit :no-merge)`. Keyed on children *and* id, so distinct
constructions never collide. -/
def termDecl (k : Nat) : FnDecl := { arity := k + 1, outArity := 1, merge := .noMerge }

/-! ### The constructors a program mentions

The fragment declares almost nothing — an undeclared name is a constructor
(`Signature.mergeOf`) — so the functions to emit tables for are read off the syntax. -/
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
  | .run => []
  | .decl f d => [(f, d.arity)]

/-- Every function the program mentions, deduplicated. One table triple is emitted per
entry. -/
def Program.ctors (P : Program) : List (FnName × Nat) := (P.flatMap Cmd.ctors).dedup

/-! ### Queries

A source pattern becomes one view read per subterm, joined on e-class variables — the
`check` expansion of `proof_encoding.md`, "Queries". The reads bind ids, so the outer
`(= e₁ e₂)` of a source equality pattern becomes id equality, which is egglog's own
`(= e3 e6)` and is why the rebuild has to have canonicalized the rows first. -/
mutual

/-- Flatten `e` into view reads. Returns the expression naming `e`'s e-class, the reads,
and the next variable number. -/
def encodeQueryExpr : Expr → Nat → Expr × List Pattern × Nat
  | .lit l, n => (.lit l, [], n)
  | .var v, n => (.var v, [], n)
  | .app f args, n =>
      match encodeQueryArgs args n with
      | (es, ps, n₁) =>
          (.var (freshVar n₁),
           ps ++ [.eq (.var (freshVar n₁)) (.app (viewName f) es)],
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

`proof_encoding.md`, "Building a term": mint an id, write the term-relation row, intern
the application into its view, and read back the view's e-class. A parent is built over
its children's canonical ids, which is what keeps views canonical.

egglog interns with `set-if-empty-<View>!`, which returns the *existing* e-class when
the shape was already there and **discards** the id it just minted. There is no such
action here, so the encoding `set`s and then reads the view back. The difference is one
extra union: where egglog drops the minted id, the plain `set` collides with the
existing row and the view's `:merge` unions the two. Both terms denote the same
application, so the equalities are the same and only the row count differs. -/
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
(`proof_encoding.md`, "Union in a rule"), so it changes which rows are written and not
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
      | (as, n₂) => (⟨q, as⟩, n₂)

/-! ### Maintenance

`proof_encoding.md`, "Rebuilding". Two families, both ordinary rules. -/
/-- Path compression, `a → b → c` to `a → c`. egglog guards it with `(!= b c)`; without
disequality the unguarded rule additionally re-`set`s edges it already holds, which
changes nothing. -/
def pathCompressRule : Rule :=
  { query := [.eq (.var "@b") (.app ufName [.var "@a"]),
              .eq (.var "@c") (.app ufName [.var "@b"])],
    actions := [.set ufName [.var "@a"] [.var "@c"]] }

/-- `@c0 … @c(k-1)`, a rebuild rule's column variables. -/
def rebuildVars (k : Nat) : List Expr :=
  (List.range k).map fun i => .var ("@c" ++ toString i)

/-- The rebuild rules for a constructor of arity `k`: one per child column, moving that
column to its union-find leader, and one for the e-class column.

egglog emits **one** rule per eq-sort occurring in the view, not one per column: its
body joins a `@UF` delta against the rebuild index, and its action re-canonicalizes
every column at once through `@UF_<Sort>_canon` (identity on miss) before deleting the
stale row. Neither piece is available here — there is no index, no `delete`, and no
identity-on-miss read, since "no row" is not a matchable fact. Neither is needed for the
equalities: rows are never removed in this model, so a half-rewritten row is an extra
row rather than a lost one, and `Database.Out` reads any of them. What egglog buys with
the one-firing form is row count. -/
def rebuildRules (f : FnName) (k : Nat) : List Rule :=
  let cs := rebuildVars k
  let view : Expr := .app (viewName f) cs
  let eclassRule : Rule :=
    { query := [.eq (.var "@e") view, .eq (.var "@x") (.app ufName [.var "@e"])],
      actions := [.set (viewName f) cs [.var "@x"]] }
  eclassRule :: (List.range k).map fun i =>
    { query := [.eq (.var "@e") view,
                .eq (.var "@x") (.app ufName [.var ("@c" ++ toString i)])],
      actions := [.set (viewName f) (cs.set i (.var "@x")) [.var "@e"]] }

/-- Every maintenance rule the encoding of `P` emits. `Rebuilt` is stated over it. -/
def maintenanceRules (P : Program) : List Rule :=
  pathCompressRule :: P.ctors.flatMap fun fk => rebuildRules fk.1 fk.2

/-! ### The transformation -/
/-- The declarations and maintenance rules, emitted once at the top.

egglog runs the maintenance rules on a `run-schedule` between the source program's
commands; with no schedules they are ordinary rules, so they fire once per `Cmd.run`
alongside the encoded source rules. -/
def encodePrelude (P : Program) : Program :=
  .decl ufName ufDecl ::
    (P.ctors.flatMap fun fk =>
      [.decl (viewName fk.1) (viewDecl fk.2), .decl (termName fk.1) (termDecl fk.2)]) ++
    (maintenanceRules P).map .rule

/-- Encode one command. A source declaration is dropped: its function becomes the
skolem-id constructor, which must stay undeclared to be a constructor, and its table
triple is in the prelude. -/
def encodeCmd : Cmd → Nat → Program × Nat
  | .action a, n => match encodeAction a n with | (as, n₁) => (as.map .action, n₁)
  | .rule r, n => match encodeRule r n with | (r', n₁) => ([.rule r'], n₁)
  | .run, n => ([.run], n)
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
need; the constructor fragment has neither, so its presence would take the source out of
`Database.CtorRows` and with it out of `mcong_iff_cong`. -/
def Action.NoSet : Action → Prop
  | .set _ _ _ => False
  | _ => True

/-- No tuple destructure. `Pattern.values` reads a row of a non-constructor function,
which the constructor fragment has none of — so like `Action.NoSet` this is a fragment
restriction rather than a limitation, and it is why `encodePattern` leaves the case
alone instead of encoding it. -/
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
  | .run => []
  | .decl _ _ => []

/-- Every variable the program mentions. -/
def Program.vars (P : Program) : List Var := (P.flatMap Cmd.vars).dedup

/-- Constructors only, and no name that would collide with a generated one. -/
structure Program.EncodeDomain (P : Program) : Prop where
  /-- Every declared function is a constructor. -/
  ctorsOnly : ∀ c ∈ P, ∀ f d, c = Cmd.decl f d → d.merge = MergeSpec.union
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

The three notions the M11 theorems are stated over. None of them is `Cong` or `MCong`:
the encoded program's tables are `.merge` functions, so `Database.CtorRows` fails on the
target and `mcong_iff_cong` does not apply there. Equality on the target side is *only*
what `@UF` and the views record. -/
/-- A union-find edge that moves. The `:merge` writes `@UF (ordering-max p p) ↦
ordering-min p p` on a self-collision, so reflexive self-loops are ordinary rows and a
leader is "no edge that moves" rather than "no row". -/
def UFEdge (d : Database) (t p : Term) : Prop := d.Out ufName [t] [p] ∧ p ≠ t

/-- `l` is `t`'s representative: reachable along edges, and itself at the end of one.

A relation rather than a function because `Database.Out` reads *any* recorded output —
the model keeps the rows a merge displaces (`MERGE.md`, "What monotonicity costs"), so a
term can have several recorded parents, every one of which is genuinely equal to it. -/
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
step changes anything.

egglog's `(saturate (seq (run @rebuilding_cleanup) (saturate (run @parent))
(run @rebuilding)))`, as a predicate on the state rather than a command, because
`Cmd.run` carries no ruleset. It is the hypothesis the completeness half of simulation
needs: until the views are re-keyed to leaders, a collision that congruence would find
has not yet happened. Any `P` can be made to satisfy it by appending `(run)`s — which is
sound for the source side too, since both sides then run the extra rounds. -/
def Rebuilt (P : Program) (d : Database) : Prop :=
  (∀ r ∈ maintenanceRules P, ∀ d' ∈ RuleResults d r, Database.Contained d' d) ∧
    MergeSaturated d

/-- `a = b` holds in the source once both terms are built.

`Cong`'s `refl` and `congr` are restricted to `db.terms`, and the encoding is not: the
rebuild re-keys a view row to its children's leaders, so the encoded database ends up
holding rows about applications the source never built — `@AddView [1,1] ↦ Add[1,2]`
after `(Add 1 2)` and `(union 1 2)`. Those rows are still *true*, but only in this
sense. It is the form `ValidSubst` already uses ("the pattern instance is added to the
database before congruence is consulted"), and adding terms adds no assertion, so it is
a conservative reading rather than a weaker one. For `a b ∈ db.terms` under
`Database.WF` it coincides with `Cong db a b`. -/
def CongOn (db : Database) (a b : Term) : Prop :=
  Cong ((db.addTerm a).addTerm b) a b

/-! ### Proof nodes

`encode` writes none of these — the proof column is what the one-value-column
restriction blocks (see the header). The vocabulary is fixed here so the M11 proof
theorems have something to quantify over, and so the shape is reviewable now.

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
