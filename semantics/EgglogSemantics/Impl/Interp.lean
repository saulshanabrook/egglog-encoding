import EgglogSemantics.Impl.Closure
import EgglogSemantics.Spec.Step

/-!
# An executable interpreter

The semantics in `Step.lean` is a function but not a computation: `runRules` unions over
a set of substitutions carved out by a predicate. This runs the same fragment
computably, so programs can actually be executed — which is what makes the model
testable against the Rust (`PLAN.md`, "Differential testing").

`FDatabase`'s components are `List`s, not `Finset`s, for one blunt reason:
`Finset.toList` is noncomputable, so anything that has to *enumerate* a `Finset` cannot
be compiled. Duplicates in the lists are harmless — the denotation is the set of members,
and `closureF` dedups through `List.toFinset` where the closure needs a `Finset`.

The e-matching enumerator differs from the spec in one respect, deliberately. The spec
takes one substitution per pattern and joins them (`Env.UnionAll`, faithful to the Redex
`Env-Union`); the enumerator assigns the *whole query's* free variables at once and then
restricts to each pattern with `Env.canon`. The two agree up to `Env.Agree`, which by
`evalLocalActions_agree` is all `runRules` can see.
-/

namespace Egglog
/-! ### Finite databases -/
/-- The executable counterpart of `Database`. Every component is a `List`; membership,
not multiplicity or order, is what it denotes. -/
structure FDatabase where
  sig : Signature
  terms : List Term
  rows : List Row
  eqs : List (Term × Term)
  env : Env
  rules : List Rule

namespace FDatabase
/-- The spec database an `FDatabase` denotes. The refinement theorems are stated against
this. -/
def toDatabase (d : FDatabase) : Database where
  sig := d.sig
  terms := {t | t ∈ d.terms}
  rows := {r | r ∈ d.rows}
  eqs := {p | p ∈ d.eqs}
  env := d.env
  rules := {r | r ∈ d.rules}

/-- The initial database. -/
def empty : FDatabase where
  sig := fun _ => none
  terms := []
  rows := []
  eqs := []
  env := []
  rules := []

/-- Insert `t` and all of its subterms.

Deduplicated on insertion. That is invisible to `toDatabase`, but not to performance: a
round's `union` copies every operand's terms, so without it the list length multiplies
each round and the per-substitution `List.toFinset` in `closureF` goes quadratic on it. -/
def addTerm (t : Term) (d : FDatabase) : FDatabase :=
  { d with terms := (t.subtermList ++ d.terms).dedup,
           rows := (t.ctorRowList ++ d.rows).dedup }

/-- `addTerm` over a list. -/
def addTerms (ts : List Term) (d : FDatabase) : FDatabase :=
  ts.foldl (fun e t => e.addTerm t) d

/-- `(set (f as…) vs)`, computed. -/
def addRow (f : FnName) (as vs : List Term) (d : FDatabase) : FDatabase :=
  let d := (d.addTerms as).addTerms vs
  { d with rows := (⟨f, as, vs⟩ :: d.rows).dedup }

/-- Assert `a = b`, inserting both terms. -/
def addEq (a b : Term) (d : FDatabase) : FDatabase :=
  { (d.addTerm a).addTerm b with eqs := ((a, b) :: d.eqs).dedup }

/-- Union two databases, taking the signature, environment and rules from the left. This
is the Redex `U_d` as `runRules` uses it. -/
def union (d₁ d₂ : FDatabase) : FDatabase :=
  { d₁ with terms := (d₁.terms ++ d₂.terms).dedup, rows := (d₁.rows ++ d₂.rows).dedup,
            eqs := (d₁.eqs ++ d₂.eqs).dedup }

/-- `terms` as a `Finset`, for the closure. -/
def termsF (d : FDatabase) : Finset Term := d.terms.toFinset

/-- `eqs` as a `Finset`. -/
def eqsF (d : FDatabase) : Finset (Term × Term) := d.eqs.toFinset

/-- The interpreter's invariant, stated on the denotation so that every `Database.WF`
lemma transfers through the `toDatabase_*` bridges. -/
def WF (d : FDatabase) : Prop := d.toDatabase.WF

/-- The congruence closure of `d`, computed. -/
def closureF (d : FDatabase) : Finset (Term × Term) := closureTotal d.termsF d.eqsF

/-- Whether two tuples are pointwise congruent. Compares a row's key and value columns
against a pattern's operands (`patternHolds`, `Pattern.values`) and two colliding rows'
keys (`Impl/Merge.lean`, `mergeOne`). -/
def congrTuple (cl : Finset (Term × Term)) (as bs : List Term) : Bool :=
  as.length == bs.length && (as.zip bs).all fun q => decide (q ∈ cl)

end FDatabase
/-! ### Enumerating substitutions -/
/-- Every assignment of `vars` to `terms`, with the domain in `vars`' order. -/
def assignments (terms : List Term) : List Var → List Env
  | [] => [[]]
  | v :: vs => terms.flatMap fun t => (assignments terms vs).map fun σ => (v, t) :: σ

/-- `σ` cut down to `vars` and put in `vars`' order. Used both to canonicalize a
substitution the spec produced and to restrict a query substitution to one pattern. -/
def Env.canon (vars : List Var) (σ : Env) : Env :=
  vars.filterMap fun v => (Env.lookup v σ).map fun t => (v, t)

/-! ### E-matching -/
/-- The free variables of a query: the variables the enumerator assigns. -/
def Query.freeVars (q : Query) (σ : Env) : List Var :=
  q.foldr (fun p acc => p.freeVars σ ∪ acc) []

/-- The `valid-subst` side conditions for one pattern, computed: the pattern's instance
is congruent — in the database extended with it — to a witness the database already
holds. -/
def patternHolds (d : FDatabase) (p : Pattern) (σ : Env) : Bool :=
  match p with
  | .values vs f as =>
    match Expr.evalList vs (d.env ++ σ), Expr.evalList as (d.env ++ σ) with
    | some us, some ts =>
      let cl := d.closureF
      d.rows.any fun r =>
        decide (r.fn = f) && FDatabase.congrTuple cl ts r.args
          && FDatabase.congrTuple cl us r.out
    | _, _ => false
  | .expr e =>
    match e.eval (d.env ++ σ) with
    | none => false
    | some t =>
      let cl := (d.addTerm t).closureF
      decide (∃ w ∈ d.terms, (w, t) ∈ cl)
  | .eq e₁ e₂ =>
    match e₁.eval (d.env ++ σ), e₂.eval (d.env ++ σ) with
    | some t₁, some t₂ =>
      let cl := ((d.addTerm t₁).addTerm t₂).closureF
      decide ((t₁, t₂) ∈ cl) && decide (∃ w ∈ d.terms, (w, t₁) ∈ cl)
    | _, _ => false

/-- The substitutions satisfying a whole query. -/
def matchQuery (d : FDatabase) (q : Query) : List Env :=
  (assignments d.terms (Query.freeVars q d.env)).filter fun σ =>
    q.all fun p => patternHolds d p (Env.canon (p.freeVars d.env) σ)

/-! ### Running -/
/-- The Redex `Eval-Action`, computed. -/
def execAction (d : FDatabase) : Action → Option FDatabase
  | .expr e => (e.eval d.env).map fun t => d.addTerm t
  | .letBind v e => (e.eval d.env).map fun t =>
      { d.addTerm t with env := (v, t) :: d.env }
  | .union e₁ e₂ =>
      (e₁.eval d.env).bind fun t₁ => (e₂.eval d.env).map fun t₂ => d.addEq t₁ t₂
  | .set f args out => (Expr.evalList args d.env).bind fun as =>
      (Expr.evalList out d.env).map fun vs => d.addRow f as vs

/-- The Redex `Eval-Global-Actions`, computed. -/
def execActions (d : FDatabase) : List Action → Option FDatabase
  | [] => some d
  | a :: as => (execAction d a).bind fun d' => execActions d' as

/-- The Redex `Eval-Local-Actions`, computed. -/
def execLocalActions (d : FDatabase) (as : List Action) (σ : Env) : Option FDatabase :=
  (execActions { d with env := d.env ++ σ } as).map fun d' =>
    { d' with env := d.env, rules := d.rules }

/-- One firing of `r` on `σ`, unioned into `acc`; nothing if the actions get stuck, which
for a well-scoped rule they do not. -/
def fireInto (d : FDatabase) (r : Rule) (acc : FDatabase) (σ : Env) : FDatabase :=
  match execLocalActions d r.actions σ with
  | some d' => acc.union d'
  | none => acc

/-- Every firing of `r`, unioned into `acc`. -/
def fireRule (d : FDatabase) (acc : FDatabase) (r : Rule) : FDatabase :=
  (matchQuery d r.query).foldl (fireInto d r) acc

/-- One round: every rule on every matching substitution, all read off the pre-state. -/
def execRunRules (d : FDatabase) : FDatabase := d.rules.foldl (fireRule d) d

/-- `execRunRules` iterated: egglog's `(run n)`. -/
def execRunRounds : Nat → FDatabase → FDatabase
  | 0, d => d
  | n + 1, d => execRunRounds n (execRunRules d)

/-- The Redex `Command-Reduction`, computed. -/
def execCmd (d : FDatabase) : Cmd → Option FDatabase
  | .action a => execAction d a
  | .rule r => some { d with rules := r :: d.rules }
  | .run => some (execRunRules d)
  | .decl f dc => some { d with sig := Function.update d.sig f (some dc) }

/-- The Redex `Egglog-Reduction`, computed. -/
def execProgram (d : FDatabase) : Program → Option FDatabase
  | [] => some d
  | c :: cs => (execCmd d c).bind fun d' => execProgram d' cs

/-- Run a program from the initial database. -/
def exec (p : Program) : Option FDatabase := execProgram FDatabase.empty p

/-- What one firing contributes. -/
def Fired (d : FDatabase) (r : Rule) (σ : Env) (d' : FDatabase) : Prop :=
  execLocalActions d r.actions σ = some d'

/-! ### Row counts

What `egglog/tests/files.rs` snapshots is one row per distinct *canonical* argument
tuple. On this side that is the number of congruence classes of `f`-applications, which
is what a differential test compares. -/
/-- Whether two argument lists are pointwise related by `cl`. -/
def congrArgs (cl : Finset (Term × Term)) (as bs : List Term) : Bool :=
  as.length == bs.length && (as.zip bs).all fun q => decide (q ∈ cl)

/-- The argument lists of `d`'s `f`-applications. -/
def FDatabase.argLists (d : FDatabase) (f : FnName) : List (List Term) :=
  d.terms.filterMap fun t =>
    match t with
    | .app g as => if g = f then some as else none
    | _ => none

/-- The number of rows egglog's table for `f` would hold: one per congruence class of
argument lists. Each list is mapped to its whole class and the distinct classes counted,
so no representative has to be chosen — there is no order on `Term` to choose one by. -/
def FDatabase.rowCount (d : FDatabase) (f : FnName) : Nat :=
  let cl := d.closureF
  let args := (d.argLists f).toFinset
  (args.image fun as => args.filter fun bs => congrArgs cl as bs).card

/-- The per-function row counts, as `files.rs` prints them. -/
def FDatabase.rowCounts (d : FDatabase) (fs : List FnName) : List (FnName × Nat) :=
  fs.map fun f => (f, d.rowCount f)

end Egglog
