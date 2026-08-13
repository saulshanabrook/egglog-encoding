import EgglogSemantics.Impl.Closure
import EgglogSemantics.Spec.Match

/-!
# An executable interpreter

`Spec/Step.lean`'s `RunRules` is a function but not a computation: it unions over a set
of substitutions carved out by a predicate. This runs the constructor fragment computably,
so programs can actually be executed — which is what makes the model testable against the
Rust (`PLAN.md`, "Differential testing"). `Proofs/Interp.lean`'s `exec_programStep` is the
equation between the two, in both directions.

`FDatabase`'s components are `List`s, not `Finset`s, for one blunt reason:
`Finset.toList` is noncomputable, so anything that has to *enumerate* a `Finset` cannot
be compiled. Duplicates in the lists are harmless — the denotation is the set of members,
and `closureF` dedups through `List.toFinset` where the closure needs a `Finset`.

The e-matching enumerator differs from the spec in two respects, both deliberately. The
spec takes one substitution per pattern and joins them (`Env.UnionAll`); the enumerator
assigns the *whole query's* free variables at once and then
restricts to each pattern with `Env.canon`. The two agree up to `Env.Agree`, which by
`evalLocalActions_agree` is all `RunRules` can see. And it assigns from
`FDatabase.valueTerms` rather than from `terms`, which is a *strict* refinement — see
there.
-/

namespace Egglog
/-! ### The table index

`Spec/` has no rows: a merge function's entry at the key `a…` with value columns `v…` is
the term `f(a…, v…)`, and a constructor's is `f(a…)`. An implementation cannot work from
that alone, because egglog's tables are not append-only — an insert *replaces* the
resident entry and a rebuild *moves* one — and reconstructing which entries are still
current by scanning a monotone term set is exactly the work a table exists to avoid.

`FDatabase.rows` is therefore an **index**: a derived structure, re-keyed by
`FDatabase.rebuild` and deleted from by `FDatabase.mergeOneOriented`, over a `terms` that
never shrinks. `FDatabase.toDatabase` drops it, so neither the re-keying nor the deletion
moves the denotation. -/
/-- One tuple of one function's table: `fn args… ↦ out…`.

`out` is a *list*, one entry per value column: egglog's tables are multi-column, and the
encoding depends on it — `@UF_<Sort>` carries a parent *and* a proof.

**A row's entry term is `fn(args… ++ out…)`**, which is the one thing the index and the
denotation have to agree on. A constructor's `FnDecl.entryWidth` is its `arity`, so a
constructor has *no* value column and its row is `⟨f, as, []⟩`, whose entry term is the
application `f(as)` itself — which is what makes its functional dependency plain
congruence. -/
@[ext]
structure Row where
  fn : FnName
  args : List Term
  out : List Term
  deriving DecidableEq

/-- The constructor entries among `t`'s subterms, each mapping its own children to itself,
in `subtermList`'s order.

A **declared merge function**'s application is an entry term `f(a…, v…)` that already
carries its value columns, and `FDatabase.addRow` indexes that one directly; synthesising
`⟨f, a… ++ v…, [f(a…, v…)]⟩` for it as well would give `f` a second, bogus key class. So
those are filtered out, and everything else — a declared constructor, or a name nobody
declared — is recorded exactly as before. `Expr.eval` builds no application of a merge
function, so on a term the evaluator produced the filter removes nothing. -/
def Term.ctorRowList (sig : Signature) (t : Term) : List Row :=
  t.subtermList.filterMap fun s =>
    match s with
    | .app f as => if (sig.mergeOf f).isSome then none else some ⟨f, as, []⟩
    | .lit _ => none

/-! ### Finite databases -/
/-- The executable counterpart of `Database`. Every component is a `List`; membership,
not multiplicity or order, is what it denotes. -/
structure FDatabase where
  sig : Signature
  terms : List Term
  /-- The table index. Not a component of the denotation — see "The table index" above. -/
  rows : List Row
  eqs : List (Term × Term)
  env : Env
  rules : List Rule

namespace FDatabase
/-- The spec database an `FDatabase` denotes. The refinement theorems are stated against
this.

**`terms` becomes the diagonal.** A `Database` has no term field — `t` is present exactly
when `t = t` is derivable — so the list contributes one reflexive equation per member and
`Database.terms` reads them back out. `toDatabase_terms` is that bridge, and it is what
every refinement theorem rests on.

**An equation is kept only where the list holds both of its sides**, which is what makes
that bridge unconditional rather than an invariant to be maintained. `Cong` can reach
`Cong db t t` by `symm` and `trans` from a *non*-reflexive pair, so an equation naming a
term the list does not hold would put a term in the denotation that the interpreter cannot
see. The restriction is not a weakening — `closureTotal` already imposes it on `eqsF`, so
this is the denotation agreeing with the computation, and it removes nothing from a
database the interpreter built: `EqsInTerms` below.

`rows` is simply dropped: every row is also an entry term in `terms`, put there by
`addRow` and never taken out, so the index carries nothing the denotation does not already
have. Synthesising the entry terms *here* instead would not work — `closureF`'s candidate
universe is `terms`, so an entry that is not in the list is congruent to nothing. -/
def toDatabase (d : FDatabase) : Database where
  sig := d.sig
  eqs := {p | p.1 = p.2 ∧ p.1 ∈ d.terms} ∪
    {p | p ∈ d.eqs ∧ p.1 ∈ d.terms ∧ p.2 ∈ d.terms}
  env := d.env
  rules := {r | r ∈ d.rules}

/-- Every term a derivation over the denotation mentions is one the list holds. Immediate
from `toDatabase`'s restriction on `eqs`: `assert` is the only rule that introduces a term,
and `congr`'s two self-congruence premises carry the memberships for it. -/
theorem toDatabase_cong_mem {d : FDatabase} {a b : Term} (h : Cong d.toDatabase a b) :
    a ∈ d.terms ∧ b ∈ d.terms := by
  match h with
  | .assert hm =>
    rcases hm with ⟨he, hd⟩ | ⟨_, h₁, h₂⟩
    · refine ⟨hd, ?_⟩
      have he' : a = b := he
      exact he' ▸ hd
    · exact ⟨h₁, h₂⟩
  | .symm h => exact (toDatabase_cong_mem h).symm
  | .trans h₁ h₂ => exact ⟨(toDatabase_cong_mem h₁).1, (toDatabase_cong_mem h₂).2⟩
  | .congr hm₁ hm₂ _ => exact ⟨(toDatabase_cong_mem hm₁).1, (toDatabase_cong_mem hm₂).1⟩

/-- **The denotation holds exactly the terms the list does.** -/
theorem toDatabase_terms (d : FDatabase) : d.toDatabase.terms = {t | t ∈ d.terms} := by
  ext t
  exact ⟨fun h => (toDatabase_cong_mem h).1, fun h => Cong.assert (Or.inl ⟨rfl, h⟩)⟩

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
           rows := (Term.ctorRowList d.sig t ++ d.rows).dedup }

/-- `addTerm` over a list. -/
def addTerms (ts : List Term) (d : FDatabase) : FDatabase :=
  ts.foldl (fun e t => e.addTerm t) d

/-- `(set (f as…) vs)`, computed: the entry term `f(as…, vs…)` — which is all
`Spec/Eval.lean`'s `evalAction` records — plus the index row.

The entry term is what keeps the index derived. `rows` is re-keyed and deleted from while
`terms` is not, so a row that has moved or gone is still an entry term the denotation
holds, and `Database.Out` reads it from every congruent key. -/
def addRow (f : FnName) (as vs : List Term) (d : FDatabase) : FDatabase :=
  let d := d.addTerm (.app f (as ++ vs))
  { d with rows := (⟨f, as, vs⟩ :: d.rows).dedup }

/-- Assert `a = b`, inserting both terms. -/
def addEq (a b : Term) (d : FDatabase) : FDatabase :=
  { (d.addTerm a).addTerm b with eqs := ((a, b) :: d.eqs).dedup }

/-- Union two databases, taking the signature, environment and rules from the left.
`Database.sUnion`, computed, at the two-operand shape `execRunRules` folds with. -/
def union (d₁ d₂ : FDatabase) : FDatabase :=
  { d₁ with terms := (d₁.terms ++ d₂.terms).dedup, rows := (d₁.rows ++ d₂.rows).dedup,
            eqs := (d₁.eqs ++ d₂.eqs).dedup }

/-! ### What `toDatabase` restricts by

`toDatabase` keeps an equation only where `terms` holds both of its sides, and
`closureTotal` imposes the same restriction on `eqsF`. Neither loses anything: `empty`
satisfies the condition, the four writers below preserve it, and they are the only ones —
every `set`, `union` and rule firing goes through them, and `Impl/Merge.lean` reaches
`eqs` and `terms` only through `addTerm` and `execActions`, a merge pass otherwise
rewriting `rows` alone. -/
/-- Every equation names terms the list holds. -/
def EqsInTerms (d : FDatabase) : Prop := ∀ p ∈ d.eqs, p.1 ∈ d.terms ∧ p.2 ∈ d.terms

theorem empty_eqsInTerms : EqsInTerms empty := by simp [EqsInTerms, empty]

/-- `addTerm` only grows `terms`. -/
theorem EqsInTerms.addTerm {d : FDatabase} (h : d.EqsInTerms) (t : Term) :
    (d.addTerm t).EqsInTerms := by
  intro p hp
  simp only [FDatabase.addTerm, List.mem_dedup, List.mem_append]
  exact ⟨Or.inr (h p hp).1, Or.inr (h p hp).2⟩

/-- `addRow` is `addTerm` on the entry term. -/
theorem EqsInTerms.addRow {d : FDatabase} (h : d.EqsInTerms) (f : FnName) (as vs : List Term) :
    (FDatabase.addRow f as vs d).EqsInTerms := h.addTerm _

/-- **The one writer that introduces a pair**, and it inserts both sides. -/
theorem EqsInTerms.addEq {d : FDatabase} (h : d.EqsInTerms) (a b : Term) :
    (FDatabase.addEq a b d).EqsInTerms := by
  have hself : ∀ t : Term, t ∈ t.subtermList := fun t => by
    cases t <;> simp [Term.subtermList]
  intro p hp
  simp only [FDatabase.addEq, List.mem_dedup, List.mem_cons] at hp
  simp only [FDatabase.addEq, FDatabase.addTerm, List.mem_dedup, List.mem_append]
  rcases hp with rfl | hp
  · exact ⟨Or.inr (Or.inl (hself a)), Or.inl (hself b)⟩
  · exact ⟨Or.inr (Or.inr (h p hp).1), Or.inr (Or.inr (h p hp).2)⟩

/-- `union` concatenates `eqs` and `terms` together. -/
theorem EqsInTerms.union {d₁ d₂ : FDatabase} (h₁ : d₁.EqsInTerms) (h₂ : d₂.EqsInTerms) :
    (d₁.union d₂).EqsInTerms := by
  intro p hp
  simp only [FDatabase.union, List.mem_dedup, List.mem_append] at hp ⊢
  rcases hp with hp | hp
  · exact ⟨Or.inl (h₁ p hp).1, Or.inl (h₁ p hp).2⟩
  · exact ⟨Or.inr (h₂ p hp).1, Or.inr (h₂ p hp).2⟩

/-- `terms` as a `Finset`, for the closure. -/
def termsF (d : FDatabase) : Finset Term := d.terms.toFinset

/-- `eqs` as a `Finset`. -/
def eqsF (d : FDatabase) : Finset (Term × Term) := d.eqs.toFinset

/-- The interpreter's invariant, stated on the denotation so that every `Database.WF`
lemma transfers through the `toDatabase_*` bridges. -/
def WF (d : FDatabase) : Prop := d.toDatabase.WF

/-- The congruence closure of `d`, computed. -/
def closureF (d : FDatabase) : Finset (Term × Term) := closureTotal d.termsF d.eqsF

/-- The terms a rule variable may be bound to: everything `terms` holds except a **merge
function's entry term**.

`terms` holds both the values the program built and the entries it recorded, and an entry
is not a value: `Dist(a…, v…)` names no e-class, it records that `Dist` at `a…` reads
`v…`. Two reasons to keep the enumerator off them. `assignments` is `|terms| ^ |vars|` by
construction, so every entry term multiplies the search; and a substitution binding a
variable to one would make `(Hit x)` build a term whose child is a table entry, which
egglog has no way to express.

This is **stricter than the specification**. `Spec/Match.lean`'s `ValidEnv` asks only that
each bound term be in `db.terms`, and deliberately does not say which of the two kinds it
is, so a spec-side substitution may bind an entry term where this enumerator will not
produce one. Firing on fewer substitutions is the safe direction — the interpreter's
result stays a state the spec reaches — but it is a refinement and not an equality, so it
is one-directional where `exec_programStep` used to be two. -/
def valueTerms (d : FDatabase) : List Term :=
  d.terms.filter fun t => match t with
    | .app f _ => (d.sig.mergeOf f).isNone
    | .lit _ => true

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

/-- `Matches`'s side conditions for one pattern, computed: the pattern's instance
is congruent — in the database extended with it — to a witness the database already
holds. The instance is added because a pattern operand may denote a term the program
never built.

The witness is a term, except at a **merge function's** entry atom, where it is a *row*
and the key and value operands are added instead. The index is what says which of that
function's recorded entries is current, and nothing else does. It says nothing about a
constructor: a constructor's entry is its own application, so the atom asks about the
term `f(a…, v…)` like any other instance, and a row — which fixes one key/value split
where the term admits every split — would answer a different question.

It compares with `closureF`, which computes exactly the specification's `Cong`. -/
def patternHolds (d : FDatabase) (p : Pattern) (σ : Env) : Bool :=
  match p with
  | .values vs f as =>
    match Expr.evalList d.sig vs (d.env ++ σ), Expr.evalList d.sig as (d.env ++ σ) with
    | some us, some ts =>
      if (d.sig.mergeOf f).isSome then
        let cl := ((d.addTerms ts).addTerms us).closureF
        d.rows.any fun r =>
          decide (r.fn = f) && FDatabase.congrTuple cl ts r.args
            && FDatabase.congrTuple cl us r.out
      else
        let t := Term.app f (ts ++ us)
        let cl := (d.addTerm t).closureF
        decide (∃ w ∈ d.terms, (w, t) ∈ cl)
    | _, _ => false
  | .expr e =>
    match e.eval d.sig (d.env ++ σ) with
    | none => false
    | some t =>
      let cl := (d.addTerm t).closureF
      decide (∃ w ∈ d.terms, (w, t) ∈ cl)
  | .eq e₁ e₂ =>
    match e₁.eval d.sig (d.env ++ σ), e₂.eval d.sig (d.env ++ σ) with
    | some t₁, some t₂ =>
      let cl := ((d.addTerm t₁).addTerm t₂).closureF
      decide ((t₁, t₂) ∈ cl) && decide (∃ w ∈ d.terms, (w, t₁) ∈ cl)
    | _, _ => false

/-- The substitutions satisfying a whole query. Assigns from `FDatabase.valueTerms`, not
from `terms`: a variable is bound to a value the program built, never to a table entry. -/
def matchQuery (d : FDatabase) (q : Query) : List Env :=
  (assignments d.valueTerms (Query.freeVars q d.env)).filter fun σ =>
    q.all fun p => patternHolds d p (Env.canon (p.freeVars d.env) σ)

/-! ### Running -/
/-- `evalAction`, computed. -/
def execAction (d : FDatabase) : Action → Option FDatabase
  | .expr e => (e.eval d.sig d.env).map fun t => d.addTerm t
  | .letBind v e => (e.eval d.sig d.env).map fun t =>
      { d.addTerm t with env := (v, t) :: d.env }
  | .union e₁ e₂ =>
      (e₁.eval d.sig d.env).bind fun t₁ => (e₂.eval d.sig d.env).bind fun t₂ =>
        if t₁.isLit || t₂.isLit then none else some (d.addEq t₁ t₂)
  | .set f args out => (Expr.evalList d.sig args d.env).bind fun as =>
      (Expr.evalList d.sig out d.env).map fun vs => d.addRow f as vs

/-- `evalActions`, computed. -/
def execActions (d : FDatabase) : List Action → Option FDatabase
  | [] => some d
  | a :: as => (execAction d a).bind fun d' => execActions d' as

/-- `evalLocalActions`, computed. -/
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

/-- One round of the ruleset `R`: every rule *of `R`* on every matching substitution, all
read off the pre-state. -/
def execRunRules (R : RulesetName) (d : FDatabase) : FDatabase :=
  (d.rules.filter fun r => r.ruleset == R).foldl (fireRule d) d

/-- Whether two states agree on the fields a round can change. `sig` is a function, and
`env`/`rules` no round touches. -/
def FDatabase.sameData (d e : FDatabase) : Bool :=
  e.terms == d.terms && e.rows == d.rows && e.eqs == d.eqs

/-- Rounds of `R`, as a relation to descend: `x` is the round after `y`, and `y` had not
settled. It is well founded at `d` exactly when `R` saturates from `d`. -/
def FDatabase.RunRel (R : RulesetName) (x y : FDatabase) : Prop :=
  execRunRules R y = x ∧ ¬ y.sameData (execRunRules R y) = true

/-- Rounds of `R` until nothing changes. Takes a **termination witness**, not fuel, so it is
total on the states where the ruleset saturates and loses nothing — `Impl/Merge.lean`'s
`mergeSaturate` pattern, one level up. `exec` runs `runSaturateF` instead, because no
witness is available at runtime: whether a ruleset saturates at a given state is not
something the caller can supply. -/
def FDatabase.runSaturate (R : RulesetName) (d : FDatabase)
    (h : Acc (FDatabase.RunRel R) d) : FDatabase :=
  Acc.rec (motive := fun _ _ => FDatabase)
    (fun x _ ih =>
      if he : x.sameData (execRunRules R x) = true then x
      else ih (execRunRules R x) ⟨rfl, he⟩) h

/-- Rounds of `R` until nothing changes, bounded by fuel that **fails** rather than
returning a prefix — `Impl/Merge.lean`'s `mergeSaturateF` pattern, one level up and for
its reason: a ruleset that really does diverge makes the run `none`, which the difftest
reports as a mismatch, rather than presenting a half-run state as a saturation.

This is what `exec` runs, and `runSaturateF_eq_runSaturate` is the price: it agrees with
`runSaturate` whenever it answers at all, and answers less often. -/
def FDatabase.runSaturateF (R : RulesetName) : Nat → FDatabase → Option FDatabase
  | 0, d => if d.sameData (execRunRules R d) then some d else none
  | n + 1, d =>
      if d.sameData (execRunRules R d) then some d
      else FDatabase.runSaturateF R n (execRunRules R d)

/-- Rounds a run allows before declaring a ruleset divergent. Unlike `mergeFuel` this
bounds no structural quantity: rounds add terms rather than shrink a class, so a
terminating ruleset can need arbitrarily many and `exec_programStep` has to say so. -/
def runFuel : Nat := 64

/-- `CmdStep`, computed. -/
def execCmd (d : FDatabase) : Cmd → Option FDatabase
  | .action a => execAction d a
  | .rule r => some { d with rules := r :: d.rules }
  | .run R => some (execRunRules R d)
  | .saturate R => d.runSaturateF R runFuel
  | .decl f dc => some { d with sig := Function.update d.sig f (some dc) }

/-- `ProgramStep`, computed. -/
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

/-- The argument lists of `d`'s `f`-applications, which for a **constructor** are its
entries' key tuples. -/
def FDatabase.argLists (d : FDatabase) (f : FnName) : List (List Term) :=
  d.terms.filterMap fun t =>
    match t with
    | .app g as => if g = f then some as else none
    | _ => none

/-- The number of rows egglog's table for a **constructor** `f` would hold: one per
congruence class of argument lists. Each list is mapped to its whole class and the
distinct classes counted, so no representative has to be chosen — there is no order on
`Term` to choose one by.

Constructors only. A merge function's entry term is `f(a…, v…)`, so `argLists` returns
key *and* value columns for one and this would count classes of the pair rather than rows
of the table. `Impl/Merge.lean`'s `keyRowCount` is the one that reads the index and counts
key classes; it agrees with this on a constructor and is what the differential test
runs. -/
def FDatabase.rowCount (d : FDatabase) (f : FnName) : Nat :=
  let cl := d.closureF
  let args := (d.argLists f).toFinset
  (args.image fun as => args.filter fun bs => congrArgs cl as bs).card

/-- The per-function row counts, as `files.rs` prints them. -/
def FDatabase.rowCounts (d : FDatabase) (fs : List FnName) : List (FnName × Nat) :=
  fs.map fun f => (f, d.rowCount f)

end Egglog
