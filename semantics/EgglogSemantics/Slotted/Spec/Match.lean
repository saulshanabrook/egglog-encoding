import EgglogSemantics.Slotted.Spec.Congruence

/-!
# Slotted e-matching

The plain matching judgement with the slotted closure: query variables range over the
representatives closed under renaming, `reps'`, an application is looked up in `live'`, and
equalities compare through `SCong`. A slot written in a query, `$v`, denotes the fixed name
`$v`. The parser stores it as `Expr.var "$v"`; its environment entry is determined by its
spelling, not chosen by a match. The free-name guards `free`, `not-free`
and `free-names-are`, and the comparisons modulo renaming `renaming-=` and `renaming-!=`, are
built-in predicate heads interpreted here rather than looked up.
-/

namespace Egglog.Slotted

/-- A slot identifier: fixed in a query, fresh when used only in actions. -/
def isSlotVar (v : Var) : Bool := v.startsWith "$"

/-- The built-in predicates of the slotted query language. -/
inductive Builtin where
  | free | notFree | freeNamesAre | renamingEq | renamingNe
  deriving DecidableEq, Repr

/-- The predicate a head names, if any. -/
def Builtin.ofName : FnName → Option Builtin
  | "free" => some .free
  | "not-free" => some .notFree
  | "free-names-are" => some .freeNamesAre
  | "renaming-=" => some .renamingEq
  | "renaming-!=" => some .renamingNe
  | _ => none

/-- Whether an expression is a built-in predicate application. -/
def _root_.Egglog.Expr.isBuiltin : Expr → Bool
  | .app f _ => (Builtin.ofName f).isSome
  | _ => false

/-- `t` is equal to `u` modulo renaming: some renaming of `t`'s free slots is congruent to `u`. -/
def RenamingEq (bind : Binders) (db : Database) (t u : Term) : Prop :=
  ∃ (m : Renaming) (t' : Term), m.WF ∧ m.Covers (slots bind t) ∧ Renames bind m t t' ∧
    SCong bind db t' u

mutual

/-- `G,σ ⊨ e` under the slotted closure: the expression evaluates and every application it
reads is in `live'`. Slot terms are always live. -/
inductive SExpr.Matches (bind : Binders) (db : Database) (σ : Env) : Expr → Prop where
  | lit {l : Lit} : Term.lit l ∈ live' bind db → SExpr.Matches bind db σ (.lit l)
  | var {v : Var} {t : Term} : Env.lookup v σ = some t → SExpr.Matches bind db σ (.var v)
  | app {f : FnName} {args : List Expr} {ts : List Term} :
      SExpr.MatchesList bind db σ args → Expr.evalList args σ = some ts →
      Term.app f ts ∈ live' bind db → SExpr.Matches bind db σ (.app f args)
  | min {a b : Expr} :
      SExpr.Matches bind db σ a → SExpr.Matches bind db σ b → SExpr.Matches bind db σ (.min a b)

/-- `SExpr.Matches` over an argument list. -/
inductive SExpr.MatchesList (bind : Binders) (db : Database) (σ : Env) : List Expr → Prop where
  | nil : SExpr.MatchesList bind db σ []
  | cons {e : Expr} {es : List Expr} :
      SExpr.Matches bind db σ e → SExpr.MatchesList bind db σ es →
      SExpr.MatchesList bind db σ (e :: es)

end

/-- `G,σ ⊨ p`: an expression pattern matches as that expression; an equality or disequality
needs both sides to match and compares them through `SCong`; a built-in predicate reads the
live free slots of its evaluated terms or compares them modulo renaming. -/
inductive SMatches (bind : Binders) (db : Database) : Pattern → Env → Prop where
  | atom {e : Expr} {σ : Env} :
      e.isBuiltin = false → SExpr.Matches bind db σ e → SMatches bind db (.expr e) σ
  | equal {e₁ e₂ : Expr} {σ : Env} {t₁ t₂ : Term} :
      SExpr.Matches bind db σ e₁ → SExpr.Matches bind db σ e₂ →
      e₁.eval σ = some t₁ → e₂.eval σ = some t₂ → SCong bind db t₁ t₂ →
      SMatches bind db (.eq e₁ e₂) σ
  | unequal {e₁ e₂ : Expr} {σ : Env} {t₁ t₂ : Term} :
      SExpr.Matches bind db σ e₁ → SExpr.Matches bind db σ e₂ →
      e₁.eval σ = some t₁ → e₂.eval σ = some t₂ → ¬ SCong bind db t₁ t₂ →
      SMatches bind db (.ne e₁ e₂) σ
  /-- `(free $s e…)`: the slot is a live free slot of one of the terms. -/
  | free {x : Expr} {es : List Expr} {σ : Env} {s : Slot} {ts : List Term} :
      isSlotName s = true → x.eval σ = some (Term.slot s) →
      SExpr.MatchesList bind db σ es → Expr.evalList es σ = some ts →
      (∃ t ∈ ts, s ∈ liveSlots bind db t) →
      SMatches bind db (.expr (.app "free" (x :: es))) σ
  /-- `(not-free $s e…)`: the slot is a live free slot of none of the terms. -/
  | notFree {x : Expr} {es : List Expr} {σ : Env} {s : Slot} {ts : List Term} :
      isSlotName s = true → x.eval σ = some (Term.slot s) →
      SExpr.MatchesList bind db σ es → Expr.evalList es σ = some ts →
      (∀ t ∈ ts, s ∉ liveSlots bind db t) →
      SMatches bind db (.expr (.app "not-free" (x :: es))) σ
  /-- `(free-names-are e $s…)`: the live free slots of the term are exactly the listed ones. -/
  | freeNamesAre {e : Expr} {xs : List Expr} {σ : Env} {t : Term} {ss : List Slot} :
      SExpr.Matches bind db σ e → e.eval σ = some t →
      (∀ s ∈ ss, isSlotName s = true) → Expr.evalList xs σ = some (ss.map Term.slot) →
      (∀ s, s ∈ liveSlots bind db t ↔ s ∈ ss) →
      SMatches bind db (.expr (.app "free-names-are" (e :: xs))) σ
  | renamingEq {a b : Expr} {σ : Env} {ta tb : Term} :
      SExpr.Matches bind db σ a → SExpr.Matches bind db σ b →
      a.eval σ = some ta → b.eval σ = some tb → RenamingEq bind db ta tb →
      SMatches bind db (.expr (.app "renaming-=" [a, b])) σ
  | renamingNe {a b : Expr} {σ : Env} {ta tb : Term} :
      SExpr.Matches bind db σ a → SExpr.Matches bind db σ b →
      a.eval σ = some ta → b.eval σ = some tb → ¬ RenamingEq bind db ta tb →
      SMatches bind db (.expr (.app "renaming-!=" [a, b])) σ

/-- `σ` binds exactly `vars`: a pattern slot denotes its own name, and every ordinary
variable ranges over `reps'`. Slot entries are a deterministic representation of constants;
there is no separate assignment of pattern names. -/
def ValidEnv' (bind : Binders) (db : Database) (vars : List Var) (σ : Env) : Prop :=
  (Env.dom σ).Perm vars ∧
  (∀ b ∈ σ, isSlotVar b.1 = true → b.2 = Term.slot b.1) ∧
  (∀ b ∈ σ, isSlotVar b.1 = false → b.2 ∈ reps' bind db)

/-- `Query'`: variables range over renamed representatives, literal slots keep their
names, and every conjunct satisfies `App'` and the guards. -/
@[blueprint "def:slotted-query"
  (statement := /--
  \begin{mathpar}
  \ir{Query'}{\sigma:\operatorname{FV}(Q)\to\operatorname{reps}'(E)\\
    \forall p\in Q.\ G,\sigma\models p}
    {G,\sigma\models Q}
  \and
  \ir{App'}{G,\sigma\models e_i\ (\forall i)\\
    \eval{f(e_1,\ldots,e_n)}\in\operatorname{live}'(G)}
    {G,\sigma\models f(e_1,\ldots,e_n)}
  \and
  \ir{Free}{\eval{e}=t\\\$s\in\operatorname{FS}(E,t)}
    {G,\sigma\models\mathtt{Free}(\$s,e)}
  \and
  \ir{NotFree}{\eval{e}=t\\\$s\notin\operatorname{FS}(E,t)}
    {G,\sigma\models\mathtt{NotFree}(\$s,e)}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
def SQueryMatches (bind : Binders) (db : Database) (q : Query) (σ : Env) : Prop :=
  ValidEnv' bind db q.vars σ ∧ ∀ p ∈ q, SMatches bind db p σ

/-- Some substitution satisfies the query. -/
def SQueryHolds (bind : Binders) (db : Database) (q : Query) : Prop :=
  ∃ σ, SQueryMatches bind db q σ

end Egglog.Slotted
