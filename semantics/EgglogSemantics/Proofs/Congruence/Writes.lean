import EgglogSemantics.Proofs.Congruence.Target
import EgglogSemantics.Proofs.Congruence.Sound
import EgglogSemantics.Proofs.Presentation
import EgglogSemantics.Proofs.Writes
import EgglogSemantics.Proofs.Diagonal

/-! The writes of a compiled head: a build writes the self-loop of every subexpression's
value, including both operands of a `min`, and, when enabled, the node row of every
application it spells; a union adds the two edges to the smaller side. Each compiled row is between
congruent source terms, goes down the term order, comes with the self-loops of its
endpoints, and every source write is derivable from the compiled rows. -/

namespace Egglog.Congruence

variable {sub : Bool}

/-- A variable of an argument is a variable of the list. -/
theorem var_mem_varsList_of_mem {v : Var} {e : Expr} : ∀ {es : List Expr}, e ∈ es →
    v ∈ e.vars → v ∈ Expr.varsList es
  | [], h, _ => by simp at h
  | e' :: es, h, hv => by
      rw [Expr.varsList_cons, List.mem_union_iff]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl hv
      · exact Or.inr (var_mem_varsList_of_mem h hv)

/-- The values a build writes self-loops for: every subexpression's value, with both
operands of a `min`. -/
inductive BuildTerm (σ : Env) : Expr → Term → Prop
  | lit (l : Lit) : BuildTerm σ (.lit l) (.lit l)
  | var {v : Var} {t : Term} : Env.lookup v σ = some t → BuildTerm σ (.var v) t
  | app_self {f : FnName} {args : List Expr} {ts : List Term} :
      Expr.evalList args σ = some ts → BuildTerm σ (.app f args) (.app f ts)
  | app_arg {f : FnName} {args : List Expr} {e : Expr} {u : Term} :
      e ∈ args → BuildTerm σ e u → BuildTerm σ (.app f args) u
  | min_left {a b : Expr} {u : Term} : BuildTerm σ a u → BuildTerm σ (.min a b) u
  | min_right {a b : Expr} {u : Term} : BuildTerm σ b u → BuildTerm σ (.min a b) u

/-- The applications a build writes node rows for: the value of every application the
expression spells. -/
inductive AppBuild (σ : Env) : Expr → FnName → List Term → Prop
  | self {f : FnName} {args : List Expr} {ts : List Term} :
      Expr.evalList args σ = some ts → AppBuild σ (.app f args) f ts
  | arg {f : FnName} {args : List Expr} {e : Expr} {g : FnName} {us : List Term} :
      e ∈ args → AppBuild σ e g us → AppBuild σ (.app f args) g us
  | min_left {a b : Expr} {g : FnName} {us : List Term} :
      AppBuild σ a g us → AppBuild σ (.min a b) g us
  | min_right {a b : Expr} {g : FnName} {us : List Term} :
      AppBuild σ b g us → AppBuild σ (.min a b) g us

/-- A node a build spells is a build term. -/
theorem AppBuild.buildTerm {σ : Env} {e : Expr} {g : FnName} {us : List Term}
    (h : AppBuild σ e g us) : BuildTerm σ e (.app g us) := by
  induction h with
  | self hts => exact .app_self hts
  | arg he _ ih => exact .app_arg he ih
  | min_left _ ih => exact .min_left ih
  | min_right _ ih => exact .min_right ih

/-- The value of an expression whose minima are over variables is a build term of it. -/
theorem BuildTerm.self {σ : Env} : ∀ {e : Expr} {t : Term}, e.MinOverVars →
    e.eval σ = some t → BuildTerm σ e t
  | .lit _, _, _, h => by
      rw [Expr.eval_lit, Option.some.injEq] at h
      rw [← h]; exact .lit _
  | .var _, _, _, h => .var h
  | .min a b, _, ho, h => by
      obtain ⟨ha, hb⟩ := Expr.minOverVars_min ho
      rw [Expr.eval_min, Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, hmap⟩ := h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
      rcases Term.least_eq_or x y with hl | hl <;> rw [hl]
      · exact .min_left (BuildTerm.self ha.minOverVars hx)
      · exact .min_right (BuildTerm.self hb.minOverVars hy)
  | .app f args, t, _, h => by
      rw [Expr.eval_app_ctor] at h
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .app_self hts

/-- A build term of a variable minimum is a binding. -/
theorem BuildTerm.binding_of_isVarMin {σ : Env} {e : Expr} {u : Term} (hb : BuildTerm σ e u)
    (he : e.IsVarMin) : ∃ v, Env.lookup v σ = some u := by
  induction hb with
  | lit l => simp [Expr.IsVarMin, Expr.isVarMinB] at he
  | var hv => exact ⟨_, hv⟩
  | app_self => simp [Expr.IsVarMin, Expr.isVarMinB] at he
  | app_arg => simp [Expr.IsVarMin, Expr.isVarMinB] at he
  | min_left _ ih => exact ih (Expr.isVarMin_min he).1
  | min_right _ ih => exact ih (Expr.isVarMin_min he).2

/-- A variable minimum spells no application. -/
theorem AppBuild.not_isVarMin {σ : Env} {e : Expr} {g : FnName} {us : List Term}
    (hb : AppBuild σ e g us) (he : e.IsVarMin) : False := by
  induction hb with
  | self => simp [Expr.IsVarMin, Expr.isVarMinB] at he
  | arg => simp [Expr.IsVarMin, Expr.isVarMinB] at he
  | min_left _ ih => exact ih (Expr.isVarMin_min he).1
  | min_right _ ih => exact ih (Expr.isVarMin_min he).2

/-- An argument's value is among the evaluated arguments. -/
theorem eval_mem_of_evalList {σ : Env} {es : List Expr} {ts : List Term}
    (hts : Expr.evalList es σ = some ts) {e : Expr} (he : e ∈ es) :
    ∃ t, e.eval σ = some t ∧ t ∈ ts := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  obtain ⟨t, ht, hev⟩ := Expr.getElem?_of_evalList hts i (List.getElem?_eq_getElem hi)
  exact ⟨t, hev, List.mem_of_getElem? ht⟩

/-- A build term is a subterm of the value or a binding: the operand of a `min` that is not
chosen is a bound variable. -/
theorem BuildTerm.subterm_or_bound {σ : Env} {e : Expr} {u t : Term} (ho : e.MinOverVars)
    (hb : BuildTerm σ e u) (h : e.eval σ = some t) :
    Term.IsSubterm u t ∨ ∃ v, Env.lookup v σ = some u := by
  induction hb generalizing t with
  | lit l =>
    rw [Expr.eval_lit, Option.some.injEq] at h
    rw [← h]; exact Or.inl (.refl _)
  | var hv =>
    rw [Expr.eval_var] at h
    rw [Option.some.inj (hv.symm.trans h)]
    exact Or.inl (.refl _)
  | app_self hts =>
    rw [Expr.eval_app_ctor, hts, Option.map_some, Option.some.injEq] at h
    rw [← h]; exact Or.inl (.refl _)
  | app_arg he _ ih =>
    rw [Expr.eval_app_ctor] at h
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨te, hev, hmem⟩ := eval_mem_of_evalList hts he
    rcases ih (Expr.minOverVarsList_mem he (Expr.minOverVars_app ho)) hev with hs | hbound
    · exact Or.inl (hs.trans (.arg hmem (.refl _)))
    · exact Or.inr hbound
  | min_left hba _ => exact Or.inr (hba.binding_of_isVarMin (Expr.minOverVars_min ho).1)
  | min_right hbb _ => exact Or.inr (hbb.binding_of_isVarMin (Expr.minOverVars_min ho).2)

/-- A node a build spells is a subterm of the value. -/
theorem AppBuild.subterm {σ : Env} {e : Expr} {g : FnName} {us : List Term} {t : Term}
    (ho : e.MinOverVars) (hb : AppBuild σ e g us) (h : e.eval σ = some t) :
    Term.IsSubterm (.app g us) t := by
  induction hb generalizing t with
  | self hts =>
    rw [Expr.eval_app_ctor, hts, Option.map_some, Option.some.injEq] at h
    rw [← h]; exact .refl _
  | arg he _ ih =>
    rw [Expr.eval_app_ctor] at h
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨te, hev, hmem⟩ := eval_mem_of_evalList hts he
    exact (ih (Expr.minOverVarsList_mem he (Expr.minOverVars_app ho)) hev).trans
      (.arg hmem (.refl _))
  | min_left hba _ => exact (hba.not_isVarMin (Expr.minOverVars_min ho).1).elim
  | min_right hbb _ => exact (hbb.not_isVarMin (Expr.minOverVars_min ho).2).elim

/-- Every subterm of a value is a build term or lies inside a variable's binding, and an
application subterm outside the bindings is a node the build spells. -/
theorem subterm_build {σ : Env} (e : Expr) : ∀ {t u : Term}, e.MinOverVars →
    e.eval σ = some t → Term.IsSubterm u t →
    (BuildTerm σ e u ∧ ∀ g us, u = .app g us → AppBuild σ e g us) ∨
      ∃ v ∈ e.vars, ∃ w, Env.lookup v σ = some w ∧ Term.IsSubterm u w := by
  induction e using Expr.recExpr with
  | lit l =>
    intro t u _ h hu
    rw [Expr.eval_lit, Option.some.injEq] at h
    subst h
    cases hu with
    | refl => exact Or.inl ⟨.lit l, fun g us heq => by cases heq⟩
  | var v =>
    intro t u _ h hu
    rw [Expr.eval_var] at h
    exact Or.inr ⟨v, by simp, t, h, hu⟩
  | min a b _ _ =>
    intro t u ho h hu
    obtain ⟨ha, hb⟩ := Expr.minOverVars_min ho
    rw [Expr.eval_min, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, hmap⟩ := h
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
    rcases Term.least_eq_or x y with hl | hl <;> rw [hl] at hu
    · obtain ⟨v, hv, hvx⟩ := ha.eval_binding hx
      exact Or.inr ⟨v, by simp [hv], x, hvx, hu⟩
    · obtain ⟨v, hv, hvy⟩ := hb.eval_binding hy
      exact Or.inr ⟨v, by simp [hv], y, hvy, hu⟩
  | app f args ih =>
    intro t u ho h hu
    rw [Expr.eval_app_ctor] at h
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
    cases hu with
    | refl =>
      refine Or.inl ⟨.app_self hts, fun g us heq => ?_⟩
      obtain ⟨rfl, rfl⟩ := Term.app.inj heq
      exact .self hts
    | arg ha hua =>
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      have hi' : i < args.length := by rw [← Expr.evalList_length hts]; exact hi
      obtain ⟨te, hte, hev⟩ := Expr.getElem?_of_evalList hts i (List.getElem?_eq_getElem hi')
      rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hte
      rw [hte] at hua
      have hoa : args[i].MinOverVars :=
        Expr.minOverVarsList_mem (List.getElem_mem hi') (Expr.minOverVars_app ho)
      rcases ih _ (List.getElem_mem hi') hoa hev hua with ⟨hb, hn⟩ | ⟨v, hv, w, hw, huw⟩
      · exact Or.inl ⟨.app_arg (List.getElem_mem hi') hb,
          fun g us heq => .arg (List.getElem_mem hi') (hn g us heq)⟩
      · exact Or.inr ⟨v, by
          rw [Expr.vars_app]
          exact var_mem_varsList_of_mem (List.getElem_mem hi') hv, w, hw, huw⟩

/-! ### The writes of a build -/

/-- The self-loop row of a value. -/
abbrev selfRow (u : Term) : Term × Term := (ufRowT u u, ufRowT u u)

/-- The node row of an application, as an equation. -/
abbrev nodeSelf (f : FnName) (as : List Term) : Term × Term := (nodeRowT f as, nodeRowT f as)

theorem build_lit (l : Lit) : encodeBuildWith { subsumption := sub } (.lit l) = [.expr (ufRow (.lit l) (.lit l))] := rfl
theorem build_var (v : Var) : encodeBuildWith { subsumption := sub } (.var v) = [.expr (ufRow (.var v) (.var v))] := rfl
theorem build_app (f : FnName) (args : List Expr) : encodeBuildWith { subsumption := sub } (.app f args) =
    encodeBuildArgsWith { subsumption := sub } args ++
      ((if sub then [.expr (nodeRow f args)] else []) ++
        [.expr (ufRow (.app f args) (.app f args))]) := by
  simp [encodeBuildWith, List.append_assoc]
theorem buildArgs_nil : encodeBuildArgsWith { subsumption := sub } [] = [] := rfl
theorem buildArgs_cons (e : Expr) (es : List Expr) :
    encodeBuildArgsWith { subsumption := sub } (e :: es) = encodeBuildWith { subsumption := sub } e ++ encodeBuildArgsWith { subsumption := sub } es := rfl

theorem write_ufRow {σ : Env} {a b : Expr} {s t : Term} (ha : a.eval σ = some s)
    (hb : b.eval σ = some t) :
    Action.write σ (.expr (ufRow a b)) = some {(ufRowT s t, ufRowT s t)} := by
  simp [Action.write, ufRow, Expr.evalList, ha, hb]

theorem writes_ufRow {σ : Env} {a b : Expr} {s t : Term} (ha : a.eval σ = some s)
    (hb : b.eval σ = some t) :
    Action.writes σ [.expr (ufRow a b)] = some {(ufRowT s t, ufRowT s t)} := by
  rw [Action.writes_singleton, write_ufRow ha hb]

theorem evalList_append_of_eval {σ : Env} {args : List Expr} {ts : List Term}
    (hts : Expr.evalList args σ = some ts) {e : Expr} {t : Term} (he : e.eval σ = some t) :
    Expr.evalList (args ++ [e]) σ = some (ts ++ [t]) := by
  induction args generalizing ts with
  | nil =>
    rw [Expr.evalList_nil, Option.some.injEq] at hts
    subst hts
    simp [Expr.evalList, he]
  | cons a as ih =>
    rw [Expr.evalList_cons, Option.bind_eq_some_iff] at hts
    obtain ⟨u, hu, hrest⟩ := hts
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
    rw [List.cons_append, Expr.evalList_cons, hu, Option.bind_some, ih hus, Option.map_some,
      List.cons_append]

/-- The node row of a build, as it evaluates. -/
theorem write_nodeRow {σ : Env} {f : FnName} {args : List Expr} {ts : List Term}
    (hts : Expr.evalList args σ = some ts) :
    Action.write σ (.expr (nodeRow f args)) = some {nodeSelf f ts} := by
  simp only [Action.write, nodeRow, nodeAtom, Expr.eval_app_ctor]
  rw [evalList_append_of_eval hts (by rw [Expr.eval_app_ctor, hts]; rfl)]
  rfl

mutual

/-- A build writes exactly the self-loops of its build terms and, when subsumption is
enabled, the node rows of the applications it spells. -/
theorem build_writes {σ : Env} : ∀ (e : Expr), e.MinOverVars →
    (∀ v ∈ e.vars, (Env.lookup v σ).isSome) →
    ∃ W, Action.writes σ (encodeBuildWith { subsumption := sub } e) = some W ∧
      ∀ q, q ∈ W ↔ (∃ u, BuildTerm σ e u ∧ q = selfRow u) ∨
        ∃ g us, sub = true ∧ AppBuild σ e g us ∧ q = nodeSelf g us
  | .lit l, _, _ => by
      refine ⟨{selfRow (.lit l)}, writes_ufRow rfl rfl, fun q => ?_⟩
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro rfl; exact Or.inl ⟨_, .lit l, rfl⟩
      · rintro (⟨u, hu, rfl⟩ | ⟨g, us, hon, hb, rfl⟩)
        · cases hu; rfl
        · cases hb
  | .var v, _, hb => by
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hb v (by simp))
      refine ⟨{selfRow t}, writes_ufRow (by simpa using ht) (by simpa using ht), fun q => ?_⟩
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro rfl; exact Or.inl ⟨t, .var ht, rfl⟩
      · rintro (⟨u, hu, rfl⟩ | ⟨g, us, hon, hb, rfl⟩)
        · cases hu with
          | var hu => rw [Option.some.inj (hu.symm.trans ht)]
        · cases hb
  | .min a b, ho, hb => by
      obtain ⟨ha, hb'⟩ := Expr.minOverVars_min ho
      obtain ⟨W₁, hW₁, hmem₁⟩ := build_writes a ha.minOverVars (fun v hv => hb v (by simp [hv]))
      obtain ⟨W₂, hW₂, hmem₂⟩ := build_writes b hb'.minOverVars (fun v hv => hb v (by simp [hv]))
      refine ⟨W₁ ∪ W₂, ?_, fun q => ?_⟩
      · simp only [encodeBuildWith]
        rw [Action.writes_append, hW₁, Option.bind_some, hW₂, Option.map_some]
      · simp only [Set.mem_union, hmem₁, hmem₂]
        constructor
        · rintro ((⟨u, hu, rfl⟩ | ⟨g, us, hon, hn, rfl⟩) | (⟨u, hu, rfl⟩ | ⟨g, us, hon, hn, rfl⟩))
          · exact Or.inl ⟨u, .min_left hu, rfl⟩
          · exact Or.inr ⟨g, us, hon, .min_left hn, rfl⟩
          · exact Or.inl ⟨u, .min_right hu, rfl⟩
          · exact Or.inr ⟨g, us, hon, .min_right hn, rfl⟩
        · rintro (⟨u, hu, rfl⟩ | ⟨g, us, hon, hn, rfl⟩)
          · cases hu with
            | min_left h => exact Or.inl (Or.inl ⟨u, h, rfl⟩)
            | min_right h => exact Or.inr (Or.inl ⟨u, h, rfl⟩)
          · cases hn with
            | min_left h => exact Or.inl (Or.inr ⟨g, us, hon, h, rfl⟩)
            | min_right h => exact Or.inr (Or.inr ⟨g, us, hon, h, rfl⟩)
  | .app f args, ho, hb => by
      obtain ⟨W, hW, hmem⟩ := buildArgs_writes args (Expr.minOverVars_app ho) (by simpa using hb)
      obtain ⟨ts, hts⟩ := Expr.evalList_isSome args (fun v hv =>
        Env.lookup_isSome_iff_mem_dom.mp (hb v (by simpa using hv)))
      have hself : Action.writes σ
          ((if sub then [.expr (nodeRow f args)] else []) ++
            [.expr (ufRow (.app f args) (.app f args))]) =
          some ({q | sub = true ∧ q = nodeSelf f ts} ∪ {selfRow (.app f ts)}) := by
        cases sub
        · simpa using writes_ufRow
            (by rw [Expr.eval_app_ctor, hts]; rfl)
            (by rw [Expr.eval_app_ctor, hts]; rfl)
        · simp only [Bool.true_eq, ↓reduceIte, List.cons_append, List.nil_append]
          rw [Action.writes, write_nodeRow hts, Option.bind_some,
            writes_ufRow (by rw [Expr.eval_app_ctor, hts]; rfl)
              (by rw [Expr.eval_app_ctor, hts]; rfl), Option.map_some]
          simp
      refine ⟨W ∪ ({q | sub = true ∧ q = nodeSelf f ts} ∪ {selfRow (.app f ts)}),
        ?_, fun q => ?_⟩
      · rw [build_app, Action.writes_append, hW, Option.bind_some, hself, Option.map_some]
      · simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, hmem]
        constructor
        · rintro ((⟨e, he, u, hu, rfl⟩ | ⟨e, he, g, us, hon, hn, rfl⟩) | ⟨hon, rfl⟩ | rfl)
          · exact Or.inl ⟨u, .app_arg he hu, rfl⟩
          · exact Or.inr ⟨g, us, hon, .arg he hn, rfl⟩
          · exact Or.inr ⟨f, ts, hon, .self hts, rfl⟩
          · exact Or.inl ⟨_, .app_self hts, rfl⟩
        · rintro (⟨u, hu, rfl⟩ | ⟨g, us, hon, hn, rfl⟩)
          · cases hu with
            | app_self hts' =>
              right; right
              rw [Option.some.inj (hts'.symm.trans hts)]
            | app_arg he hu => exact Or.inl (Or.inl ⟨_, he, u, hu, rfl⟩)
          · cases hn with
            | self hts' =>
              right; left
              exact ⟨hon, by rw [Option.some.inj (hts'.symm.trans hts)]⟩
            | arg he hn => exact Or.inl (Or.inr ⟨_, he, g, us, hon, hn, rfl⟩)

theorem buildArgs_writes {σ : Env} : ∀ (es : List Expr), Expr.MinOverVarsList es →
    (∀ v ∈ Expr.varsList es, (Env.lookup v σ).isSome) →
    ∃ W, Action.writes σ (encodeBuildArgsWith { subsumption := sub } es) = some W ∧
      ∀ q, q ∈ W ↔ (∃ e ∈ es, ∃ u, BuildTerm σ e u ∧ q = selfRow u) ∨
        ∃ e ∈ es, ∃ g us, sub = true ∧ AppBuild σ e g us ∧ q = nodeSelf g us
  | [], _, _ => ⟨∅, by rw [buildArgs_nil]; rfl, by simp⟩
  | e :: es, ho, hb => by
      obtain ⟨hoe, hoes⟩ := Expr.minOverVarsList_cons ho
      obtain ⟨W₁, hW₁, hmem₁⟩ := build_writes e hoe (fun v hv => hb v (by simp [hv]))
      obtain ⟨W₂, hW₂, hmem₂⟩ := buildArgs_writes es hoes (fun v hv => hb v (by simp [hv]))
      refine ⟨W₁ ∪ W₂, ?_, fun q => ?_⟩
      · rw [buildArgs_cons, Action.writes_append, hW₁, Option.bind_some, hW₂, Option.map_some]
      · simp only [Set.mem_union, hmem₁, hmem₂, List.mem_cons]
        constructor
        · rintro ((⟨u, hu, rfl⟩ | ⟨g, us, hon, hn, rfl⟩) |
            (⟨e', he', u, hu, rfl⟩ | ⟨e', he', g, us, hon, hn, rfl⟩))
          · exact Or.inl ⟨e, Or.inl rfl, u, hu, rfl⟩
          · exact Or.inr ⟨e, Or.inl rfl, g, us, hon, hn, rfl⟩
          · exact Or.inl ⟨e', Or.inr he', u, hu, rfl⟩
          · exact Or.inr ⟨e', Or.inr he', g, us, hon, hn, rfl⟩
        · rintro (⟨e', rfl | he', u, hu, rfl⟩ | ⟨e', rfl | he', g, us, hon, hn, rfl⟩)
          · exact Or.inl (Or.inl ⟨u, hu, rfl⟩)
          · exact Or.inr (Or.inl ⟨e', he', u, hu, rfl⟩)
          · exact Or.inl (Or.inr ⟨g, us, hon, hn, rfl⟩)
          · exact Or.inr (Or.inr ⟨e', he', g, us, hon, hn, rfl⟩)

end

end Egglog.Congruence
