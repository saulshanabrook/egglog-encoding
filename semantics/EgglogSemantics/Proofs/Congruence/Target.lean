import EgglogSemantics.Congruence.Read
import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Proofs.Subsume
import EgglogSemantics.Proofs.Step
import EgglogSemantics.Proofs.Source.Ctors
import EgglogSemantics.Proofs.Source.Arity

/-! The compiled state read as a union-find with node rows and markers. A row is an asserted
`@UF(k, p)`, live or stale; `Edge` (from `Read.lean`) is the live row; a node row
`@Node_f(ā, f(ā))` records a held application, and a marker `@Sub_f(ā)` a spelling the
source subsumed. The facts here hold on every diagonal target state of that shape. -/

namespace Egglog.Congruence

/-- The union-find row `@UF(k, p)` as a term. -/
abbrev ufRowT (k p : Term) : Term := .app ufName [k, p]

/-- The node row `@Node_f(a₁, …, aₙ, f(a₁, …, aₙ))` as a term. -/
abbrev nodeRowT (f : FnName) (as : List Term) : Term := .app (nodeName f) (as ++ [.app f as])

/-- The marker row `@Sub_f(a₁, …, aₙ)` as a term. -/
abbrev subRowT (f : FnName) (as : List Term) : Term := .app (subName f) as

theorem ufRowT_inj {k p k' p' : Term} (h : ufRowT k p = ufRowT k' p') : k = k' ∧ p = p' := by
  have := Term.app.inj h
  simp only [List.cons.injEq, and_true] at this
  exact this.2

theorem nodeRowT_inj {f g : FnName} {as bs : List Term} (h : nodeRowT f as = nodeRowT g bs) :
    f = g ∧ as = bs := by
  have h' := Term.app.inj h
  have hf := nodeName_inj h'.1
  subst hf
  exact ⟨rfl, (List.append_inj' h'.2 rfl).1⟩

theorem subRowT_inj {f g : FnName} {as bs : List Term} (h : subRowT f as = subRowT g bs) :
    f = g ∧ as = bs := by
  have h' := Term.app.inj h
  exact ⟨subName_inj h'.1, h'.2⟩

/-- The row `@UF(k, p)` is asserted, live or stale. -/
def Row (d : Database) (k p : Term) : Prop := (ufRowT k p, ufRowT k p) ∈ d.eqs

/-- The keys of the union-find: the terms with a row. -/
def Keys (d : Database) : Set Term := {k | ∃ p, Row d k p}

/-- The node row of the application `f(as)` is asserted. -/
def Node (d : Database) (f : FnName) (as : List Term) : Prop :=
  (nodeRowT f as, nodeRowT f as) ∈ d.eqs

/-- The marker of the spelling `f(as)` is asserted. -/
def Marker (d : Database) (f : FnName) (as : List Term) : Prop :=
  (subRowT f as, subRowT f as) ∈ d.eqs

/-- A name a source program may use: outside the generated `@` namespace. -/
def SourceName (f : FnName) : Prop := ¬ "@".isPrefixOf f = true

/-- Every application inside the term is of a source name. -/
def _root_.Egglog.Term.SourceShaped (t : Term) : Prop :=
  ∀ g bs, Term.app g bs ∈ t.subterms → SourceName g

/-- The rows read as equations. -/
def view (d : Database) : Database := ⟨{q | Row d q.1 q.2}, ∅⟩

/-- The live rows read as equations. -/
def liveView (d : Database) : Database := ⟨{q | Edge d q.1 q.2}, ∅⟩

/-! ### Names -/

/-- The union-find name is generated. -/
theorem atPrefix_ufName : "@".isPrefixOf ufName = true := by
  rw [ufName, String.isPrefixOf, String.startsWith_string_iff,
    show ("@").toList = ['@'] from by decide, show ("@UF").toList = ['@', 'U', 'F'] from by decide]
  exact ⟨['U', 'F'], rfl⟩

theorem not_sourceName_ufName : ¬ SourceName ufName := fun h => h atPrefix_ufName

theorem not_sourceName_nodeName (f : FnName) : ¬ SourceName (nodeName f) :=
  fun h => h (atPrefix_nodeName f)

theorem not_sourceName_subName (f : FnName) : ¬ SourceName (subName f) :=
  fun h => h (atPrefix_subName f)

theorem SourceName.ne_ufName {f : FnName} (h : SourceName f) : f ≠ ufName :=
  fun hf => not_sourceName_ufName (hf ▸ h)

theorem SourceName.ne_nodeName {f : FnName} (h : SourceName f) (g : FnName) : f ≠ nodeName g :=
  fun hf => not_sourceName_nodeName g (hf ▸ h)

theorem SourceName.ne_subName {f : FnName} (h : SourceName f) (g : FnName) : f ≠ subName g :=
  fun hf => not_sourceName_subName g (hf ▸ h)

theorem Term.SourceShaped.head {f : FnName} {as : List Term}
    (h : Term.SourceShaped (.app f as)) : SourceName f :=
  h f as (Term.self_mem_subterms _)

theorem Term.SourceShaped.subterm {t s : Term} (h : t.SourceShaped) (hs : s ∈ t.subterms) :
    s.SourceShaped := fun g bs hg => h g bs (hg.trans hs)

/-- A source-shaped term is no generated row and holds none. -/
theorem Term.SourceShaped.ne_ufRowT {t : Term} (h : t.SourceShaped) (k p : Term) :
    t ≠ ufRowT k p := fun ht => not_sourceName_ufName (Term.SourceShaped.head (ht ▸ h))

theorem Term.SourceShaped.ne_nodeRowT {t : Term} (h : t.SourceShaped) (f : FnName)
    (as : List Term) : t ≠ nodeRowT f as := fun ht => not_sourceName_nodeName f (Term.SourceShaped.head (ht ▸ h))

theorem Term.SourceShaped.ne_subRowT {t : Term} (h : t.SourceShaped) (f : FnName)
    (as : List Term) : t ≠ subRowT f as := fun ht => not_sourceName_subName f (Term.SourceShaped.head (ht ▸ h))

theorem Term.SourceShaped.not_mentions_uf {t : Term} (h : t.SourceShaped) :
    ¬ Term.Mentions ufName t := fun ⟨args, hs⟩ => not_sourceName_ufName (h ufName args hs)

/-- A source-shaped term never applies the union-find name. -/
theorem sourceShaped_of_ctorsIn {P : Program} (hdom : P.Fragment) {t : Term}
    (ht : Term.CtorsIn P t) : t.SourceShaped := by
  intro g bs hs
  exact noAt_of_mem_ctors hdom (ht g bs hs)

theorem not_mentions_uf_of_ctorsIn {P : Program} (hdom : P.Fragment) {t : Term}
    (ht : Term.CtorsIn P t) : ¬ Term.Mentions ufName t :=
  Term.SourceShaped.not_mentions_uf (sourceShaped_of_ctorsIn hdom ht)

/-! ### Rows, nodes, markers and keys -/

theorem Row.mem_terms {d : Database} {k p : Term} (h : Row d k p) : ufRowT k p ∈ d.terms :=
  ⟨_, h, Or.inl (Term.self_mem_subterms _)⟩

theorem Row.key_mem_terms {d : Database} {k p : Term} (h : Row d k p) : k ∈ d.terms :=
  ⟨_, h, Or.inl (.arg (by simp) (.refl _))⟩

theorem Row.mem_keys {d : Database} {k p : Term} (h : Row d k p) : k ∈ Keys d := ⟨p, h⟩

theorem Row.mono {d e : Database} (h : d.eqs ⊆ e.eqs) {k p : Term} (hr : Row d k p) :
    Row e k p := h hr

theorem Node.mem_terms {d : Database} {f : FnName} {as : List Term} (h : Node d f as) :
    nodeRowT f as ∈ d.terms := ⟨_, h, Or.inl (Term.self_mem_subterms _)⟩

theorem Node.mono {d e : Database} (h : d.eqs ⊆ e.eqs) {f : FnName} {as : List Term}
    (hn : Node d f as) : Node e f as := h hn

theorem Marker.mem_terms {d : Database} {f : FnName} {as : List Term} (h : Marker d f as) :
    subRowT f as ∈ d.terms := ⟨_, h, Or.inl (Term.self_mem_subterms _)⟩

theorem Marker.mono {d e : Database} (h : d.eqs ⊆ e.eqs) {f : FnName} {as : List Term}
    (hm : Marker d f as) : Marker e f as := h hm

theorem Keys.mono {d e : Database} (h : d.eqs ⊆ e.eqs) : Keys d ⊆ Keys e :=
  fun _ ⟨p, hr⟩ => ⟨p, hr.mono h⟩

theorem Keys.subset_terms (d : Database) : Keys d ⊆ d.terms :=
  fun _ ⟨_, hr⟩ => hr.key_mem_terms

@[simp] theorem view_eqs (d : Database) : (view d).eqs = {q | Row d q.1 q.2} := rfl
@[simp] theorem view_subsumed (d : Database) : (view d).subsumed = ∅ := rfl
@[simp] theorem liveView_eqs (d : Database) : (liveView d).eqs = {q | Edge d q.1 q.2} := rfl
@[simp] theorem liveView_subsumed (d : Database) : (liveView d).subsumed = ∅ := rfl

theorem view_mono {d e : Database} (h : d.eqs ⊆ e.eqs) : (view d).eqs ⊆ (view e).eqs :=
  fun _ hq => hq.mono h

/-- A row is an equation of the view. -/
theorem Row.cong_view {d : Database} {k p : Term} (hr : Row d k p) : Cong (view d) k p :=
  .direct hr

/-- A live row is an equation of the live view. -/
theorem Edge.cong_liveView {d : Database} {k p : Term} (he : Edge d k p) :
    Cong (liveView d) k p := .direct he

/-! ### The shape of a compiled state -/

/-- The equations of a compiled state are reflexive pairs of union-find rows, node rows,
markers and keys; keys are source-shaped, the parent of a row is a key, and the node of a
node row or marker is a key. -/
structure Shape (d : Database) : Prop where
  eqs : ∀ q ∈ d.eqs, (∃ k p, q = (ufRowT k p, ufRowT k p)) ∨
    (∃ f as, q = (nodeRowT f as, nodeRowT f as)) ∨ (∃ f as, q = (subRowT f as, subRowT f as)) ∨
    (∃ t, q = (t, t) ∧ t ∈ Keys d)
  keys : ∀ k ∈ Keys d, k.SourceShaped
  parents : ∀ k p, Row d k p → p ∈ Keys d
  nodes : ∀ f as, Node d f as → Term.app f as ∈ Keys d
  markers : ∀ f as, Marker d f as → Term.app f as ∈ Keys d

namespace Shape

variable {d : Database} (hs : Shape d)
include hs

theorem key_sourceName {f : FnName} {ts : List Term} (hk : Term.app f ts ∈ Keys d) :
    SourceName f := Term.SourceShaped.head (hs.keys _ hk)

/-- A subterm of a key is a source-shaped term. -/
theorem subterm_sourceShaped {k s : Term} (hk : k ∈ Keys d) (hsub : s ∈ k.subterms) :
    s.SourceShaped := Term.SourceShaped.subterm (hs.keys k hk) hsub

/-- Every held term is a row, a node row, a marker, or a subterm of a key. -/
theorem mem_terms_iff {t : Term} :
    t ∈ d.terms ↔ (∃ k p, Row d k p ∧ t = ufRowT k p) ∨
      (∃ f as, Node d f as ∧ t = nodeRowT f as) ∨
      (∃ f as, Marker d f as ∧ t = subRowT f as) ∨ ∃ k ∈ Keys d, t ∈ k.subterms := by
  constructor
  · rintro ⟨q, hq, hsub⟩
    rcases hs.eqs q hq with ⟨k, p, rfl⟩ | ⟨f, as, rfl⟩ | ⟨f, as, rfl⟩ | ⟨u, rfl, hu⟩
    · have hrow : Row d k p := hq
      have main : t ∈ (ufRowT k p).subterms →
          (∃ k p, Row d k p ∧ t = ufRowT k p) ∨ (∃ f as, Node d f as ∧ t = nodeRowT f as) ∨
          (∃ f as, Marker d f as ∧ t = subRowT f as) ∨ ∃ k ∈ Keys d, t ∈ k.subterms := by
        intro h
        rw [Term.subterms_app] at h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact Or.inl ⟨k, p, hrow, rfl⟩
        · obtain ⟨u, hu', hs'⟩ := Set.mem_iUnion₂.mp h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu'
          rcases hu' with rfl | rfl
          · exact Or.inr (Or.inr (Or.inr ⟨u, hrow.mem_keys, hs'⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨u, hs.parents _ _ hrow, hs'⟩))
      exact hsub.elim main main
    · have hnode : Node d f as := hq
      have hkey := hs.nodes f as hnode
      have main : t ∈ (nodeRowT f as).subterms →
          (∃ k p, Row d k p ∧ t = ufRowT k p) ∨ (∃ f as, Node d f as ∧ t = nodeRowT f as) ∨
          (∃ f as, Marker d f as ∧ t = subRowT f as) ∨ ∃ k ∈ Keys d, t ∈ k.subterms := by
        intro h
        rw [Term.subterms_app] at h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact Or.inr (Or.inl ⟨f, as, hnode, rfl⟩)
        · obtain ⟨u, hu', hs'⟩ := Set.mem_iUnion₂.mp h
          rw [List.mem_append, List.mem_singleton] at hu'
          refine Or.inr (Or.inr (Or.inr ⟨.app f as, hkey, ?_⟩))
          rcases hu' with hu' | rfl
          · exact Term.arg_subterms hu' hs'
          · exact hs'
      exact hsub.elim main main
    · have hmark : Marker d f as := hq
      have hkey := hs.markers f as hmark
      have main : t ∈ (subRowT f as).subterms →
          (∃ k p, Row d k p ∧ t = ufRowT k p) ∨ (∃ f as, Node d f as ∧ t = nodeRowT f as) ∨
          (∃ f as, Marker d f as ∧ t = subRowT f as) ∨ ∃ k ∈ Keys d, t ∈ k.subterms := by
        intro h
        rw [Term.subterms_app] at h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact Or.inr (Or.inr (Or.inl ⟨f, as, hmark, rfl⟩))
        · obtain ⟨u, hu', hs'⟩ := Set.mem_iUnion₂.mp h
          exact Or.inr (Or.inr (Or.inr ⟨.app f as, hkey, Term.arg_subterms hu' hs'⟩))
      exact hsub.elim main main
    · exact Or.inr (Or.inr (Or.inr ⟨u, hu, hsub.elim id id⟩))
  · rintro (⟨k, p, hr, rfl⟩ | ⟨f, as, hn, rfl⟩ | ⟨f, as, hm, rfl⟩ | ⟨k, ⟨p, hr⟩, hsub⟩)
    · exact hr.mem_terms
    · exact hn.mem_terms
    · exact hm.mem_terms
    · exact ⟨_, hr, Or.inl (.arg (by simp) hsub)⟩

/-- A term that is a union-find row's own head is the row: no generated row sits inside a
source-shaped key, a node row or a marker. -/
theorem uf_mem_terms_iff {k p : Term} : ufRowT k p ∈ d.terms ↔ Row d k p := by
  constructor
  · intro h
    rcases hs.mem_terms_iff.mp h with ⟨k', p', hr, heq⟩ | ⟨f, as, _, heq⟩ | ⟨f, as, _, heq⟩ |
      ⟨k', hk', hsub⟩
    · obtain ⟨rfl, rfl⟩ := ufRowT_inj heq
      exact hr
    · exact ((nodeName_ne_ufName f) (Term.app.inj heq).1.symm).elim
    · exact ((subName_ne_ufName f) (Term.app.inj heq).1.symm).elim
    · exact (not_sourceName_ufName (Term.SourceShaped.head (hs.subterm_sourceShaped hk' hsub))).elim
  · exact Row.mem_terms

theorem node_mem_terms_iff {f : FnName} {as : List Term} :
    nodeRowT f as ∈ d.terms ↔ Node d f as := by
  constructor
  · intro h
    rcases hs.mem_terms_iff.mp h with ⟨k', p', _, heq⟩ | ⟨g, bs, hn, heq⟩ | ⟨g, bs, _, heq⟩ |
      ⟨k', hk', hsub⟩
    · exact ((nodeName_ne_ufName f) (Term.app.inj heq).1).elim
    · obtain ⟨rfl, rfl⟩ := nodeRowT_inj heq
      exact hn
    · exact ((subName_ne_nodeName g f) (Term.app.inj heq).1.symm).elim
    · exact (not_sourceName_nodeName f (Term.SourceShaped.head (hs.subterm_sourceShaped hk' hsub))).elim
  · exact Node.mem_terms

theorem marker_mem_terms_iff {f : FnName} {as : List Term} :
    subRowT f as ∈ d.terms ↔ Marker d f as := by
  constructor
  · intro h
    rcases hs.mem_terms_iff.mp h with ⟨k', p', _, heq⟩ | ⟨g, bs, _, heq⟩ | ⟨g, bs, hm, heq⟩ |
      ⟨k', hk', hsub⟩
    · exact ((subName_ne_ufName f) (Term.app.inj heq).1).elim
    · exact ((subName_ne_nodeName f g) (Term.app.inj heq).1).elim
    · obtain ⟨rfl, rfl⟩ := subRowT_inj heq
      exact hm
    · exact (not_sourceName_subName f (Term.SourceShaped.head (hs.subterm_sourceShaped hk' hsub))).elim
  · exact Marker.mem_terms

/-- A held application of a source name is a subterm of a key. -/
theorem app_mem_terms_iff {f : FnName} (hf : SourceName f) {ts : List Term} :
    Term.app f ts ∈ d.terms ↔ ∃ k ∈ Keys d, Term.app f ts ∈ k.subterms := by
  constructor
  · intro h
    rcases hs.mem_terms_iff.mp h with ⟨k', p', _, heq⟩ | ⟨g, bs, _, heq⟩ | ⟨g, bs, _, heq⟩ | h
    · exact (hf.ne_ufName (Term.app.inj heq).1).elim
    · exact (hf.ne_nodeName g (Term.app.inj heq).1).elim
    · exact (hf.ne_subName g (Term.app.inj heq).1).elim
    · exact h
  · rintro ⟨k, ⟨p, hr⟩, hsub⟩
    exact ⟨_, hr, Or.inl (.arg (by simp) hsub)⟩

end Shape

/-! ### Live rows -/

/-- At a diagonal state a term is live exactly when it is held and not subsumed. -/
theorem live_iff_of_diag {d : Database} (hd : d.Diag) {t : Term} :
    t ∈ d.live ↔ t ∈ d.terms ∧ ¬ (∃ f ts, t = Term.app f ts ∧ t ∈ d.subsumed) := by
  unfold Database.live
  simp only [Set.mem_setOf_eq, Cong.iff_eq_and_mem_of_diag hd, true_and]
  apply and_congr_right
  intro _
  apply not_congr
  constructor
  · rintro ⟨u, hu, hr⟩
    obtain ⟨f, as, bs, rfl, rfl, hc⟩ := hr
    rw [hc.eq_of_diag hd]
    exact ⟨f, bs, rfl, hu⟩
  · rintro ⟨f, ts, rfl, hs⟩
    refine ⟨_, hs, Database.SameRow.self_app ?_⟩
    exact Database.toCong (by assumption)

/-- An application is live exactly when it is held and not subsumed. -/
theorem app_live_iff {d : Database} (hd : d.Diag) {f : FnName} {ts : List Term} :
    Term.app f ts ∈ d.live ↔ Term.app f ts ∈ d.terms ∧ Term.app f ts ∉ d.subsumed := by
  rw [live_iff_of_diag hd]
  apply and_congr_right
  intro _
  constructor
  · exact fun h hs => h ⟨f, ts, rfl, hs⟩
  · rintro h ⟨g, us, heq, hs⟩
    exact h (heq ▸ hs)

/-- A literal is live exactly when it is held. -/
theorem lit_live_iff {d : Database} (hd : d.Diag) {l : Lit} :
    Term.lit l ∈ d.live ↔ Term.lit l ∈ d.terms := by
  rw [live_iff_of_diag hd]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rintro ⟨f, ts, heq, _⟩
    cases heq

/-- A live row is an asserted row that is not marked. -/
theorem edge_iff {d : Database} (hd : d.Diag) (hs : Shape d) {k p : Term} :
    Edge d k p ↔ Row d k p ∧ ufRowT k p ∉ d.subsumed := by
  unfold Edge
  rw [app_live_iff hd, hs.uf_mem_terms_iff]

theorem Edge.row {d : Database} (hd : d.Diag) (hs : Shape d) {k p : Term}
    (h : Edge d k p) : Row d k p := ((edge_iff hd hs).mp h).1

theorem Edge.of_row {d : Database} (hd : d.Diag) (hs : Shape d) {k p : Term} (hr : Row d k p)
    (hn : ufRowT k p ∉ d.subsumed) : Edge d k p := (edge_iff hd hs).mpr ⟨hr, hn⟩

/-- Live rows persist when rows grow and no new union-find row is marked. -/
theorem Edge.mono {d e : Database} (hd : d.Diag) (hsd : Shape d) (he : e.Diag) (hse : Shape e)
    (heqs : d.eqs ⊆ e.eqs) (hsub : ∀ k p, ufRowT k p ∈ e.subsumed → ufRowT k p ∈ d.subsumed)
    {k p : Term} (h : Edge d k p) : Edge e k p := by
  rw [edge_iff hd hsd] at h
  exact Edge.of_row he hse (h.1.mono heqs) (fun hs => h.2 (hsub k p hs))

/-- The live-row equations are among the row equations. -/
theorem liveView_subset_view {d : Database} (hd : d.Diag) (hs : Shape d) :
    (liveView d).eqs ⊆ (view d).eqs := fun _ hq => Edge.row hd hs hq

/-- Representatives of a diagonal state are all of its terms. -/
theorem mem_reps_of_diag {d : Database} (hd : d.Diag) {t : Term} (ht : t ∈ d.terms) :
    t ∈ d.reps := by
  rw [hd.reps_eq_terms]; exact ht

/-- A subsumed application is not live. -/
theorem not_live_of_subsumed {d : Database} {f : FnName} {ts : List Term}
    (hs : Term.app f ts ∈ d.subsumed) : Term.app f ts ∉ d.live := by
  intro hl
  exact hl.2 ⟨_, hs, Database.SameRow.self_app hl.1⟩

end Egglog.Congruence
