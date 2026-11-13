import EgglogSemantics.Slotted.Spec.Step
import EgglogSemantics.Impl.Interp

/-!
# Bounded evaluation of the slotted specification

The slotted closure relates infinitely many terms: every renaming of a known equation is
one. This module evaluates the specification over a finite **slot universe** `S` and a
finite **term universe** `U`: the renamings considered are the injections of a term's free
slots into `S`, the fresh bound names come from `S`, and the closure is the least relation on
`U × U` closed under the `SCong` rules so restricted. On a universe closed under subterms
and under renaming over `S` (`termUniverse`) this decides the checks of small programs.

What is proved: every result of `renameAll` is a result of the action (`renameAll_sound`),
and every two terms the bounded closure puts in one class are `SCong`-related
(`closure_sound`); so a check
the evaluator finds to hold through `=` patterns holds in the specification whenever the
universe is complete for the query's representatives. What is bounded: a pair the closure
does not relate, a slot it does not find redundant, and a check it finds to fail are
statements about the universe, not about the specification. The tests in
`Slotted/Tests/Examples.lean` say which kind each assertion is.
-/

namespace Egglog.Slotted.Bounded

/-! ### Injections and the action over a finite slot universe -/

/-- All injective assignments of the keys `A`, in order, to distinct values of `S`. -/
def injections {α β : Type} [DecidableEq β] : List α → List β → List (List (α × β))
  | [], _ => [[]]
  | a :: as, S => S.flatMap fun s => (injections as (S.erase s)).map fun ρ => (a, s) :: ρ

theorem mem_injections_fst {α β : Type} [DecidableEq β] :
    ∀ {A : List α} {S : List β} {ρ : List (α × β)}, ρ ∈ injections A S → ρ.map Prod.fst = A
  | [], _, ρ, h => by simp [injections] at h; simp [h]
  | a :: as, S, ρ, h => by
    simp only [injections, List.mem_flatMap, List.mem_map] at h
    obtain ⟨s, _, ρ', hρ', rfl⟩ := h
    simp [mem_injections_fst hρ']

theorem mem_injections_snd {α β : Type} [DecidableEq β] :
    ∀ {A : List α} {S : List β} {ρ : List (α × β)}, ρ ∈ injections A S →
      ∀ p ∈ ρ, p.2 ∈ S
  | [], _, ρ, h => by simp [injections] at h; simp [h]
  | a :: as, S, ρ, h => by
    simp only [injections, List.mem_flatMap, List.mem_map] at h
    obtain ⟨s, hs, ρ', hρ', rfl⟩ := h
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hs
    · exact List.mem_of_mem_erase (mem_injections_snd hρ' p hp)

theorem mem_injections_snd_nodup {α β : Type} [DecidableEq β] :
    ∀ {A : List α} {S : List β} {ρ : List (α × β)}, S.Nodup → ρ ∈ injections A S →
      (ρ.map Prod.snd).Nodup
  | [], _, ρ, _, h => by simp [injections] at h; simp [h]
  | a :: as, S, ρ, hS, h => by
    simp only [injections, List.mem_flatMap, List.mem_map] at h
    obtain ⟨s, hs, ρ', hρ', rfl⟩ := h
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨fun ⟨p, hp, hps⟩ => ?_, mem_injections_snd_nodup (hS.erase s) hρ'⟩
    have := mem_injections_snd hρ' p hp
    rw [hps] at this
    exact (List.Nodup.not_mem_erase hS) this

/-- An injection of distinct keys into a duplicate-free universe is a partial injection. -/
theorem wf_of_injections {A : List Slot} {S : List Slot} {ρ : Renaming} (hA : A.Nodup)
    (hS : S.Nodup) (h : ρ ∈ injections A S) : ρ.WF := by
  have h1 : (ρ.map Prod.fst).Nodup := mem_injections_fst h ▸ hA
  have h2 := mem_injections_snd_nodup hS h
  refine ⟨fun p hp q hq hpq => ?_, fun p hp q hq hpq => ?_⟩
  · exact congrArg Prod.snd (List.inj_on_of_nodup_map h1 hp hq hpq)
  · exact congrArg Prod.fst (List.inj_on_of_nodup_map h2 hp hq hpq)

/-- The injection's keys are its domain. -/
theorem covers_of_injections {A : List Slot} {S : List Slot} {ρ : Renaming}
    (h : ρ ∈ injections A S) : ρ.Covers A := by
  intro s hs
  unfold Renaming.dom
  rw [mem_injections_fst h]
  exact hs

/-- The product of per-position choices. -/
def product : List (List Term) → List (List Term)
  | [] => [[]]
  | c :: cs => c.flatMap fun a => (product cs).map fun as => a :: as

/-- The names of `S` that are fresh for `t` and `m`. -/
def freshNames (S : List Slot) (t : Term) (m : Renaming) : List Slot :=
  S.filter fun r => decide (r ∉ allSlots t ∧ r ∉ m.dom ∧ r ∉ m.img)

mutual

/-- Every result of `m * t` whose fresh bound names come from `S`. -/
def renameAll (bind : Binders) (S : List Slot) (m : Renaming) : Term → List Term
  | .lit l => [.lit l]
  | .app f args =>
    if isSlotApp f args then
      match m.apply f with
      | some s' => [Term.slot s']
      | none => []
    else
      (injections (bind.bindingPositions f) (freshNames S (.app f args) m)).flatMap fun ρ =>
        (renameAllArgs bind S (plans bind m f args ρ) args).map (Term.app f)

/-- `renameAll` over the arguments, following the plans. -/
def renameAllArgs (bind : Binders) (S : List Slot) : List Plan → List Term → List (List Term)
  | [], [] => [[]]
  | .fresh r :: ps, _ :: as => (renameAllArgs bind S ps as).map fun as' => Term.slot r :: as'
  | .child m :: ps, a :: as =>
    (renameAll bind S m a).flatMap fun a' => (renameAllArgs bind S ps as).map fun as' => a' :: as'
  | _, _ => []

end

/-- Whether `f` has binding position `j`, as a membership. -/
theorem isBinding_iff (bind : Binders) (f : FnName) (j : Nat) :
    bind.isBinding f j = true ↔ j ∈ (bind f).map Prod.fst := by
  unfold Binders.isBinding
  rw [List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, by simpa using h⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, by simpa using h⟩

/-- A choice from `injections` over the fresh names is a `Fresh` choice. -/
theorem fresh_of_injections {bind : Binders} {S : List Slot} {m : Renaming} {f : FnName}
    {args : List Term} {ρ : FreshChoice} (hS : S.Nodup)
    (h : ρ ∈ injections (bind.bindingPositions f) (freshNames S (.app f args) m)) :
    Fresh bind f args m ρ := by
  have hfst := mem_injections_fst h
  refine ⟨fun j => ?_, ?_, mem_injections_snd_nodup (hS.filter _) h, fun r hr => ?_⟩
  · rw [hfst, isBinding_iff, Binders.bindingPositions, List.mem_dedup]
  · rw [hfst]; exact List.nodup_dedup _
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    have := mem_injections_snd h p hp
    simp only [freshNames, List.mem_filter, decide_eq_true_eq] at this
    exact this.2

mutual

/-- Every result `renameAll` lists is a result of the action. -/
theorem renameAll_sound (bind : Binders) (S : List Slot) (hS : S.Nodup) (m : Renaming) :
    ∀ (t t' : Term), t' ∈ renameAll bind S m t → Renames bind m t t'
  | .lit l, t', h => by
    simp only [renameAll, List.mem_singleton] at h
    subst h
    exact .lit
  | .app f args, t', h => by
    unfold renameAll at h
    split at h
    · rename_i hslot
      split at h
      · rename_i s' happ
        simp only [List.mem_singleton] at h
        subst h
        have hargs : args = [] := by
          simp only [isSlotApp, Bool.and_eq_true, List.isEmpty_iff] at hslot
          exact hslot.2
        subst hargs
        exact .slot (by simpa [isSlotApp] using hslot) happ
      · simp at h
    · rename_i hslot
      obtain ⟨ρ, hρ, h⟩ := List.mem_flatMap.mp h
      obtain ⟨args', hargs', rfl⟩ := List.mem_map.mp h
      exact .app (by simpa using hslot) (fresh_of_injections hS hρ)
        (renameAllArgs_sound bind S hS _ args args' hargs')

theorem renameAllArgs_sound (bind : Binders) (S : List Slot) (hS : S.Nodup) :
    ∀ (ps : List Plan) (as as' : List Term), as' ∈ renameAllArgs bind S ps as →
      RenamesList bind ps as as'
  | [], [], as', h => by
    simp only [renameAllArgs, List.mem_singleton] at h
    subst h
    exact .nil
  | .fresh r :: ps, a :: as, as', h => by
    simp only [renameAllArgs, List.mem_map] at h
    obtain ⟨bs, hbs, rfl⟩ := h
    exact .fresh (renameAllArgs_sound bind S hS ps as bs hbs)
  | .child m :: ps, a :: as, as', h => by
    simp only [renameAllArgs, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a', ha', bs, hbs, rfl⟩ := h
    exact .child (renameAll_sound bind S hS m a a' ha') (renameAllArgs_sound bind S hS ps as bs hbs)
  | [], _ :: _, _, h => by simp [renameAllArgs] at h
  | .fresh _ :: _, [], _, h => by simp [renameAllArgs] at h
  | .child _ :: _, [], _, h => by simp [renameAllArgs] at h

end

/-! ### The bounded closure, as a partition -/

/-- The classes of the terms known to exist: disjoint lists, one per class of the bounded
closure. Symmetry and transitivity are implicit, so a round only adds terms and merges
classes. -/
abbrev Classes := List (List Term)

namespace Classes

/-- The class holding `t`, if any. -/
def classOf (cs : Classes) (t : Term) : Option (List Term) := cs.find? fun cls => t ∈ cls

/-- Whether `t` is known to exist. -/
def has (cs : Classes) (t : Term) : Bool := cs.any fun cls => t ∈ cls

/-- Whether `a` and `b` share a class: the bounded `SCong`. -/
def cong (cs : Classes) (a b : Term) : Bool := cs.any fun cls => a ∈ cls ∧ b ∈ cls

/-- Every term in some class. -/
def terms (cs : Classes) : List Term := cs.flatMap id

/-- Add `t` as a class of its own unless it is present. -/
def addRefl (cs : Classes) (t : Term) : Classes := if cs.has t then cs else [t] :: cs

/-- Merge the classes of `a` and `b`; nothing when they share one or either is absent. -/
def merge (cs : Classes) (a b : Term) : Classes :=
  if cs.cong a b then cs else
    match cs.classOf a, cs.classOf b with
    | some ca, some cb => (ca ++ cb) :: cs.filter fun cls => cls ≠ ca ∧ cls ≠ cb
    | _, _ => cs

/-- Record `a ∼ b`: both exist, and they share a class. -/
def assert (cs : Classes) (a b : Term) : Classes :=
  if cs.cong a b then cs else ((cs.addRefl a).addRefl b).merge a b

def assertAll (cs : Classes) (ps : List (Term × Term)) : Classes :=
  ps.foldl (fun cs p => cs.assert p.1 p.2) cs

/-- Every class of `c` sits inside a class of `d`. -/
def le (c d : Classes) : Bool := c.all fun cls => cls.all fun a => cls.all fun b => d.cong a b

/-- Every two members of a class are `SCong`-related. -/
def Sound (bind : Binders) (db : Database) (cs : Classes) : Prop :=
  ∀ cls ∈ cs, ∀ a ∈ cls, ∀ b ∈ cls, SCong bind db a b

theorem cong_sound {bind : Binders} {db : Database} {cs : Classes} (h : Sound bind db cs)
    {a b : Term} (hab : cs.cong a b = true) : SCong bind db a b := by
  simp only [cong, List.any_eq_true, decide_eq_true_eq] at hab
  obtain ⟨cls, hcls, ha, hb⟩ := hab
  exact h cls hcls a ha b hb

theorem addRefl_sound {bind : Binders} {db : Database} {cs : Classes} (h : Sound bind db cs)
    {t : Term} (ht : SCong bind db t t) : Sound bind db (cs.addRefl t) := by
  unfold addRefl
  split
  · exact h
  · intro cls hcls a ha b hb
    rcases List.mem_cons.mp hcls with rfl | hcls
    · simp only [List.mem_singleton] at ha hb
      subst ha
      subst hb
      exact ht
    · exact h cls hcls a ha b hb

theorem merge_sound {bind : Binders} {db : Database} {cs : Classes} (h : Sound bind db cs)
    {a b : Term} (hab : SCong bind db a b) : Sound bind db (cs.merge a b) := by
  unfold merge
  split
  · exact h
  · split
    · rename_i ca cb hca hcb
      have hca' : ca ∈ cs := List.mem_of_find?_eq_some hca
      have hcb' : cb ∈ cs := List.mem_of_find?_eq_some hcb
      have haca : a ∈ ca := by simpa using List.find?_some hca
      have hbcb : b ∈ cb := by simpa using List.find?_some hcb
      intro cls hcls x hx y hy
      rcases List.mem_cons.mp hcls with rfl | hcls
      · rcases List.mem_append.mp hx with hx | hx <;> rcases List.mem_append.mp hy with hy | hy
        · exact h ca hca' x hx y hy
        · exact .trans (h ca hca' x hx a haca) (.trans hab (h cb hcb' b hbcb y hy))
        · exact .trans (h cb hcb' x hx b hbcb) (.trans (.symm hab) (h ca hca' a haca y hy))
        · exact h cb hcb' x hx y hy
      · exact h cls (List.mem_of_mem_filter hcls) x hx y hy
    · exact h

theorem assert_sound {bind : Binders} {db : Database} {cs : Classes} (h : Sound bind db cs)
    {a b : Term} (hab : SCong bind db a b) : Sound bind db (cs.assert a b) := by
  unfold assert
  split
  · exact h
  · exact merge_sound
      (addRefl_sound (addRefl_sound h (.trans hab (.symm hab))) (.trans (.symm hab) hab)) hab

theorem assertAll_sound {bind : Binders} {db : Database} {ps : List (Term × Term)} :
    ∀ {cs : Classes}, Sound bind db cs → (∀ p ∈ ps, SCong bind db p.1 p.2) →
      Sound bind db (cs.assertAll ps) := by
  induction ps with
  | nil => intro cs h _; exact h
  | cons p ps ih =>
    intro cs h hps
    show Sound bind db ((cs.assert p.1 p.2).assertAll ps)
    exact ih (assert_sound h (hps p List.mem_cons_self)) fun q hq =>
      hps q (List.mem_cons_of_mem _ hq)

end Classes

/-- Positionwise congruence under `cs`: binding positions agree, term children share a
class. -/
def congrArgsB (bind : Binders) (cs : Classes) (f : FnName) :
    Nat → List Term → List Term → Bool
  | _, [], [] => true
  | k, a :: as, b :: bs =>
    (if bind.isBinding f k then a == b else cs.cong a b) && congrArgsB bind cs f (k + 1) as bs
  | _, _, _ => false

/-- The injections of the free slots of a pair into `S`: the renamings the `Rename` rule is
applied with. Any renaming defined on more slots gives a subset of their results. -/
def pairRenamings (bind : Binders) (S : List Slot) (p : Term × Term) : List Renaming :=
  injections (slots bind p.1 ∪ slots bind p.2).dedup S

/-- The facts one round derives from the classes: reflexivity of the slot terms of `U`,
children of existing applications, congruent spellings in `U`, and renamings over `S` of the
pairs of a class's first member with each member; transitivity in the partition supplies the
renamings of the other pairs under the same renaming. -/
def facts (bind : Binders) (S : List Slot) (U : List Term) (cs : Classes) :
    List (Term × Term) :=
  (U.filterMap fun t => if t.isSlot then some (t, t) else none) ++
  (cs.flatMap fun cls => cls.flatMap fun t =>
    match t with
    | .app _ as => as.map fun s => (s, s)
    | _ => []) ++
  (cs.flatMap fun cls => cls.flatMap fun t =>
    match t with
    | .app f as => U.filterMap fun u =>
        match u with
        | .app g bs =>
          if f = g then (if congrArgsB bind cs f 0 as bs then some (t, u) else none) else none
        | _ => none
    | _ => []) ++
  (cs.flatMap fun cls =>
    match cls with
    | [] => []
    | t :: _ => cls.flatMap fun u =>
      (pairRenamings bind S (t, u)).flatMap fun m =>
        (renameAll bind S m t).flatMap fun t' => (renameAll bind S m u).map fun u' => (t', u'))

/-- One round: every fact asserted. -/
def step (bind : Binders) (S : List Slot) (U : List Term) (cs : Classes) : Classes :=
  cs.assertAll (facts bind S U cs)

/-- Rounds until one changes neither the number of classes nor the number of terms, which is
when it asserted nothing new, within the fuel. -/
def closure (bind : Binders) (S : List Slot) (U : List Term) : Nat → Classes → Classes
  | 0, cs => cs
  | n + 1, cs =>
    let cs' := step bind S U cs
    if cs'.length = cs.length ∧ cs'.terms.length = cs.terms.length then cs
    else closure bind S U n cs'

/-- The bounded `SCong`: the closure of the stored equations over `U`. On a universe closed
under subterms and renaming over `S`, every term a round adds is in `U`, so every changing
round adds a term of `U` or merges two classes and the fuel suffices. -/
def scong (bind : Binders) (S : List Slot) (U : List Term) (eqs : List (Term × Term)) :
    Classes :=
  closure bind S U (2 * U.length + 2) (Classes.assertAll [] eqs)

/-- The state a list of equations and subsumed rows denotes. -/
def toDatabase (eqs : List (Term × Term)) (subsumed : List Term) : Database :=
  ⟨{p | p ∈ eqs}, {t | t ∈ subsumed}⟩

theorem slot_of_isSlot : ∀ {t : Term}, t.isSlot = true →
    ∃ s, isSlotName s = true ∧ t = Term.slot s
  | .lit _, h => by simp [Term.isSlot, Term.slotName?] at h
  | .app f [], h => by
    simp only [Term.isSlot, Term.slotName?] at h
    split at h
    · rename_i hs
      exact ⟨f, hs, rfl⟩
    · simp at h
  | .app _ (_ :: _), h => by simp [Term.isSlot, Term.slotName?] at h

theorem congrArgsB_sound {bind : Binders} {db : Database} {cs : Classes}
    (h : Classes.Sound bind db cs) (f : FnName) :
    ∀ (k : Nat) (as bs : List Term), congrArgsB bind cs f k as bs = true →
      SCongArgs bind db f k as bs
  | _, [], [], _ => .nil
  | k, a :: as, b :: bs, hc => by
    simp only [congrArgsB, Bool.and_eq_true] at hc
    refine .cons (fun hb => ?_) (fun hb => ?_) (congrArgsB_sound h f (k + 1) as bs hc.2)
    · have := hc.1; rw [if_pos hb] at this; exact eq_of_beq this
    · have := hc.1; rw [if_neg (by simp [hb])] at this; exact Classes.cong_sound h this
  | _, [], _ :: _, hc => by simp [congrArgsB] at hc
  | _, _ :: _, [], hc => by simp [congrArgsB] at hc

/-- Every fact a round derives holds. -/
theorem facts_sound {bind : Binders} {db : Database} {S : List Slot} (hS : S.Nodup)
    {U : List Term} {cs : Classes} (h : Classes.Sound bind db cs) :
    ∀ q ∈ facts bind S U cs, SCong bind db q.1 q.2 := by
  intro q hq
  simp only [facts, List.mem_append] at hq
  rcases hq with ((hq | hq) | hq) | hq
  · obtain ⟨t, _, ht⟩ := List.mem_filterMap.mp hq
    split at ht
    · rename_i hslot
      simp only [Option.some.injEq] at ht
      subst ht
      obtain ⟨s, hs, rfl⟩ := slot_of_isSlot hslot
      exact .slot hs
    · simp at ht
  · obtain ⟨cls, hcls, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨t, ht, hq⟩ := List.mem_flatMap.mp hq
    have htt := h cls hcls t ht t ht
    split at hq
    · rename_i f as
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
      exact .child htt hs
    · simp at hq
  · obtain ⟨cls, hcls, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨t, ht, hq⟩ := List.mem_flatMap.mp hq
    have htt := h cls hcls t ht t ht
    split at hq
    · rename_i f as
      obtain ⟨u, _hu, hu⟩ := List.mem_filterMap.mp hq
      split at hu
      · rename_i g bs
        split at hu
        · rename_i hfg
          subst hfg
          split at hu
          · rename_i hc
            simp only [Option.some.injEq] at hu
            subst hu
            exact .congr htt (congrArgsB_sound h f 0 as bs hc)
          · simp at hu
        · simp at hu
      · simp at hu
    · simp at hq
  · obtain ⟨cls, hcls, hq⟩ := List.mem_flatMap.mp hq
    split at hq
    · simp at hq
    · rename_i t rest
      obtain ⟨u, hu, hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨m, hm, hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨t', ht', hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hq
      have ht : t ∈ t :: rest := List.mem_cons_self
      have hwf : m.WF := wf_of_injections (List.nodup_dedup _) hS hm
      have hcov := covers_of_injections hm
      refine .rename (h _ hcls t ht u hu) hwf (fun s hs => hcov s ?_) (fun s hs => hcov s ?_)
        (renameAll_sound bind S hS m t t' ht') (renameAll_sound bind S hS m u u' hu')
      · exact List.mem_dedup.mpr (List.mem_union_left hs _)
      · exact List.mem_dedup.mpr (List.mem_union_right _ hs)

theorem step_sound {bind : Binders} {db : Database} {S : List Slot} (hS : S.Nodup)
    {U : List Term} {cs : Classes} (h : Classes.Sound bind db cs) :
    Classes.Sound bind db (step bind S U cs) :=
  Classes.assertAll_sound h (facts_sound hS h)

/-- Every two terms the bounded closure puts in one class are `SCong`-related. -/
theorem closure_sound {bind : Binders} {db : Database} {S : List Slot} (hS : S.Nodup)
    {U : List Term} : ∀ (n : Nat) {cs : Classes}, Classes.Sound bind db cs →
      Classes.Sound bind db (closure bind S U n cs)
  | 0, _, h => h
  | n + 1, cs, h => by
    unfold closure
    try simp only []
    split
    · exact h
    · exact closure_sound hS n (step_sound hS h)

/-- The bounded `SCong` of a state is sound for that state. -/
theorem scong_sound {bind : Binders} {S : List Slot} (hS : S.Nodup) {U : List Term}
    {eqs : List (Term × Term)} {subsumed : List Term} :
    Classes.Sound bind (toDatabase eqs subsumed) (scong bind S U eqs) :=
  closure_sound hS _ (Classes.assertAll_sound (fun _ h => by simp at h) fun p hp => .direct hp)

/-! ### Universes -/

/-- The subterm closure of a term list, each term once. -/
def subtermClosure (ts : List Term) : List Term := (ts.flatMap Term.subtermList).dedup

/-- Close `U` under renaming over `S`: every result of every injection of a term's free slots
into `S`, with its subterms, until nothing is new. Terminates because every result uses
names from `S` and the finitely many shapes of `U`, but the measure is not written down. -/
partial def closeUnderRenaming (bind : Binders) (S : List Slot) (U : List Term) : List Term :=
  let new := ((U.flatMap fun t => (injections (slots bind t).dedup S).flatMap fun m =>
    (renameAll bind S m t).flatMap Term.subtermList).filter (· ∉ U)).dedup
  if new.isEmpty then U else closeUnderRenaming bind S (U ++ new)

/-- The term universe generated by `seeds` over the slot universe `S`. -/
def termUniverse (bind : Binders) (S : List Slot) (seeds : List Term) : List Term :=
  closeUnderRenaming bind S (subtermClosure seeds)

/-! ### A closed state and its readings -/

/-- A state with its bounded closure. `reps'` and the live terms are computed once, by
`Closure.make`. -/
structure Closure where
  bind : Binders
  S : List Slot
  U : List Term
  /-- The bounded `SCong`. -/
  classes : Classes
  /-- The stored terms, `terms(E)`. -/
  terms : List Term
  subsumed : List Term
  /-- `reps'`: every renaming over `S` of a least stored spelling. -/
  reps' : List Term
  /-- The terms of `U` in `live'`. -/
  liveTerms : List Term

namespace Closure

def cong (c : Closure) (a b : Term) : Bool := c.classes.cong a b

/-- The least stored spelling of each class: `sreps`, read off the classes. -/
def srepsOf (cs : Classes) (terms : List Term) : List Term :=
  terms.filter fun t => terms.all fun s => !cs.cong s t || !Term.blt s t

/-- Every renaming of a term over `S`, from the injections of its free slots. -/
def renamingsOf (bind : Binders) (S : List Slot) (t : Term) : List Term :=
  (injections (slots bind t).dedup S).flatMap fun m => renameAll bind S m t

/-- `sreps`. -/
def sreps (c : Closure) : List Term := srepsOf c.classes c.terms

/-- The subsumed rows closed under renaming: `X'`. -/
def subsumed' (c : Closure) : List Term := (c.subsumed.flatMap (renamingsOf c.bind c.S)).dedup

def sameRow' (c : Closure) : Term → Term → Bool
  | .app f as, .app g bs => f == g && congrArgsB c.bind c.classes f 0 as bs
  | _, _ => false

/-- `live'`. -/
def live' (c : Closure) (t : Term) : Bool :=
  c.cong t t && !(c.subsumed'.any fun u => c.sameRow' t u)

/-- `Redundant`, with the fresh name drawn from `S`. -/
def redundant (c : Closure) (t : Term) (s : Slot) : Bool :=
  c.S.any fun r => decide (r ∉ allSlots t) &&
    (renameAll c.bind c.S ((Renaming.id (slots c.bind t)).update s r) t).any fun t' => c.cong t t'

/-- `FS`: the free slots not found redundant. -/
def liveSlots (c : Closure) (t : Term) : List Slot :=
  (slots c.bind t).filter fun s => !c.redundant t s

/-- `RenamingEq`, over the injections into `S`. -/
def renamingEq (c : Closure) (t u : Term) : Bool :=
  (injections (slots c.bind t).dedup c.S).any fun m =>
    (renameAll c.bind c.S m t).any fun t' => c.cong t' u

/-! #### The reference pattern evaluator -/

mutual

/-- `SExpr.Matches`, evaluated. -/
def exprB (c : Closure) (σ : Env) : Expr → Bool
  | .lit l => c.live' (.lit l)
  | .var v => (Env.lookup v σ).isSome
  | .app f args =>
    c.exprsB σ args &&
      match Expr.evalList args σ with
      | some ts => c.live' (.app f ts)
      | none => false
  | .min a b => c.exprB σ a && c.exprB σ b

def exprsB (c : Closure) (σ : Env) : List Expr → Bool
  | [] => true
  | e :: es => c.exprB σ e && c.exprsB σ es

end

/-- The slot a slot argument denotes under `σ`, if it is one. -/
def slotArg (σ : Env) (x : Expr) : Option Slot :=
  match x.eval σ with
  | some (.app s []) => if isSlotName s then some s else none
  | _ => none

/-- `SMatches`, evaluated. -/
def patternB (c : Closure) (σ : Env) : Pattern → Bool
  | .expr (.app "free" (x :: es)) =>
    match slotArg σ x, Expr.evalList es σ with
    | some s, some ts => c.exprsB σ es && ts.any fun t => decide (s ∈ c.liveSlots t)
    | _, _ => false
  | .expr (.app "not-free" (x :: es)) =>
    match slotArg σ x, Expr.evalList es σ with
    | some s, some ts => c.exprsB σ es && ts.all fun t => decide (s ∉ c.liveSlots t)
    | _, _ => false
  | .expr (.app "free-names-are" (e :: xs)) =>
    match e.eval σ, xs.mapM (slotArg σ) with
    | some t, some ss =>
      c.exprB σ e && (c.liveSlots t).all (· ∈ ss) && ss.all (· ∈ c.liveSlots t)
    | _, _ => false
  | .expr (.app "renaming-=" [a, b]) =>
    match a.eval σ, b.eval σ with
    | some ta, some tb => c.exprB σ a && c.exprB σ b && c.renamingEq ta tb
    | _, _ => false
  | .expr (.app "renaming-!=" [a, b]) =>
    match a.eval σ, b.eval σ with
    | some ta, some tb => c.exprB σ a && c.exprB σ b && !c.renamingEq ta tb
    | _, _ => false
  | .expr e => !e.isBuiltin && c.exprB σ e
  | .eq a b =>
    match a.eval σ, b.eval σ with
    | some ta, some tb => c.exprB σ a && c.exprB σ b && c.cong ta tb
    | _, _ => false
  | .ne a b =>
    match a.eval σ, b.eval σ with
    | some ta, some tb => c.exprB σ a && c.exprB σ b && !c.cong ta tb
    | _, _ => false

/-- `ValidEnv'`, evaluated: literal slots to themselves, ordinary variables to `reps'`. -/
def validEnvB (c : Closure) (vars : List Var) (σ : Env) : Bool :=
  (Env.dom σ).isPerm vars &&
  σ.all (fun b => if isSlotVar b.1 then b.2 == Term.slot b.1 else decide (b.2 ∈ c.reps'))

/-! #### Candidate substitutions

Enumerating every assignment of the variables is far too slow even here, so candidates are
read off the universe: an application pattern is unified against every live term, a bare
variable ranges over `reps'`, a literal slot denotes itself. The candidates are then filtered by
`validEnvB` and `patternB`, so what is found is exactly what the reference evaluator accepts
among the candidates, and the soundness of a match rests on the evaluator alone. -/

/-- Extend `σ` so that `e` evaluates to `t`, syntactically. -/
def unify (σ : Env) : Expr → Term → Option Env
  | .var v, t =>
    match Env.lookup v σ with
    | some t' => if t' = t then some σ else none
    | none =>
      if isSlotVar v && t != Term.slot v then none else some ((v, t) :: σ)
  | .lit l, .lit l' => if l = l' then some σ else none
  | .app f args, .app g ts => if f = g then unifyList σ args ts else none
  | _, _ => none
where
  unifyList (σ : Env) : List Expr → List Term → Option Env
    | [], [] => some σ
    | e :: es, t :: ts => (unify σ e t).bind fun σ' => unifyList σ' es ts
    | _, _ => none

/-- The terms an expression may denote: the live terms for an application, `reps'` for a
variable, the literal for a literal. -/
def domain (c : Closure) (σ : Env) : Expr → List Term
  | .var v =>
    match Env.lookup v σ with
    | some t => [t]
    | none => if isSlotVar v then [Term.slot v] else c.reps'
  | .lit l => [.lit l]
  | .app _ _ => c.liveTerms
  | .min _ _ => []

/-- Extend `σ` by matching `e` against its domain. -/
def extend (c : Closure) (σ : Env) (e : Expr) : List Env :=
  (c.domain σ e).filterMap fun t => unify σ e t

/-- Extend `σ` by matching a list of expressions in turn. -/
def extendAll (c : Closure) (σ : Env) : List Expr → List Env
  | [] => [σ]
  | e :: es => (c.extend σ e).flatMap fun σ' => c.extendAll σ' es

/-- The expressions a pattern binds variables through. -/
def patternExprs : Pattern → List Expr
  | .expr (.app f args) => if (Builtin.ofName f).isSome then args else [.app f args]
  | .expr e => [e]
  | .eq a b => [a, b]
  | .ne a b => [a, b]

/-- Candidate substitutions for a query: the patterns that bind, in order, built-in
predicates last. -/
def candidates (c : Closure) (q : Query) : List Env :=
  let (builtins, others) := q.partition fun p => match p with
    | .expr e => e.isBuiltin
    | _ => false
  (others ++ builtins).foldl (fun σs p => σs.flatMap fun σ => c.extendAll σ (patternExprs p)) [[]]

/-- `SQueryMatches`, bounded: the candidates the reference evaluator accepts. -/
def matchQuery (c : Closure) (q : Query) : List Env :=
  (c.candidates q).filter fun σ => c.validEnvB q.vars σ && q.all (c.patternB σ)

/-- Every assignment of ordinary variables to `reps'`, with fixed literal slots.
Exhaustive, so only used to seed the universe. -/
def assignments (c : Closure) (vars : List Var) : List Env :=
  let svars := vars.filter isSlotVar
  let tvars := vars.filter fun v => !isSlotVar v
  (Egglog.assignments c.reps' tvars).map fun σ =>
    (svars.map fun v => (v, Term.slot v)) ++ σ

/-- The terms a query's expressions evaluate to under every assignment: what the universe
must hold for the query to be decided. -/
def instances (c : Closure) (q : Query) : List Term :=
  ((c.assignments q.vars).flatMap fun σ => q.flatMap fun p =>
    (patternExprs p).filterMap fun e => e.eval σ).dedup

/-- A closure with its caches. -/
def make (bind : Binders) (S : List Slot) (U : List Term) (classes : Classes)
    (terms subsumed : List Term) : Closure :=
  let c : Closure := { bind, S, U, classes, terms, subsumed, reps' := [], liveTerms := [] }
  { c with reps' := ((srepsOf classes terms).flatMap (renamingsOf bind S)).dedup,
           liveTerms := U.filter c.live' }

end Closure

/-! ### States, rounds, and schedules -/

/-- A finite state: the stored equations and subsumed rows. -/
structure State where
  eqs : List (Term × Term) := []
  subsumed : List Term := []

namespace State

def terms (st : State) : List Term :=
  subtermClosure (st.eqs.flatMap fun p => [p.1, p.2])

/-- The closure of the state over the universe its terms and `extra` generate. -/
def close (bind : Binders) (S : List Slot) (st : State) (extra : List Term) : Closure :=
  let U := termUniverse bind S (st.terms ++ extra)
  Closure.make bind S U (scong bind S U st.eqs) st.terms st.subsumed

/-- The closure after seeding the universe with a query's instances, so the query is decided
on it. -/
def closeFor (bind : Binders) (S : List Slot) (st : State) (q : Query) : Closure :=
  st.close bind S ((st.close bind S []).instances q)

/-- `SQueryHolds`, bounded. -/
def holds (bind : Binders) (S : List Slot) (st : State) (q : Query) : Bool :=
  !((st.closeFor bind S q).matchQuery q).isEmpty

end State

/-- The equations and subsumed rows one action writes; `none` where it is stuck. -/
def actionWrites (σ : Env) : Action → Option (List (Term × Term) × List Term)
  | .expr e => (e.eval σ).map fun t => ([(t, t)], [])
  | .union a b =>
    (a.eval σ).bind fun ta => (b.eval σ).bind fun tb =>
      if ta.isLit || tb.isLit then none else some ([(ta, tb)], [])
  | .subsume f es => (Expr.evalList es σ).map fun ts => ([(.app f ts, .app f ts)], [.app f ts])

def actionsWrites (σ : Env) : List Action → Option (List (Term × Term) × List Term)
  | [] => some ([], [])
  | a :: as => (actionWrites σ a).bind fun w => (actionsWrites σ as).map fun ws =>
      (w.1 ++ ws.1, w.2 ++ ws.2)

/-- Every assignment of a rule's action-only slot variables to distinct slots of `S` that no
value of `σ` mentions. -/
def freshChoices (S : List Slot) (r : Rule) (σ : Env) : List Env :=
  let used := σ.flatMap fun b => allSlots b.2
  (injections (freshVars r) (S.filter (· ∉ used))).map fun ν => ν.map fun p => (p.1, Term.slot p.2)

/-- `SRunRules`, bounded: every match of every rule under every fresh choice. -/
def round (bind : Binders) (S : List Slot) (rs : List Rule) (st : State) : State :=
  let c := st.close bind S []
  let writes := rs.flatMap fun r => (c.matchQuery r.query).flatMap fun σ =>
    (freshChoices S r σ).filterMap fun ν => actionsWrites (ν ++ σ) r.actions
  { eqs := (st.eqs ++ writes.flatMap Prod.fst).dedup,
    subsumed := (st.subsumed ++ writes.flatMap Prod.snd).dedup }

/-- `SameMeaning'`, bounded: the same closure and the same live terms. -/
def sameMeaning (c d : Closure) : Bool :=
  c.classes.le d.classes && d.classes.le c.classes &&
    c.liveTerms.all d.live' && d.liveTerms.all c.live'

/-- `SReach`, bounded, with fuel for saturation. -/
def exec (bind : Binders) (S : List Slot) (fuel : Nat) (st : State) : Schedule → Option State
  | .run rs => some (round bind S rs st)
  | .seq S₁ S₂ => (exec bind S fuel st S₁).bind fun st' => exec bind S fuel st' S₂
  | .saturate body => saturate fuel st body
where
  saturate : Nat → State → Schedule → Option State
    | 0, _, _ => none
    | n + 1, st, body =>
      (exec bind S fuel st body).bind fun st' =>
        if sameMeaning (st.close bind S []) (st'.close bind S []) then some st'
        else saturate n st' body

/-- The outcome of a slotted program, bounded: `some true` when the final check holds. -/
def observe (S : List Slot) (P : Slotted.Program) (fuel : Nat := 16) : Option Bool :=
  (exec P.binders S fuel {} P.plain.schedule).map fun st =>
    st.holds P.binders S P.plain.check

end Egglog.Slotted.Bounded
