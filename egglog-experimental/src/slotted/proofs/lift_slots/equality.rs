//! Lift encoded equality steps and maintenance rules.

use super::*;

/// A failed candidate match carries only the conflicting nodes, so rejected
/// candidates never render (potentially very large) terms for diagnostics.
pub(super) enum SlotMismatch {
    Terms(TermId, TermId),
    Conflict(i64, i64, i64),
}

impl SlotLifter<'_> {
    /// Record that `proof` proves `lhs = …`, so `lhs`'s reflexivity is available.
    pub(super) fn note(&mut self, proof: ViewId) -> ViewId {
        let p = self.out.edge(proof).clone();
        self.known.entry(p.lhs).or_insert(proof);
        if p.rhs != p.lhs {
            let s = self.out.sym(proof);
            self.known.entry(p.rhs).or_insert(s);
        }
        proof
    }

    /// `t = t`: by fiat for a term the program built, else from any proof
    /// stating something about it.
    pub(super) fn reflexive(&mut self, t: TermId) -> LiftResult<ViewId> {
        if self.program.is_built(&self.out.term_dag, t) {
            return Ok(self.out.fiat(t, t));
        }
        if let Some(&p) = self.known.get(&t) {
            let s = self.out.sym(p);
            return self.out.trans(p, s).map_err(|e| e.to_string());
        }
        // a term the same as a built or known one up to a renaming of its slots:
        // its reflexivity follows by equivariance of the known equality
        let candidates: Vec<TermId> = self
            .program
            .built_terms(&self.out.term_dag)
            .into_iter()
            .chain(self.known.keys().copied())
            .collect();
        for other in candidates {
            let mut pairs = BTreeMap::new();
            if other == t || self.match_slots(other, t, &mut pairs).is_err() {
                continue;
            }
            let Some(sigma) = Renaming::completing(pairs.iter().map(|(k, v)| (*k, *v))) else {
                continue;
            };
            let r = self.reflexive(other)?; // other = other
            let reframed = self.out.reframe(r, sigma); // other = σ⁻¹·t
            let s = self.out.sym(reframed); // t = σ·other
            let back = self.out.trans(s, reframed).map_err(|e| e.to_string())?; // t = t
            return Ok(self.note(back));
        }
        Err(format!(
            "no proof establishes the term {}",
            self.out_string(t)
        ))
    }

    /// Establish a class from the carrier equalities in a premise's derivation.
    fn establish(&mut self, class: TermId, premise: ProofId) -> LiftResult<ViewId> {
        let term = self.dec(class)?;
        let mut pending = vec![premise];
        let mut seen = HashSet::default();
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            let proof = self.egg.get(id);
            if (proof.lhs() == class || proof.rhs() == class)
                && self.eq(id).is_ok()
                && let Ok(proof) = self.reflexive(term)
            {
                return Ok(proof);
            }
            match proof.justification() {
                Justification::Rule { premise_proofs, .. } => pending.extend(premise_proofs),
                Justification::MergeFn {
                    old_proof,
                    new_proof,
                    ..
                } => pending.extend([*old_proof, *new_proof]),
                Justification::Trans(a, b) => pending.extend([*a, *b]),
                Justification::Congr {
                    proof, child_proof, ..
                } => pending.extend([*proof, *child_proof]),
                Justification::Sym(proof)
                | Justification::Proj { proof, .. }
                | Justification::ContainerNormalize { proof } => pending.push(*proof),
                Justification::Fiat | Justification::Eval => {}
            }
        }
        self.reflexive(term)
    }

    pub(super) fn trans(&mut self, p: ViewId, q: ViewId) -> LiftResult<ViewId> {
        let r = self.out.trans(p, q).map_err(|e| e.to_string())?;
        Ok(self.note(r))
    }

    /// `σ·t1 = (σ∘m)·t2` from `t1 = m·t2`.
    pub(super) fn rename_both(&mut self, p: ViewId, sigma: &Renaming) -> ViewId {
        if sigma.is_identity() {
            return p;
        }
        let r = self.out.equivariance(p, sigma);
        self.note(r)
    }

    /// Reframe `p`'s right-hand side onto `target`, which must be the same term up
    /// to a bijection of slot names.
    pub(super) fn align(&mut self, p: ViewId, target: TermId) -> LiftResult<ViewId> {
        let rhs = self.out.edge(p).rhs;
        if rhs == target {
            return Ok(p);
        }
        let mut pairs: BTreeMap<i64, i64> = BTreeMap::new();
        self.unify_slots(rhs, target, &mut pairs).map_err(|e| {
            format!(
                "aligning {} with {}: {e}",
                self.out_string(rhs),
                self.out_string(target)
            )
        })?;
        let sigma = Renaming::completing(pairs.iter().map(|(k, v)| (*k, *v))).ok_or_else(|| {
            format!(
                "aligning {} with {} needs a non-bijective renaming {pairs:?}",
                self.out_string(rhs),
                self.out_string(target)
            )
        })?;
        let r = self.out.reframe(p, sigma);
        let got = self.out.edge(r).rhs;
        if got != target {
            return Err(format!(
                "alignment of {} with {} produced {}",
                self.out_string(rhs),
                self.out_string(target),
                self.out_string(got)
            ));
        }
        Ok(self.note(r))
    }

    pub(super) fn unify_slots(
        &self,
        a: TermId,
        b: TermId,
        pairs: &mut BTreeMap<i64, i64>,
    ) -> LiftResult<()> {
        self.match_slots(a, b, pairs).map_err(|error| match error {
            SlotMismatch::Terms(a, b) => format!(
                "cannot align {} with {}",
                self.out_string(a),
                self.out_string(b)
            ),
            SlotMismatch::Conflict(sa, prev, sb) => {
                format!("slot ${sa} would have to be both ${prev} and ${sb}")
            }
        })
    }

    pub(super) fn match_slots(
        &self,
        a: TermId,
        b: TermId,
        pairs: &mut BTreeMap<i64, i64>,
    ) -> Result<(), SlotMismatch> {
        let dag = &self.out.term_dag;
        let mut pending = vec![(a, b)];
        let mut seen = HashSet::default();
        while let Some((a, b)) = pending.pop() {
            if !seen.insert((a, b)) {
                continue;
            }
            match (dag.get(a), dag.get(b)) {
                (Term::Var(x), Term::Var(y)) => {
                    let (sa, sb) = (
                        super::super::terms::slot_of(dag, a),
                        super::super::terms::slot_of(dag, b),
                    );
                    match (sa, sb) {
                        (Some(sa), Some(sb)) => match pairs.get(&sa) {
                            Some(&prev) if prev != sb => {
                                return Err(SlotMismatch::Conflict(sa, prev, sb));
                            }
                            _ => {
                                pairs.insert(sa, sb);
                            }
                        },
                        _ if x == y => (),
                        _ => return Err(SlotMismatch::Terms(a, b)),
                    }
                }
                (Term::Lit(x), Term::Lit(y)) if x == y => (),
                (Term::App(h1, c1), Term::App(h2, c2)) if h1 == h2 && c1.len() == c2.len() => {
                    pending.extend(c1.iter().copied().zip(c2.iter().copied()).rev());
                }
                _ => return Err(SlotMismatch::Terms(a, b)),
            }
        }
        Ok(())
    }

    /// The slotted proof of the equality an egglog proof denotes: for a carrier
    /// equality, that equality; for a row, the equality the row as the consumer
    /// reads it (its right-hand side) denotes.
    pub(super) fn eq(&mut self, id: ProofId) -> LiftResult<ViewId> {
        if let Some(&p) = self.eq_memo.get(&id) {
            return Ok(p);
        }
        let proof = self.egg.get(id).clone();
        let result = if self.is_carrier_term(proof.lhs()) {
            self.eq_direct(id)?
        } else {
            self.row_eq(id, true)?
        };
        self.eq_memo.insert(id, result);
        Ok(result)
    }

    /// The equality an egglog proof denotes, by its justification.
    pub(super) fn eq_direct(&mut self, id: ProofId) -> LiftResult<ViewId> {
        let proof = self.egg.get(id).clone();
        let (lhs, rhs) = (proof.lhs(), proof.rhs());
        let result = match proof.justification() {
            Justification::Fiat => {
                if lhs == rhs {
                    if self.is_carrier_term(lhs) {
                        let t = self.dec(lhs)?;
                        self.reflexive(t)?
                    } else {
                        self.row_fiat(lhs)?
                    }
                } else {
                    let (l, r) = (self.dec(lhs)?, self.dec(rhs)?);
                    self.source_union(l, &Renaming::identity(), r)?
                }
            }
            Justification::Sym(p) => {
                let q = self.eq(*p)?;
                let s = self.out.sym(q);
                self.note(s)
            }
            Justification::Trans(p, q) => {
                let (a, b) = (self.eq(*p)?, self.eq(*q)?);
                self.trans(a, b)?
            }
            Justification::Congr {
                proof,
                child_index,
                child_proof,
            } => self
                .congr(*proof, *child_index, *child_proof, rhs)
                .map_err(|e| format!("in a congruence at {child_index}: {e}"))?,
            Justification::Proj { proof, .. } => {
                // Reuse an established surface term, translating the parent if needed.
                let term = self.dec(lhs)?;
                self.reflexive(term).or_else(|_| {
                    self.eq(*proof)?;
                    self.reflexive(term)
                })?
            }
            Justification::Rule {
                name,
                premise_proofs,
                substitution,
            } => {
                let name = name.clone();
                let prems = premise_proofs.clone();
                let subst = substitution.clone();
                if lhs == rhs
                    && self.is_carrier_term(lhs)
                    && let Ok(t) = self.dec(lhs)
                    && let Ok(r) = self.reflexive(t)
                {
                    // a term the rule built that is already at hand
                    return Ok(r);
                }
                let r = self
                    .rule(&name, &prems, &subst, lhs, rhs)
                    .map_err(|e| format!("in rule {:?}: {e}", name.lines().next().unwrap_or("")))?;
                if lhs == rhs && self.is_carrier_term(lhs) {
                    // the term the rule built equals itself
                    self.orient(r, lhs, rhs)?
                } else {
                    r
                }
            }
            Justification::MergeFn { function, .. } => {
                return Err(format!("merge of {function} does not denote an equality"));
            }
            Justification::ContainerNormalize { .. } | Justification::Eval => {
                return Err(format!(
                    "proof {id} ({}) does not denote an equality",
                    self.egg_string(lhs)
                ));
            }
        };
        Ok(result)
    }

    /// A row stated at the top level.
    fn row_fiat(&mut self, row: TermId) -> LiftResult<ViewId> {
        let (head, args) = self.app(row).ok_or("not a row")?;
        match row_kind(head) {
            RowKind::Edge => {
                let (a, b) = (self.dec(args[0])?, self.dec(args[2])?);
                let m = self.slot_map(args[1])?;
                let completion = self.complete(&m, b);
                if a == b && completion.is_identity() {
                    self.reflexive(a)
                } else {
                    self.source_union(a, &completion, b)
                }
            }
            _ => Err(format!(
                "top-level row {} denotes no equality",
                self.egg_string(row)
            )),
        }
    }

    /// Decoding gives binders fresh names, independently of the source reader.
    /// Only the recorded source union is Fiat; transport it to the decoded
    /// spellings using the proof algebra, keeping the source's free slots fixed.
    fn source_union(&mut self, lhs: TermId, m: &Renaming, rhs: TermId) -> LiftResult<ViewId> {
        let target = rename(&mut self.out.term_dag, m, rhs);
        for u in &self.program.unions {
            for (a, b) in [(u.lhs, u.rhs), (u.rhs, u.lhs)] {
                let mut left = BTreeMap::new();
                let mut right = BTreeMap::new();
                if self.match_slots(a, lhs, &mut left).is_err()
                    || self.match_slots(b, target, &mut right).is_err()
                    || self
                        .program
                        .free_slots(&self.out.term_dag, a)
                        .iter()
                        .any(|s| left.get(s) != Some(s))
                    || self
                        .program
                        .free_slots(&self.out.term_dag, b)
                        .iter()
                        .any(|s| right.get(s) != Some(s))
                {
                    continue;
                }
                let Some(rho) = Renaming::completing(left) else {
                    continue;
                };
                let p = self.out.fiat(a, b);
                let p = self.rename_both(p, &rho);
                return self.align(p, rhs);
            }
        }
        Err(format!(
            "no source union establishes {} = {m}·{}",
            self.out_string(lhs),
            self.out_string(rhs)
        ))
    }

    pub(super) fn congr(
        &mut self,
        proof: ProofId,
        child_index: usize,
        child_proof: ProofId,
        conclusion_rhs: TermId,
    ) -> LiftResult<ViewId> {
        let base = self.egg.get(proof).clone();
        let base_rhs = base.rhs();
        if self.is_carrier_term(base_rhs) {
            // `t1 = F(.., c, ..)` and `c = c'`: congruence at the surface column.
            let p = self.eq(proof)?;
            let (head, _) = self.app(base_rhs).ok_or("congr on a non-application")?;
            let j = self.surface_column(head, child_index)?;
            let completion = self.edge_memo.get(&(base_rhs, j)).cloned().ok_or_else(|| {
                format!(
                    "no decoded edge for column {j} of {}",
                    self.egg_string(base_rhs)
                )
            })?;
            let c = self.eq(child_proof)?;
            let mut renamed = self.rename_both(c, &completion);
            let target = self.dec(conclusion_rhs)?;
            let child = self.subterm_at(target, &[j])?;
            let actual = self.out.edge(renamed).clone();
            let content = rename(&mut self.out.term_dag, &actual.renaming, actual.rhs);
            // Choose new RHS names before congruence can identify them with siblings.
            if let Some(renaming) = term_renaming(
                &self.out.term_dag,
                &[(actual.lhs, actual.lhs), (content, child)],
            ) {
                renamed = self.rename_both(renamed, &renaming);
            }
            let r = self.out.congr(p, j, renamed).map_err(|e| e.to_string())?;
            let occurrences = self.row_occurrences(conclusion_rhs)?;
            let aligned = self.fit(r, target, &occurrences)?;
            // A congruence whose base is reflexive may be read in either
            // direction later; both endpoints are now known.
            Ok(self.note(aligned))
        } else {
            // A row re-keyed by a union: the same statement about an equal term.
            let old = self.eq(proof)?;
            let (head, args) = self.app(base_rhs).ok_or("congr on a non-row")?;
            // the child proof relates the column's old class with the new, in
            // whichever direction the union-find stated it
            let c = self.eq(child_proof)?;
            let old_col = self.dec(args[child_index])?;
            let c = if self.out.edge(c).lhs == old_col {
                c
            } else {
                let s = self.out.sym(c);
                self.note(s)
            };
            let kind = row_kind(head);
            let (lhs_col, rhs_col) = match kind {
                RowKind::Edge => (0, 2),
                RowKind::Invocation => (2, 0),
                RowKind::Other => {
                    return Err(format!(
                        "congruence on a row that denotes no equality: {}",
                        self.egg_string(base_rhs)
                    ));
                }
            };
            let _ = args;
            let context = |this: &Self, e: String| {
                format!(
                    "re-keying {} at {child_index} by {}: {e}",
                    this.egg_string(base_rhs),
                    this.prop_string(c)
                )
            };
            if child_index == lhs_col {
                let s = self.out.sym(c);
                self.trans(s, old).map_err(|e| context(self, e))
            } else if child_index == rhs_col {
                self.trans(old, c).map_err(|e| context(self, e))
            } else {
                Err(format!(
                    "congruence on the renaming column of {}",
                    self.egg_string(base_rhs)
                ))
            }
        }
    }

    /// The equality a rule firing concludes, by the rule.
    pub(super) fn rule(
        &mut self,
        name: &str,
        prems: &[ProofId],
        subst: &IndexMap<String, TermId>,
        lhs: TermId,
        rhs: TermId,
    ) -> LiftResult<ViewId> {
        match rule_kind(self.program, name) {
            RuleKind::OrientMax => self.eq(prems[0]),
            RuleKind::OrientMin => {
                let p = self.eq(prems[0])?;
                let s = self.out.sym(p);
                Ok(self.note(s))
            }
            RuleKind::SeedIdentity => {
                let c = self.sub(subst, "_c")?;
                let t = self.dec(c)?;
                self.reflexive(t).or_else(|_| self.establish(c, prems[0]))
            }
            RuleKind::Transitivity => {
                let (p, q) = (self.eq(prems[0])?, self.eq(prems[1])?);
                self.trans(p, q)
            }
            RuleKind::OneLeader => {
                let (p, q) = (self.eq(prems[0])?, self.eq(prems[1])?);
                let s = self.out.sym(p);
                self.trans(s, q)
            }
            RuleKind::RestateEdge | RuleKind::ShapeEqual | RuleKind::BinderStrip => {
                self.eq(prems[0])
            }
            RuleKind::BinderRefresh => {
                // the node rebuilt with its bound slot renamed: the same term up to
                // the names of its binders
                let node = self.eq(prems[0])?; // node = row
                let node_egg = self.sub(subst, "_node")?;
                self.finish_union(node, lhs, rhs, node_egg)
            }
            RuleKind::Invocation => {
                // `a = m·c` and `name = m∘g`: `a = name·c` through the symmetry g.
                let p = self.eq(prems[0])?;
                let (m, c, name) = (
                    self.slot_map(self.sub(subst, "_m")?)?,
                    self.sub(subst, "_c")?,
                    self.slot_map(self.sub(subst, "_name")?)?,
                );
                let grp = self.group(self.sub(subst, "_grp")?)?;
                let g = grp
                    .iter()
                    .find(|g| compose(&m, g) == name)
                    .cloned()
                    .ok_or("coset-min's element is not in the group")?;
                if is_identity(&g) {
                    return Ok(p);
                }
                let s = self.symmetry(c, &g, prems[1])?;
                self.trans(p, s)
            }
            RuleKind::InvocationMerge => {
                let (pa, pb) = (self.eq(prems[0])?, self.eq(prems[1])?);
                let s = self.out.sym(pb);
                let r = self.trans(pa, s)?;
                self.orient(r, lhs, rhs)
            }
            RuleKind::ShapeCollision => {
                let r = self.shape_collision(prems, subst)?;
                Ok(r)
            }
            RuleKind::ShapeDedup => {
                let r = self.shape_dedup(prems, subst)?;
                Ok(r)
            }
            RuleKind::Migration => {
                let edge = self.eq(prems[0])?; // e2 = m·e1
                let row = self.eq(prems[1])?; // e2 = row
                let s = self.out.sym(edge); // e1 = m⁻¹·e2
                let p = self.trans(s, row)?; // e1 = ·row
                let e1 = self.sub(subst, "_e1")?;
                self.finish_union(p, lhs, rhs, e1)
            }
            RuleKind::ChildUpdate => {
                let edge = self.eq(prems[0])?; // c = m·c'
                let node = self.eq(prems[1])?; // node = row
                let j: usize = name
                    .rsplit('/')
                    .next()
                    .and_then(|s| s.parse().ok())
                    .ok_or("child-update without a column")?;
                let row = self.out.edge(node).rhs;
                let row_egg = self.egg.get(prems[1]).rhs();
                let completion = self.edge_memo.get(&(row_egg, j)).cloned().ok_or_else(|| {
                    format!("no decoded edge for column {j} of {}", self.out_string(row))
                })?;
                let renamed = self.rename_both(edge, &completion);
                let r = self
                    .out
                    .congr(node, j, renamed)
                    .map_err(|e| e.to_string())?;
                let r = self.note(r);
                let node_egg = self.sub(subst, "_node")?;
                self.finish_union(r, lhs, rhs, node_egg)
            }
            RuleKind::Apply(user) => self.apply_rule(user, prems, subst, lhs, rhs),
            _ => Err(format!("no translation for rule {name:?}")),
        }
    }

    /// `p: origin = ·X` where the egglog step relates `origin` with the term it
    /// built, or states the built term's own reflexivity: align `X` with the
    /// built term's surface form and turn the proof the way the step states it.
    fn finish_union(
        &mut self,
        p: ViewId,
        lhs: TermId,
        rhs: TermId,
        origin: TermId,
    ) -> LiftResult<ViewId> {
        let built = if lhs == rhs {
            lhs
        } else if lhs == origin {
            rhs
        } else if rhs == origin {
            lhs
        } else {
            return Err(format!(
                "the step relates {} and {}, neither of which is its origin {}",
                self.egg_string(lhs),
                self.egg_string(rhs),
                self.egg_string(origin)
            ));
        };
        let target = self.dec(built)?;
        let occ = self.row_occurrences(built)?;
        let p = self.fit(p, target, &occ)?;
        self.orient(p, lhs, rhs)
    }

    /// Turn `p` (an equality between the surface forms of the egglog proof's
    /// two sides, in some direction) around to match the egglog proposition.
    pub(super) fn orient(&mut self, p: ViewId, lhs: TermId, rhs: TermId) -> LiftResult<ViewId> {
        let (l, r) = (self.dec(lhs)?, self.dec(rhs)?);
        let prop = self.out.edge(p).clone();
        if l == r {
            // the step's own conclusion: the term it built equals itself
            if prop.lhs == l {
                let s = self.out.sym(p);
                return self.trans(p, s);
            }
            if prop.rhs == l {
                let s = self.out.sym(p);
                return self.trans(s, p);
            }
        }
        if prop.lhs == l {
            Ok(p)
        } else if prop.lhs == r && prop.rhs == l {
            let s = self.out.sym(p);
            Ok(self.note(s))
        } else {
            Err(format!(
                "derived {} where the egglog step relates {} and {}",
                self.prop_string(p),
                self.out_string(l),
                self.out_string(r)
            ))
        }
    }

    /// `t1 = m·t2` restated as `t1 = (m·t2)`: the renaming applied, so the
    /// right-hand side is the term the proposition is about.
    pub(super) fn content_form(&mut self, p: ViewId) -> ViewId {
        let m = self.out.edge(p).renaming.clone();
        let r = self.out.reframe(p, m);
        self.note(r)
    }
}
