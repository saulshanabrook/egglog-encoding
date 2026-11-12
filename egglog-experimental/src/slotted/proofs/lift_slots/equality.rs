//! Lift encoded equality steps and maintenance rules.

use super::*;

/// The first term or slot conflict in a structural match.
pub(super) enum SlotMismatch {
    Terms(TermId, TermId),
    Conflict(i64, i64, i64),
}

impl SlotLifter<'_, NativeProofs<'_>> {
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
        Err(format!(
            "no proof establishes the term {}",
            self.out_string(t)
        ))
    }

    /// Compose through an exact or alpha-equivalent middle term.
    pub(super) fn trans(&mut self, mut p: ViewId, q: ViewId) -> LiftResult<ViewId> {
        let left = self.out.edge(p).rhs;
        let middle = self.out.edge(q).lhs;
        if left != middle
            && self.term_shapes.get(&self.out.term_dag, left)
                == self.term_shapes.get(&self.out.term_dag, middle)
            && self.program.alpha_eq(&mut self.out.term_dag, left, middle)
        {
            let renaming = self.out.edge(p).renaming.clone();
            let actual = rename(&mut self.out.term_dag, &renaming, middle);
            let proof = self.out.proof(p);
            let proof = self.out.alpha(proof, actual);
            p = self.out.view(proof, middle, renaming);
        }
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
        let result = if let Some(&source) = self.anchors.get(&id) {
            self.anchored_proof(source, proof.lhs(), proof.rhs())?
        } else if self.is_carrier_term(proof.lhs()) {
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
        if self.is_carrier_term(lhs) {
            if let Some(&proof) = self.eq_memo.get(&id) {
                return Ok(proof);
            }
            if let Some(&source) = self.anchors.get(&id) {
                return self.anchored_proof(source, lhs, rhs);
            }
        }
        let result = match proof.justification() {
            Justification::Fiat => {
                let source = *self
                    .anchors
                    .get(&id)
                    .ok_or_else(|| format!("proof {id} has no recorded source occurrence"))?;
                return self.anchored_proof(source, lhs, rhs);
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
                .congr(id, *proof, *child_index, *child_proof)
                .map_err(|e| format!("in a congruence at {child_index}: {e}"))?,
            Justification::Proj { proof, child_index } => {
                let row = self.egg.get(*proof).rhs();
                if self.is_carrier_term(row) {
                    self.project(*proof, *child_index)?
                } else {
                    let term = self.dec(lhs)?;
                    if !self.program.is_built(&self.out.term_dag, term)
                        && !self.known.contains_key(&term)
                    {
                        self.eq(*proof)?;
                    }
                    self.reflexive(term)?
                }
            }
            Justification::Rule { name, .. } => {
                if lhs == rhs && self.is_carrier_term(lhs) {
                    let term = self.dec(lhs)?;
                    if self.program.is_built(&self.out.term_dag, term)
                        || self.known.contains_key(&term)
                    {
                        return self.reflexive(term);
                    }
                }
                let r = self.rule(id).map_err(|e| {
                    format!(
                        "in rule {:?} at proof {id}: {e}",
                        name.lines().next().unwrap_or("")
                    )
                })?;
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

    pub(super) fn existence_from(
        &mut self,
        mut proof: ViewId,
        target: TermId,
    ) -> LiftResult<ViewId> {
        proof = self.content_form(proof);
        let actual = self.out.edge(proof).rhs;
        if actual != target {
            if self.term_shapes.get(&self.out.term_dag, actual)
                != self.term_shapes.get(&self.out.term_dag, target)
            {
                return Err(format!(
                    "recorded term {actual} and requested term {target} have different structures"
                ));
            }
            let renaming = term_renaming(&self.out.term_dag, &[(actual, target)])
                .or_else(|| {
                    self.program
                        .renaming_between(&mut self.out.term_dag, actual, target)
                })
                .ok_or_else(|| {
                    format!("recorded term {actual} is not a renaming of requested term {target}")
                })?;
            proof = self.rename_both(proof, &renaming);
        }
        let mut ordinary = self.out.proof(proof);
        if self.out.proposition(ordinary).rhs != target {
            ordinary = self.out.alpha(ordinary, target);
        }
        proof = self.out.plain(ordinary);
        if self.out.edge(proof).lhs == target {
            return Ok(self.note(proof));
        }
        let back = self.out.sym(proof);
        self.trans(back, proof)
    }

    fn anchored_proof(&mut self, source: ProofId, lhs: TermId, rhs: TermId) -> LiftResult<ViewId> {
        let mut proof = self.out.plain(source);
        if self.is_carrier_term(lhs) && lhs == rhs {
            let target = self.dec(lhs)?;
            return self.existence_from(proof, target);
        }
        let (left, right, content, renaming) = if self.is_carrier_term(lhs) {
            let (left, right) = (self.dec(lhs)?, self.dec(rhs)?);
            (left, right, right, Renaming::identity())
        } else {
            let (a, mapping, b) = self.row_sides(rhs)?;
            let (left, right) = (self.dec(a)?, self.dec(b)?);
            let renaming = self.complete(&mapping, right);
            let content = rename(&mut self.out.term_dag, &renaming, right);
            (left, right, content, renaming)
        };
        let actual = self.out.edge(proof).clone();
        let endpoints = [(actual.lhs, left), (actual.rhs, content)];
        if endpoints.iter().any(|(actual, target)| actual != target) {
            let coordinates = term_renaming(&self.out.term_dag, &endpoints)
                .or_else(|| {
                    let mut coordinates = BTreeMap::new();
                    for (actual, target) in endpoints {
                        let renaming = self.program.renaming_between(
                            &mut self.out.term_dag,
                            actual,
                            target,
                        )?;
                        for slot in self.program.free_slots(&self.out.term_dag, actual) {
                            let image = renaming.apply(slot);
                            if coordinates
                                .insert(slot, image)
                                .is_some_and(|old| old != image)
                            {
                                return None;
                            }
                        }
                    }
                    Renaming::completing(coordinates)
                })
                .ok_or_else(|| {
                    format!(
                        "recorded equality has no common coordinates for endpoints {} and {}",
                        left, content,
                    )
                })?;
            proof = self.rename_both(proof, &coordinates);
        }
        let mut ordinary = self.out.proof(proof);
        let proposition = self.out.proposition(ordinary).clone();
        if !self
            .program
            .alpha_eq(&mut self.out.term_dag, proposition.lhs, left)
            || !self
                .program
                .alpha_eq(&mut self.out.term_dag, proposition.rhs, content)
        {
            return Err(format!(
                "recorded equality {} does not denote {} = {}",
                self.prop_string(proof),
                self.out_string(left),
                self.out_string(content)
            ));
        }
        if proposition.lhs != left {
            let view = self.out.plain(ordinary);
            let reversed = self.out.sym(view);
            ordinary = self.out.proof(reversed);
            ordinary = self.out.alpha(ordinary, left);
            let view = self.out.plain(ordinary);
            let reversed = self.out.sym(view);
            ordinary = self.out.proof(reversed);
        }
        if self.out.proposition(ordinary).rhs != content {
            ordinary = self.out.alpha(ordinary, content);
        }
        let proof = self.out.view(ordinary, right, renaming);
        Ok(self.note(proof))
    }

    pub(super) fn project(&mut self, parent: ProofId, physical: usize) -> LiftResult<ViewId> {
        self.project_side(parent, physical, true)
    }

    pub(super) fn project_side(
        &mut self,
        parent: ProofId,
        physical: usize,
        rhs: bool,
    ) -> LiftResult<ViewId> {
        let statement = self.egg.get(parent);
        let row = if rhs {
            statement.rhs()
        } else {
            statement.lhs()
        };
        let head = self
            .app(row)
            .ok_or("projection parent is not a constructor")?
            .0;
        let column = self.surface_column(head, physical)?;
        let target = self.dec(row)?;
        let mut parent = self.eq(parent)?;
        if !rhs {
            parent = self.out.sym(parent);
        }
        let parent = self.align(parent, target)?;
        let projected = self
            .out
            .project(parent, column)
            .map_err(|e| e.to_string())?;
        let completion = self.edge_memo[&(row, column)].inverse();
        Ok(self.rename_both(projected, &completion))
    }

    pub(super) fn congr(
        &mut self,
        id: ProofId,
        proof: ProofId,
        child_index: usize,
        child_proof: ProofId,
    ) -> LiftResult<ViewId> {
        let conclusion_rhs = self.egg.get(id).rhs();
        let base = self.egg.get(proof).clone();
        let base_rhs = base.rhs();
        let child = self.egg.get(child_proof);
        if child.lhs() == child.rhs() {
            // Ground extraction retains congruences on literal and renaming
            // operands too. A reflexive operand leaves the source step intact.
            return self.eq(proof);
        }
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
            let occurrences = self.row_occurrences(id, true)?;
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
    pub(super) fn rule(&mut self, id: ProofId) -> LiftResult<ViewId> {
        let proof = self.egg.get(id).clone();
        let (lhs, rhs) = (proof.lhs(), proof.rhs());
        let Justification::Rule {
            name,
            premise_proofs: prems,
            substitution: subst,
        } = proof.justification()
        else {
            return Err("rule replay requires a rule proof".into());
        };
        match rule_kind(self.program, name) {
            RuleKind::OrientMax => self.eq(prems[0]),
            RuleKind::OrientMin => {
                let p = self.eq(prems[0])?;
                let s = self.out.sym(p);
                Ok(self.note(s))
            }
            RuleKind::SeedIdentity => self.support_class(prems[0], true),
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
                self.finish_union(id, node, lhs, rhs, node_egg)
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
                let (index, least) = crate::slotted::runtime::group::coset_min_with_index(&m, &grp)
                    .ok_or("coset-min has an empty group")?;
                if !least.iter().eq(name.iter()) {
                    return Err("recorded coset-min differs from its primitive inputs".into());
                }
                let g = &grp[index];
                let s = self.symmetry(c, g, prems[1])?;
                self.trans(p, s)
            }
            RuleKind::InvocationMerge => {
                let (mut pa, pb) = (self.eq(prems[0])?, self.eq(prems[1])?);
                // Equal partial names may have different completions. Prove
                // their difference irrelevant before identifying the classes.
                let adjustment = self
                    .out
                    .edge(pa)
                    .renaming
                    .inverse()
                    .compose(&self.out.edge(pb).renaming);
                if !adjustment.is_identity() {
                    let support = Support {
                        origin: SupportOrigin::Row {
                            proof: prems[0],
                            column: Some(0),
                        },
                        transport: None,
                    };
                    let class = self.sub(subst, "_c")?;
                    let certificate = self.support_permutation(support, class, &adjustment)?;
                    pa = self.trans(pa, certificate)?;
                }
                let s = self.out.sym(pb);
                let r = self.trans(pa, s)?;
                self.orient(r, lhs, rhs)
            }
            RuleKind::ShapeCollision => {
                let r = self.shape_collision(prems, subst)?;
                Ok(r)
            }
            RuleKind::ShapeDedup => {
                let r = self.shape_dedup(name, prems, subst)?;
                Ok(r)
            }
            RuleKind::Migration => {
                let edge = self.eq(prems[0])?; // e2 = m·e1
                let row = self.eq(prems[1])?; // e2 = row
                let s = self.out.sym(edge); // e1 = m⁻¹·e2
                let p = self.trans(s, row)?; // e1 = ·row
                let e1 = self.sub(subst, "_e1")?;
                self.finish_union(id, p, lhs, rhs, e1)
            }
            RuleKind::ChildUpdate => {
                let edge = self.eq(prems[0])?; // c = m·c'
                let node = self.eq(prems[1])?; // node = row
                let row = self.out.edge(node).rhs;
                let row_egg = self.egg.get(prems[1]).rhs();
                let j = self.updated_column(name, row_egg)?;
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
                self.finish_union(id, r, lhs, rhs, node_egg)
            }
            RuleKind::Apply(user) => self.apply_rule(id, user, prems, subst, lhs, rhs),
            _ => Err(format!("no translation for rule {name:?}")),
        }
    }

    /// `p: origin = ·X` where the egglog step relates `origin` with the term it
    /// built, or states the built term's own reflexivity: align `X` with the
    /// built term's surface form and turn the proof the way the step states it.
    fn finish_union(
        &mut self,
        id: ProofId,
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
        let occ = self.row_occurrences(id, built == rhs)?;
        let p = self.fit(p, target, &occ)?;
        self.orient(p, lhs, rhs)
    }

    /// Turn `p` (an equality between the surface forms of the egglog proof's
    /// two sides, in some direction) around to match the egglog proposition.
    pub(super) fn orient(&mut self, p: ViewId, lhs: TermId, rhs: TermId) -> LiftResult<ViewId> {
        let (l, r) = (self.dec(lhs)?, self.dec(rhs)?);
        let prop = self.out.edge(p).clone();
        if lhs == rhs {
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
