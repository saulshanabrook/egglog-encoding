//! Align lifted equalities with the original query.

use super::*;

impl SlotLifter<'_> {
    /// Reframe `p`'s content onto `target`, renaming redundant slots at the
    /// occurrences where a plain bijection fails.
    pub(super) fn fit(
        &mut self,
        p: ViewId,
        target: TermId,
        occ: &HashMap<Vec<usize>, Occurrence>,
    ) -> LiftResult<ViewId> {
        let mut p = self.content_form(p);
        for _ in 0..64 {
            let content = self.out.edge(p).rhs;
            if content == target {
                return Ok(p);
            }
            let mut pairs: Vec<(Vec<usize>, i64, i64)> = vec![];
            self.slot_pairs(content, target, &mut vec![], &mut pairs)?;
            // a bijection where it is one; a conflict names both positions, since
            // either may be the one holding a redundant slot
            let mut beta: BTreeMap<i64, (i64, Vec<usize>)> = BTreeMap::new();
            let mut inverse_beta: BTreeMap<i64, (i64, Vec<usize>)> = BTreeMap::new();
            let mut conflict: Option<Vec<(Vec<usize>, i64, i64)>> = None;
            for (path, x, t) in &pairs {
                match (beta.get(x), inverse_beta.get(t)) {
                    (Some((t0, path0)), _) if t0 != t => {
                        conflict = Some(vec![(path.clone(), *x, *t), (path0.clone(), *x, *t0)]);
                        break;
                    }
                    (None, Some((x0, path0))) if x0 != x => {
                        conflict = Some(vec![(path.clone(), *x, *t), (path0.clone(), *x0, *t)]);
                        break;
                    }
                    _ => {
                        beta.insert(*x, (*t, path.clone()));
                        inverse_beta.insert(*t, (*x, path.clone()));
                    }
                }
            }
            let beta: BTreeMap<i64, i64> = beta.iter().map(|(k, (v, _))| (*k, *v)).collect();
            let inverse_beta: BTreeMap<i64, i64> =
                inverse_beta.iter().map(|(k, (v, _))| (*k, *v)).collect();
            let Some(candidates) = conflict else {
                let sigma = Renaming::completing(beta.into_iter()).ok_or("non-bijective fit")?;
                let r = self.out.reframe(p, sigma);
                let got = self.out.edge(r).rhs;
                if got != target {
                    return Err(format!(
                        "fitting {} onto {} produced {}",
                        self.out_string(content),
                        self.out_string(target),
                        self.out_string(got)
                    ));
                }
                return Ok(self.note(r));
            };
            // the names each position may take: the target's, the slot already
            // sent to the target's, and only then a fresh one -- a fresh name is
            // progress only where nothing names the slot's destination
            let mut attempts: Vec<(Vec<usize>, i64, i64)> = vec![];
            for (path, x, t) in &candidates {
                if *t != *x {
                    attempts.push((path.clone(), *x, *t));
                }
                if let Some(&x0) = inverse_beta.get(t)
                    && x0 != *x
                {
                    attempts.push((path.clone(), *x, x0));
                }
            }
            for (path, x, _) in &candidates {
                let f = self.fresh();
                attempts.push((path.clone(), *x, f));
            }
            let mut errors: Vec<String> = vec![];
            let mut found: Option<(Vec<usize>, ViewId)> = None;
            let mut any = false;
            'attempts: for (path, x, want) in attempts {
                // the occurrences holding this position, innermost first: the
                // slot may be redundant in any of them, or a symmetry of one may
                // move it
                let mut occ_path = path.clone();
                loop {
                    if let Some(&cls) = occ.get(&occ_path) {
                        any = true;
                        let o = self.subterm_at(content, &occ_path)?;
                        if all_slots(&self.out.term_dag, o).contains(&want) {
                            match self.occurrence_symmetry(cls, o, x, want) {
                                Ok(sym) => {
                                    found = Some((occ_path, sym));
                                    break 'attempts;
                                }
                                Err(e) => errors.push(format!(
                                    "slot ${x} of {} would have to become ${want}, which it also holds ({e})",
                                    self.out_string(o)
                                )),
                            }
                        } else {
                            match self.occurrence_cert(cls, o, x, want) {
                                Ok(cert) => {
                                    found = Some((occ_path, cert));
                                    break 'attempts;
                                }
                                Err(e) => errors.push(e),
                            }
                        }
                    }
                    if occ_path.pop().is_none() {
                        break;
                    }
                }
            }
            if !any {
                errors.push("no occurrence holds the conflicting slots".to_string());
            }
            let Some((occ_path, cert)) = found else {
                return Err(format!(
                    "fitting {} onto {}: {}",
                    self.out_string(content),
                    self.out_string(target),
                    errors.join("; ")
                ));
            };
            if occ_path.is_empty() {
                // the whole content: compose directly
                p = self.trans(p, cert)?;
                p = self.content_form(p);
            } else {
                p = self.congr_at(p, &occ_path, cert)?;
                p = self.content_form(p);
            }
            if self.out.edge(p).rhs == content {
                return Err(format!(
                    "fitting {} onto {}: a certificate changed nothing: {} at {occ_path:?}\n{}",
                    self.out_string(content),
                    self.out_string(target),
                    self.prop_string(cert),
                    self.out.proof_to_string(cert)
                ));
            }
        }
        let content = self.out.edge(p).rhs;
        Err(format!(
            "fitting {} onto {} did not converge",
            self.out_string(content),
            self.out_string(target)
        ))
    }

    /// Rename the free slots of `p`'s content, one certificate at a time, until
    /// they are the target's; bound names are left to the final coordinate alignment. Fails where
    /// a free slot that differs is not redundant.
    pub(super) fn fit_content(
        &mut self,
        p: ViewId,
        target: TermId,
        occ: &HashMap<Vec<usize>, Occurrence>,
    ) -> LiftResult<ViewId> {
        let mut p = self.content_form(p);
        for _ in 0..64 {
            let content = self.out.edge(p).rhs;
            let free = self.program.free_slots(&self.out.term_dag, content);
            let mut pairs: Vec<(Vec<usize>, i64, i64)> = vec![];
            self.slot_pairs(content, target, &mut vec![], &mut pairs)?;
            let differing: Vec<&(Vec<usize>, i64, i64)> = pairs
                .iter()
                .filter(|(_, x, t)| x != t && free.contains(x))
                .collect();
            let slots = all_slots(&self.out.term_dag, content);
            // a slot whose target name is free to take, else any (through a
            // fresh name, to break a cycle)
            let chosen = differing
                .iter()
                .find(|(_, _, t)| !slots.contains(t))
                .or(differing.first())
                .cloned()
                .cloned();
            let Some((path, x, t)) = chosen else {
                return self.fit(p, target, occ);
            };
            let mut occ_path = path.clone();
            let mut errors = Vec::new();
            let (sub, cert) = loop {
                if let Some(&o) = occ.get(&occ_path) {
                    let sub = self.subterm_at(content, &occ_path)?;
                    let want = if all_slots(&self.out.term_dag, sub).contains(&t) {
                        self.fresh()
                    } else {
                        t
                    };
                    match self.occurrence_cert(o, sub, x, want) {
                        Ok(cert) => break (sub, cert),
                        Err(error) => errors.push(error),
                    }
                }
                if occ_path.pop().is_none() {
                    return Err(errors.join("; "));
                }
            };
            log::debug!("content fit certificate: {}", self.prop_string(cert));
            p = if occ_path.is_empty() {
                self.trans(p, cert)?
            } else {
                self.congr_at(p, &occ_path, cert)?
            };
            p = self.content_form(p);
            if self.out.edge(p).rhs == content {
                return Err(format!(
                    "the certificate for ${x} in {} changed nothing: {}\n{}",
                    self.out_string(sub),
                    self.prop_string(cert),
                    self.out.proof_to_string(cert)
                ));
            }
        }
        Err("content fitting did not converge".into())
    }

    pub(super) fn subterm_at(&self, term: TermId, path: &[usize]) -> LiftResult<TermId> {
        let mut t = term;
        for &j in path {
            t = match self.out.term_dag.get(t) {
                Term::App(_, kids) => *kids.get(j).ok_or("path out of range")?,
                _ => return Err("path into a non-application".into()),
            };
        }
        Ok(t)
    }

    fn slot_pairs(
        &self,
        a: TermId,
        b: TermId,
        path: &mut Vec<usize>,
        out: &mut Vec<(Vec<usize>, i64, i64)>,
    ) -> LiftResult<()> {
        let dag = &self.out.term_dag;
        match (dag.get(a).clone(), dag.get(b).clone()) {
            (Term::Var(_), Term::Var(_)) => {
                match (
                    super::super::terms::slot_of(dag, a),
                    super::super::terms::slot_of(dag, b),
                ) {
                    (Some(x), Some(y)) => {
                        out.push((path.clone(), x, y));
                        Ok(())
                    }
                    _ if a == b => Ok(()),
                    _ => Err(format!(
                        "cannot fit {} to {}",
                        self.out_string(a),
                        self.out_string(b)
                    )),
                }
            }
            (Term::Lit(x), Term::Lit(y)) if x == y => Ok(()),
            (Term::App(h1, c1), Term::App(h2, c2)) if h1 == h2 && c1.len() == c2.len() => {
                for (j, (x, y)) in c1.iter().zip(c2.iter()).enumerate() {
                    path.push(j);
                    self.slot_pairs(*x, *y, path, out)?;
                    path.pop();
                }
                Ok(())
            }
            _ => Err(format!(
                "cannot fit {} to {}",
                self.out_string(a),
                self.out_string(b)
            )),
        }
    }

    pub(super) fn claim(
        &mut self,
        root: ProofId,
        claim: &Claim,
        query: &ProofNames,
        roots: [&str; 2],
    ) -> LiftResult<ViewId> {
        let frame = matched_frame(self.egg, root, query)?;
        let coset = Self::coset_symmetry(&frame, roots)?;
        let root = query_firing(self.egg, root, &query.frame)?;
        let proof = self.egg.get(root).clone();
        let Justification::Rule {
            premise_proofs,
            substitution,
            ..
        } = proof.justification().clone()
        else {
            unreachable!("query_firing returns a rule firing")
        };
        let classes = roots.map(|root| {
            query
                .classes
                .get(root)
                .ok_or_else(|| format!("no class binding for claim root {root}"))
        });
        let [class_a, class_b] = classes;
        let cls_a = self.sub(&substitution, class_a?)?;
        let cls_b = self.sub(&substitution, class_b?)?;
        let bridges = HashMap::default();
        let side = |i: usize| -> LiftResult<ExpandCtx<'_>> {
            let names = query.patterns.get(i).ok_or("missing claim pattern names")?;
            Ok(ExpandCtx {
                prems: &premise_proofs,
                subst: &substitution,
                classes: query.classes.clone(),
                readings: query.readings.clone(),
                names: names.iter().cloned().collect(),
                bridges: &bridges,
            })
        };
        let src_a = self
            .program
            .refresh_binders(&mut self.out.term_dag, claim.lhs);
        let src_b = self
            .program
            .refresh_binders(&mut self.out.term_dag, claim.rhs);
        let ctx_a = side(0)?;
        let Expansion {
            proof: pa,
            occurrences: occ_a,
            ..
        } = self.expand(cls_a, src_a, &[], &ctx_a, HashMap::default())?;
        let pa = self.fit(pa, src_a, &occ_a)?; // cls_a = ·src_a
        let ctx_b = side(1)?;
        let Expansion {
            proof: pb,
            occurrences: occ_b,
            ..
        } = self.expand(cls_b, src_b, &[], &ctx_b, HashMap::default())?;
        for (path, o) in &occ_b {
            log::debug!(
                "claim side b occurrence {path:?}: {}",
                self.egg_string(o.cls)
            );
        }
        let pb = self.fit(pb, src_b, &occ_b)?; // cls_b = ·src_b
        let e = if cls_a == cls_b {
            let t = self.dec(cls_a)?;
            self.reflexive(t)?
        } else {
            let prem = premise_proofs
                .iter()
                .copied()
                .find(|p| {
                    let pr = self.egg.get(*p);
                    (pr.lhs(), pr.rhs()) == (cls_a, cls_b)
                })
                .ok_or("the claim has no proof of its class equality")?;
            self.eq(prem)?
        };
        let sa = self.out.sym(pa);
        let left = self.trans(sa, e)?;
        let result = self.trans(left, pb)?;
        self.finish_claim(
            result,
            pb,
            claim,
            cls_a,
            &premise_proofs,
            Some(&coset),
            &occ_b,
        )
    }

    /// `result: src_a = M·src_b` says what the claim says once `M` leaves the
    /// free slots of `src_b` alone; redundant slots and the symmetry `coset-same`
    /// chose can fix it.
    #[allow(clippy::too_many_arguments)]
    fn finish_claim(
        &mut self,
        result: ViewId,
        pb: ViewId,
        claim: &Claim,
        cls_a: TermId,
        premise_proofs: &[ProofId],
        coset: Option<&SlotMap>,
        occ_b: &HashMap<Vec<usize>, Occurrence>,
    ) -> LiftResult<ViewId> {
        if claim.kind == super::super::format::ClaimKind::RenamingEq {
            return Ok(result);
        }
        let src_b = self.out.edge(pb).rhs;
        let src_a = self.out.edge(result).lhs;
        let free = self.program.free_slots(&self.out.term_dag, src_b);
        let free_a = self.program.free_slots(&self.out.term_dag, src_a);
        let result = self.fix_redundant(result, pb, src_b, &free)?;
        let result = match self.fit_content(result, src_b, occ_b) {
            Ok(r) => r,
            Err(e) => {
                log::debug!("content fit of the claim failed: {e}");
                result
            }
        };
        let prop = self.out.normalize(self.out.edge(result).clone());
        if !prop.renaming.moves_any(&free) || !prop.renaming.moves_any(&free_a) {
            return Ok(result);
        }
        // try the symmetry coset-same picked, in either direction
        if let Some(g) = coset {
            let grp_proof = premise_proofs
                .iter()
                .copied()
                .find(|p| {
                    let t = self.egg.get(*p).lhs();
                    self.app(t).is_some_and(|(h, a)| {
                        h.starts_with("EclassGroup_") && a.first() == Some(&cls_a)
                    })
                })
                .ok_or("claim without a group row")?;
            let t = self.dec(cls_a)?;
            let mut notes: Vec<String> = vec![];
            for cand in [g.clone(), inverse(g)] {
                let s = match self.symmetry(cls_a, &cand, grp_proof) {
                    Ok(s) => s,
                    Err(e) => {
                        notes.push(format!("symmetry {}: {e}", slot_map_string(&cand)));
                        continue;
                    }
                };
                {
                    // insert the symmetry where the chain passes through the class
                    let Some(at) = self.known.get(&t).copied() else {
                        continue;
                    };
                    let _ = at;
                    // rebuild: result = (src_a = ·cls_a) ; sym ; (cls_a = ·src_b)
                    let to_class = self.chain_to(result, t);
                    let Some((left, right)) = to_class else {
                        continue;
                    };
                    let left = self.trans(left, s)?;
                    let r = self.trans(left, right)?;
                    let r = self.fix_redundant(r, pb, src_b, &free)?;
                    // a redundant slot the symmetry exposed, as on the main path
                    let r = match self.fit_content(r, src_b, occ_b) {
                        Ok(r) => r,
                        Err(e) => {
                            log::debug!("content fit after the symmetry failed: {e}");
                            r
                        }
                    };
                    let prop = self.out.normalize(self.out.edge(r).clone());
                    if !prop.renaming.moves_any(&free) || !prop.renaming.moves_any(&free_a) {
                        return Ok(r);
                    }
                    notes.push(format!(
                        "with symmetry {}: {}",
                        slot_map_string(&cand),
                        self.prop_string(r)
                    ));
                }
            }
            return Err(format!(
                "the claim's proof came out as {} which moves a free slot of {} ({})",
                self.prop_string(result),
                self.out_string(src_b),
                notes.join("; ")
            ));
        }
        Err(format!(
            "the claim's proof came out as {} which moves a free slot of {}",
            self.prop_string(result),
            self.out_string(src_b)
        ))
    }

    /// Split a transitivity chain at the proof whose right-hand side is `mid`:
    /// `(lhs = ·mid, mid = ·rhs)`.
    fn chain_to(&mut self, proof: ViewId, mid: TermId) -> Option<(ViewId, ViewId)> {
        match self.out.chain(proof) {
            Some((a, b)) => {
                if self.out.edge(a).rhs == mid {
                    return Some((a, b));
                }
                if let Some((a1, a2)) = self.chain_to(a, mid) {
                    let right = self.out.trans(a2, b).ok()?;
                    return Some((a1, right));
                }
                if let Some((b1, b2)) = self.chain_to(b, mid) {
                    let left = self.out.trans(a, b1).ok()?;
                    return Some((left, b2));
                }
                None
            }
            _ => None,
        }
    }

    /// Where `result: src_a = M·src_b` moves a free slot `s` of `src_b` to a slot
    /// absent from `src_b`, and the class term `pb` reaches `src_b` through lacks
    /// both, the slot is redundant: `src_b = (s u)·src_b` follows, and composing it
    /// in fixes `s`.
    fn fix_redundant(
        &mut self,
        mut result: ViewId,
        pb: ViewId,
        src_b: TermId,
        free: &BTreeSet<i64>,
    ) -> LiftResult<ViewId> {
        let src_slots = all_slots(&self.out.term_dag, src_b);
        let to_class = self.out.sym(pb); // src_b = ·cls_b
        for _ in 0..free.len() + 1 {
            let m = self.out.normalize(self.out.edge(result).clone()).renaming;
            let Some(&s) = free.iter().find(|s| m.apply(**s) != **s) else {
                return Ok(result);
            };
            let u = m.inverse().apply(s);
            if src_slots.contains(&u) {
                return Ok(result);
            }
            let tau = Renaming::new([(s, u), (u, s)]).unwrap();
            let renamed = self.rename_both(to_class, &tau); // τ·src_b = ·cls_b
            let (p1, p2) = (
                self.out.normalize(self.out.edge(to_class).clone()),
                self.out.normalize(self.out.edge(renamed).clone()),
            );
            if p1.renaming != p2.renaming || p1.rhs != p2.rhs {
                return Ok(result);
            }
            let back = self.out.sym(renamed);
            let cert = self.trans(to_class, back)?; // src_b = ·(τ·src_b)
            let cert = self.out.reframe(cert, tau.inverse()); // src_b = τ·src_b
            let cert = self.note(cert);
            result = self.trans(result, cert)?;
        }
        Ok(result)
    }

    /// The group element relating the roots in their shared query frame.
    fn coset_symmetry(frame: &Fr, roots: [&str; 2]) -> LiftResult<SlotMap> {
        let a = frame.ren(roots[0]).ok_or("claim frame has no left root")?;
        let b = frame.ren(roots[1]).ok_or("claim frame has no right root")?;
        Ok(compose(&inverse(&b), &a))
    }
}
