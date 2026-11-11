//! Align lifted equalities with the original query.

use super::*;

impl SlotLifter<'_, NativeProofs<'_>> {
    /// Align a built head using the supports of its input occurrences. The
    /// shared coordinates are determined by supported slots and written slot
    /// arguments; each input's remaining names are transported independently.
    pub(super) fn align_occurrences(
        &mut self,
        proof: ViewId,
        target: TermId,
        occurrences: &HashMap<Vec<usize>, Occurrence>,
        reframe: bool,
    ) -> LiftResult<ViewId> {
        let mut proof = self.content_form(proof);
        let mut content = self.out.edge(proof).rhs;
        if content == target {
            return Ok(proof);
        }
        let requested = target;
        let mut target = target;
        if !reframe {
            (content, target) =
                self.program
                    .canonical_binders(&mut self.out.term_dag, content, target);
            let ordinary = self.out.proof(proof);
            let ordinary = self.out.alpha(ordinary, content);
            proof = self.out.plain(ordinary);
        }
        if reframe && let Some(coordinates) = self.term_coordinates(content, target) {
            let proof = self.out.reframe(proof, coordinates);
            let renaming = self.out.edge(proof).renaming.clone();
            let actual = rename(&mut self.out.term_dag, &renaming, target);
            let ordinary = self.out.proof(proof);
            let ordinary = self.out.alpha(ordinary, actual);
            return Ok(self.out.view(ordinary, target, renaming));
        }
        let mut opaque = HashMap::default();
        let mut coordinates = Vec::new();
        let mut pending = vec![(content, target, Vec::new())];
        while let Some((from, to, path)) = pending.pop() {
            if let Some(occurrence) = occurrences.get(&path) {
                let class = self.dec(occurrence.cls)?;
                let (basis, class_coordinates) = match occurrence.row {
                    Some((_, row)) => {
                        let row = self.out.edge(row);
                        (row.rhs, row.renaming.inverse())
                    }
                    None => (class, Renaming::identity()),
                };
                if let Some(from) = self.term_coordinates(basis, from)
                    && let Some(to) = self.term_coordinates(basis, to)
                {
                    let mut slots = self.program.free_slots(&self.out.term_dag, class);
                    if let Some(support) = occurrence.support {
                        let support = self.support_slots(support)?;
                        slots.retain(|slot| support.contains(slot));
                    }
                    coordinates.extend(slots.into_iter().map(|slot| {
                        (
                            from.apply(class_coordinates.apply(slot)),
                            to.apply(class_coordinates.apply(slot)),
                        )
                    }));
                    opaque.insert(path, *occurrence);
                    continue;
                }
            }
            match (self.out.term_dag.get(from), self.out.term_dag.get(to)) {
                (Term::App(a, left), Term::App(b, right))
                    if a == b && left.len() == right.len() =>
                {
                    pending.extend(left.iter().zip(right).enumerate().map(|(i, (&a, &b))| {
                        let mut path = path.clone();
                        path.push(i);
                        (a, b, path)
                    }));
                }
                (Term::Var(_), Term::Var(_)) => {
                    let a = slot_of(&self.out.term_dag, from).ok_or("non-slot in built head")?;
                    let b = slot_of(&self.out.term_dag, to).ok_or("non-slot in encoded head")?;
                    coordinates.push((a, b));
                }
                (a, b) if a == b => {}
                _ => return Err("constructed head and source instance differ in shape".into()),
            }
        }
        let coordinates = Renaming::completing(coordinates)
            .ok_or("constructed head identifies distinct supported coordinates")?;
        if reframe {
            proof = self.out.reframe(proof, coordinates);
        } else if !coordinates.is_identity() {
            return Err(format!(
                "recorded occurrence supports require a nonidentity coordinate change {coordinates}"
            ));
        }
        let mut paths: Vec<_> = opaque.keys().collect();
        paths.sort();
        for path in paths {
            let from = self.subterm_at(self.out.edge(proof).rhs, path)?;
            let to = self.subterm_at(target, path)?;
            if from == to {
                continue;
            }
            let occurrence = opaque[path];
            let class = self.dec(occurrence.cls)?;
            let (basis, class_coordinates) = match occurrence.row {
                Some((_, row)) => {
                    let row = self.out.edge(row);
                    (row.rhs, row.renaming.inverse())
                }
                None => (class, Renaming::identity()),
            };
            let from_coordinates = self
                .term_coordinates(basis, from)
                .ok_or("built occurrence differs from its input class")?;
            let to_coordinates = self
                .term_coordinates(basis, to)
                .ok_or("encoded occurrence differs from its input class")?;
            let permutation = class_coordinates
                .inverse()
                .compose(&from_coordinates.inverse())
                .compose(&to_coordinates)
                .compose(&class_coordinates);
            let mut certificate =
                if permutation.moves_any(&self.program.free_slots(&self.out.term_dag, class)) {
                    let support = occurrence
                        .support
                        .ok_or("built input lacks its recorded support")?;
                    self.support_permutation(support, occurrence.cls, &permutation)?
                } else {
                    let proof = self.reflexive(class)?;
                    let target = rename(&mut self.out.term_dag, &permutation, class);
                    let proof = self.out.proof(proof);
                    let proof = self.out.alpha(proof, target);
                    self.out.view(proof, class, permutation)
                };
            if let Some((_, row)) = occurrence.row {
                let back = self.out.sym(row);
                certificate = self.transport(certificate, back)?;
            }
            certificate = self.rename_both(certificate, &from_coordinates);
            let mut ordinary = self.out.proof(certificate);
            if self.out.proposition(ordinary).lhs != from {
                let reverse = self.out.plain(ordinary);
                let reverse = self.out.sym(reverse);
                ordinary = self.out.proof(reverse);
                ordinary = self.out.alpha(ordinary, from);
                let reverse = self.out.plain(ordinary);
                let reverse = self.out.sym(reverse);
                ordinary = self.out.proof(reverse);
            }
            if self.out.proposition(ordinary).rhs != to {
                ordinary = self.out.alpha(ordinary, to);
            }
            let certificate = self.out.plain(ordinary);
            proof = if path.is_empty() {
                self.trans(proof, certificate)?
            } else {
                self.congr_at(proof, path, certificate)?
            };
        }
        if self.out.edge(proof).rhs != target {
            return Err("recorded input transports did not produce the constructed head".into());
        }
        if !reframe && target != requested {
            let ordinary = self.out.proof(proof);
            let ordinary = self.out.alpha(ordinary, requested);
            proof = self.out.plain(ordinary);
        }
        Ok(proof)
    }

    pub(super) fn term_coordinates(&mut self, from: TermId, to: TermId) -> Option<Renaming> {
        if self.term_shapes.get(&self.out.term_dag, from)
            != self.term_shapes.get(&self.out.term_dag, to)
        {
            return None;
        }
        term_renaming(&self.out.term_dag, &[(from, to)]).or_else(|| {
            self.program
                .renaming_between(&mut self.out.term_dag, from, to)
        })
    }

    pub(super) fn fit(
        &mut self,
        proof: ViewId,
        target: TermId,
        occurrences: &HashMap<Vec<usize>, Occurrence>,
    ) -> LiftResult<ViewId> {
        self.align_occurrences(proof, target, occurrences, true)
    }

    pub(super) fn fit_content(
        &mut self,
        proof: ViewId,
        target: TermId,
        occurrences: &HashMap<Vec<usize>, Occurrence>,
    ) -> LiftResult<ViewId> {
        self.align_occurrences(proof, target, occurrences, false)
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

    pub(super) fn claim(
        &mut self,
        root: ProofId,
        claim: &Claim,
        query: &ProofNames,
        roots: [&str; 2],
        patterns: [TermId; 2],
    ) -> LiftResult<ViewId> {
        let frame = matched_frame(self.egg.store, root, query)?;
        let coset = Self::coset_symmetry(&frame, roots)?;
        let root = query_firing(self.egg.store, root, &query.frame)?;
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
        let selected = self.selected_readings(root, None, &substitution)?;
        let side = |i: usize| -> LiftResult<ExpandCtx<'_>> {
            let names = query.patterns.get(i).ok_or("missing claim pattern names")?;
            Ok(ExpandCtx {
                firing: root,
                root_binding: query.classes.get(roots[i]).cloned(),
                prems: &premise_proofs,
                subst: &substitution,
                readings: query.readings.clone(),
                labels: &query.atoms,
                selected: &selected,
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
        let patterns = patterns.map(|pattern| {
            self.program
                .refresh_binders(&mut self.out.term_dag, pattern)
        });
        let ctx_a = side(0)?;
        let Expansion {
            proof: pa,
            occurrences: occ_a,
            ..
        } = self.expand(cls_a, patterns[0], &[], &ctx_a, HashMap::default())?;
        let pa = self.fit(pa, src_a, &occ_a)?; // cls_a = ·src_a
        let ctx_b = side(1)?;
        let Expansion {
            proof: pb,
            occurrences: occ_b,
            ..
        } = self.expand(cls_b, patterns[1], &[], &ctx_b, HashMap::default())?;
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
        let mut left = self.out.sym(pa);
        if claim.kind != super::super::format::ClaimKind::RenamingEq && !is_identity(&coset) {
            let group = self.group_premise(&premise_proofs, cls_a)?;
            let symmetry = self.symmetry(cls_a, &inverse(&coset), group)?;
            left = self.trans(left, symmetry)?;
        }
        let left = self.trans(left, e)?;
        let result = self.trans(left, pb)?;
        self.finish_claim(result, pb, claim, &occ_b)
    }

    /// Finish a claim after applying the symmetry selected by its query frame.
    fn finish_claim(
        &mut self,
        result: ViewId,
        pb: ViewId,
        claim: &Claim,
        occ_b: &HashMap<Vec<usize>, Occurrence>,
    ) -> LiftResult<ViewId> {
        if claim.kind == super::super::format::ClaimKind::RenamingEq {
            return Ok(result);
        }
        let src_b = self.out.edge(pb).rhs;
        let src_a = self.out.edge(result).lhs;
        let free = self.program.free_slots(&self.out.term_dag, src_b);
        let free_a = self.program.free_slots(&self.out.term_dag, src_a);
        let prop = self.out.normalize(self.out.edge(result).clone());
        if !prop.renaming.moves_any(&free) || !prop.renaming.moves_any(&free_a) {
            return Ok(result);
        }
        let result = self.fit_content(result, src_b, occ_b)?;
        let prop = self.out.normalize(self.out.edge(result).clone());
        if !prop.renaming.moves_any(&free) || !prop.renaming.moves_any(&free_a) {
            return Ok(result);
        }
        Err(format!(
            "the claim's proof came out as {} which moves a free slot of {}",
            self.prop_string(result),
            self.out_string(src_b)
        ))
    }

    /// The group element relating the roots in their shared query frame.
    fn coset_symmetry(frame: &Fr, roots: [&str; 2]) -> LiftResult<SlotMap> {
        let a = frame.ren(roots[0]).ok_or("claim frame has no left root")?;
        let b = frame.ren(roots[1]).ok_or("claim frame has no right root")?;
        Ok(compose(&inverse(&b), &a))
    }
}
