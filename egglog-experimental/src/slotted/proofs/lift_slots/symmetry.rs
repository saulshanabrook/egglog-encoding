//! Derive surface equalities from class groups.

use super::*;

impl SlotLifter<'_, NativeProofs<'_>> {
    /// `dec(c) = g·dec(c)` for an element `g` of `c`'s group, through the proof
    /// of a group or selected-reading row, retaining class-key congruences.
    pub(super) fn symmetry(
        &mut self,
        c: TermId,
        g: &SlotMap,
        grp_proof: ProofId,
    ) -> LiftResult<ViewId> {
        self.symmetry_side(c, g, grp_proof, true, None)
            .map_err(|e| {
                format!(
                    "symmetry {} of {} through {}: {e}",
                    slot_map_string(g),
                    self.egg_string(c),
                    self.egg_string(self.egg.get(grp_proof).lhs())
                )
            })
    }

    /// Prove a fresh swap for a slot outside the recorded element's domain.
    pub(super) fn group_certificate(
        &mut self,
        c: TermId,
        g: &SlotMap,
        proof: ProofId,
        slot: i64,
        fresh: i64,
    ) -> LiftResult<ViewId> {
        if g.contains_key(&slot) {
            return Err("the group element retains the requested redundant slot".into());
        }
        self.symmetry_side(c, g, proof, true, Some((slot, fresh)))
    }

    fn symmetry_side(
        &mut self,
        c: TermId,
        g: &SlotMap,
        grp_proof: ProofId,
        rhs: bool,
        redundant: Option<(i64, i64)>,
    ) -> LiftResult<ViewId> {
        if redundant.is_some() {
            return self.symmetry_replay(c, g, grp_proof, rhs, redundant);
        }
        let key = (grp_proof, rhs, c, g.clone());
        if let Some(&proof) = self.symmetry_memo.get(&key) {
            return Ok(proof);
        }
        let proof = self.symmetry_replay(c, g, grp_proof, rhs, None)?;
        self.symmetry_memo.insert(key, proof);
        Ok(proof)
    }

    fn symmetry_replay(
        &mut self,
        c: TermId,
        g: &SlotMap,
        grp_proof: ProofId,
        rhs: bool,
        redundant: Option<(i64, i64)>,
    ) -> LiftResult<ViewId> {
        let proof = self.egg.get(grp_proof).clone();
        match proof.justification() {
            Justification::Sym(inner) => {
                return self.symmetry_side(c, g, *inner, !rhs, redundant);
            }
            Justification::Trans(a, b) => {
                return self.symmetry_side(c, g, if rhs { *b } else { *a }, rhs, redundant);
            }
            Justification::Congr { proof: base, .. } if !rhs => {
                return self.symmetry_side(c, g, *base, false, redundant);
            }
            _ => {}
        }
        match proof.justification() {
            Justification::Rule {
                name,
                premise_proofs,
                substitution,
            } => {
                let name = name.clone();
                let prems = premise_proofs.clone();
                let subst = substitution.clone();
                match rule_kind(self.program, &name) {
                    kind @ (RuleKind::ReadingSmall
                    | RuleKind::ReadingBig
                    | RuleKind::CosetReadings
                    | RuleKind::CosetRepair) => {
                        let prefix =
                            if matches!(kind, RuleKind::ReadingSmall | RuleKind::ReadingBig) {
                                "CosetReps_"
                            } else {
                                "EclassGroup_"
                            };
                        let source = prems
                            .into_iter()
                            .find(|p| {
                                self.app(self.egg.get(*p).rhs())
                                    .is_some_and(|(head, _)| head.starts_with(prefix))
                            })
                            .ok_or_else(|| format!("reading has no {prefix} premise"))?;
                        self.symmetry_side(c, g, source, true, redundant)
                    }
                    RuleKind::SeedIdentity => {
                        if let Some((slot, fresh)) = redundant {
                            return self.cert_from(prems[0], c, slot, fresh);
                        }
                        if !is_identity(g) {
                            return Err(format!("{} is not the identity", slot_map_string(g)));
                        }
                        let proof = self.support_class(prems[0], true)?;
                        self.symmetry_matches(proof, c, g)
                    }
                    RuleKind::SelfSymmetry | RuleKind::SelfEdgeSymmetry => {
                        let p = self.eq(prems[0])?;
                        if let Some((slot, fresh)) = redundant {
                            let support = self.support_premise(&prems, c)?;
                            let slots = self.support_slots(Support::new(support))?;
                            if !slots.contains(&slot) {
                                return self.cert_from(support, c, slot, fresh);
                            }
                            let m = self.slot_map(self.sub(&subst, "_m")?)?;
                            if !m.contains_key(&slot) {
                                return self.edge_certificate(prems[0], 2, true, slot, fresh);
                            }
                            let renaming = self.out.edge(p).renaming.clone();
                            let certificate = self.cert_from(
                                support,
                                c,
                                renaming.apply(slot),
                                renaming.apply(fresh),
                            )?;
                            let reverse = self.out.sym(p);
                            return self.transport(certificate, reverse);
                        }
                        self.symmetry_matches(p, c, g)
                    }
                    RuleKind::NodeSymmetry => {
                        if let Some((slot, fresh)) = redundant {
                            let support = self.support_premise(&prems, c)?;
                            let slots = self.support_slots(Support::new(support))?;
                            if !slots.contains(&slot) {
                                return self.cert_from(support, c, slot, fresh);
                            }
                            let symmetry = self.symmetry(c, g, grp_proof)?;
                            let renaming = self.out.edge(symmetry).renaming.clone();
                            if slots.contains(&renaming.apply(slot)) {
                                return self.node_certificate(prems[0], slot, fresh);
                            }
                            let certificate = self.cert_from(
                                support,
                                c,
                                renaming.apply(slot),
                                renaming.apply(fresh),
                            )?;
                            let reverse = self.out.sym(symmetry);
                            return self.transport(certificate, reverse);
                        }
                        let row_eq = self.eq(prems[0])?;
                        let row = self.egg.get(prems[0]).rhs();
                        let classes = self.slotted_classes(row)?;
                        let groups: SymmetryPremises = classes
                            .iter()
                            .enumerate()
                            .map(|(k, &class)| {
                                class
                                    .map(|class| {
                                        Ok((
                                            self.sub(&subst, &format!("_g{}", k + 1))?,
                                            self.group_premise(&prems, class)?,
                                        ))
                                    })
                                    .transpose()
                            })
                            .collect::<LiftResult<_>>()?;
                        let slots = self.slot_map(self.sub(&subst, "_cs")?)?;
                        self.node_symmetry(row_eq, row, &groups, c, g, Some(&slots))
                    }
                    RuleKind::GroupRestore => self.symmetry_side(c, g, prems[0], true, redundant),
                    RuleKind::GroupEmpty => Err("an emptied group has no elements".into()),
                    RuleKind::GroupShrink => {
                        let source = prems[0];
                        let elements = self
                            .group_of_row(self.egg.get(source).rhs())?
                            .into_iter()
                            .map(|element| (element, source))
                            .collect::<Vec<_>>();
                        let slots = self.slot_map(self.sub(&subst, "_cs")?)?;
                        if let Some((slot, fresh)) = redundant {
                            let support = self.support_premise(&prems, c)?;
                            return self.product_certificate(c, g, &elements, support, slot, fresh);
                        }
                        self.product_symmetry(c, g, &elements, Some(&slots))
                    }
                    other => Err(format!("no symmetry provenance through {other:?}")),
                }
            }
            Justification::MergeFn {
                function,
                old_proof,
                new_proof,
            } => {
                let (old_proof, new_proof) = (*old_proof, *new_proof);
                if function.starts_with("GroupReplace_") || function.starts_with("CosetReps_") {
                    return self.symmetry_side(c, g, new_proof, true, redundant);
                }
                for side in [old_proof, new_proof] {
                    let maps = self.group_of_row(self.egg.get(side).rhs())?;
                    if maps.contains(g) {
                        return self.symmetry_side(c, g, side, true, redundant);
                    }
                }
                Err("neither operand of the group union contains the recorded element".into())
            }
            Justification::Congr {
                proof: base,
                child_proof,
                child_index,
            } => {
                if *child_index != 0 {
                    return self.symmetry_side(c, g, *base, true, redundant);
                }
                // the row's class moved: c0 = c; symmetries of dec(c0) transport
                let (base, child_proof) = (*base, *child_proof);
                let c0 = {
                    let t = self.egg.get(base).rhs();
                    self.app(t).ok_or("not a group row")?.1[0]
                };
                if let Some((slot, fresh)) = redundant {
                    let e = self.eq(child_proof)?;
                    let renaming = self.out.edge(e).renaming.clone();
                    let certificate = self.symmetry_side(
                        c0,
                        g,
                        base,
                        true,
                        Some((renaming.apply(slot), renaming.apply(fresh))),
                    )?;
                    let se = self.out.sym(e);
                    return self.transport(certificate, se);
                }
                let s0 = self.symmetry(c0, g, base)?;
                let e = self.eq(child_proof)?; // c0 = n·c
                let se = self.out.sym(e);
                let p = self.trans(se, s0)?;
                self.trans(p, e)
            }
            Justification::Trans(..) | Justification::Sym(..) => unreachable!(),
            Justification::Fiat => Err("a group stated by fiat".into()),
            other => Err(format!("no symmetry provenance through {other:?}")),
        }
    }

    /// The premise stating `cls`'s group row.
    pub(super) fn group_premise(&self, prems: &[ProofId], cls: TermId) -> LiftResult<ProofId> {
        self.function_premise(prems, "EclassGroup_", cls)?
            .ok_or_else(|| format!("no group premise for {}", self.egg_string(cls)))
    }

    /// Prove a product of witnessed symmetries, optionally restricted to `slots`.
    pub(super) fn product_symmetry(
        &mut self,
        c: TermId,
        g: &SlotMap,
        elements: &[(SlotMap, ProofId)],
        slots: Option<&SlotMap>,
    ) -> LiftResult<ViewId> {
        let generators: Vec<_> = elements
            .iter()
            .map(|(element, _)| {
                slots.map_or_else(
                    || element.clone(),
                    |slots| compose(slots, &compose(element, slots)),
                )
            })
            .collect();
        use crate::slotted::runtime::group::close_with;

        let mut steps = Vec::new();
        let closed = close_with(&generators, |step| steps.push(step));
        let root = closed
            .iter()
            .position(|element| element.iter().eq(g.iter()))
            .ok_or_else(|| format!("{} is not generated by the group", slot_map_string(g)))?;
        let proof = self.product_step(c, elements, &steps, root, &mut HashMap::default())?;
        self.symmetry_matches(proof, c, g)
    }

    fn product_step(
        &mut self,
        c: TermId,
        elements: &[(SlotMap, ProofId)],
        steps: &[crate::slotted::runtime::group::Composition],
        root: usize,
        lifted: &mut HashMap<usize, ViewId>,
    ) -> LiftResult<ViewId> {
        use crate::slotted::runtime::group::Composition;
        let mut pending = vec![(root, false)];
        while let Some((at, ready)) = pending.pop() {
            if lifted.contains_key(&at) {
                continue;
            }
            let proof = match steps[at] {
                Composition::Input(i) => self.symmetry(c, &elements[i].0, elements[i].1)?,
                Composition::Product(a, b) => {
                    if !ready {
                        pending.extend([(at, true), (b, false), (a, false)]);
                        continue;
                    }
                    self.trans(lifted[&a], lifted[&b])?
                }
            };
            lifted.insert(at, proof);
        }
        Ok(lifted[&root])
    }

    fn product_certificate(
        &mut self,
        c: TermId,
        g: &SlotMap,
        elements: &[(SlotMap, ProofId)],
        support: ProofId,
        mut slot: i64,
        mut fresh: i64,
    ) -> LiftResult<ViewId> {
        let slots: SlotMap = self
            .support_slots(Support::new(support))?
            .into_iter()
            .map(|slot| (slot, slot))
            .collect();
        if !slots.contains_key(&slot) {
            return self.cert_from(support, c, slot, fresh);
        }
        use crate::slotted::runtime::group::{Composition, close_with};
        let generators: Vec<_> = elements
            .iter()
            .map(|(element, _)| compose(&slots, &compose(element, &slots)))
            .collect();
        let mut steps = Vec::new();
        let closed = close_with(&generators, |step| steps.push(step));
        let mut at = closed
            .iter()
            .position(|element| element.iter().eq(g.iter()))
            .ok_or("group closure did not produce its recorded element")?;
        let mut lifted = HashMap::default();
        let mut transport = None;
        let certificate = loop {
            match steps[at] {
                Composition::Input(i) => {
                    let (element, source) = &elements[i];
                    if !slots.contains_key(&slot) {
                        break self.cert_from(support, c, slot, fresh)?;
                    }
                    if !element.contains_key(&slot) {
                        break self.group_certificate(c, element, *source, slot, fresh)?;
                    }
                    let symmetry = self.symmetry(c, element, *source)?;
                    let renaming = self.out.edge(symmetry).renaming.clone();
                    let certificate =
                        self.cert_from(support, c, renaming.apply(slot), renaming.apply(fresh))?;
                    let reverse = self.out.sym(symmetry);
                    break self.transport(certificate, reverse)?;
                }
                Composition::Product(a, b) => {
                    if !closed[b].contains_key(&slot) {
                        at = b;
                        continue;
                    }
                    let symmetry = self.product_step(c, elements, &steps, b, &mut lifted)?;
                    let renaming = self.out.edge(symmetry).renaming.clone();
                    slot = renaming.apply(slot);
                    fresh = renaming.apply(fresh);
                    let reverse = self.out.sym(symmetry);
                    transport = Some(match transport {
                        Some(previous) => self.trans(previous, reverse)?,
                        None => reverse,
                    });
                    at = a;
                }
            }
        };
        match transport {
            Some(transport) => self.transport(certificate, transport),
            None => Ok(certificate),
        }
    }

    /// `p` proves `dec(c) = m·dec(c)`; it is the symmetry `g` when `m` and `g`
    /// agree on the class's slots.
    fn symmetry_matches(&mut self, p: ViewId, c: TermId, g: &SlotMap) -> LiftResult<ViewId> {
        let t = self.dec(c)?;
        let prop = self.out.edge(p).clone();
        if prop.lhs != t || prop.rhs != t {
            return Err(format!(
                "{} is not a symmetry of {}",
                self.prop_string(p),
                self.out_string(t)
            ));
        }
        if g.iter().all(|(k, v)| prop.renaming.apply(*k) == *v) {
            return Ok(p);
        }
        Err(format!(
            "{} does not give the symmetry {}",
            self.prop_string(p),
            slot_map_string(g)
        ))
    }

    /// A symmetry a node gives its class: a reading of the children that spells
    /// the row's canonical edges again.
    pub(super) fn node_symmetry(
        &mut self,
        row_eq: ViewId,
        row: TermId,
        groups: &[Option<(TermId, ProofId)>],
        c: TermId,
        g: &SlotMap,
        slots: Option<&SlotMap>,
    ) -> LiftResult<ViewId> {
        let (head, args) = self.app(row).ok_or("not a row")?;
        let ctor = self
            .program
            .constructors
            .get(head)
            .ok_or("unknown constructor")?
            .clone();
        let mut edges: Vec<SlotMap> = vec![];
        let mut classes: Vec<Option<TermId>> = vec![];
        let mut i = 0;
        for col in &ctor.columns {
            match col {
                ColumnKind::Child => {
                    edges.push(self.slot_map(args[i])?);
                    classes.push(Some(args[i + 1]));
                    i += 2;
                }
                ColumnKind::Var | ColumnKind::Binder => {
                    edges.push(self.slot_column(args[i])?);
                    classes.push(None);
                    i += 1;
                }
                ColumnKind::Payload(_) => i += 1,
            }
        }
        let group_values: Vec<Vec<SlotMap>> = groups
            .iter()
            .map(|group| match group {
                Some((g, _)) => self.group(*g),
                None => Ok(vec![[(0, 0)].into_iter().collect()]),
            })
            .collect::<LiftResult<_>>()?;
        let mut selected = None;
        node_shape_with(
            &edges,
            &group_values,
            |_, _| {},
            |element, readings| {
                let output = slots.map_or_else(
                    || element.clone(),
                    |slots| compose(slots, &compose(element, slots)),
                );
                if selected.is_none() && output == *g {
                    selected = Some((element.clone(), readings.to_vec()));
                }
            },
        );
        let (symmetry, gs) = selected.ok_or("node-shape did not produce its recorded symmetry")?;
        // dec(row) = F(m̂_i·c_i) = F((m̂_i∘ĝ_i)·c_i) = σ·dec(row)
        let mut p = self.reflexive(self.out.edge(row_eq).rhs)?;
        let mut k = 0;
        for (j, col) in ctor.columns.iter().enumerate() {
            if matches!(col, ColumnKind::Payload(_)) {
                continue;
            }
            let gi = &gs[k];
            k += 1;
            if is_identity(gi) {
                continue;
            }
            let (_, gp) = groups[k - 1].ok_or("a rigid port has a nonidentity reading")?;
            let s = self.symmetry(classes[k - 1].ok_or("rigid port has no class")?, gi, gp)?;
            let completion = self.edge_memo[&(row, j)].clone();
            let renamed = self.rename_both(s, &completion);
            p = self.out.congr(p, j, renamed).map_err(|e| e.to_string())?;
            p = self.note(p);
        }
        // the right-hand side is now σ·dec(row) up to fresh names: align its coordinates
        let row_term = self.out.edge(row_eq).rhs;
        let sigma = Renaming::completing(symmetry.iter().map(|(k, v)| (*k, *v)))
            .ok_or("node symmetry is not injective")?;
        let target = rename(&mut self.out.term_dag, &sigma, row_term);
        let aligned = self.align(p, target)?;
        // dec(row) = σ'·(σ·row) → reframe by σ⁻¹ to state it on the row itself
        let r = self.out.reframe(aligned, sigma.inverse());
        let r = self.note(r);
        // and the class is the row
        let s = self.out.sym(row_eq);
        let left = self.trans(row_eq, r)?;
        let full = self.trans(left, s)?;
        let t = self.dec(c)?;
        self.symmetry_matches(full, c, g).map_err(|_| {
            format!(
                "node symmetry of {} came out as {}",
                self.out_string(t),
                self.prop_string(full)
            )
        })
    }
}
