//! Derive surface equalities from class groups.

use super::*;

impl SlotLifter<'_> {
    /// `dec(c) = g·dec(c)` for an element `g` of `c`'s group, through the proof
    /// of the group row.
    pub(super) fn symmetry(
        &mut self,
        c: TermId,
        g: &SlotMap,
        grp_proof: ProofId,
    ) -> LiftResult<ViewId> {
        self.symmetry_inner(c, g, grp_proof).map_err(|e| {
            format!(
                "symmetry {} of {} through {}: {e}",
                slot_map_string(g),
                self.egg_string(c),
                self.egg_string(self.egg.get(grp_proof).lhs())
            )
        })
    }

    fn symmetry_inner(&mut self, c: TermId, g: &SlotMap, grp_proof: ProofId) -> LiftResult<ViewId> {
        if is_identity(g) {
            let t = self.dec(c)?;
            return self.reflexive(t);
        }
        let proof = self.egg.get(grp_proof).clone();
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
                    RuleKind::SeedIdentity => {
                        Err(format!("{} is not the identity", slot_map_string(g)))
                    }
                    RuleKind::SelfSymmetry | RuleKind::SelfEdgeSymmetry => {
                        let p = self.eq(prems[0])?;
                        self.symmetry_matches(p, c, g)
                    }
                    RuleKind::NodeSymmetry => {
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
                        self.node_symmetry(row_eq, row, &groups, c, g)
                    }
                    RuleKind::GroupRestore => self.symmetry(c, g, prems[0]),
                    RuleKind::GroupEmpty => Err("an emptied group has no elements".into()),
                    RuleKind::GroupShrink => {
                        let source = prems[0];
                        let elements = self
                            .group_of_row(self.egg.get(source).lhs())?
                            .into_iter()
                            .map(|element| (element, source))
                            .collect::<Vec<_>>();
                        let slots = self.slot_map(self.sub(&subst, "_cs")?)?;
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
                if function.starts_with("GroupReplace_") {
                    return self.symmetry(c, g, new_proof);
                }
                let mut elements = Vec::new();
                for side in [old_proof, new_proof] {
                    let maps = self.group_of_row(self.egg.get(side).lhs())?;
                    if maps.contains(g) {
                        return self.symmetry(c, g, side);
                    }
                    elements.extend(maps.into_iter().map(|element| (element, side)));
                }
                self.product_symmetry(c, g, &elements, None)
            }
            Justification::Congr {
                proof: base,
                child_proof,
                ..
            } => {
                // the row's class moved: c0 = c; symmetries of dec(c0) transport
                let (base, child_proof) = (*base, *child_proof);
                let c0 = {
                    let t = self.egg.get(base).lhs();
                    self.app(t).ok_or("not a group row")?.1[0]
                };
                let s0 = self.symmetry(c0, g, base)?;
                let e = self.eq(child_proof)?; // c0 = n·c
                let se = self.out.sym(e);
                let p = self.trans(se, s0)?;
                self.trans(p, e)
            }
            Justification::Trans(a, b) => {
                // a reflexive row restated through a congruence: use the base
                let (a, b) = (*a, *b);
                self.symmetry(c, g, a).or_else(|_| self.symmetry(c, g, b))
            }
            Justification::Sym(a) => self.symmetry(c, g, *a),
            Justification::Fiat => Err("a group stated by fiat".into()),
            other => Err(format!("no symmetry provenance through {other:?}")),
        }
    }

    /// The premise stating `cls`'s group row.
    pub(super) fn group_premise(&self, prems: &[ProofId], cls: TermId) -> LiftResult<ProofId> {
        prems
            .iter()
            .copied()
            .find(|q| {
                let t = self.egg.get(*q).lhs();
                self.app(t)
                    .is_some_and(|(h, a)| h.starts_with("EclassGroup_") && a.first() == Some(&cls))
            })
            .ok_or_else(|| format!("no group premise for {}", self.egg_string(cls)))
    }

    /// The symmetries a group row's provenance states outright, as proofs
    /// `dec(c) = m̂·dec(c)` with their full renamings: the rows that equate the
    /// class with a renaming of itself, before restriction to its slots.
    pub(super) fn symmetry_sources(&mut self, grp_proof: ProofId) -> LiftResult<Vec<ViewId>> {
        let proof = self.egg.get(grp_proof).clone();
        match proof.justification().clone() {
            Justification::Rule {
                name,
                premise_proofs: prems,
                substitution,
            } => match rule_kind(self.program, &name) {
                RuleKind::SelfSymmetry | RuleKind::SelfEdgeSymmetry => {
                    let p = self.eq(prems[0])?;
                    Ok(vec![p])
                }
                RuleKind::NodeSymmetry => {
                    let c = self.sub(&substitution, "_c")?;
                    let group = self.group(self.sub(&substitution, "_syms")?)?;
                    group
                        .iter()
                        .filter(|g| !is_identity(g))
                        .map(|g| self.symmetry(c, g, grp_proof))
                        .collect()
                }
                RuleKind::GroupRestore | RuleKind::GroupShrink => self.symmetry_sources(prems[0]),
                _ => Ok(vec![]),
            },
            Justification::MergeFn {
                function,
                old_proof,
                new_proof,
            } => {
                if function.starts_with("GroupReplace_") {
                    return self.symmetry_sources(new_proof);
                }
                let mut out = self.symmetry_sources(old_proof)?;
                out.extend(self.symmetry_sources(new_proof)?);
                Ok(out)
            }
            Justification::Congr {
                proof: base,
                child_proof,
                ..
            } => {
                let sources = self.symmetry_sources(base)?;
                let e = self.eq(child_proof)?; // c0 = n·c
                let mut out = vec![];
                for s0 in sources {
                    let se = self.out.sym(e);
                    let p = self.trans(se, s0)?;
                    out.push(self.trans(p, e)?);
                }
                Ok(out)
            }
            Justification::Trans(a, b) => {
                let mut out = self.symmetry_sources(a)?;
                out.extend(self.symmetry_sources(b)?);
                Ok(out)
            }
            Justification::Sym(a) => self.symmetry_sources(a),
            _ => Ok(vec![]),
        }
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
        // Find the word on the surviving slots, retaining its original witnesses.
        let mut seen: BTreeMap<SlotMap, Vec<usize>> = BTreeMap::new();
        let mut frontier: Vec<SlotMap> = vec![];
        for (i, e) in generators.iter().enumerate() {
            if seen.insert(e.clone(), vec![i]).is_none() {
                frontier.push(e.clone());
            }
        }
        while !seen.contains_key(g) && !frontier.is_empty() {
            let mut next = vec![];
            for h in &frontier {
                for (i, e) in generators.iter().enumerate() {
                    let prod = compose(h, e);
                    if !seen.contains_key(&prod) {
                        let mut path = seen[h].clone();
                        path.push(i);
                        seen.insert(prod.clone(), path);
                        next.push(prod);
                    }
                }
            }
            frontier = next;
        }
        let path = seen
            .get(g)
            .cloned()
            .ok_or_else(|| format!("{} is not generated by the group", slot_map_string(g)))?;
        let mut proof: Option<ViewId> = None;
        for i in path {
            let s = self.symmetry(c, &elements[i].0, elements[i].1)?;
            proof = Some(match proof {
                None => s,
                Some(p) => self.trans(p, s)?,
            });
        }
        let proof = proof.ok_or("empty symmetry product")?;
        self.symmetry_matches(proof, c, g)
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
                    edges.push(self.slot_map(args[i])?);
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
        let own = shape(&edges);
        for (variant, gs) in readings(&edges, &group_values) {
            let spelled = shape(&variant);
            if spelled.edges != own.edges {
                continue;
            }
            let symmetry: SlotMap = own
                .back
                .iter()
                .filter_map(|(n, &slot)| spelled.back.get(n).map(|&image| (slot, image)))
                .collect();
            if !g.iter().all(|(k, v)| symmetry.get(k) == Some(v)) {
                continue;
            }
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
            return self.symmetry_matches(full, c, g).map_err(|_| {
                format!(
                    "node symmetry of {} came out as {}",
                    self.out_string(t),
                    self.prop_string(full)
                )
            });
        }
        Err(format!(
            "no reading of {} gives the symmetry {}",
            self.egg_string(row),
            slot_map_string(g)
        ))
    }

    /// Every proof in the egglog store of a group row of `cls`.
    pub(super) fn group_proofs(&mut self, cls: TermId) -> Vec<ProofId> {
        self.group_index
            .get_or_insert_with(|| row_proofs(self.egg, "EclassGroup_"))
            .get(&cls)
            .cloned()
            .unwrap_or_default()
    }

    /// Walk from a `Reading` or `CosetReps` row's proof to the `EclassGroup` row
    /// its elements came from.
    pub(super) fn group_row_behind(&self, proof: ProofId) -> LiftResult<ProofId> {
        let p = self.egg.get(proof);
        let head = self.app(p.lhs()).map(|(h, _)| h).unwrap_or("");
        if head.starts_with("EclassGroup_") {
            return Ok(proof);
        }
        match p.justification() {
            Justification::Rule {
                premise_proofs,
                name,
                ..
            } => {
                let kind = rule_kind(self.program, name);
                match kind {
                    RuleKind::ReadingSmall | RuleKind::ReadingBig => self.group_row_behind(
                        *premise_proofs
                            .iter()
                            .find(|q| {
                                let t = self.egg.get(**q).lhs();
                                self.app(t)
                                    .is_some_and(|(h, _)| h.starts_with("CosetReps_"))
                            })
                            .ok_or("reading without its coset row")?,
                    ),
                    RuleKind::CosetReadings | RuleKind::CosetRepair => self.group_row_behind(
                        *premise_proofs
                            .iter()
                            .find(|q| {
                                let t = self.egg.get(**q).lhs();
                                self.app(t)
                                    .is_some_and(|(h, _)| h.starts_with("EclassGroup_"))
                            })
                            .ok_or("coset row without its group row")?,
                    ),
                    other => Err(format!("no group behind rule {other:?}")),
                }
            }
            Justification::MergeFn { new_proof, .. } => self.group_row_behind(*new_proof),
            Justification::Congr { proof, .. } => self.group_row_behind(*proof),
            Justification::Trans(a, _) | Justification::Sym(a) => self.group_row_behind(*a),
            other => Err(format!("no group behind {other:?}")),
        }
    }
}
